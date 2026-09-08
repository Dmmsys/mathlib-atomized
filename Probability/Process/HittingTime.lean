/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Tactic.AdaptationNote

/-!
# Hitting times

Given a stochastic process, the hitting time provides the first time the process "hits" some
subset of the state space. The hitting time is a stopping time in the case that the time index is
discrete and the process is strongly adapted (this is true in a far more general setting however
we have only proved it for the discrete case so far).

## Main definition

* `MeasureTheory.hittingBtwn u s n m`: the first time a stochastic process `u` enters a set `s`
  after time `n` and before time `m`
* `MeasureTheory.hittingAfter u s n`: the first time a stochastic process `u` enters a set `s`
  after time `n`

## Main results

* `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`: a discrete hitting time of an adapted process
  is a stopping time
* `MeasureTheory.Adapted.isStoppingTime_hittingAfter`: a discrete hitting time of a adapted process
  is a stopping time

-/

@[expose] public section


open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

section Basic

variable [Preorder ι] [InfSet ι] {u : ι → Ω → β}

open scoped Classical in
/-- Hitting time: given a stochastic process `u` and a set `s`, `hittingBtwn u s n m` is
the first time `u` is in `s` after time `n` and before time `m` (if `u` does not hit `s`
after time `n` and before `m` then the hitting time is simply `m`).

The hitting time is a stopping time if the process is strongly adapted and discrete. -/
/-
**MeasureTheory.hittingBtwn** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn (u : ι -> Ω -> β) (s : Set β) (n m : ι) : Ω -> ι
参数：u : ι -> Ω -> β；s : Set β；n m : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Hitting time: given a stochastic process `u` and a set `s`, `hittingBtwn u s n m
` is
the first time `u` is in `s` after time `n` and before time `m` (if `u` does not
 hit `s`
after time `n` and before `m` then the hitting time is simply `m`).

The hitting time is a stopping time if the process is strongly adapted and discr
ete.
-/
noncomputable def hittingBtwn (u : ι → Ω → β)
    (s : Set β) (n m : ι) : Ω → ι :=
  fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s
    then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m

open scoped Classical in
/-- Hitting time: given a stochastic process `u` and a set `s`, `hittingAfter u s n` is
the first time `u` is in `s` after time `n` (if `u` does not hit `s` after time `n` then the
hitting time is `⊤`). -/
/-
**MeasureTheory.hittingAfter** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter (u : ι -> Ω -> β) (s : Set β) (n : ι) : Ω -> WithTop ι
参数：u : ι -> Ω -> β；s : Set β；n : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Hitting time: given a stochastic process `u` and a set `s`, `hittingAfter u s n`
 is
the first time `u` is in `s` after time `n` (if `u` does not hit `s` after time 
`n` then the
hitting time is `⊤`).
-/
noncomputable def hittingAfter (u : ι → Ω → β) (s : Set β) (n : ι) :
    Ω → WithTop ι :=
  fun x ↦ if ∃ j, n ≤ j ∧ u j x ∈ s then (sInf {i : ι | n ≤ i ∧ u i x ∈ s} : ι) else ⊤

open scoped Classical in
/-
**MeasureTheory.hittingBtwn_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_def (u : ι -> Ω -> β) (s : Set β) (n m : ι) : hittingBtwn u s 
n m = fun x => if exists j in Set.Icc n m, u j x in s then sInf (Set.Icc n m int
er {i : ι | u i x in s}) else m
参数：u : ι -> Ω -> β；s : Set β；n m : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hittingBtwn_def (u : ι → Ω → β) (s : Set β) (n m : ι) :
    hittingBtwn u s n m =
    fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m :=
  rfl

open scoped Classical in
/-
**MeasureTheory.hittingAfter_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_def (u : ι -> Ω -> β) (s : Set β) (n : ι) : hittingAfter u s 
n = fun x => if exists j, n <= j ∧ u j x in s then ((sInf {i : ι | n <= i ∧ u i 
x in s} : ι) : WithTop ι) else ⊤
参数：u : ι -> Ω -> β；s : Set β；n : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hittingAfter_def (u : ι → Ω → β) (s : Set β) (n : ι) :
    hittingAfter u s n =
    fun x => if ∃ j, n ≤ j ∧ u j x ∈ s
      then ((sInf {i : ι | n ≤ i ∧ u i x ∈ s} : ι) : WithTop ι) else ⊤ := rfl

@[simp]
/-
**MeasureTheory.hittingBtwn_empty** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_empty (n m : ι) : hittingBtwn u ∅ n m = fun _ => m
参数：n m : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `infSet_to_nonempty`：∀ (α : Type u_1) [InfSet α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hittingBtwn_empty (n m : ι) : hittingBtwn u ∅ n m = fun _ ↦ m := by ext; simp [hittingBtwn]

@[simp]
/-
**MeasureTheory.hittingAfter_empty** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_empty (n : ι) : hittingAfter u ∅ n = fun _ => ⊤
参数：n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `infSet_to_nonempty`：∀ (α : Type u_1) [InfSet α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hittingAfter_empty (n : ι) : hittingAfter u ∅ n = fun _ ↦ ⊤ := by ext; simp [hittingAfter]

@[simp]
/-
**MeasureTheory.hittingBtwn_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_univ {ι : Type*} [ConditionallyCompleteLinearOrder ι] {u : ι -
> Ω -> β} (n m : ι) : hittingBtwn u .univ n m = fun _ => min n m
参数：n m : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `csInf_Icc`：csInf_Icc {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a b : α} (h : a <= b) : sInf (Icc a b) = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
-/
lemma hittingBtwn_univ {ι : Type*} [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} (n m : ι) :
    hittingBtwn u .univ n m = fun _ ↦ min n m := by
  ext ω
  simp only [hittingBtwn_def, Set.mem_Icc, Set.mem_univ, and_true, Set.ofPred_true, Set.inter_univ]
  by_cases hnm : n ≤ m <;> simp [hnm] <;> grind

@[simp]
/-
**MeasureTheory.hittingAfter_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_univ {ι : Type*} [ConditionallyCompleteLattice ι] {u : ι -> Ω
 -> β} (n : ι) : hittingAfter u .univ n = fun _ => (n : WithTop ι)
参数：n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csInf_Ici`：csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a : α} : sInf (Ici a) = a
-/
lemma hittingAfter_univ {ι : Type*} [ConditionallyCompleteLattice ι] {u : ι → Ω → β} (n : ι) :
    hittingAfter u .univ n = fun _ ↦ (n : WithTop ι) := by
  ext ω
  classical
  simp only [hittingAfter_def, Set.mem_univ, and_true]
  rw [if_pos ⟨n, le_rfl⟩]
  exact_mod_cast csInf_Ici

end Basic

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} {s : Set β} {n i : ι} {ω : Ω}

/-- This lemma is strictly weaker than `hittingBtwn_of_le`. -/
/-
**MeasureTheory.hittingBtwn_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_of_lt {m : ι} (h : m < n) : hittingBtwn u s n m ω = m
参数：h : m < n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma is strictly weaker than `hittingBtwn_of_le`.
-/
theorem hittingBtwn_of_lt {m : ι} (h : m < n) : hittingBtwn u s n m ω = m := by
  grind [hittingBtwn, not_le, Set.Icc_eq_empty]
/-
**MeasureTheory.hittingBtwn_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_le {m : ι} (ω : Ω) : hittingBtwn u s n m ω <= m
参数：ω : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, BddBelow (
Set.Icc b a)
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem hittingBtwn_le {m : ι} (ω : Ω) : hittingBtwn u s n m ω ≤ m := by
  simp only [hittingBtwn]
  split_ifs with h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    change j ∈ {i | u i ω ∈ s} at hj₂
    exact (csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter hj₁ hj₂)).trans hj₁.2
  · exact le_rfl
/-
**MeasureTheory.notMem_of_lt_hittingBtwn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：notMem_of_lt_hittingBtwn {m k : ι} (hk₁ : k < hittingBtwn u s n m ω) (hk₂ 
: n <= k) : u k ω ∉ s
参数：hk₁ : k < hittingBtwn u s n m ω；hk₂ : n <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.hittingBtwn_le`：hittingBtwn_le {m : ι} (ω : Ω) : hittingBt
wn u s n m ω <= m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, BddBelow (
Set.Icc b a)
-/
theorem notMem_of_lt_hittingBtwn {m k : ι} (hk₁ : k < hittingBtwn u s n m ω) (hk₂ : n ≤ k) :
    u k ω ∉ s := by
  intro h
  have hexists : ∃ j ∈ Set.Icc n m, u j ω ∈ s := ⟨k, ⟨hk₂, le_trans hk₁.le <| hittingBtwn_le _⟩, h⟩
  refine not_le.2 hk₁ ?_
  simp_rw [hittingBtwn, if_pos hexists]
  exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le <| hittingBtwn_le _⟩, h⟩
/-
**MeasureTheory.notMem_of_lt_hittingAfter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：notMem_of_lt_hittingAfter {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : 
n <= k) : u k ω ∉ s
参数：hk₁ : k < hittingAfter u s n ω；hk₂ : n <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingAfter.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n
 : ι) (x : Ω),   Meas…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, BddBelow (Se
t.Ici a)
-/
theorem notMem_of_lt_hittingAfter {k : ι} (hk₁ : k < hittingAfter u s n ω) (hk₂ : n ≤ k) :
    u k ω ∉ s := by
  refine fun h ↦ not_le.2 hk₁ ?_
  rw [hittingAfter, if_pos ⟨k, hk₂, h⟩]
  exact_mod_cast csInf_le bddBelow_Ici.inter_of_left ⟨hk₂, h⟩
/-
**MeasureTheory.hittingBtwn_eq_end_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：hittingBtwn_eq_end_iff {m : ι} : hittingBtwn u s n m ω = m ↔ (exists j in 
Set.Icc n m, u j ω in s) -> sInf (Set.Icc n m inter {i : ι | u i ω in s}) = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingBtwn.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Typ
e u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n 
m : ι) (x : Ω),   Me…
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hittingBtwn_eq_end_iff {m : ι} : hittingBtwn u s n m ω = m ↔
    (∃ j ∈ Set.Icc n m, u j ω ∈ s) → sInf (Set.Icc n m ∩ {i : ι | u i ω ∈ s}) = m := by
  classical
  rw [hittingBtwn, ite_eq_right_iff]
/-
**MeasureTheory.hittingAfter_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：hittingAfter_eq_top_iff : hittingAfter u s n ω = ⊤ ↔ forall j, n <= j -> u
 j ω ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hittingAfter_eq_top_iff : hittingAfter u s n ω = ⊤ ↔ ∀ j, n ≤ j → u j ω ∉ s := by
  simp [hittingAfter]
/-
**MeasureTheory.hittingBtwn_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_of_le {m : ι} (hmn : m <= n) : hittingBtwn u s n m ω = m
参数：hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingBtwn.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Typ
e u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n 
m : ι) (x : Ω),   Me…
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用定理 `forall_exists_index`：∀ {α : Sort u_1} {p : α → Prop} {q : (∃ x, p x) → P
rop}, (∀ (h : ∃ x, p x), q h) ↔ ∀ (x : α) (h : p x), q ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `csInf_singleton`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOr
derInf α] (a : α), sInf {a} = a
· 使用定理 `MeasureTheory.hittingBtwn_of_lt`：hittingBtwn_of_lt {m : ι} (h : m < n) :
 hittingBtwn u s n m ω = m
-/
theorem hittingBtwn_of_le {m : ι} (hmn : m ≤ n) : hittingBtwn u s n m ω = m := by
  obtain rfl | h := le_iff_eq_or_lt.1 hmn
  · classical
    rw [hittingBtwn, ite_eq_right_iff, forall_exists_index]
    conv => intro; rw [Set.mem_Icc, Set.Icc_self, and_imp, and_imp]
    intro i hi₁ hi₂ hi
    rw [Set.inter_eq_left.2, csInf_singleton]
    exact Set.singleton_subset_iff.2 (le_antisymm hi₂ hi₁ ▸ hi)
  · exact hittingBtwn_of_lt h
/-
**MeasureTheory.le_hittingBtwn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_hittingBtwn {m : ι} (hnm : n <= m) (ω : Ω) : n <= hittingBtwn u s n m ω
参数：hnm : n <= m；ω : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem le_hittingBtwn {m : ι} (hnm : n ≤ m) (ω : Ω) : n ≤ hittingBtwn u s n m ω := by
  simp only [hittingBtwn]
  split_ifs with h
  · refine le_csInf ?_ fun b hb => ?_
    · obtain ⟨k, hk_Icc, hk_s⟩ := h
      exact ⟨k, hk_Icc, hk_s⟩
    · rw [Set.mem_inter_iff] at hb
      exact hb.1.1
  · exact hnm
/-
**MeasureTheory.le_hittingAfter** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：le_hittingAfter (ω : Ω) : n <= hittingAfter u s n ω
参数：ω : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma le_hittingAfter (ω : Ω) : n ≤ hittingAfter u s n ω := by
  simp only [hittingAfter]
  split_ifs with h
  · exact_mod_cast le_csInf h fun b hb => hb.1
  · simp
/-
**MeasureTheory.le_hittingBtwn_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：le_hittingBtwn_of_exists {m : ι} (h_exists : exists j in Set.Icc n m, u j 
ω in s) : n <= hittingBtwn u s n m ω
参数：h_exists : exists j in Set.Icc n m, u j ω in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_hittingBtwn`：le_hittingBtwn {m : ι} (hnm : n <= m) (ω :
 Ω) : n <= hittingBtwn u s n m ω
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.Icc_eq_empty_of_lt`：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem le_hittingBtwn_of_exists {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    n ≤ hittingBtwn u s n m ω := by
  refine le_hittingBtwn ?_ ω
  by_contra h
  rw [Set.Icc_eq_empty_of_lt (not_le.mp h)] at h_exists
  simp at h_exists
/-
**MeasureTheory.hittingBtwn_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_mem_Icc {m : ι} (hnm : n <= m) (ω : Ω) : hittingBtwn u s n m ω
 in Set.Icc n m
参数：hnm : n <= m；ω : Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_hittingBtwn`：le_hittingBtwn {m : ι} (hnm : n <= m) (ω :
 Ω) : n <= hittingBtwn u s n m ω
· 使用定理 `MeasureTheory.hittingBtwn_le`：hittingBtwn_le {m : ι} (ω : Ω) : hittingBt
wn u s n m ω <= m
-/
theorem hittingBtwn_mem_Icc {m : ι} (hnm : n ≤ m) (ω : Ω) : hittingBtwn u s n m ω ∈ Set.Icc n m :=
  ⟨le_hittingBtwn hnm ω, hittingBtwn_le ω⟩
/-
**MeasureTheory.hittingBtwn_mem_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_mem_set [WellFoundedLT ι] {m : ι} (h_exists : exists j in Set.
Icc n m, u j ω in s) : u (hittingBtwn u s n m ω) ω in s
参数：h_exists : exists j in Set.Icc n m, u j ω in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
-/
theorem hittingBtwn_mem_set [WellFoundedLT ι] {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    u (hittingBtwn u s n m ω) ω ∈ s := by
  simp_rw [hittingBtwn, if_pos h_exists]
  have h_nonempty : (Set.Icc n m ∩ {i : ι | u i ω ∈ s}).Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  have h_mem := csInf_mem h_nonempty
  rw [Set.mem_inter_iff] at h_mem
  exact h_mem.2
/-
**MeasureTheory.hittingAfter_mem_set** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_mem_set [WellFoundedLT ι] (h_exists : exists j, n <= j ∧ u j 
ω in s) : u (hittingAfter u s n ω).untopA ω in s
参数：h_exists : exists j, n <= j ∧ u j ω in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingAfter.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n
 : ι) (x : Ω),   Meas…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
-/
lemma hittingAfter_mem_set [WellFoundedLT ι] (h_exists : ∃ j, n ≤ j ∧ u j ω ∈ s) :
    u (hittingAfter u s n ω).untopA ω ∈ s := by
  rw [hittingAfter, if_pos h_exists]
  have h_nonempty : {i : ι | n ≤ i ∧ u i ω ∈ s}.Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  exact (csInf_mem h_nonempty).2
/-
**MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：hittingBtwn_mem_set_of_hittingBtwn_lt [WellFoundedLT ι] {m : ι} (hl : hitt
ingBtwn u s n m ω < m) : u (hittingBtwn u s n m ω) ω in s
参数：hl : hittingBtwn u s n m ω < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hittingBtwn_mem_set`：hittingBtwn_mem_set [WellFoundedLT ι]
 {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s) : u (hittingBtwn u s n
 m ω) ω in s
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem hittingBtwn_mem_set_of_hittingBtwn_lt [WellFoundedLT ι] {m : ι}
    (hl : hittingBtwn u s n m ω < m) :
    u (hittingBtwn u s n m ω) ω ∈ s := by
  by_cases h : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · exact hittingBtwn_mem_set h
  · simp_rw [hittingBtwn, if_neg h] at hl
    exact False.elim (hl.ne rfl)
/-
**MeasureTheory.hittingAfter_mem_set_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：hittingAfter_mem_set_of_ne_top [WellFoundedLT ι] (hl : hittingAfter u s n 
ω != ⊤) : u (hittingAfter u s n ω).untopA ω in s
参数：hl : hittingAfter u s n ω != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `MeasureTheory.hittingAfter_mem_set`：hittingAfter_mem_set [WellFoundedLT 
ι] (h_exists : exists j, n <= j ∧ u j ω in s) : u (hittingAfter u s n ω).untopA 
ω in s
-/
lemma hittingAfter_mem_set_of_ne_top [WellFoundedLT ι] (hl : hittingAfter u s n ω ≠ ⊤) :
    u (hittingAfter u s n ω).untopA ω ∈ s := by
  simp only [ne_eq, hittingAfter_eq_top_iff, not_forall, not_not] at hl
  obtain ⟨j, hj₁, hj₂⟩ := hl
  exact hittingAfter_mem_set ⟨j, hj₁, hj₂⟩
/-
**MeasureTheory.hittingBtwn_le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_le_of_mem {m : ι} (hin : n <= i) (him : i <= m) (his : u i ω i
n s) : hittingBtwn u s n m ω <= i
参数：hin : n <= i；him : i <= m；his : u i ω in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, BddBelow (
Set.Icc b a)
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
-/
theorem hittingBtwn_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) :
    hittingBtwn u s n m ω ≤ i := by
  have h_exists : ∃ k ∈ Set.Icc n m, u k ω ∈ s := ⟨i, ⟨hin, him⟩, his⟩
  simp_rw [hittingBtwn, if_pos h_exists]
  exact csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter ⟨hin, him⟩ his)
/-
**MeasureTheory.hittingAfter_le_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：hittingAfter_le_of_mem (hin : n <= i) (his : u i ω in s) : hittingAfter u 
s n ω <= i
参数：hin : n <= i；his : u i ω in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingAfter.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n
 : ι) (x : Ω),   Meas…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, BddBelow (Se
t.Ici a)
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
-/
lemma hittingAfter_le_of_mem (hin : n ≤ i) (his : u i ω ∈ s) :
    hittingAfter u s n ω ≤ i := by
  have h_exists : ∃ k, n ≤ k ∧ u k ω ∈ s := ⟨i, hin, his⟩
  rw [hittingAfter, if_pos h_exists]
  exact_mod_cast csInf_le (BddBelow.inter_of_left bddBelow_Ici) (Set.mem_inter hin his)
/-
**MeasureTheory.hittingBtwn_le_iff_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：hittingBtwn_le_iff_of_exists [WellFoundedLT ι] {m : ι} (h_exists : exists 
j in Set.Icc n m, u j ω in s) : hittingBtwn u s n m ω <= i ↔ exists j in Set.Icc
 n i, u j ω in s
参数：h_exists : exists j in Set.Icc n m, u j ω in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_hittingBtwn_of_exists`：le_hittingBtwn_of_exists {m : ι}
 (h_exists : exists j in Set.Icc n m, u j ω in s) : n <= hittingBtwn u s n m ω
· 使用定理 `MeasureTheory.hittingBtwn_mem_set`：hittingBtwn_mem_set [WellFoundedLT ι]
 {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s) : u (hittingBtwn u s n
 m ω) ω in s
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `min_rec'`：min_rec' (p : α -> Prop) (ha : p a) (hb : p b) : p (min a b)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.hittingBtwn_le_of_mem`：hittingBtwn_le_of_mem {m : ι} (hin 
: n <= i) (him : i <= m) (his : u i ω in s) : hittingBtwn u s n m ω <= i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
-/
theorem hittingBtwn_le_iff_of_exists [WellFoundedLT ι] {m : ι}
    (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    hittingBtwn u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  constructor <;> intro h'
  · exact ⟨hittingBtwn u s n m ω, ⟨le_hittingBtwn_of_exists h_exists, h'⟩,
      hittingBtwn_mem_set h_exists⟩
  · have h'' : ∃ k ∈ Set.Icc n (min m i), u k ω ∈ s := by
      obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h'
      refine ⟨min k₁ k₂, ⟨le_min hk₁_mem.1 hk₂_mem.1, min_le_min hk₁_mem.2 hk₂_mem.2⟩, ?_⟩
      exact min_rec' (fun j => u j ω ∈ s) hk₁_s hk₂_s
    obtain ⟨k, hk₁, hk₂⟩ := h''
    refine le_trans ?_ (hk₁.2.trans (min_le_right _ _))
    exact hittingBtwn_le_of_mem hk₁.1 (hk₁.2.trans (min_le_left _ _)) hk₂
/-
**MeasureTheory.hittingAfter_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_le_iff [WellFoundedLT ι] : hittingAfter u s n ω <= i ↔ exists
 j in Set.Icc n i, u j ω in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.le_hittingAfter`：le_hittingAfter (ω : Ω) : n <= hittingAft
er u s n ω
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.hittingAfter_mem_set_of_ne_top`：hittingAfter_mem_set_of_ne
_top [WellFoundedLT ι] (hl : hittingAfter u s n ω != ⊤) : u (hittingAfter u s n 
ω).untopA ω in s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `MeasureTheory.hittingAfter_le_of_mem`：hittingAfter_le_of_mem (hin : n <=
 i) (his : u i ω in s) : hittingAfter u s n ω <= i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma hittingAfter_le_iff [WellFoundedLT ι] :
    hittingAfter u s n ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω ≠ ⊤ := fun h ↦ by simp [h] at h'
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    refine ⟨(hittingAfter u s n ω).untopA, ?_, hittingAfter_mem_set_of_ne_top h_top⟩
    lift (hittingAfter u s n ω) to ι using h_top with i'
    norm_cast at h' h_le
  · obtain ⟨j, hj₁, hj₂⟩ := h'
    refine le_trans ?_ (mod_cast hj₁.2 : (j : WithTop ι) ≤ i)
    exact hittingAfter_le_of_mem hj₁.1 hj₂
/-
**MeasureTheory.hittingBtwn_le_iff_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：hittingBtwn_le_iff_of_lt [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m) : 
hittingBtwn u s n m ω <= i ↔ exists j in Set.Icc n i, u j ω in s
参数：i : ι；hi : i < m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingBtwn_le_iff_of_exists`：hittingBtwn_le_iff_of_exists
 [WellFoundedLT ι] {m : ι} (h_exists : exists j in Set.Icc n m, u j ω in s) : hi
ttingBtwn u s n m ω <= i ↔ exist…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem hittingBtwn_le_iff_of_lt [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m) :
    hittingBtwn u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  by_cases h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · rw [hittingBtwn_le_iff_of_exists h_exists]
  · simp_rw [hittingBtwn, if_neg h_exists]
    push Not at h_exists
    simp only [not_le.mpr hi, Set.mem_Icc, false_iff, not_exists, not_and, and_imp]
    exact fun k hkn hki => h_exists k ⟨hkn, hki.trans hi.le⟩
/-
**MeasureTheory.hittingBtwn_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_lt_iff {m : ι} (i : ι) (hi : i <= m) : hittingBtwn u s n m ω <
 i ↔ exists j in Set.Ico n i, u j ω in s
参数：i : ι；hi : i <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_hittingBtwn_of_exists`：le_hittingBtwn_of_exists {m : ι}
 (h_exists : exists j in Set.Icc n m, u j ω in s) : n <= hittingBtwn u s n m ω
· 使用定理 `MeasureTheory.le_hittingBtwn`：le_hittingBtwn {m : ι} (hnm : n <= m) (ω :
 Ω) : n <= hittingBtwn u s n m ω
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `csInf_lt_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLinearOrder 
α] {s : Set α} {a : α},   BddBelow s → s.Nonempty → (sInf s < a ↔ ∃ b ∈ s, b < a
)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.hittingBtwn.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Typ
e u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n 
m : ι) (x : Ω),   Me…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.hittingBtwn_le_of_mem`：hittingBtwn_le_of_mem {m : ι} (hin 
: n <= i) (him : i <= m) (his : u i ω in s) : hittingBtwn u s n m ω <= i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem hittingBtwn_lt_iff {m : ι} (i : ι) (hi : i ≤ m) :
    hittingBtwn u s n m ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h : ∃ j ∈ Set.Icc n m, u j ω ∈ s := by
      by_contra h
      simp_rw [hittingBtwn, if_neg h, ← not_le] at h'
      exact h' hi
    have hni : n < i := (le_hittingBtwn_of_exists h).trans_lt h'
    have h_le := le_hittingBtwn (u := u) (s := s) (hni.le.trans hi) ω
    rw [hittingBtwn, if_pos h, csInf_lt_iff] at h'
    rotate_left
    · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    · exact h
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq] at h'
    obtain ⟨j, ⟨⟨hnj, hjm⟩, hj_mem⟩, hji⟩ := h'
    exact ⟨j, ⟨hnj, hji⟩, hj_mem⟩
  · obtain ⟨k, hk₁, hk₂⟩ := h'
    refine lt_of_le_of_lt ?_ hk₁.2
    exact hittingBtwn_le_of_mem hk₁.1 (hk₁.2.le.trans hi) hk₂
/-
**MeasureTheory.hittingAfter_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_lt_iff : hittingAfter u s n ω < i ↔ exists j in Set.Ico n i, 
u j ω in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.hittingAfter_eq_top_iff`：hittingAfter_eq_top_iff : hitting
After u s n ω = ⊤ ↔ forall j, n <= j -> u j ω ∉ s
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `MeasureTheory.le_hittingAfter`：le_hittingAfter (ω : Ω) : n <= hittingAft
er u s n ω
· 使用定理 `csInf_lt_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLinearOrder 
α] {s : Set α} {a : α},   BddBelow s → s.Nonempty → (sInf s < a ↔ ∃ b ∈ s, b < a
)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.hittingAfter.eq_1`：∀ {Ω : Type u_1} {β : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] [inst_1 : InfSet ι] (u : ι → Ω → β) (s : Set β)   (n
 : ι) (x : Ω),   Meas…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `MeasureTheory.hittingAfter_le_of_mem`：hittingAfter_le_of_mem (hin : n <=
 i) (his : u i ω in s) : hittingAfter u s n ω <= i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hittingAfter_lt_iff :
    hittingAfter u s n ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h_top : hittingAfter u s n ω ≠ ⊤ := fun h ↦ by simp [h] at h'
    have h_exists : ∃ j, n ≤ j ∧ u j ω ∈ s := by
      rw [ne_eq, hittingAfter_eq_top_iff] at h_top
      push Not at h_top
      exact h_top
    have h_le := le_hittingAfter (u := u) (s := s) (n := n) ω
    rw [hittingAfter, if_pos h_exists] at h'
    norm_cast at h'
    rw [csInf_lt_iff] at h'
    rotate_left
    · exact ⟨n, by simp [mem_lowerBounds]; grind⟩
    · exact h_exists
    simp only [Set.mem_ofPred_eq] at h'
    obtain ⟨j, hj₁, hj₂⟩ := h'
    exact ⟨j, ⟨hj₁.1, hj₂⟩, hj₁.2⟩
  · obtain ⟨j, hj₁, hj₂⟩ := h'
    refine lt_of_le_of_lt ?_ (mod_cast hj₁.2 : (j : WithTop ι) < i)
    exact hittingAfter_le_of_mem hj₁.1 hj₂
/-
**MeasureTheory.hittingBtwn_eq_hittingBtwn_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：hittingBtwn_eq_hittingBtwn_of_exists {m₁ m₂ : ι} (h : m₁ <= m₂) (h' : exis
ts j in Set.Icc n m₁, u j ω in s) : hittingBtwn u s n m₁ ω = hittingBtwn u s n m
₂ ω
参数：h : m₁ <= m₂；h' : exists j in Set.Icc n m₁, u j ω in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Set.Icc_subset_Icc_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ ≤ a₁ → Set.Icc b a₂ ⊆ Set.Icc b a₁
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `BddBelow.inter_of_left`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, BddBelow s → BddBelow (s ∩ t)
· 使用定理 `bddBelow_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, BddBelow (
Set.Icc b a)
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem hittingBtwn_eq_hittingBtwn_of_exists {m₁ m₂ : ι} (h : m₁ ≤ m₂)
    (h' : ∃ j ∈ Set.Icc n m₁, u j ω ∈ s) : hittingBtwn u s n m₁ ω = hittingBtwn u s n m₂ ω := by
  simp only [hittingBtwn, if_pos h']
  obtain ⟨j, hj₁, hj₂⟩ := h'
  rw [if_pos]
  · refine le_antisymm ?_ (by gcongr; exacts [bddBelow_Icc.inter_of_left, ⟨j, hj₁, hj₂⟩])
    refine le_csInf ⟨j, Set.Icc_subset_Icc_right h hj₁, hj₂⟩ fun i hi => ?_
    by_cases hi' : i ≤ m₁
    · exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hi.1.1, hi'⟩, hi.2⟩
    · change j ∈ {i | u i ω ∈ s} at hj₂
      exact ((csInf_le bddBelow_Icc.inter_of_left ⟨hj₁, hj₂⟩).trans hj₁.2).trans (le_of_not_ge hi')
  exact ⟨j, ⟨hj₁.1, hj₁.2.trans h⟩, hj₂⟩

/-- `hittingBtwn` is nonincreasing with respect to the set. -/
/-
**MeasureTheory.hittingBtwn_anti** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_anti (u : ι -> Ω -> β) (n m : ι) : Antitone (hittingBtwn u · n
 m)
参数：u : ι -> Ω -> β；n m : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `csInf_le_of_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
`hittingBtwn` is nonincreasing with respect to the set.
-/
lemma hittingBtwn_anti (u : ι → Ω → β) (n m : ι) : Antitone (hittingBtwn u · n m) := by
  intro E F hEF ω
  simp only [hittingBtwn_def]
  split_ifs with hF hE hE
  · gcongr
    exact ⟨n, by simp [mem_lowerBounds]; grind⟩
  · obtain ⟨t, ht⟩ := hF
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp

/-- `hittingAfter` is nonincreasing with respect to the set. -/
/-
**MeasureTheory.hittingAfter_anti** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_anti (u : ι -> Ω -> β) (n : ι) : Antitone (hittingAfter u · n
)
参数：u : ι -> Ω -> β；n : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`hittingAfter` is nonincreasing with respect to the set.
-/
lemma hittingAfter_anti (u : ι → Ω → β) (n : ι) : Antitone (hittingAfter u · n) := by
  intro E F hEF ω
  simp only [hittingAfter_def]
  split_ifs with hF hE hE
  · norm_cast
    gcongr
    exact ⟨n, by simp only [mem_lowerBounds]; grind⟩
  · simp
  · obtain ⟨t, ht⟩ := hE
    exact absurd ⟨t, ht.1, hEF ht.2⟩ hF
  · simp
/-
**MeasureTheory.hittingBtwn_apply_anti** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：hittingBtwn_apply_anti (u : ι -> Ω -> β) (n m : ι) (ω : Ω) : Antitone (hit
tingBtwn u · n m ω)
参数：u : ι -> Ω -> β；n m : ι；ω : Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.hittingBtwn_anti`：hittingBtwn_anti (u : ι -> Ω -> β) (n m 
: ι) : Antitone (hittingBtwn u · n m)
-/
lemma hittingBtwn_apply_anti (u : ι → Ω → β) (n m : ι) (ω : Ω) :
    Antitone (hittingBtwn u · n m ω) := fun _ _ hEF ↦ hittingBtwn_anti u n m hEF ω
/-
**MeasureTheory.hittingAfter_apply_anti** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：hittingAfter_apply_anti (u : ι -> Ω -> β) (n : ι) (ω : Ω) : Antitone (hitt
ingAfter u · n ω)
参数：u : ι -> Ω -> β；n : ι；ω : Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.hittingAfter_anti`：hittingAfter_anti (u : ι -> Ω -> β) (n 
: ι) : Antitone (hittingAfter u · n)
-/
lemma hittingAfter_apply_anti (u : ι → Ω → β) (n : ι) (ω : Ω) :
    Antitone (hittingAfter u · n ω) := fun _ _ hst ↦ hittingAfter_anti u n hst ω

/-- `hittingBtwn` is monotone with respect to the maximal time. -/
/-
**MeasureTheory.hittingBtwn_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：hittingBtwn_mono_right (u : ι -> Ω -> β) (s : Set β) (n : ι) : Monotone (h
ittingBtwn u s n · ω)
参数：u : ι -> Ω -> β；s : Set β；n : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.hittingBtwn_eq_hittingBtwn_of_exists`：hittingBtwn_eq_hitti
ngBtwn_of_exists {m₁ m₂ : ι} (h : m₁ <= m₂) (h' : exists j in Set.Icc n m₁, u j 
ω in s) : hittingBtwn u s n m₁ ω = hitti…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`hittingBtwn` is monotone with respect to the maximal time.
-/
theorem hittingBtwn_mono_right (u : ι → Ω → β) (s : Set β) (n : ι) :
    Monotone (hittingBtwn u s n · ω) := by
  intro m₁ m₂ hm
  by_cases h : ∃ j ∈ Set.Icc n m₁, u j ω ∈ s
  · exact (hittingBtwn_eq_hittingBtwn_of_exists hm h).le
  · simp_rw [hittingBtwn, if_neg h]
    split_ifs with h'
    · obtain ⟨j, hj₁, hj₂⟩ := h'
      refine le_csInf ⟨j, hj₁, hj₂⟩ ?_
      by_contra! ⟨i, hi₁, hi₂⟩
      exact h ⟨i, ⟨hi₁.1.1, hi₂.le⟩, hi₁.2⟩
    · exact hm

/-- `hittingBtwn` is monotone with respect to the minimal time. -/
/-
**MeasureTheory.hittingBtwn_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_mono_left (u : ι -> Ω -> β) (s : Set β) (m : ι) : Monotone (hi
ttingBtwn u s · m)
参数：u : ι -> Ω -> β；s : Set β；m : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `csInf_le_of_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
`hittingBtwn` is monotone with respect to the minimal time.
-/
lemma hittingBtwn_mono_left (u : ι → Ω → β) (s : Set β) (m : ι) :
    Monotone (hittingBtwn u s · m) := by
  intro n n' hnn' ω
  simp only [hittingBtwn]
  split_ifs with h_n h_n' h_n'
  · gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · obtain ⟨t, ht⟩ := h_n
    exact csInf_le_of_le ⟨n, by simp [mem_lowerBounds]; grind⟩ ht ht.1.2
  · have ⟨t, ht⟩ := h_n'
    exact absurd ⟨t, ⟨hnn'.trans ht.1.1, ht.1.2⟩, ht.2⟩ h_n
  · simp

/-- `hittingAfter` is monotone with respect to the minimal time. -/
/-
**MeasureTheory.hittingAfter_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_mono (u : ι -> Ω -> β) (s : Set β) : Monotone (hittingAfter u
 s)
参数：u : ι -> Ω -> β；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
`hittingAfter` is monotone with respect to the minimal time.
-/
lemma hittingAfter_mono (u : ι → Ω → β) (s : Set β) : Monotone (hittingAfter u s) := by
  intro n m hnm ω
  simp only [hittingAfter]
  split_ifs with h_n h_m h_m
  · norm_cast
    gcongr
    exacts [⟨n, by simp [mem_lowerBounds]; grind⟩]
  · simp
  · have ⟨t, ht⟩ := h_m
    exact absurd ⟨t, hnm.trans ht.1, ht.2⟩ h_n
  · simp
/-
**MeasureTheory.hittingBtwn_apply_mono_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：hittingBtwn_apply_mono_right (u : ι -> Ω -> β) (s : Set β) (n : ι) (ω : Ω)
 : Monotone (hittingBtwn u s n · ω)
参数：u : ι -> Ω -> β；s : Set β；n : ι；ω : Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hittingBtwn_mono_right`：hittingBtwn_mono_right (u : ι -> Ω
 -> β) (s : Set β) (n : ι) : Monotone (hittingBtwn u s n · ω)
-/
lemma hittingBtwn_apply_mono_right (u : ι → Ω → β) (s : Set β) (n : ι) (ω : Ω) :
    Monotone (hittingBtwn u s n · ω) := fun _ _ hnn' ↦ hittingBtwn_mono_right u s n hnn'
/-
**MeasureTheory.hittingBtwn_apply_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：hittingBtwn_apply_mono_left (u : ι -> Ω -> β) (s : Set β) (m : ι) (ω : Ω) 
: Monotone (hittingBtwn u s · m ω)
参数：u : ι -> Ω -> β；s : Set β；m : ι；ω : Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.hittingBtwn_mono_left`：hittingBtwn_mono_left (u : ι -> Ω -
> β) (s : Set β) (m : ι) : Monotone (hittingBtwn u s · m)
-/
lemma hittingBtwn_apply_mono_left (u : ι → Ω → β) (s : Set β) (m : ι) (ω : Ω) :
    Monotone (hittingBtwn u s · m ω) := fun _ _ hnn' ↦ hittingBtwn_mono_left u s m hnn' ω
/-
**MeasureTheory.hittingAfter_apply_mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：hittingAfter_apply_mono (u : ι -> Ω -> β) (s : Set β) (ω : Ω) : Monotone (
hittingAfter u s · ω)
参数：u : ι -> Ω -> β；s : Set β；ω : Ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.hittingAfter_mono`：hittingAfter_mono (u : ι -> Ω -> β) (s 
: Set β) : Monotone (hittingAfter u s)
-/
lemma hittingAfter_apply_mono (u : ι → Ω → β) (s : Set β) (ω : Ω) :
    Monotone (hittingAfter u s · ω) := fun _ _ hnm ↦ hittingAfter_mono u s hnm ω

end Inequalities

/-- A discrete hitting time is a stopping time. -/
/-
**MeasureTheory.Adapted.isStoppingTime_hittingBtwn** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : ConditionallyCompleteLinearOrder ι]   [WellFoundedLT ι] [Countable ι] {x : 
MeasurableSpace β} {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {s : Set β
}   {n n' : ι},   MeasureTheory.Adapted f u →     MeasurableSet s → MeasureTheor
y.IsStoppingTime f fun ω => ↑(MeasureTheory.hittingBtwn u s n n' ω)
参数：MeasureTheory.hittingBtwn u s n n' ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.hittingBtwn_le`：hittingBtwn_le {m : ι} (ω : Ω) : hittingBt
wn u s n m ω <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.hittingBtwn_le_iff_of_lt`：hittingBtwn_le_iff_of_lt [WellFo
undedLT ι] {m : ι} (i : ι) (hi : i < m) : hittingBtwn u s n m ω <= i ↔ exists j 
in Set.Icc n i, u j ω in s
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A discrete hitting time is a stopping time.
-/
theorem Adapted.isStoppingTime_hittingBtwn [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    [Countable ι] {_ : MeasurableSpace β} {f : Filtration ι m} {u : ι → Ω → β} {s : Set β}
    {n n' : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (fun ω ↦ (hittingBtwn u s n n' ω : ι)) := by
  intro i
  rcases le_or_gt n' i with hi | hi
  · have h_le : ∀ ω, hittingBtwn u s n n' ω ≤ i := fun x => (hittingBtwn_le x).trans hi
    simp [h_le]
  · have h_set_eq_Union : {ω | hittingBtwn u s n n' ω ≤ i} = ⋃ j ∈ Set.Icc n i, u j ⁻¹' s := by
      ext; simp [hittingBtwn_le_iff_of_lt _ hi]
    simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

@[deprecated (since := "2026-01-25")]
alias hittingBtwn_isStoppingTime := Adapted.isStoppingTime_hittingBtwn
/-
**MeasureTheory.Adapted.isStoppingTime_hittingAfter** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : ConditionallyCompleteLinearOrder ι]   [WellFoundedLT ι] [Countable ι] {x : 
MeasurableSpace β} {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {s : Set β
}   {n : ι},   MeasureTheory.Adapted f u → MeasurableSet s → MeasureTheory.IsSto
ppingTime f (MeasureTheory.hittingAfter u s n)
参数：MeasureTheory.hittingAfter u s n。
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Adapted.isStoppingTime_hittingAfter [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] {_ : MeasurableSpace β} {f : Filtration ι m} {u : ι → Ω → β}
    {s : Set β} {n : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (hittingAfter u s n) := by
  intro i
  have h_set_eq_Union : {ω | hittingAfter u s n ω ≤ i} = ⋃ j ∈ Set.Icc n i, u j ⁻¹' s := by
    ext; simp [hittingAfter_le_iff]
  simpa [h_set_eq_Union] using MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j) hs)

@[deprecated (since := "2026-01-25")]
alias hittingAfter_isStoppingTime := Adapted.isStoppingTime_hittingAfter
/-
**MeasureTheory.stoppedValue_hittingBtwn_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：stoppedValue_hittingBtwn_mem [ConditionallyCompleteLinearOrder ι] [WellFou
ndedLT ι] {u : ι -> Ω -> β} {s : Set β} {n m : ι} {ω : Ω} (h : exists j in Set.I
cc n m, u j ω in s) : stoppedValue u (fun ω => (hittingBtwn u s n m ω : ι)) ω in
 s
参数：h : exists j in Set.Icc n m, u j ω in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem stoppedValue_hittingBtwn_mem [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    {u : ι → Ω → β} {s : Set β} {n m : ι} {ω : Ω} (h : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    stoppedValue u (fun ω ↦ (hittingBtwn u s n m ω : ι)) ω ∈ s := by
  simp only [stoppedValue, hittingBtwn, if_pos h]
  obtain ⟨j, hj₁, hj₂⟩ := h
  have : sInf (Set.Icc n m ∩ {i | u i ω ∈ s}) ∈ Set.Icc n m ∩ {i | u i ω ∈ s} :=
    csInf_mem (Set.nonempty_of_mem ⟨hj₁, hj₂⟩)
  exact this.2

/-- The hitting time of a discrete process with the starting time indexed by a stopping time
is a stopping time. -/
/-
**MeasureTheory.Adapted.isStoppingTime_hittingBtwn_isStoppingTime** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Adapted`。
形式化陈述：∀ {Ω : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [in
st : ConditionallyCompleteLinearOrder ι]   [WellFoundedLT ι] [Countable ι] [inst
_3 : TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]   [inst_6 
: MeasurableSpace β] {f : MeasureTheory.Filtration ι m} {u : ι → Ω → β} {τ : Ω →
 WithTop ι},   MeasureTheory.IsStoppingTime f τ →     ∀ {N : ι},       (∀ (x : Ω
), τ x ≤ ↑N) →         ∀ {s : Set β},           MeasurableSet s →             Me
asureTheory.Adapted f u →               MeasureTheory.IsStoppingTime f fun x => 
↑(MeasureTheory.hittingBtwn u s (τ x).untopA N x)
参数：∀ (x : Ω), τ x ≤ ↑N；MeasureTheory.hittingBtwn u s (τ x).untopA N x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.le_hittingBtwn`：le_hittingBtwn {m : ι} (hnm : n <= m) (ω :
 Ω) : n <= hittingBtwn u s n m ω
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.Filtration.mono`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Meas
urableSpace Ω} [inst : Preorder ι] {i j : ι}   (f : MeasureTheory.Filtration ι m
), i ≤ j → ↑f i ≤ ↑…
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_eq`：∀ {Ω : Type u_1} {ι : Typ
e u_3} {m : MeasurableSpace Ω} [inst : LinearOrder ι] {f : MeasureTheory.Filtrat
ion ι m}   {τ : Ω → WithTop ι} [ins…
· 使用定理 `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`：∀ {Ω : Type u_1} {β : 
Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : ConditionallyCompleteLi
nearOrder ι]   [WellFoundedLT ι] [Coun…

--- 原说明 ---
The hitting time of a discrete process with the starting time indexed by a stopp
ing time
is a stopping time.
-/
theorem Adapted.isStoppingTime_hittingBtwn_isStoppingTime [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [MeasurableSpace β] {f : Filtration ι m} {u : ι → Ω → β}
    {τ : Ω → WithTop ι} (hτ : IsStoppingTime f τ)
    {N : ι} (hτbdd : ∀ x, τ x ≤ N) {s : Set β} (hs : MeasurableSet s) (hf : Adapted f u) :
    IsStoppingTime f fun x ↦ (hittingBtwn u s (τ x).untopA N x : ι) := by
  intro n
  have h₁ : {x | hittingBtwn u s (τ x).untopA N x ≤ n} =
    (⋃ i ≤ n, {x | τ x = i} ∩ {x | hittingBtwn u s i N x ≤ n}) ∪
      ⋃ i > n, {x | τ x = i} ∩ {x | hittingBtwn u s i N x ≤ n} := by
    ext x
    simp only [Set.mem_ofPred_eq, gt_iff_lt, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      exists_and_left, exists_prop]
    specialize hτbdd x
    have h_top : τ x ≠ ⊤ := fun h => by simp [h] at hτbdd
    lift τ x to ι using h_top with t
    simp [← or_and_right, le_or_gt]
  have h₂ : ⋃ i > n, {x | τ x = i} ∩ {x | hittingBtwn u s i N x ≤ n} = ∅ := by
    ext x
    simp only [gt_iff_lt, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_prop,
      Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
    refine fun m hm hτ ↦ hm.trans_le <| le_hittingBtwn ?_ x
    specialize hτbdd x
    have h_top : τ x ≠ ⊤ := fun h => by simp [h] at hτbdd
    lift τ x to ι using h_top with t
    rw [hτ] at hτbdd
    exact mod_cast hτbdd
  simp only [WithTop.coe_le_coe, h₁, h₂, Set.union_empty]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi =>
    (f.mono hi _ (hτ.measurableSet_eq i)).inter ?_
  simpa using hf.isStoppingTime_hittingBtwn hs n

@[deprecated (since := "2026-01-25")]
alias isStoppingTime_hittingBtwn_isStoppingTime := Adapted.isStoppingTime_hittingBtwn_isStoppingTime

section CompleteLattice

variable [CompleteLattice ι] {u : ι → Ω → β} {s : Set β}

/-
**MeasureTheory.hittingBtwn_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingBtwn_eq_sInf (ω : Ω) : hittingBtwn u s ⊥ ⊤ ω = sInf {i : ι | u i ω 
in s}
参数：ω : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
· 使用定理 `Set.Iic_top`：Iic_top : Iic (⊤ : α) = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_eq_top`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, sI
nf s = ⊤ ↔ ∀ a ∈ s, a = ⊤
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem hittingBtwn_eq_sInf (ω : Ω) : hittingBtwn u s ⊥ ⊤ ω = sInf {i : ι | u i ω ∈ s} := by
  simp only [hittingBtwn, Set.Icc_bot,
    Set.Iic_top, Set.univ_inter, ite_eq_left_iff, not_exists]
  intro h_notMem_s
  symm
  rw [sInf_eq_top]
  simp only [Set.mem_univ, true_and] at h_notMem_s
  exact fun i hi_mem_s => absurd hi_mem_s (h_notMem_s i)
/-
**MeasureTheory.hittingAfter_eq_sInf** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：hittingAfter_eq_sInf [forall ω, Decidable (exists j, u j ω in s)] (ω : Ω) 
: hittingAfter u s ⊥ ω = if exists j, u j ω in s then ((sInf {i : ι | u i ω in s
} : ι) : WithTop ι) else (⊤ : WithTop ι)
参数：exists j, u j ω in s；ω : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hittingAfter_eq_sInf [∀ ω, Decidable (∃ j, u j ω ∈ s)] (ω : Ω) :
    hittingAfter u s ⊥ ω
      = if ∃ j, u j ω ∈ s then ((sInf {i : ι | u i ω ∈ s} : ι) : WithTop ι)
        else (⊤ : WithTop ι) := by
  simp [hittingAfter]

end CompleteLattice

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
variable {u : ι → Ω → β} {s : Set β}

/-
**MeasureTheory.hittingBtwn_bot_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：hittingBtwn_bot_le_iff {i n : ι} {ω : Ω} (hx : exists j, j <= n ∧ u j ω in
 s) : hittingBtwn u s ⊥ n ω <= i ↔ exists j <= i, u j ω in s
参数：hx : exists j, j <= n ∧ u j ω in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hittingBtwn_le_iff_of_lt`：hittingBtwn_le_iff_of_lt [WellFo
undedLT ι] {m : ι} (i : ι) (hi : i < m) : hittingBtwn u s n m ω <= i ↔ exists j 
in Set.Icc n i, u j ω in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.hittingBtwn_le`：hittingBtwn_le {m : ι} (ω : Ω) : hittingBt
wn u s n m ω <= m
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
theorem hittingBtwn_bot_le_iff {i n : ι} {ω : Ω} (hx : ∃ j, j ≤ n ∧ u j ω ∈ s) :
    hittingBtwn u s ⊥ n ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s := by
  rcases lt_or_ge i n with hi | hi
  · rw [hittingBtwn_le_iff_of_lt _ hi]
    simp
  · simp only [(hittingBtwn_le ω).trans hi, true_iff]
    obtain ⟨j, hj₁, hj₂⟩ := hx
    exact ⟨j, hj₁.trans hi, hj₂⟩
/-
**MeasureTheory.hittingAfter_bot_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：hittingAfter_bot_le_iff {i : ι} {ω : Ω} : hittingAfter u s ⊥ ω <= i ↔ exis
ts j <= i, u j ω in s
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
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hittingAfter_bot_le_iff {i : ι} {ω : Ω} :
    hittingAfter u s ⊥ ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s := by
  simp [hittingAfter_le_iff]

end ConditionallyCompleteLinearOrderBot

end MeasureTheory

