/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete
partial order, as opposed to a conditionally complete lattice.

-/

public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section ConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α] {a b : α}

@[to_dual]
/-
**Directed.isLUB_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.isLUB_ciSup [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f) 
(H : BddAbove (range f)) : IsLUB (range f) (⨆ i, f i)
参数：hd : Directed (· <= ·) f；H : BddAbove (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem Directed.isLUB_ciSup [Nonempty ι] {f : ι → α} (hd : Directed (· ≤ ·) f)
    (H : BddAbove (range f)) : IsLUB (range f) (⨆ i, f i) :=
  hd.directedOn_range.isLUB_csSup (range_nonempty f) H

@[to_dual]
/-
**DirectedOn.isLUB_ciSup_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.isLUB_ciSup_set {f : β -> α} {s : Set β} (hd : DirectedOn (· <=
 ·) (f '' s)) (H : BddAbove (f '' s)) (Hne : s.Nonempty) : IsLUB (f '' s) (⨆ i :
 s, f i)
参数：hd : DirectedOn (· <= ·) (f '' s)；H : BddAbove (f '' s)；Hne : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem DirectedOn.isLUB_ciSup_set {f : β → α} {s : Set β} (hd : DirectedOn (· ≤ ·) (f '' s))
    (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact hd.isLUB_csSup (Hne.image _) H

@[to_dual Directed.le_ciInf_iff]
/-
**Directed.ciSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hd : Directed (· 
<= ·) f) (hf : BddAbove (range f)) : iSup f <= a ↔ forall i, f i <= a
参数：hd : Directed (· <= ·) f；hf : BddAbove (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `Directed.isLUB_ciSup`：Directed.isLUB_ciSup [Nonempty ι] {f : ι -> α} (hd
 : Directed (· <= ·) f) (H : BddAbove (range f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem Directed.ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α}
    (hd : Directed (· ≤ ·) f) (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| hd.isLUB_ciSup hf).trans forall_mem_range

@[to_dual DirectedOn.le_ciInf_set_iff]
/-
**DirectedOn.ciSup_set_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (
hs : s.Nonempty) (hd : DirectedOn (· <= ·) (f '' s)) (hf : BddAbove (f '' s)) : 
⨆ i : s, f i <= a ↔ forall i in s, f i <= a
参数：hs : s.Nonempty；hd : DirectedOn (· <= ·) (f '' s)；hf : BddAbove (f '' s)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `DirectedOn.isLUB_ciSup_set`：DirectedOn.isLUB_ciSup_set {f : β -> α} {s :
 Set β} (hd : DirectedOn (· <= ·) (f '' s)) (H : BddAbove (f '' s)) (Hne : s.Non
empty) : IsLUB (…
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
theorem DirectedOn.ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hd : DirectedOn (· ≤ ·) (f '' s)) (hf : BddAbove (f '' s)) :
    ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| hd.isLUB_ciSup_set hf hs).trans forall_mem_image

@[to_dual Directed.ciInf_le_of_le]
/-
**Directed.le_ciSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.le_ciSup_of_le {f : ι -> α} (hd : Directed (· <= ·) f) (H : BddAb
ove (range f)) (c : ι) (h : a <= f c) : a <= iSup f
参数：hd : Directed (· <= ·) f；H : BddAbove (range f)；c : ι；h : a <= f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Directed.le_ciSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderSup α] {f : ι → α},   Directed (fun x1 x2 => x1 ≤ x2) f → Bd
dAbove …
-/
theorem Directed.le_ciSup_of_le {f : ι → α} (hd : Directed (· ≤ ·) f)
    (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (hd.le_ciSup H c)

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[to_dual (attr := gcongr low)
/-- The indexed infimum of two functions are comparable if the functions are pointwise
comparable -/]
/-
**Directed.ciSup_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.ciSup_mono {f g : ι -> α} (hdf : Directed (· <= ·) f) (hdg : Dire
cted (· <= ·) g) (B : BddAbove (range g)) (H : forall x, f x <= g x) : iSup f <=
 iSup g
参数：hdf : Directed (· <= ·) f；hdg : Directed (· <= ·) g；B : BddAbove (range g)；H 
: forall x, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Directed.ciSup_le`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderSup α] {f : ι → α} {a : α} [Nonempty ι],   Directed (fun x1 
x2 => x…
· 使用定理 `Directed.le_ciSup_of_le`：Directed.le_ciSup_of_le {f : ι -> α} (hd : Dire
cted (· <= ·) f) (H : BddAbove (range f)) (c : ι) (h : a <= f c) : a <= iSup f
-/
theorem Directed.ciSup_mono {f g : ι → α} (hdf : Directed (· ≤ ·) f)
    (hdg : Directed (· ≤ ·) g) (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact hdf.ciSup_le fun x ↦ hdg.le_ciSup_of_le B x (H x)

@[to_dual DirectedOn.ciInf_set_le]
/-
**DirectedOn.le_ciSup_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.le_ciSup_set {f : β -> α} {s : Set β} (hd : DirectedOn (· <= ·)
 (f '' s)) (H : BddAbove (f '' s)) {c : β} (hc : c in s) : f c <= ⨆ i : s, f i
参数：hd : DirectedOn (· <= ·) (f '' s)；H : BddAbove (f '' s)；hc : c in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
-/
theorem DirectedOn.le_ciSup_set {f : β → α} {s : Set β} (hd : DirectedOn (· ≤ ·) (f '' s))
    (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) : f c ≤ ⨆ i : s, f i :=
  (hd.le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

@[to_dual (attr := simp)]
/-
**ciSup_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `csSup_singleton`：csSup_singleton (a : α) : sSup {a} = a
-/
theorem ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a := by
  rw [iSup, range_const, csSup_singleton]

@[to_dual (attr := simp)]
/-
**ciSup_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s default
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ciSup_unique [Unique ι] {s : ι → α} : ⨆ i, s i = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[to_dual]
/-
**ciSup_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι -> α) : ⨆ i, s i = s i
参数：i : ι；s : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨆ i, s i = s i :=
  @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[to_dual]
/-
**ciSup_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f hp
参数：hp : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ciSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp := by
  simp [hp]

@[to_dual]
/-
**ciSup_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_neg {p : Prop} {f : p -> α} (hp : ¬ p) : ⨆ (h : p), f h = sSup (∅ : 
Set α)
参数：hp : ¬ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.range_eq_empty_iff`：range_eq_empty_iff {f : ι -> α} : range f = ∅ ↔ 
IsEmpty ι
· 使用定理 `isEmpty_Prop`：isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p
-/
lemma ciSup_neg {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨆ (h : p), f h = sSup (∅ : Set α) := by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

@[to_dual]
/-
**ciSup_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_eq_ite {p : Prop} [Decidable p] {f : p -> α} : (⨆ h : p, f h) = if h
 : p then f h else sSup (∅ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `ciSup_neg`：ciSup_neg {p : Prop} {f : p -> α} (hp : ¬ p) : ⨆ (h : p), f h
 = sSup (∅ : Set α)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
lemma ciSup_eq_ite {p : Prop} [Decidable p] {f : p → α} :
    (⨆ h : p, f h) = if h : p then f h else sSup (∅ : Set α) := by
  by_cases H : p <;> simp [ciSup_neg, H]

@[to_dual]
/-
**cbiSup_eq_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiSup_eq_of_forall {p : ι -> Prop} {f : Subtype p -> α} (hp : forall i, p
 i) : ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f
参数：hp : forall i, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem cbiSup_eq_of_forall {p : ι → Prop} {f : Subtype p → α} (hp : ∀ i, p i) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f := by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp
  · rintro - ⟨i, rfl⟩
    simp

@[to_dual]
/-
**cbiSup_eq_of_forall_not** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cbiSup_eq_of_forall_not {p : ι -> Prop} {f : forall i, p i -> α} (hp : for
all i, ¬p i) : ⨆ (i) (h : p i), f i h = sSup ∅
参数：hp : forall i, ¬p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cbiSup_eq_of_forall_not {p : ι → Prop} {f : ∀ i, p i → α} (hp : ∀ i, ¬p i) :
    ⨆ (i) (h : p i), f i h = sSup ∅ := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty']
  · have (i : ι) : IsEmpty (p i) := ⟨hp i⟩
    simp only [iSup_of_empty', ciSup_const]

@[to_dual]
/-
**cbiSup_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiSup_empty {f : β -> α} : ⨆ i in (∅ : Set β), f i = sSup ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cbiSup_eq_of_forall_not`：cbiSup_eq_of_forall_not {p : ι -> Prop} {f : fo
rall i, p i -> α} (hp : forall i, ¬p i) : ⨆ (i) (h : p i), f i h = sSup ∅
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem cbiSup_empty {f : β → α} : ⨆ i ∈ (∅ : Set β), f i = sSup ∅ :=
  cbiSup_eq_of_forall_not Set.notMem_empty

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual Directed.ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/]
/-
**Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι 
-> α} (hd : Directed (· <= ·) f) (h₁ : forall i, f i <= b) (h₂ : forall w, w < b
 -> exists i, w < f i) : ⨆ i : ι, f i = b
参数：hd : Directed (· <= ·) f；h₁ : forall i, f i <= b；h₂ : forall w, w < b -> exis
ts i, w < f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.csSup_eq_of_forall_le_of_forall_lt_exists_gt`：∀ {α : Type u_1
} [inst : ConditionallyCompletePartialOrderSup α] {s : Set α} {b : α},   Directe
dOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty → (…
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
-/
theorem Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α}
    (hd : Directed (· ≤ ·) f) (h₁ : ∀ i, f i ≤ b) (h₂ : ∀ w, w < b → ∃ i, w < f i) :
    ⨆ i : ι, f i = b :=
  hd.directedOn_range.csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f)
    (forall_mem_range.mpr h₁) fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- **Nested intervals lemma**: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
/-
**Monotone.ciSup_mem_iInter_Icc_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.ciSup_mem_iInter_Icc_of_antitone [Preorder β] [IsDirectedOrder β]
 {f g : β -> α} (hf : Monotone f) (hg : Antitone g) (h : f <= g) : (⨆ n, f n) in
 ⋂ n, Icc (f n) (g n)
参数：hf : Monotone f；hg : Antitone g；h : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Monotone.forall_le_of_antitone`：Monotone.forall_le_of_antitone [IsDirect
edOrder α] [Preorder β] {f g : α -> β} (hf : Monotone f) (hg : Antitone g) (h : 
f <= g) (m n : α) : …
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `Directed.le_ciSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderSup α] {f : ι → α},   Directed (fun x1 x2 => x1 ≤ x2) f → Bd
dAbove …
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Directed.ciSup_le`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderSup α] {f : ι → α} {a : α} [Nonempty ι],   Directed (fun x1 
x2 => x…

--- 原说明 ---
**Nested intervals lemma**: if `f` is a monotone sequence, `g` is an antitone se
quence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n
]`.
-/
theorem Monotone.ciSup_mem_iInter_Icc_of_antitone [Preorder β] [IsDirectedOrder β]
    {f g : β → α} (hf : Monotone f) (hg : Antitone g) (h : f ≤ g) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine mem_iInter.2 fun n => ?_
  have : Nonempty β := ⟨n⟩
  have h₁ : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  have h₂ : Directed (· ≤ ·) f := hf.directed_le
  exact ⟨h₂.le_ciSup ⟨g <| n, forall_mem_range.2 h₁⟩ _, h₂.ciSup_le h₁⟩

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
/-
**ciSup_mem_iInter_Icc_of_antitone_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_mem_iInter_Icc_of_antitone_Icc [Preorder β] [IsDirectedOrder β] {f g
 : β -> α} (h : Antitone fun n => Icc (f n) (g n)) (h' : forall n, f n <= g n) :
 (⨆ n, f n) in ⋂ n, Icc (f n) (g n)
参数：h : Antitone fun n => Icc (f n) (g n)；h' : forall n, f n <= g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.ciSup_mem_iInter_Icc_of_antitone`：Monotone.ciSup_mem_iInter_Icc
_of_antitone [Preorder β] [IsDirectedOrder β] {f g : β -> α} (hf : Monotone f) (
hg : Antitone g) (h : f <= g) :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Icc_subset_Icc_iff`：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`.
-/
theorem ciSup_mem_iInter_Icc_of_antitone_Icc [Preorder β] [IsDirectedOrder β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

@[to_dual]
/-
**Directed.Ici_ciSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Directed.Ici_ciSup [Nonempty ι] {f : ι -> α} (hd : Directed (· <= ·) f) (h
f : BddAbove (range f)) : Ici (⨆ i, f i) = ⋂ i, Ici (f i)
参数：hd : Directed (· <= ·) f；hf : BddAbove (range f)。
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
· 使用定理 `Directed.ciSup_le_iff`：Directed.ciSup_le_iff [Nonempty ι] {f : ι -> α} {
a : α} (hd : Directed (· <= ·) f) (hf : BddAbove (range f)) : iSup f <= a ↔ fora
ll i, f i <…
-/
lemma Directed.Ici_ciSup [Nonempty ι] {f : ι → α} (hd : Directed (· ≤ ·) f)
    (hf : BddAbove (range f)) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) := by
  ext
  simpa using hd.ciSup_le_iff hf

@[to_dual]
/-
**ciSup_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_Iic [Preorder β] {f : β -> α} (a : β) (hf : Monotone f) : ⨆ x : Iic 
a, f x = f a
参数：a : β；hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Directed.le_ciSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderSup α] {f : ι → α},   Directed (fun x1 x2 => x1 ≤ x2) f → Bd
dAbove …
· 使用定理 `Directed.ciSup_le_iff`：Directed.ciSup_le_iff [Nonempty ι] {f : ι -> α} {
a : α} (hd : Directed (· <= ·) f) (hf : BddAbove (range f)) : iSup f <= a ↔ fora
ll i, f i <…
-/
theorem ciSup_Iic [Preorder β] {f : β → α} (a : β) (hf : Monotone f) :
    ⨆ x : Iic a, f x = f a := by
  have hd : Directed (· ≤ ·) (fun x : Iic a ↦ f x) := fun x y ↦ ⟨⟨a, le_refl a⟩, ⟨hf x.2, hf y.2⟩⟩
  have H : BddAbove (range fun x : Iic a ↦ f x) := ⟨f a, fun _ ↦ by aesop⟩
  apply (hd.le_ciSup H (⟨a, le_refl a⟩ : Iic a)).antisymm'
  rw [hd.ciSup_le_iff H]
  rintro ⟨a, h⟩
  exact hf h

end ConditionallyCompletePartialOrderSup

/-
**Directed.ciInf_le_ciSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Directed.ciInf_le_ciSup [ConditionallyCompletePartialOrder α] [Nonempty ι]
 {f : ι -> α} (hd : Directed (· >= ·) f) (hf : BddBelow (range f)) (hd' : Direct
ed (· <= ·) f) (hf' : BddAbove (range f)) : ⨅ i, f i <= ⨆ i, f i
参数：hd : Directed (· >= ·) f；hf : BddBelow (range f)；hd' : Directed (· <= ·) f；hf
' : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Directed.ciInf_le`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderInf α] {f : ι → α},   Directed (fun x1 x2 => x2 ≤ x1) f → Bd
dBelow …
· 使用定理 `Directed.le_ciSup`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Conditionally
CompletePartialOrderSup α] {f : ι → α},   Directed (fun x1 x2 => x1 ≤ x2) f → Bd
dAbove …
-/
lemma Directed.ciInf_le_ciSup [ConditionallyCompletePartialOrder α] [Nonempty ι] {f : ι → α}
    (hd : Directed (· ≥ ·) f) (hf : BddBelow (range f))
    (hd' : Directed (· ≤ ·) f) (hf' : BddAbove (range f)) :
    ⨅ i, f i ≤ ⨆ i, f i :=
  (hd.ciInf_le hf (Classical.arbitrary _)).trans <| hd'.le_ciSup hf' (Classical.arbitrary _)

namespace GaloisConnection

section Sup

variable [ConditionallyCompletePartialOrderSup α] [ConditionallyCompletePartialOrderSup β]
    [Nonempty ι] {l : α → β} {u : β → α}

@[to_dual u_csInf_of_directedOn']
/-
**GaloisConnection.l_csSup_of_directedOn'** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConne
ction`。
形式化陈述：l_csSup_of_directedOn' (gc : GaloisConnection l u) {s : Set α} (hd : Direc
tedOn (· <= ·) s) (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = sSup (l 
'' s)
参数：gc : GaloisConnection l u；hd : DirectedOn (· <= ·) s；hne : s.Nonempty；hbdd : 
BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `GaloisConnection.isLUB_l_image`：isLUB_l_image {s : Set α} {a : α} (h : I
sLUB s a) : IsLUB (l '' s) (l a)
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
-/
theorem l_csSup_of_directedOn' (gc : GaloisConnection l u) {s : Set α}
    (hd : DirectedOn (· ≤ ·) s) (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) :=
  gc.isLUB_l_image (hd.isLUB_csSup hne hbdd) |>.unique <|
    (hd.mono_comp gc.monotone_l).isLUB_csSup (hne.image l) (gc.monotone_l.map_bddAbove hbdd)

@[to_dual u_csInf_of_directedOn]
/-
**GaloisConnection.l_csSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnec
tion`。
形式化陈述：l_csSup_of_directedOn (gc : GaloisConnection l u) {s : Set α} (hd : Direct
edOn (· <= ·) s) (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, 
l x
参数：gc : GaloisConnection l u；hd : DirectedOn (· <= ·) s；hne : s.Nonempty；hbdd : 
BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `GaloisConnection.l_csSup_of_directedOn'`：l_csSup_of_directedOn' (gc : Ga
loisConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s) (hne : s.Nonempty) 
(hbdd : BddAbove s) : l (sSup…
-/
theorem l_csSup_of_directedOn (gc : GaloisConnection l u) {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x := by
  simpa only [← comp_def, ← sSup_range, range_comp, Subtype.range_coe_subtype, ofPred_mem_eq]
    using gc.l_csSup_of_directedOn' hd hne hbdd

@[to_dual u_ciInf_of_directed]
/-
**GaloisConnection.l_ciSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnecti
on`。
形式化陈述：l_ciSup_of_directed (gc : GaloisConnection l u) {f : ι -> α} (hd : Directe
d (· <= ·) f) (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i)
参数：gc : GaloisConnection l u；hd : Directed (· <= ·) f；hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `GaloisConnection.l_csSup_of_directedOn`：l_csSup_of_directedOn (gc : Galo
isConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s) (hne : s.Nonempty) (h
bdd : BddAbove s) : l (sSup …
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `iSup_range'`：iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b 
= ⨆ i, g (f i)
-/
theorem l_ciSup_of_directed (gc : GaloisConnection l u) {f : ι → α} (hd : Directed (· ≤ ·) f)
    (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i) := by
  rw [iSup, gc.l_csSup_of_directedOn hd.directedOn_range (range_nonempty _) hf, iSup_range']

@[to_dual u_ciInf_set_of_directedOn]
/-
**GaloisConnection.l_ciSup_set_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `GaloisCo
nnection`。
形式化陈述：l_ciSup_set_of_directedOn (gc : GaloisConnection l u) {s : Set γ} {f : γ -
> α} (hd : DirectedOn (· <= ·) (f '' s)) (hf : BddAbove (f '' s)) (hne : s.Nonem
pty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i)
参数：gc : GaloisConnection l u；hd : DirectedOn (· <= ·) (f '' s)；hf : BddAbove (f 
'' s)；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `GaloisConnection.l_ciSup_of_directed`：l_ciSup_of_directed (gc : GaloisCo
nnection l u) {f : ι -> α} (hd : Directed (· <= ·) f) (hf : BddAbove (range f)) 
: l (⨆ i, f i) = ⨆ i, l (f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
theorem l_ciSup_set_of_directedOn (gc : GaloisConnection l u) {s : Set γ} {f : γ → α}
    (hd : DirectedOn (· ≤ ·) (f '' s)) (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  refine gc.l_ciSup_of_directed ?_ hf
  simpa [← directedOn_range, ← comp_def, range_comp]

end Sup

end GaloisConnection

namespace OrderIso

section Sup

variable [ConditionallyCompletePartialOrderSup α] [ConditionallyCompletePartialOrderSup β]
  [Nonempty ι]

-- these need to have `directed` in their names.
@[to_dual]
/-
**OrderIso.map_csSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_csSup_of_directedOn (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·)
 s) (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = ⨆ x : s, e x
参数：e : α ≃o β；hd : DirectedOn (· <= ·) s；hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_csSup_of_directedOn`：l_csSup_of_directedOn (gc : Galo
isConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s) (hne : s.Nonempty) (h
bdd : BddAbove s) : l (sSup …
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_csSup_of_directedOn (e : α ≃o β) {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup_of_directedOn hd hne hbdd

@[to_dual]
/-
**OrderIso.map_csSup_of_directedOn'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_csSup_of_directedOn' (e : α ≃o β) {s : Set α} (hd : DirectedOn (· <= ·
) s) (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s)
参数：e : α ≃o β；hd : DirectedOn (· <= ·) s；hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_csSup_of_directedOn'`：l_csSup_of_directedOn' (gc : Ga
loisConnection l u) {s : Set α} (hd : DirectedOn (· <= ·) s) (hne : s.Nonempty) 
(hbdd : BddAbove s) : l (sSup…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_csSup_of_directedOn' (e : α ≃o β) {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup_of_directedOn' hd hne hbdd

@[to_dual]
/-
**OrderIso.map_ciSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_ciSup_of_directed (e : α ≃o β) {f : ι -> α} (hd : Directed (· <= ·) f)
 (hf : BddAbove (range f)) : e (⨆ i, f i) = ⨆ i, e (f i)
参数：e : α ≃o β；hd : Directed (· <= ·) f；hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_ciSup_of_directed`：l_ciSup_of_directed (gc : GaloisCo
nnection l u) {f : ι -> α} (hd : Directed (· <= ·) f) (hf : BddAbove (range f)) 
: l (⨆ i, f i) = ⨆ i, l (f…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_ciSup_of_directed (e : α ≃o β) {f : ι → α} (hd : Directed (· ≤ ·) f)
    (hf : BddAbove (range f)) : e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup_of_directed hd hf

@[to_dual]
/-
**OrderIso.map_ciSup_set_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_ciSup_set_of_directedOn (e : α ≃o β) {s : Set γ} {f : γ -> α} (hd : Di
rectedOn (· <= ·) (f '' s)) (hf : BddAbove (f '' s)) (hne : s.Nonempty) : e (⨆ i
 : s, f i) = ⨆ i : s, e (f i)
参数：e : α ≃o β；hd : DirectedOn (· <= ·) (f '' s)；hf : BddAbove (f '' s)；hne : s.N
onempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_ciSup_set_of_directedOn`：l_ciSup_set_of_directedOn (g
c : GaloisConnection l u) {s : Set γ} {f : γ -> α} (hd : DirectedOn (· <= ·) (f 
'' s)) (hf : BddAbove (f '' s)) …
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_ciSup_set_of_directedOn (e : α ≃o β) {s : Set γ} {f : γ → α}
    (hd : DirectedOn (· ≤ ·) (f '' s)) (hf : BddAbove (f '' s)) (hne : s.Nonempty) :
    e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set_of_directedOn hd hf hne

end Sup

end OrderIso

