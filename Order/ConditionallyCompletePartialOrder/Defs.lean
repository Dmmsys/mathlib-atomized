/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.SetNotation

/-! # Conditionally complete partial orders

This file defines *conditionally complete partial orders* with suprema, infima or both. These are
partial orders where every nonempty, upwards (downwards) directed set which is
bounded above (below) has a least upper bound (greatest lower bound). This class extends `SupSet`
(`InfSet`) and the requirement is that `sSup` (`sInf`) must be the least upper bound.

The three classes defined herein are:

+ `ConditionallyCompletePartialOrderSup` for partial orders with suprema,
+ `ConditionallyCompletePartialOrderInf` for partial orders with infima, and
+ `ConditionallyCompletePartialOrder` for partial orders with both suprema and infima

One common use case for these classes is the order on a von Neumann algebra, or W⋆-algebra.
This is the strongest order-theoretic structure satisfied by a von Neumann algebra;
in particular it is *not* a conditionally complete *lattice*, and indeed it is a lattice if and only
if the algebra is commutative. In addition, `ℂ` can be made to satisfy this class (one must provide
a suitable `SupSet` instance), with the order `w ≤ z ↔ w.re ≤ z.re ∧ w.im = z.im`, which is
available in the `ComplexOrder` namespace.

These use cases are the motivation for defining three classes, as compared with other parts of the
order theory library, where only the supremum versions are defined (e.g., `CompletePartialOrder` and
`OmegaCompletePartialOrder`). We note that, if these classes are used outside of order theory, then
it is more likely that the infimum versions would be useful. Indeed, whenever the underlying type
has an antitone involution (e.g., if it is an ordered ring, then negation would be such a map),
then any `ConditionallyCompletePartialOrder{Sup,Inf}` is automatically a
`ConditionallyCompletePartialOrder`. Because of the `to_dual` attribute, the additional overhead
required to add and maintain the infimum version is minimal.

-/

public section

variable {ι : Sort*} {α : Type*}

/-- Conditionally complete partial orders (with infima) are partial orders
where every nonempty, directed set which is bounded below has a greatest lower bound. -/
/-
**ConditionallyCompletePartialOrderInf** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditionally complete partial orders (with infima) are partial orders
where every nonempty, directed set which is bounded below has a greatest lower b
ound.
-/
class ConditionallyCompletePartialOrderInf (α : Type*)
    extends PartialOrder α, InfSet α where
  /-- For each nonempty, directed set `s` which is bounded below, `sInf s` is
  the greatest lower bound of `s`. -/
  isGLB_csInf_of_directed :
    ∀ s, DirectedOn (· ≥ ·) s → s.Nonempty → BddBelow s → IsGLB s (sInf s)

/-- Conditionally complete partial orders (with suprema) are partial orders
where every nonempty, directed set which is bounded above has a least upper bound. -/
@[to_dual existing]
/-
**ConditionallyCompletePartialOrderSup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditionally complete partial orders (with suprema) are partial orders
where every nonempty, directed set which is bounded above has a least upper boun
d.
-/
class ConditionallyCompletePartialOrderSup (α : Type*)
    extends PartialOrder α, SupSet α where
  /-- For each nonempty, directed set `s` which is bounded above, `sSup s` is
  the least upper bound of `s`. -/
  isLUB_csSup_of_directed :
    ∀ s, DirectedOn (· ≤ ·) s → s.Nonempty → BddAbove s → IsLUB s (sSup s)

/-- Conditionally complete partial orders (with suprema and infima) are partial orders
where every nonempty, directed set which is bounded above (respectively, below) has a
least upper (respectively, greatest lower) bound. -/
/-
**ConditionallyCompletePartialOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conditionally complete partial orders (with suprema and infima) are partial orde
rs
where every nonempty, directed set which is bounded above (respectively, below) 
has a
least upper (respectively, greatest lower) bound.
-/
class ConditionallyCompletePartialOrder (α : Type*)
    extends ConditionallyCompletePartialOrderSup α, ConditionallyCompletePartialOrderInf α where

attribute [to_dual existing]
  ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α]
variable {f : ι → α} {s : Set α} {a : α}

@[to_dual]
/-
**DirectedOn.isLUB_csSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty → BddAbove s → IsLUB s (s
Sup s)
参数：fun x1 x2 => x1 ≤ x2；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed`：∀ {α : Typ
e u_3} [self : ConditionallyCompletePartialOrderSup α] (s : Set α),   DirectedOn
 (fun x1 x2 => x1 ≤ x2) s → s.Nonempty → BddAbove …
-/
protected lemma DirectedOn.isLUB_csSup (h_dir : DirectedOn (· ≤ ·) s)
    (h_non : s.Nonempty) (h_bdd : BddAbove s) : IsLUB s (sSup s) :=
  ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed s h_dir h_non h_bdd

@[to_dual csInf_le]
/-
**DirectedOn.le_csSup** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAbove s → a ∈ s → a ≤ sSu
p s
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
-/
protected lemma DirectedOn.le_csSup (hs : DirectedOn (· ≤ ·) s)
    (h_bdd : BddAbove s) (ha : a ∈ s) : a ≤ sSup s :=
  (hs.isLUB_csSup ⟨a, ha⟩ h_bdd).1 ha

@[to_dual le_csInf]
/-
**DirectedOn.csSup_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : ConditionallyCompletePartialOrderSup α] {s : Set 
α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty → (∀ b ∈ s, b ≤ a
) → sSup s ≤ a
参数：fun x1 x2 => x1 ≤ x2；∀ b ∈ s, b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DirectedOn.isLUB_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompletePa
rtialOrderSup α] {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Nonempty
 → BddAbove …
-/
protected lemma DirectedOn.csSup_le (hd : DirectedOn (· ≤ ·) s) (h_non : s.Nonempty)
    (ha : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (hd.isLUB_csSup h_non ⟨a, ha⟩).2 ha

@[to_dual ciInf_le]
/-
**Directed.le_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : ConditionallyCompletePartialOrderS
up α] {f : ι → α},   Directed (fun x1 x2 => x1 ≤ x2) f → BddAbove (Set.range f) 
→ ∀ (i : ι), f i ≤ ⨆ j, f j
参数：fun x1 x2 => x1 ≤ x2；Set.range f；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.le_csSup`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → BddAb
ove s → a…
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
protected lemma Directed.le_ciSup (hf : Directed (· ≤ ·) f)
    (hf_bdd : BddAbove (Set.range f)) (i : ι) : f i ≤ ⨆ j, f j :=
  hf.directedOn_range.le_csSup hf_bdd <| Set.mem_range_self _

@[to_dual le_ciInf]
/-
**Directed.ciSup_le** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : ConditionallyCompletePartialOrderS
up α] {f : ι → α} {a : α} [Nonempty ι],   Directed (fun x1 x2 => x1 ≤ x2) f → (∀
 (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
参数：fun x1 x2 => x1 ≤ x2；∀ (i : ι), f i ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedOn.csSup_le`：∀ {α : Type u_2} [inst : ConditionallyCompleteParti
alOrderSup α] {s : Set α} {a : α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → s.Non
empty → (…
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
protected lemma Directed.ciSup_le [Nonempty ι] (hf : Directed (· ≤ ·) f)
    (ha : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  hf.directedOn_range.csSup_le (Set.range_nonempty _) <| Set.forall_mem_range.2 ha
