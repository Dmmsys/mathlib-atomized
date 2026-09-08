/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Wrenna Robson, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Closure

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : Set α` and `t : Set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
* [Birkhoff, Garrett *Lattice Theory*][birkhoff1940]

## Tags

concept, formal concept analysis, intent, extent, object, attribute
-/

@[expose] public section


open Function OrderDual Order Set

variable {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Lower and upper polars -/

/-- The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
/-
**upperPolar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：upperPolar (s : Set α) : Set β
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of
 all elements
which `r` relates to all elements of `s`.
-/
def upperPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

/-- The lower polar of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
/-
**lowerPolar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lowerPolar (t : Set β) : Set α
参数：t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower polar of `t : Set β` along a relation `r : α → β → Prop` is the set of
 all elements
which `r` relates to all elements of `t`.
-/
def lowerPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }
/-
**upperPolar_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} {s : Set α} [inst : LE α], upperPolar (fun x1 x2 => x1 ≤ 
x2) s = upperBounds s
参数：fun x1 x2 => x1 ≤ x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem upperPolar_le [LE α] : upperPolar (· ≤ ·) s = upperBounds s := rfl
/-
**lowerPolar_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {β : Type u_3} {t : Set β} [inst : LE β], lowerPolar (fun x1 x2 => x1 ≤ 
x2) t = lowerBounds t
参数：fun x1 x2 => x1 ≤ x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem lowerPolar_le [LE β] : lowerPolar (· ≤ ·) t = lowerBounds t := rfl

variable {r} {a : α} {b : β}
/-
**mem_upperPolar_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_upperPolar_iff : b in upperPolar r s ↔ forall ⦃a⦄, a in s -> r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_upperPolar_iff : b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b := .rfl
/-
**mem_lowerPolar_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_lowerPolar_iff : a in lowerPolar r t ↔ forall ⦃b⦄, b in t -> r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_lowerPolar_iff : a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b := .rfl
/-
**subset_upperPolar_iff_subset_lowerPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_upperPolar_iff_subset_lowerPolar : t subseteq upperPolar r s ↔ s su
bseteq lowerPolar r t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_upperPolar_iff_subset_lowerPolar :
    t ⊆ upperPolar r s ↔ s ⊆ lowerPolar r t :=
  ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩

variable (r)
/-
**gc_upperPolar_lowerPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_upperPolar_lowerPolar : GaloisConnection (toDual ∘ upperPolar r) (lower
Polar r ∘ ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_upperPolar_iff_subset_lowerPolar`：subset_upperPolar_iff_subset_lo
werPolar : t subseteq upperPolar r s ↔ s subseteq lowerPolar r t
-/
theorem gc_upperPolar_lowerPolar :
    GaloisConnection (toDual ∘ upperPolar r) (lowerPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar
/-
**gc_lowerPolar_upperPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_lowerPolar_upperPolar : GaloisConnection (toDual ∘ lowerPolar r) (upper
Polar r ∘ ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_upperPolar_iff_subset_lowerPolar`：subset_upperPolar_iff_subset_lo
werPolar : t subseteq upperPolar r s ↔ s subseteq lowerPolar r t
-/
theorem gc_lowerPolar_upperPolar :
    GaloisConnection (toDual ∘ lowerPolar r) (upperPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar
/-
**upperPolar_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_swap (t : Set β) : upperPolar (swap r) t = lowerPolar r t
参数：t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem upperPolar_swap (t : Set β) : upperPolar (swap r) t = lowerPolar r t :=
  rfl
/-
**lowerPolar_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_swap (s : Set α) : lowerPolar (swap r) s = upperPolar r s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lowerPolar_swap (s : Set α) : lowerPolar (swap r) s = upperPolar r s :=
  rfl

@[simp]
/-
**upperPolar_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_empty : upperPolar r ∅ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
-/
theorem upperPolar_empty : upperPolar r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim

@[simp]
/-
**lowerPolar_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_empty : lowerPolar r ∅ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperPolar_empty`：upperPolar_empty : upperPolar r ∅ = univ
-/
theorem lowerPolar_empty : lowerPolar r ∅ = univ :=
  upperPolar_empty _

@[simp]
/-
**mem_upperPolar_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_upperPolar_singleton : b in upperPolar r {a} ↔ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_upperPolar_singleton : b ∈ upperPolar r {a} ↔ r a b := by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
/-
**mem_lowerPolar_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_lowerPolar_singleton : a in lowerPolar r {b} ↔ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_lowerPolar_singleton : a ∈ lowerPolar r {b} ↔ r a b := by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
/-
**upperPolar_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_union (s₁ s₂ : Set α) : upperPolar r (s₁ union s₂) = upperPolar
 r s₁ inter upperPolar r s₂
参数：s₁ s₂ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `forall₂_or_left`：forall₂_or_left : (forall x, p x ∨ q x -> r x) ↔ (foral
l x, p x -> r x) ∧ forall x, q x -> r x
-/
theorem upperPolar_union (s₁ s₂ : Set α) :
    upperPolar r (s₁ ∪ s₂) = upperPolar r s₁ ∩ upperPolar r s₂ :=
  ext fun _ => forall₂_or_left

@[simp]
/-
**lowerPolar_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_union (t₁ t₂ : Set β) : lowerPolar r (t₁ union t₂) = lowerPolar
 r t₁ inter lowerPolar r t₂
参数：t₁ t₂ : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperPolar_union`：upperPolar_union (s₁ s₂ : Set α) : upperPolar r (s₁ un
ion s₂) = upperPolar r s₁ inter upperPolar r s₂
-/
theorem lowerPolar_union (t₁ t₂ : Set β) :
    lowerPolar r (t₁ ∪ t₂) = lowerPolar r t₁ ∩ lowerPolar r t₂ :=
  upperPolar_union ..

@[simp]
/-
**upperPolar_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_iUnion (f : ι -> Set α) : upperPolar r (⋃ i, f i) = ⋂ i, upperP
olar r (f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
theorem upperPolar_iUnion (f : ι → Set α) :
    upperPolar r (⋃ i, f i) = ⋂ i, upperPolar r (f i) :=
  (gc_upperPolar_lowerPolar r).l_iSup

@[simp]
/-
**lowerPolar_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_iUnion (f : ι -> Set β) : lowerPolar r (⋃ i, f i) = ⋂ i, lowerP
olar r (f i)
参数：f : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperPolar_iUnion`：upperPolar_iUnion (f : ι -> Set α) : upperPolar r (⋃ 
i, f i) = ⋂ i, upperPolar r (f i)
-/
theorem lowerPolar_iUnion (f : ι → Set β) :
    lowerPolar r (⋃ i, f i) = ⋂ i, lowerPolar r (f i) :=
  upperPolar_iUnion ..
/-
**upperPolar_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_iUnion (f : ι -> Set α) : upperPolar r (⋃ i, f i) = ⋂ i, upperP
olar r (f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
theorem upperPolar_iUnion₂ (f : ∀ i, κ i → Set α) :
    upperPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), upperPolar r (f i j) :=
  (gc_upperPolar_lowerPolar r).l_iSup₂
/-
**lowerPolar_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_iUnion (f : ι -> Set β) : lowerPolar r (⋃ i, f i) = ⋂ i, lowerP
olar r (f i)
参数：f : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperPolar_iUnion`：upperPolar_iUnion (f : ι -> Set α) : upperPolar r (⋃ 
i, f i) = ⋂ i, upperPolar r (f i)
-/
theorem lowerPolar_iUnion₂ (f : ∀ i, κ i → Set β) :
    lowerPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), lowerPolar r (f i j) :=
  upperPolar_iUnion₂ ..
/-
**subset_lowerPolar_upperPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_lowerPolar_upperPolar (s : Set α) : s subseteq lowerPolar r (upperP
olar r s)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
theorem subset_lowerPolar_upperPolar (s : Set α) :
    s ⊆ lowerPolar r (upperPolar r s) :=
  (gc_upperPolar_lowerPolar r).le_u_l _
/-
**subset_upperPolar_lowerPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_upperPolar_lowerPolar (t : Set β) : t subseteq upperPolar r (lowerP
olar r t)
参数：t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_lowerPolar_upperPolar`：subset_lowerPolar_upperPolar (s : Set α) :
 s subseteq lowerPolar r (upperPolar r s)
-/
theorem subset_upperPolar_lowerPolar (t : Set β) :
    t ⊆ upperPolar r (lowerPolar r t) :=
  subset_lowerPolar_upperPolar _ t

@[simp]
/-
**upperPolar_lowerPolar_upperPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_lowerPolar_upperPolar (s : Set α) : upperPolar r (lowerPolar r 
<| upperPolar r s) = upperPolar r s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
theorem upperPolar_lowerPolar_upperPolar (s : Set α) :
    upperPolar r (lowerPolar r <| upperPolar r s) = upperPolar r s :=
  (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[simp]
/-
**lowerPolar_upperPolar_lowerPolar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_upperPolar_lowerPolar (t : Set β) : lowerPolar r (upperPolar r 
<| lowerPolar r t) = lowerPolar r t
参数：t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperPolar_lowerPolar_upperPolar`：upperPolar_lowerPolar_upperPolar (s : 
Set α) : upperPolar r (lowerPolar r <| upperPolar r s) = upperPolar r s
-/
theorem lowerPolar_upperPolar_lowerPolar (t : Set β) :
    lowerPolar r (upperPolar r <| lowerPolar r t) = lowerPolar r t :=
  upperPolar_lowerPolar_upperPolar _ t
/-
**upperPolar_anti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_anti : Antitone (upperPolar r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
theorem upperPolar_anti : Antitone (upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_l
/-
**lowerPolar_anti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_anti : Antitone (lowerPolar r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperPolar_anti`：upperPolar_anti : Antitone (upperPolar r)
-/
theorem lowerPolar_anti : Antitone (lowerPolar r) :=
  upperPolar_anti _
/-
**lowerPolar_upperPolar_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerPolar_upperPolar_monotone : Monotone (lowerPolar r ∘ upperPolar r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u_comp_l`：∀ {α : Type u} {β : Type v} [inst : 
Preorder α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l 
u → Monotone (u ∘ l)
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
theorem lowerPolar_upperPolar_monotone : Monotone (lowerPolar r ∘ upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_u_comp_l
/-
**upperPolar_lowerPolar_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperPolar_lowerPolar_monotone : Monotone (upperPolar r ∘ lowerPolar r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u_comp_l`：∀ {α : Type u} {β : Type v} [inst : 
Preorder α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l 
u → Monotone (u ∘ l)
· 使用定理 `gc_lowerPolar_upperPolar`：gc_lowerPolar_upperPolar : GaloisConnection (t
oDual ∘ lowerPolar r) (upperPolar r ∘ ofDual)
-/
theorem upperPolar_lowerPolar_monotone : Monotone (upperPolar r ∘ lowerPolar r) :=
  (gc_lowerPolar_upperPolar r).monotone_u_comp_l

/-- The `extentClosure` of a set is the smallest extent containing it. See
`IsExtent.lowerPolar_upperPolar_subset` for this proof. -/
@[simps!]
/-
**extentClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：extentClosure (r : α -> β -> Prop) : ClosureOperator (Set α)
参数：r : α -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)

--- 原说明 ---
The `extentClosure` of a set is the smallest extent containing it. See
`IsExtent.lowerPolar_upperPolar_subset` for this proof.
-/
def extentClosure (r : α → β → Prop) : ClosureOperator (Set α) :=
  (gc_upperPolar_lowerPolar r).closureOperator

/-- The `intentClosure` of a set is the smallest intent containing it. See
`IsIntent.upperPolar_lowerPolar_subset` for this proof. -/
@[simps!]
/-
**intentClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：intentClosure (r : α -> β -> Prop) : ClosureOperator (Set β)
参数：r : α -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `gc_lowerPolar_upperPolar`：gc_lowerPolar_upperPolar : GaloisConnection (t
oDual ∘ lowerPolar r) (upperPolar r ∘ ofDual)

--- 原说明 ---
The `intentClosure` of a set is the smallest intent containing it. See
`IsIntent.upperPolar_lowerPolar_subset` for this proof.
-/
def intentClosure (r : α → β → Prop) : ClosureOperator (Set β) :=
  (gc_lowerPolar_upperPolar r).closureOperator

/-! ### Intent and extent -/

namespace Order

variable {r}

/--
A set is an extent when either of the following equivalent definitions holds:

- The `lowerPolar` of its `upperPolar` is itself.
- The set is the `lowerPolar` of some other set.

The latter is used as a definition, but one can rewrite using the former via `IsExtent.eq`.
-/
/-
**Order.IsExtent** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：IsExtent (r : α -> β -> Prop) (s : Set α)
参数：r : α -> β -> Prop；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is an extent when either of the following equivalent definitions holds:

- The `lowerPolar` of its `upperPolar` is itself.
- The set is the `lowerPolar` of some other set.

The latter is used as a definition, but one can rewrite using the former via `Is
Extent.eq`.
-/
def IsExtent (r : α → β → Prop) (s : Set α) := s ∈ range (lowerPolar r)
/-
**Order.isExtent_lowerPolar** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t : Set β}, Order.IsEx
tent r (lowerPolar r t)
参数：lowerPolar r t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem isExtent_lowerPolar : IsExtent r (lowerPolar r t) := ⟨_, rfl⟩
/-
**Order.isExtent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isExtent_iff : IsExtent r s ↔ lowerPolar r (upperPolar r s) = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerPolar_upperPolar_lowerPolar`：lowerPolar_upperPolar_lowerPolar (t : 
Set β) : lowerPolar r (upperPolar r <| lowerPolar r t) = lowerPolar r t
-/
theorem isExtent_iff : IsExtent r s ↔ lowerPolar r (upperPolar r s) = s :=
  ⟨fun ⟨t, h⟩ ↦ h ▸ lowerPolar_upperPolar_lowerPolar r t, fun h ↦ ⟨_, h⟩⟩

alias ⟨IsExtent.eq, _⟩ := isExtent_iff

@[simp]
/-
**Order.IsExtent.univ** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsExtent`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop}, Order.IsExtent r Set.u
niv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.isExtent_iff`：isExtent_iff : IsExtent r s ↔ lowerPolar r (upperPol
ar r s) = s
· 使用定理 `GaloisConnection.u_l_top`：u_l_top {l : α -> β} {u : β -> α} (gc : Galois
Connection l u) : u (l ⊤) = ⊤
· 使用定理 `gc_upperPolar_lowerPolar`：gc_upperPolar_lowerPolar : GaloisConnection (t
oDual ∘ upperPolar r) (lowerPolar r ∘ ofDual)
-/
protected theorem IsExtent.univ : IsExtent r univ :=
  isExtent_iff.2 (gc_upperPolar_lowerPolar r).u_l_top
/-
**Order.IsExtent.inter** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsExtent`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s s' : Set α},   Order
.IsExtent r s → Order.IsExtent r s' → Order.IsExtent r (s ∩ s')
参数：s ∩ s'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lowerPolar_union`：lowerPolar_union (t₁ t₂ : Set β) : lowerPolar r (t₁ un
ion t₂) = lowerPolar r t₁ inter lowerPolar r t₂
-/
protected theorem IsExtent.inter {s' : Set α} :
    IsExtent r s → IsExtent r s' → IsExtent r (s ∩ s') := by
  simp_rw [IsExtent, mem_range, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨_, lowerPolar_union r t t'⟩
/-
**Order.IsExtent.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsExtent`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} {r : α → β → Prop} (f : ι →
 Set α),   (∀ (i : ι), Order.IsExtent r (f i)) → Order.IsExtent r (⋂ i, f i)
参数：f : ι → Set α；∀ (i : ι), Order.IsExtent r (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lowerPolar_iUnion`：lowerPolar_iUnion (f : ι -> Set β) : lowerPolar r (⋃ 
i, f i) = ⋂ i, lowerPolar r (f i)
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用定理 `Order.IsExtent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s
 : Set α}, Order.IsExtent r s → lowerPolar r (upperPolar r s) = s
-/
protected theorem IsExtent.iInter (f : ι → Set α) (hf : ∀ i, IsExtent r (f i)) :
    IsExtent r (⋂ i, f i) :=
  ⟨_, (lowerPolar_iUnion ..).trans (iInter_congr fun i ↦ (hf i).eq)⟩
/-
**Order.IsExtent.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsExtent`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} {r : α → β → Prop} (f : ι →
 Set α),   (∀ (i : ι), Order.IsExtent r (f i)) → Order.IsExtent r (⋂ i, f i)
参数：f : ι → Set α；∀ (i : ι), Order.IsExtent r (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lowerPolar_iUnion`：lowerPolar_iUnion (f : ι -> Set β) : lowerPolar r (⋃ 
i, f i) = ⋂ i, lowerPolar r (f i)
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用定理 `Order.IsExtent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s
 : Set α}, Order.IsExtent r s → lowerPolar r (upperPolar r s) = s
-/
protected theorem IsExtent.iInter₂ (f : ∀ i, κ i → Set α) (hf : ∀ i j, IsExtent r (f i j)) :
    IsExtent r (⋂ (i) (j), f i j) :=
  ⟨_, (lowerPolar_iUnion₂ ..).trans (iInter₂_congr fun i j ↦ (hf i j).eq)⟩
/-
**Order.IsExtent.lowerPolar_upperPolar_subset** 是 Mathlib 中的一个定理，位于命名空间 `Order.I
sExtent`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s s' : Set α},   Order
.IsExtent r s → s' ⊆ s → lowerPolar r (upperPolar r s') ⊆ s
参数：upperPolar r s'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsExtent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s
 : Set α}, Order.IsExtent r s → lowerPolar r (upperPolar r s) = s
· 使用定理 `lowerPolar_upperPolar_monotone`：lowerPolar_upperPolar_monotone : Monoton
e (lowerPolar r ∘ upperPolar r)
-/
theorem IsExtent.lowerPolar_upperPolar_subset {s' : Set α} (h : IsExtent r s) (hs' : s' ⊆ s) :
    lowerPolar r (upperPolar r s') ⊆ s := by
  rw [← h.eq]
  exact lowerPolar_upperPolar_monotone r hs'

/--
A set is an intent when either of the following equivalent definitions holds:

- The `upperPolar` of its `lowerPolar` is itself.
- The set is the `upperPolar` of some other set.

The latter is used as a definition, but one can rewrite using the former via `IsIntent.eq`.
-/
/-
**Order.IsIntent** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：IsIntent (r : α -> β -> Prop) (t : Set β)
参数：r : α -> β -> Prop；t : Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set is an intent when either of the following equivalent definitions holds:

- The `upperPolar` of its `lowerPolar` is itself.
- The set is the `upperPolar` of some other set.

The latter is used as a definition, but one can rewrite using the former via `Is
Intent.eq`.
-/
def IsIntent (r : α → β → Prop) (t : Set β) := t ∈ range (upperPolar r)
/-
**Order.isIntent_upperPolar** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s : Set α}, Order.IsIn
tent r (upperPolar r s)
参数：upperPolar r s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem isIntent_upperPolar : IsIntent r (upperPolar r s) := ⟨_, rfl⟩
/-
**Order.isIntent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：isIntent_iff : IsIntent r t ↔ upperPolar r (lowerPolar r t) = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isExtent_iff`：isExtent_iff : IsExtent r s ↔ lowerPolar r (upperPol
ar r s) = s
-/
theorem isIntent_iff : IsIntent r t ↔ upperPolar r (lowerPolar r t) = t := isExtent_iff

alias ⟨IsIntent.eq, _⟩ := isIntent_iff
/-
**Order.IsIntent.univ** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsIntent`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop}, Order.IsIntent r Set.u
niv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.univ`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop},
 Order.IsExtent r Set.univ
-/
@[simp] protected theorem IsIntent.univ : IsIntent r univ := IsExtent.univ
/-
**Order.IsIntent.inter** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsIntent`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t t' : Set β},   Order
.IsIntent r t → Order.IsIntent r t' → Order.IsIntent r (t ∩ t')
参数：t ∩ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.inter`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop}
 {s s' : Set α},   Order.IsExtent r s → Order.IsExtent r s' → Order.IsExtent r (
s ∩ s')
-/
protected theorem IsIntent.inter {t' : Set β} :
    IsIntent r t → IsIntent r t' → IsIntent r (t ∩ t') :=
  IsExtent.inter
/-
**Order.IsIntent.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsIntent`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} {r : α → β → Prop} (f : ι →
 Set β),   (∀ (i : ι), Order.IsIntent r (f i)) → Order.IsIntent r (⋂ i, f i)
参数：f : ι → Set β；∀ (i : ι), Order.IsIntent r (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.iInter`：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} {r
 : α → β → Prop} (f : ι → Set α),   (∀ (i : ι), Order.IsExtent r (f i)) → Order.
IsExtent r …
-/
protected theorem IsIntent.iInter (f : ι → Set β) (hf : ∀ i, IsIntent r (f i)) :
    IsIntent r (⋂ i, f i) :=
  IsExtent.iInter _ hf
/-
**Order.IsIntent.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsIntent`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} {r : α → β → Prop} (f : ι →
 Set β),   (∀ (i : ι), Order.IsIntent r (f i)) → Order.IsIntent r (⋂ i, f i)
参数：f : ι → Set β；∀ (i : ι), Order.IsIntent r (f i)；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.iInter`：∀ {ι : Sort u_1} {α : Type u_2} {β : Type u_3} {r
 : α → β → Prop} (f : ι → Set α),   (∀ (i : ι), Order.IsExtent r (f i)) → Order.
IsExtent r …
-/
protected theorem IsIntent.iInter₂ (f : ∀ i, κ i → Set β) (hf : ∀ i j, IsIntent r (f i j)) :
    IsIntent r (⋂ (i) (j), f i j) :=
  IsExtent.iInter₂ _ hf
/-
**Order.IsIntent.upperPolar_lowerPolar_subset** 是 Mathlib 中的一个定理，位于命名空间 `Order.I
sIntent`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t t' : Set β},   Order
.IsIntent r t → t' ⊆ t → upperPolar r (lowerPolar r t') ⊆ t
参数：lowerPolar r t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsIntent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t
 : Set β}, Order.IsIntent r t → upperPolar r (lowerPolar r t) = t
· 使用定理 `upperPolar_lowerPolar_monotone`：upperPolar_lowerPolar_monotone : Monoton
e (upperPolar r ∘ lowerPolar r)
-/
theorem IsIntent.upperPolar_lowerPolar_subset {t' : Set β} (h : IsIntent r t) (ht' : t' ⊆ t) :
    upperPolar r (lowerPolar r t') ⊆ t := by
  rw [← h.eq]
  exact upperPolar_lowerPolar_monotone r ht'

end Order

/-! ### Concepts -/

variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
/-
**Concept** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → (β : Type u_3) → (α → β → Prop) → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of 
sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and 
`t` is the set of
all elements that are `r`-related to all of `s`.
-/
structure Concept where
  /-- The extent of a concept. -/
  extent : Set α
  /-- The intent of a concept. -/
  intent : Set β
  /-- The intent consists of all elements related to all elements of the extent. -/
  upperPolar_extent : upperPolar r extent = intent
  /-- The extent consists of all elements related to all elements of the intent. -/
  lowerPolar_intent : lowerPolar r intent = extent

initialize_simps_projections Concept (as_prefix extent, as_prefix intent)

namespace Concept

variable {r r' α β}
variable {c d : Concept α β r} {c' : Concept α α r'}

attribute [simp] upperPolar_extent lowerPolar_intent

/-- See `Concept.ext'` for a version using the intent. -/
@[ext]
/-
**Concept.ext** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ext (h : c.extent = d.extent) : c = d
参数：h : c.extent = d.extent。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Concept.ext'` for a version using the intent.
-/
theorem ext (h : c.extent = d.extent) : c = d := by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  subst h
  rfl

/-- See `Concept.ext` for a version using the extent. -/
/-
**Concept.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ext' (h : c.intent = d.intent) : c = d
参数：h : c.intent = d.intent。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Concept.ext` for a version using the extent.
-/
theorem ext' (h : c.intent = d.intent) : c = d := by
  obtain ⟨s₁, t₁, _, rfl⟩ := c
  obtain ⟨s₂, t₂, _, rfl⟩ := d
  subst h
  rfl
/-
**Concept.extent_injective** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：extent_injective : Injective (@extent α β r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ext`：ext (h : c.extent = d.extent) : c = d
-/
theorem extent_injective : Injective (@extent α β r) := fun _ _ => ext
/-
**Concept.intent_injective** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：intent_injective : Injective (@intent α β r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ext'`：ext' (h : c.intent = d.intent) : c = d
-/
theorem intent_injective : Injective (@intent α β r) := fun _ _ => ext'

/-- Copy a concept, adjusting definitional equalities. -/
@[simps]
/-
**Concept.copy** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：copy (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi :
 i = c.intent) : Concept α β r where extent
参数：c : Concept α β r；e : Set α；i : Set β；he : e = c.extent；hi : i = c.intent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy a concept, adjusting definitional equalities.
-/
def copy (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi : i = c.intent) :
    Concept α β r where
  extent := e
  intent := i
  upperPolar_extent := he ▸ hi ▸ c.upperPolar_extent
  lowerPolar_intent := he ▸ hi ▸ c.lowerPolar_intent
/-
**Concept.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：copy_eq (c : Concept α β r) (e : Set α) (i : Set β) (he hi) : c.copy e i h
e hi = c
参数：c : Concept α β r；e : Set α；i : Set β；he hi。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ext`：ext (h : c.extent = d.extent) : c = d
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Concept.copy.congr_simp`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Pr
op} (c c_1 : Concept α β r) (e_c : c = c_1) (e e_1 : Set α)   (e_e : e = e_1) (i
 i_1 : Set β)…
· 使用定理 `Concept.extent_copy`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} 
(c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent)   (hi : i = c.in
tent), (c…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem copy_eq (c : Concept α β r) (e : Set α) (i : Set β) (he hi) : c.copy e i he hi = c := by
  ext; simp_all

variable (r s) in
/-- Define a concept from an extent, by setting the intent to its upper polar. -/
@[simps]
/-
**Concept.ofIsExtent** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：ofIsExtent (hs : IsExtent r s) : Concept α β r where extent
参数：hs : IsExtent r s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s
 : Set α}, Order.IsExtent r s → lowerPolar r (upperPolar r s) = s

--- 原说明 ---
Define a concept from an extent, by setting the intent to its upper polar.
-/
def ofIsExtent (hs : IsExtent r s) : Concept α β r where
  extent := s
  intent := upperPolar r s
  upperPolar_extent := rfl
  lowerPolar_intent := hs.eq

@[simp]
/-
**Concept.isExtent_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isExtent_extent (c : Concept α β r) : IsExtent r c.extent
参数：c : Concept α β r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isExtent_lowerPolar`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} {t : Set β}, Order.IsExtent r (lowerPolar r t)
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
-/
theorem isExtent_extent (c : Concept α β r) : IsExtent r c.extent :=
  lowerPolar_intent c ▸ isExtent_lowerPolar
/-
**Concept.isExtent_iff_exists_concept** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isExtent_iff_exists_concept : IsExtent r s ↔ exists c : Concept α β r, c.e
xtent = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.isExtent_extent`：isExtent_extent (c : Concept α β r) : IsExtent 
r c.extent
-/
theorem isExtent_iff_exists_concept : IsExtent r s ↔ ∃ c : Concept α β r, c.extent = s :=
  ⟨fun h ↦ ⟨ofIsExtent _ _ h, rfl⟩, fun ⟨c, h⟩ ↦ h ▸ c.isExtent_extent⟩

variable (r t) in
/-- Define a concept from an intent, by setting the extent to its lower polar. -/
@[simps]
/-
**Concept.ofIsIntent** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：ofIsIntent (ht : IsIntent r t) : Concept α β r where extent
参数：ht : IsIntent r t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsIntent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t
 : Set β}, Order.IsIntent r t → upperPolar r (lowerPolar r t) = t

--- 原说明 ---
Define a concept from an intent, by setting the extent to its lower polar.
-/
def ofIsIntent (ht : IsIntent r t) : Concept α β r where
  extent := lowerPolar r t
  intent := t
  upperPolar_extent := ht.eq
  lowerPolar_intent := rfl

@[simp]
/-
**Concept.isIntent_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isIntent_intent (c : Concept α β r) : IsIntent r c.intent
参数：c : Concept α β r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isIntent_upperPolar`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} {s : Set α}, Order.IsIntent r (upperPolar r s)
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
-/
theorem isIntent_intent (c : Concept α β r) : IsIntent r c.intent :=
  upperPolar_extent c ▸ isIntent_upperPolar
/-
**Concept.isIntent_iff_exists_concept** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isIntent_iff_exists_concept : IsIntent r t ↔ exists c : Concept α β r, c.i
ntent = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.isIntent_intent`：isIntent_intent (c : Concept α β r) : IsIntent 
r c.intent
-/
theorem isIntent_iff_exists_concept : IsIntent r t ↔ ∃ c : Concept α β r, c.intent = t :=
  ⟨fun h ↦ ⟨ofIsIntent _ _ h, rfl⟩, fun ⟨c, h⟩ ↦ h ▸ c.isIntent_intent⟩

/-- The concept generated from the upper polar of a set, i.e. the smallest concept containing the
set of objects `s`. -/
@[simps!]
/-
**Concept.ofObjects** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：ofObjects (r : α -> β -> Prop) (s : Set α) : Concept α β r
参数：r : α -> β -> Prop；s : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isIntent_upperPolar`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} {s : Set α}, Order.IsIntent r (upperPolar r s)

--- 原说明 ---
The concept generated from the upper polar of a set, i.e. the smallest concept c
ontaining the
set of objects `s`.
-/
def ofObjects (r : α → β → Prop) (s : Set α) : Concept α β r :=
  ofIsIntent r _ (isIntent_upperPolar (s := s))

/-- The concept generated by a single object. -/
/-
**Concept.ofObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `Concept`。
形式化陈述：ofObject (r : α -> β -> Prop) (a : α) : Concept α β r
参数：r : α -> β -> Prop；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concept generated by a single object.
-/
abbrev ofObject (r : α → β → Prop) (a : α) : Concept α β r := ofObjects r {a}

@[simp]
/-
**Concept.ofObjects_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ofObjects_extent : ofObjects r c.extent = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.intent_injective`：intent_injective : Injective (@intent α β r)
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
-/
theorem ofObjects_extent : ofObjects r c.extent = c :=
  intent_injective c.upperPolar_extent
/-
**Concept.extent_ofObjects_of_isExtent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：extent_ofObjects_of_isExtent (hs : IsExtent r s) : (ofObjects r s).extent 
= s
参数：hs : IsExtent r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s
 : Set α}, Order.IsExtent r s → lowerPolar r (upperPolar r s) = s
-/
theorem extent_ofObjects_of_isExtent (hs : IsExtent r s) : (ofObjects r s).extent = s :=
  hs.eq
/-
**Concept.leftInverse_ofObjects_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：leftInverse_ofObjects_extent : LeftInverse (ofObjects r) extent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ofObjects_extent`：ofObjects_extent : ofObjects r c.extent = c
-/
theorem leftInverse_ofObjects_extent : LeftInverse (ofObjects r) extent :=
  fun _ ↦ ofObjects_extent
/-
**Concept.leftInvOn_extent_ofObjects** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：leftInvOn_extent_ofObjects : Set.LeftInvOn extent (ofObjects r) {s | IsExt
ent r s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {s
 : Set α}, Order.IsExtent r s → lowerPolar r (upperPolar r s) = s
-/
theorem leftInvOn_extent_ofObjects : Set.LeftInvOn extent (ofObjects r) {s | IsExtent r s} :=
  fun _ ↦ IsExtent.eq
/-
**Concept.surjective_ofObjects** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：surjective_ofObjects : Surjective (ofObjects r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Concept.leftInverse_ofObjects_extent`：leftInverse_ofObjects_extent : Lef
tInverse (ofObjects r) extent
-/
theorem surjective_ofObjects : Surjective (ofObjects r) :=
  leftInverse_ofObjects_extent.surjective

/-- The concept generated from the lower polar of a set, i.e. the smallest concept whose set of
attributes is contained in `t`. -/
@[simps!]
/-
**Concept.ofAttributes** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：ofAttributes (r : α -> β -> Prop) (t : Set β) : Concept α β r
参数：r : α -> β -> Prop；t : Set β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.isExtent_lowerPolar`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} {t : Set β}, Order.IsExtent r (lowerPolar r t)
-/
def ofAttributes (r : α → β → Prop) (t : Set β) : Concept α β r :=
  ofIsExtent r _ (isExtent_lowerPolar (t := t))

/-- The concept generated by a single attribute. -/
/-
**Concept.ofAttribute** 是 Mathlib 中的一个缩写定义，位于命名空间 `Concept`。
形式化陈述：ofAttribute (r : α -> β -> Prop) (b : β) : Concept α β r
参数：r : α -> β -> Prop；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The concept generated by a single attribute.
-/
abbrev ofAttribute (r : α → β → Prop) (b : β) : Concept α β r := ofAttributes r {b}

@[simp]
/-
**Concept.ofAttributes_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ofAttributes_intent : ofAttributes r c.intent = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.extent_injective`：extent_injective : Injective (@extent α β r)
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
-/
theorem ofAttributes_intent : ofAttributes r c.intent = c :=
  extent_injective c.lowerPolar_intent
/-
**Concept.intent_ofAttributes_of_isIntent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：intent_ofAttributes_of_isIntent (hs : IsIntent r t) : (ofAttributes r t).i
ntent = t
参数：hs : IsIntent r t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsIntent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t
 : Set β}, Order.IsIntent r t → upperPolar r (lowerPolar r t) = t
-/
theorem intent_ofAttributes_of_isIntent (hs : IsIntent r t) : (ofAttributes r t).intent = t :=
  hs.eq
/-
**Concept.leftInverse_ofAttributes_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：leftInverse_ofAttributes_extent : LeftInverse (ofAttributes r) intent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.extent_injective`：extent_injective : Injective (@extent α β r)
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
-/
theorem leftInverse_ofAttributes_extent : LeftInverse (ofAttributes r) intent :=
  fun c ↦ extent_injective c.lowerPolar_intent
/-
**Concept.leftInvOn_ofObjects_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：leftInvOn_ofObjects_intent : Set.LeftInvOn intent (ofAttributes r) {s | Is
Intent r s}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsIntent.eq`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} {t
 : Set β}, Order.IsIntent r t → upperPolar r (lowerPolar r t) = t
-/
theorem leftInvOn_ofObjects_intent : Set.LeftInvOn intent (ofAttributes r) {s | IsIntent r s} :=
  fun _ ↦ IsIntent.eq
/-
**Concept.surjective_ofAttributes** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：surjective_ofAttributes : Surjective (ofAttributes r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Concept.leftInverse_ofAttributes_extent`：leftInverse_ofAttributes_extent
 : LeftInverse (ofAttributes r) intent
-/
theorem surjective_ofAttributes : Surjective (ofAttributes r) :=
  leftInverse_ofAttributes_extent.surjective
/-
**Concept.rel_extent_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：rel_extent_intent {x y} (hx : x in c.extent) (hy : y in c.intent) : r x y
参数：hx : x in c.extent；hy : y in c.intent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
-/
theorem rel_extent_intent {x y} (hx : x ∈ c.extent) (hy : y ∈ c.intent) : r x y := by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

/-- Note that if `r'` is the `≤` relation, this theorem will often not be true! -/
/-
**Concept.disjoint_extent_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：disjoint_extent_intent [Std.Irrefl r'] : Disjoint c'.extent c'.intent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `Concept.rel_extent_intent`：rel_extent_intent {x y} (hx : x in c.extent) 
(hy : y in c.intent) : r x y

--- 原说明 ---
Note that if `r'` is the `≤` relation, this theorem will often not be true!
-/
theorem disjoint_extent_intent [Std.Irrefl r'] : Disjoint c'.extent c'.intent := by
  rw [disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  exact irrefl x (rel_extent_intent hx hx')
/-
**Concept.mem_extent_of_rel_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：mem_extent_of_rel_extent [IsTrans α r'] {x y} (hy : r' y x) (hx : x in c'.
extent) : y in c'.extent
参数：hy : r' y x；hx : x in c'.extent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Concept.rel_extent_intent`：rel_extent_intent {x y} (hx : x in c.extent) 
(hy : y in c.intent) : r x y
-/
theorem mem_extent_of_rel_extent [IsTrans α r'] {x y} (hy : r' y x) (hx : x ∈ c'.extent) :
    y ∈ c'.extent := by
  rw [← lowerPolar_intent]
  exact fun z hz ↦ _root_.trans hy (rel_extent_intent hx hz)
/-
**Concept.mem_intent_of_intent_rel** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：mem_intent_of_intent_rel [IsTrans α r'] {x y} (hy : r' x y) (hx : x in c'.
intent) : y in c'.intent
参数：hy : r' x y；hx : x in c'.intent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Concept.rel_extent_intent`：rel_extent_intent {x y} (hx : x in c.extent) 
(hy : y in c.intent) : r x y
-/
theorem mem_intent_of_intent_rel [IsTrans α r'] {x y} (hy : r' x y) (hx : x ∈ c'.intent) :
    y ∈ c'.intent := by
  rw [← upperPolar_extent]
  exact fun z hz ↦ _root_.trans (rel_extent_intent hz hx) hy
/-
**Concept.codisjoint_extent_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：codisjoint_extent_intent [Std.Trichotomous r'] [IsTrans α r'] : Codisjoint
 c'.extent c'.intent
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
· 使用定理 `Concept.mem_extent_of_rel_extent`：mem_extent_of_rel_extent [IsTrans α r'
] {x y} (hy : r' y x) (hx : x in c'.extent) : y in c'.extent
-/
theorem codisjoint_extent_intent [Std.Trichotomous r'] [IsTrans α r'] :
    Codisjoint c'.extent c'.intent := by
  rw [codisjoint_iff_le_sup]
  refine fun x _ ↦ or_iff_not_imp_left.2 fun hx ↦ ?_
  rw [← upperPolar_extent]
  intro y hy
  apply Not.imp_symm <| Std.Trichotomous.trichotomous x y (hx <| mem_extent_of_rel_extent · hy)
  exact (hx <| · ▸ hy)
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Concept α β r) := .lift _ extent_injective
/-
**Concept.isCompl_extent_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isCompl_extent_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') : Is
Compl c'.extent c'.intent
参数：c' : Concept α α r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.disjoint_extent_intent`：disjoint_extent_intent [Std.Irrefl r'] :
 Disjoint c'.extent c'.intent
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
· 使用定理 `Concept.codisjoint_extent_intent`：codisjoint_extent_intent [Std.Trichoto
mous r'] [IsTrans α r'] : Codisjoint c'.extent c'.intent
· 使用定理 `IsStrictTotalOrder.toTrichotomous`：∀ {α : Sort u_1} {lt : α → α → Prop} 
[self : IsStrictTotalOrder α lt], Std.Trichotomous lt
· 使用定理 `IsStrictOrder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsS
trictOrder α r], IsTrans α r
-/
theorem isCompl_extent_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') :
    IsCompl c'.extent c'.intent :=
  ⟨c'.disjoint_extent_intent, c'.codisjoint_extent_intent⟩

@[simp]
/-
**Concept.compl_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：compl_extent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.extentᶜ 
= c'.intent
参数：c' : Concept α α r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `Concept.isCompl_extent_intent`：isCompl_extent_intent [IsStrictTotalOrder
 α r'] (c' : Concept α α r') : IsCompl c'.extent c'.intent
-/
theorem compl_extent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.extentᶜ = c'.intent :=
  c'.isCompl_extent_intent.compl_eq

@[simp]
/-
**Concept.compl_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：compl_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.intentᶜ 
= c'.extent
参数：c' : Concept α α r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Concept.isCompl_extent_intent`：isCompl_extent_intent [IsStrictTotalOrder
 α r'] (c' : Concept α α r') : IsCompl c'.extent c'.intent
-/
theorem compl_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.intentᶜ = c'.extent :=
  c'.isCompl_extent_intent.symm.compl_eq

@[simp]
/-
**Concept.extent_subset_extent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：extent_subset_extent_iff : c.extent subseteq d.extent ↔ c <= d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extent_subset_extent_iff : c.extent ⊆ d.extent ↔ c ≤ d :=
  Iff.rfl

@[simp]
/-
**Concept.extent_ssubset_extent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：extent_ssubset_extent_iff : c.extent ⊂ d.extent ↔ c < d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extent_ssubset_extent_iff : c.extent ⊂ d.extent ↔ c < d :=
  Iff.rfl

@[simp]
/-
**Concept.intent_subset_intent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：intent_subset_intent_iff : c.intent subseteq d.intent ↔ d <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.extent_subset_extent_iff`：extent_subset_extent_iff : c.extent su
bseteq d.extent ↔ c <= d
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
· 使用定理 `lowerPolar_anti`：lowerPolar_anti : Antitone (lowerPolar r)
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
· 使用定理 `upperPolar_anti`：upperPolar_anti : Antitone (upperPolar r)
-/
theorem intent_subset_intent_iff : c.intent ⊆ d.intent ↔ d ≤ c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[simp]
/-
**Concept.intent_ssubset_intent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：intent_ssubset_intent_iff : c.intent ⊂ d.intent ↔ d < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ssubset_iff_subset_not_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder
 α] [inst : Preorder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ ¬b ⊆ a
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `Concept.intent_subset_intent_iff`：intent_subset_intent_iff : c.intent su
bseteq d.intent ↔ d <= c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem intent_ssubset_intent_iff : c.intent ⊂ d.intent ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_ge,
    intent_subset_intent_iff, intent_subset_intent_iff]
/-
**Concept.strictMono_extent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：strictMono_extent : StrictMono (@extent α β r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Concept.extent_ssubset_extent_iff`：extent_ssubset_extent_iff : c.extent 
⊂ d.extent ↔ c < d
-/
theorem strictMono_extent : StrictMono (@extent α β r) := fun _ _ =>
  extent_ssubset_extent_iff.2
/-
**Concept.strictAnti_intent** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：strictAnti_intent : StrictAnti (@intent α β r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Concept.intent_ssubset_intent_iff`：intent_ssubset_intent_iff : c.intent 
⊂ d.intent ↔ d < c
-/
theorem strictAnti_intent : StrictAnti (@intent α β r) := fun _ _ =>
  intent_ssubset_intent_iff.2

@[simp]
/-
**Concept.isLowerSet_extent_le** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isLowerSet_extent_le {α : Type*} [Preorder α] (c : Concept α α (· <= ·)) :
 IsLowerSet c.extent
参数：c : Concept α α (· <= ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.mem_extent_of_rel_extent`：mem_extent_of_rel_extent [IsTrans α r'
] {x y} (hy : r' y x) (hx : x in c'.extent) : y in c'.extent
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem isLowerSet_extent_le {α : Type*} [Preorder α] (c : Concept α α (· ≤ ·)) :
    IsLowerSet c.extent :=
  @mem_extent_of_rel_extent _ _ _ _

@[simp]
/-
**Concept.isUpperSet_intent_le** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isUpperSet_intent_le {α : Type*} [Preorder α] (c : Concept α α (· <= ·)) :
 IsUpperSet c.intent
参数：c : Concept α α (· <= ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.mem_intent_of_intent_rel`：mem_intent_of_intent_rel [IsTrans α r'
] {x y} (hy : r' x y) (hx : x in c'.intent) : y in c'.intent
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem isUpperSet_intent_le {α : Type*} [Preorder α] (c : Concept α α (· ≤ ·)) :
    IsUpperSet c.intent :=
  @mem_intent_of_intent_rel _ _ _ _

@[simp]
/-
**Concept.isLowerSet_extent_lt** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isLowerSet_extent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)
) : IsLowerSet c.extent
参数：c : Concept α α (· < ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Concept.mem_extent_of_rel_extent`：mem_extent_of_rel_extent [IsTrans α r'
] {x y} (hy : r' y x) (hx : x in c'.extent) : y in c'.extent
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isLowerSet_extent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)) :
    IsLowerSet c.extent := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_extent_of_rel_extent hb ha

@[simp]
/-
**Concept.isUpperSet_intent_lt** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：isUpperSet_intent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)
) : IsUpperSet c.intent
参数：c : Concept α α (· < ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Concept.mem_intent_of_intent_rel`：mem_intent_of_intent_rel [IsTrans α r'
] {x y} (hy : r' x y) (hx : x in c'.intent) : y in c'.intent
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isUpperSet_intent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)) :
    IsUpperSet c.intent := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_intent_of_intent_rel hb ha

@[simps!]
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Concept α β r) where
  max c d := ofIsIntent _ _ (c.isIntent_intent.inter d.isIntent_intent)

alias extent_sup := extent_max
alias intent_sup := intent_max

@[simps!]
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Concept α β r) where
  min c d := ofIsExtent _ _ (c.isExtent_extent.inter d.isExtent_extent)

alias extent_inf := extent_min
alias intent_inf := intent_min
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (Concept α β r) :=
  extent_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (Concept α β r) :=
  (toDual.injective.comp intent_injective).semilatticeSup _ (by simp) (by simp) fun _ _ ↦ rfl
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (Concept α β r) where

@[simp]
/-
**Concept.ofObjects_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ofObjects_le_iff : ofObjects r s <= c ↔ s subseteq c.extent
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.extent_subset_extent_iff`：extent_subset_extent_iff : c.extent su
bseteq d.extent ↔ c <= d
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_lowerPolar_upperPolar`：subset_lowerPolar_upperPolar (s : Set α) :
 s subseteq lowerPolar r (upperPolar r s)
· 使用定理 `Order.IsExtent.lowerPolar_upperPolar_subset`：∀ {α : Type u_2} {β : Type 
u_3} {r : α → β → Prop} {s s' : Set α},   Order.IsExtent r s → s' ⊆ s → lowerPol
ar r (upperPolar r s') ⊆ s
· 使用定理 `Concept.isExtent_extent`：isExtent_extent (c : Concept α β r) : IsExtent 
r c.extent
-/
theorem ofObjects_le_iff : ofObjects r s ≤ c ↔ s ⊆ c.extent := by
  rw [← extent_subset_extent_iff]
  exact ⟨((subset_lowerPolar_upperPolar r s).trans ·),
    (isExtent_extent c).lowerPolar_upperPolar_subset⟩
/-
**Concept.le_ofObjects_of_extent_subset** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：le_ofObjects_of_extent_subset (h : c.extent subseteq s) : c <= ofObjects r
 s
参数：h : c.extent subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
· 使用定理 `Antitone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antit
one…
· 使用定理 `lowerPolar_anti`：lowerPolar_anti : Antitone (lowerPolar r)
· 使用定理 `upperPolar_anti`：upperPolar_anti : Antitone (upperPolar r)
-/
theorem le_ofObjects_of_extent_subset (h : c.extent ⊆ s) : c ≤ ofObjects r s := by
  simpa using! (lowerPolar_anti r).comp (upperPolar_anti r) h

@[simp]
/-
**Concept.le_ofAttributes_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：le_ofAttributes_iff : c <= ofAttributes r t ↔ t subseteq c.intent
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.intent_subset_intent_iff`：intent_subset_intent_iff : c.intent su
bseteq d.intent ↔ d <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_upperPolar_lowerPolar`：subset_upperPolar_lowerPolar (t : Set β) :
 t subseteq upperPolar r (lowerPolar r t)
· 使用定理 `Order.IsIntent.upperPolar_lowerPolar_subset`：∀ {α : Type u_2} {β : Type 
u_3} {r : α → β → Prop} {t t' : Set β},   Order.IsIntent r t → t' ⊆ t → upperPol
ar r (lowerPolar r t') ⊆ t
· 使用定理 `Concept.isIntent_intent`：isIntent_intent (c : Concept α β r) : IsIntent 
r c.intent
-/
theorem le_ofAttributes_iff : c ≤ ofAttributes r t ↔ t ⊆ c.intent := by
  rw [← intent_subset_intent_iff]
  exact ⟨((subset_upperPolar_lowerPolar r t).trans ·),
    (isIntent_intent c).upperPolar_lowerPolar_subset⟩
/-
**Concept.ofAttributes_le_of_intent_subset** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ofAttributes_le_of_intent_subset (h : c.intent subseteq t) : ofAttributes 
r t <= c
参数：h : c.intent subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Concept.intent_subset_intent_iff`：intent_subset_intent_iff : c.intent su
bseteq d.intent ↔ d <= c
· 使用定理 `Concept.intent_ofAttributes`：∀ {α : Type u_2} {β : Type u_3} (r : α → β 
→ Prop) (t : Set β),   (Concept.ofAttributes r t).intent = upperPolar r (lowerPo
lar r t)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent
· 使用定理 `Antitone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antit
one…
· 使用定理 `upperPolar_anti`：upperPolar_anti : Antitone (upperPolar r)
· 使用定理 `lowerPolar_anti`：lowerPolar_anti : Antitone (lowerPolar r)
-/
theorem ofAttributes_le_of_intent_subset (h : c.intent ⊆ t) : ofAttributes r t ≤ c := by
  rw [← intent_subset_intent_iff]
  simpa using (upperPolar_anti r).comp (lowerPolar_anti r) h
/-
**Concept.ofObject_le_ofAttribute_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：ofObject_le_ofAttribute_iff {a b} : ofObject r a <= ofAttribute r b ↔ r a 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Concept.intent_ofObjects`：∀ {α : Type u_2} {β : Type u_3} (r : α → β → P
rop) (s : Set α), (Concept.ofObjects r s).intent = upperPolar r s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofObject_le_ofAttribute_iff {a b} : ofObject r a ≤ ofAttribute r b ↔ r a b := by
  simp

@[simps!]
/-
**Concept.instBoundedOrderConcept** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
形式化陈述：instBoundedOrderConcept : BoundedOrder (Concept α β r) where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsExtent.univ`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop},
 Order.IsExtent r Set.univ
· 使用定理 `Order.IsIntent.univ`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop},
 Order.IsIntent r Set.univ
-/
instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := ofIsExtent _ _ .univ
  le_top _ := subset_univ _
  bot := ofIsIntent _ _ .univ
  bot_le _ := intent_subset_intent_iff.1 <| subset_univ _

@[simps!]
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Concept α β r) where
  sInf S := ofIsExtent _ _ (.iInter₂ _ fun c (_ : c ∈ S) ↦ c.isExtent_extent)

@[simps!]
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (Concept α β r) where
  sSup S := ofIsIntent _ _ (.iInter₂ _ fun c (_ : c ∈ S) ↦ c.isIntent_intent)

/-- One half of the **fundamental theorem of concept lattices**: every concept lattice is a complete
lattice.

See `DedekindCut.principalIso` for the second half. -/
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One half of the **fundamental theorem of concept lattices**: every concept latti
ce is a complete
lattice.

See `DedekindCut.principalIso` for the second half.
-/
instance : CompleteLattice (Concept α β r) where
  isLUB_sSup s := by
    refine ⟨fun _ hc ↦ ?_, fun _ hc ↦ ?_⟩
    · exact intent_subset_intent_iff.1 <| biInter_subset_of_mem hc
    · exact intent_subset_intent_iff.1 <|
        subset_iInter₂ fun a ha ↦ intent_subset_intent_iff.2 (hc ha)
  isGLB_sInf s := ⟨fun _ ↦ biInter_subset_of_mem, fun _ ↦ subset_iInter₂⟩

@[simp]
/-
**Concept.extent_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：extent_iSup (f : ι -> Concept α β r) : (⨆ i, f i).extent = lowerPolar r (⋂
 i, (f i).intent)
参数：f : ι -> Concept α β r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Concept.extent_sSup`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} 
(S : Set (Concept α β r)),   (sSup S).extent = lowerPolar r (⋂ i ∈ S, i.intent)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extent_iSup (f : ι → Concept α β r) :
    (⨆ i, f i).extent = lowerPolar r (⋂ i, (f i).intent) := by
  simp_rw [iSup, extent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]
/-
**Concept.intent_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：intent_iSup (f : ι -> Concept α β r) : (⨆ i, f i).intent = ⋂ i, (f i).inte
nt
参数：f : ι -> Concept α β r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Concept.intent_sSup`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} 
(S : Set (Concept α β r)), (sSup S).intent = ⋂ i ∈ S, i.intent
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intent_iSup (f : ι → Concept α β r) : (⨆ i, f i).intent = ⋂ i, (f i).intent := by
  simp_rw [iSup, intent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]
/-
**Concept.extent_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：extent_iInf (f : ι -> Concept α β r) : (⨅ i, f i).extent = ⋂ i, (f i).exte
nt
参数：f : ι -> Concept α β r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Concept.extent_sInf`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} 
(S : Set (Concept α β r)), (sInf S).extent = ⋂ i ∈ S, i.extent
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extent_iInf (f : ι → Concept α β r) : (⨅ i, f i).extent = ⋂ i, (f i).extent := by
  simp_rw [iInf, extent_sInf, ← Set.iInf_eq_iInter, iInf_range]

@[simp]
/-
**Concept.intent_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：intent_iInf (f : ι -> Concept α β r) : (⨅ i, f i).intent = upperPolar r (⋂
 i, (f i).extent)
参数：f : ι -> Concept α β r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Concept.intent_sInf`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → Prop} 
(S : Set (Concept α β r)),   (sInf S).intent = upperPolar r (⋂ i ∈ S, i.extent)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intent_iInf (f : ι → Concept α β r) :
    (⨅ i, f i).intent = upperPolar r (⋂ i, (f i).extent) := by
  simp_rw [iInf, intent_sInf, ← Set.iInf_eq_iInter, iInf_range]
/-
**Concept.** 是 Mathlib 中的一个实例，位于命名空间 `Concept`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
/-
**Concept.swap** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：swap (c : Concept α β r) : Concept β α (swap r)
参数：c : Concept α β r。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.lowerPolar_intent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), lowerPolar r self.intent = self.extent
· 使用定理 `Concept.upperPolar_extent`：∀ {α : Type u_2} {β : Type u_3} {r : α → β → 
Prop} (self : Concept α β r), upperPolar r self.extent = self.intent

--- 原说明 ---
Swap the sets of a concept to make it a concept of the dual context.
-/
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]
/-
**Concept.swap_swap** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：swap_swap (c : Concept α β r) : c.swap.swap = c
参数：c : Concept α β r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.ext`：ext (h : c.extent = d.extent) : c = d
-/
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
/-
**Concept.swap_le_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：swap_le_swap_iff : c.swap <= d.swap ↔ d <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.intent_subset_intent_iff`：intent_subset_intent_iff : c.intent su
bseteq d.intent ↔ d <= c
-/
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  intent_subset_intent_iff

@[simp]
/-
**Concept.swap_lt_swap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Concept`。
形式化陈述：swap_lt_swap_iff : c.swap < d.swap ↔ d < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.intent_ssubset_intent_iff`：intent_ssubset_intent_iff : c.intent 
⊂ d.intent ↔ d < c
-/
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  intent_ssubset_intent_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
/-
**Concept.swapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Concept`。
形式化陈述：swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Concept.swap_swap`：swap_swap (c : Concept α β r) : c.swap.swap = c

--- 原说明 ---
The dual of a concept lattice is isomorphic to the concept lattice of the dual c
ontext.
-/
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept

