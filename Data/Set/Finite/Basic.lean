/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Nontriviality

/-!
# Finite sets

This file provides `Fintype` instances for many set constructions. It also proves basic facts about
finite sets and gives ways to manipulate `Set.Finite` expressions.

Note that the instances in this file are selected somewhat arbitrarily on the basis of them not
needing any imports beyond `Data.Fintype.Card` (which is required by `Finite.ofFinset`); they can
certainly be organized better.

## Main definitions

* `Set.Finite.toFinset` to noncomputably produce a `Finset` from a `Set.Finite` proof.
  (See `Set.toFinset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

@[expose] public section

assert_not_exists Monoid

open Set Function
open scoped symmDiff

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-
**Set.finite_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_iff_nonempty_fintype`：finite_iff_nonempty_fintype (α : Type*) : F
inite α ↔ Nonempty (Fintype α)
-/
theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  finite_iff_nonempty_fintype s

protected alias ⟨Finite.nonempty_fintype, _⟩ := finite_def

/-- Construct a `Finite` instance for a `Set` from a `Finset` with the same elements. -/
/-
**Set.Finite.ofFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {p : Set α} (s : Finset α), (∀ (x : α), x ∈ s ↔ x ∈ p) → p.
Finite
参数：s : Finset α；∀ (x : α), x ∈ s ↔ x ∈ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Construct a `Finite` instance for a `Set` from a `Finset` with the same elements
.
-/
protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.Finite :=
  have := Fintype.ofFinset s H; p.toFinite

/-- A finite set coerced to a type is a `Fintype`.
This is the `Fintype` projection for a `Set.Finite`.

Note that because `Finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
@[instance_reducible]
/-
**Set.Finite.fintype** 是 Mathlib 中的一个定义，位于命名空间 `Set.Finite`。
形式化陈述：{α : Type u} → {s : Set α} → s.Finite → Fintype ↑s
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.nonempty_fintype`：∀ {α : Type u} {s : Set α}, s.Finite → None
mpty (Fintype ↑s)

--- 原说明 ---
A finite set coerced to a type is a `Fintype`.
This is the `Fintype` projection for a `Set.Finite`.

Note that because `Finite` isn't a typeclass, this definition will not fire if i
t
is made into an instance
-/
protected noncomputable def Finite.fintype {s : Set α} (h : s.Finite) : Fintype s :=
  h.nonempty_fintype.some

/-- Using choice, get the `Finset` that represents this `Set`. -/
/-
**Set.Finite.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Set.Finite`。
形式化陈述：{α : Type u} → {s : Set α} → s.Finite → Finset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Using choice, get the `Finset` that represents this `Set`.
-/
protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
  @Set.toFinset _ _ h.fintype
/-
**Set.Finite.toFinset_eq_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} [inst : Fintype ↑s] (h : s.Finite), h.toFinset 
= s.toFinset
参数：h : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.toFinset.eq_1`：∀ {α : Type u} {s : Set α} (h : s.Finite), h.t
oFinset = s.toFinset
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Finite.toFinset_eq_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset = s.toFinset := by
  rw [Finite.toFinset, Subsingleton.elim h.fintype]

@[simp]
/-
**Set.toFinite_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinite_toFinset (s : Set α) [Fintype s] : s.toFinite.toFinset = s.toFins
et
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_eq_toFinset`：∀ {α : Type u} {s : Set α} [inst : Fint
ype ↑s] (h : s.Finite), h.toFinset = s.toFinset
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem toFinite_toFinset (s : Set α) [Fintype s] : s.toFinite.toFinset = s.toFinset :=
  s.toFinite.toFinset_eq_toFinset
/-
**Set.Finite.exists_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∃ s', ∀ (a : α), a ∈ s' ↔ a ∈ s
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.nonempty_fintype`：∀ {α : Type u} {s : Set α}, s.Finite → None
mpty (Fintype ↑s)
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem Finite.exists_finset {s : Set α} (h : s.Finite) :
    ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, fun _ => mem_toFinset⟩
/-
**Set.Finite.exists_finset_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∃ s', ↑s' = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.nonempty_fintype`：∀ {α : Type u} {s : Set α}, s.Finite → None
mpty (Fintype ↑s)
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
theorem Finite.exists_finset_coe {s : Set α} (h : s.Finite) : ∃ s' : Finset α, ↑s' = s := by
  cases h.nonempty_fintype
  exact ⟨s.toFinset, s.coe_toFinset⟩

/-- Finite sets can be lifted to finsets. -/
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite sets can be lifted to finsets.
-/
instance : CanLift (Set α) (Finset α) (↑) Set.Finite where prf _ hs := hs.exists_finset_coe

/-! ### Basic properties of `Set.Finite.toFinset` -/


namespace Finite

variable {s t : Set α} {a : α} (hs : s.Finite) {ht : t.Finite}

@[simp]
/-
**Set.Finite.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Finite), a ∈ hs.toFinset ↔ a ∈ 
s
参数：hs : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
protected theorem mem_toFinset : a ∈ hs.toFinset ↔ a ∈ s :=
  @mem_toFinset _ _ hs.fintype _

@[simp]
/-
**Set.Finite.coe_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs.toFinset = s
参数：hs : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
protected theorem coe_toFinset : (hs.toFinset : Set α) = s :=
  @coe_toFinset _ _ hs.fintype

@[simp]
/-
**Set.Finite.toFinset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} (hs : s.Finite), hs.toFinset.Nonempty ↔ s.Nonem
pty
参数：hs : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem toFinset_nonempty : hs.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, Finite.coe_toFinset]

/-- Note that this is an equality of types not holding definitionally. Use wisely. -/
/-
**Set.Finite.coeSort_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：coeSort_toFinset : ↥hs.toFinset = ↥s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_sort_coe`：coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _
) = s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
Note that this is an equality of types not holding definitionally. Use wisely.
-/
theorem coeSort_toFinset : ↥hs.toFinset = ↥s := by
  rw [← Finset.coe_sort_coe _, hs.coe_toFinset]

/-- The identity map, bundled as an equivalence between the subtypes of `s : Set α` and of
`h.toFinset : Finset α`, where `h` is a proof of finiteness of `s`. -/
/-
**Set.Finite.subtypeEquivToFinset** 是 Mathlib 中的一个定义，位于命名空间 `Set.Finite`。
形式化陈述：{α : Type u} → {s : Set α} → (hs : s.Finite) → { x // x ∈ s } ≃ ↥hs.toFins
et
参数：hs : s.Finite。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity map, bundled as an equivalence between the subtypes of `s : Set α` 
and of
`h.toFinset : Finset α`, where `h` is a proof of finiteness of `s`.
-/
@[simps!] def subtypeEquivToFinset : {x // x ∈ s} ≃ {x // x ∈ hs.toFinset} :=
  (Equiv.refl α).subtypeEquiv fun _ ↦ hs.mem_toFinset.symm

variable {hs}

@[simp]
/-
**Set.Finite.toFinset_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {ht : t.Finite}, hs.toFinset 
= ht.toFinset ↔ s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_inj`：toFinset_inj {s t : Set α} [Fintype s] [Fintype t] : s
.toFinset = t.toFinset ↔ s = t
-/
protected theorem toFinset_inj : hs.toFinset = ht.toFinset ↔ s = t :=
  @toFinset_inj _ _ _ hs.fintype ht.fintype

@[simp]
/-
**Set.Finite.toFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：toFinset_subset {t : Finset α} : hs.toFinset subseteq t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_subset {t : Finset α} : hs.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]

@[simp]
/-
**Set.Finite.toFinset_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：toFinset_ssubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toFinset_ssubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]

@[simp]
/-
**Set.Finite.subset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：subset_toFinset {s : Finset α} : s subseteq ht.toFinset ↔ ↑s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_toFinset {s : Finset α} : s ⊆ ht.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, Finite.coe_toFinset]

@[simp]
/-
**Set.Finite.ssubset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：ssubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ssubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, Finite.coe_toFinset]

@[gcongr, mono]
/-
**Set.Finite.toFinset_subset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {ht : t.Finite}, hs.toFinset 
⊆ ht.toFinset ↔ s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_subset_toFinset : hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t := by
  simp only [← Finset.coe_subset, Finite.coe_toFinset]

@[gcongr, mono]
/-
**Set.Finite.toFinset_ssubset_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {ht : t.Finite}, hs.toFinset 
⊂ ht.toFinset ↔ s ⊂ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_ssubset_toFinset : hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  simp only [← Finset.coe_ssubset, Finite.coe_toFinset]

protected alias ⟨_, toFinset_mono⟩ := Finite.toFinset_subset_toFinset

protected alias ⟨_, toFinset_strictMono⟩ := Finite.toFinset_ssubset_toFinset

@[simp high]
/-
**Set.Finite.toFinset_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [inst : Fintype α] (p : α → Prop) [inst_1 : DecidablePred p
] (h : {x | p x}.Finite),   h.toFinset = {x | p x}
参数：p : α → Prop；h : {x | p x}.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem toFinset_ofPred [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : { x | p x }.Finite) : h.toFinset = ({x | p x} : Finset α) := by simp

@[deprecated (since := "2026-07-09")] protected alias toFinset_setOf := Set.Finite.toFinset_ofPred

@[simp]
nonrec theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.fintype ht.fintype
/-
**Set.Finite.toFinset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : 
t.Finite) (h : (s ∩ t).Finite),   h.toFinset = hs.toFinset ∩ ht.toFinset
参数：hs : s.Finite；ht : t.Finite；h : (s ∩ t).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_inter [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∩ t).Finite) : h.toFinset = hs.toFinset ∩ ht.toFinset := by
  ext
  simp
/-
**Set.Finite.toFinset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : 
t.Finite) (h : (s ∪ t).Finite),   h.toFinset = hs.toFinset ∪ ht.toFinset
参数：hs : s.Finite；ht : t.Finite；h : (s ∪ t).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_union [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∪ t).Finite) : h.toFinset = hs.toFinset ∪ ht.toFinset := by
  ext
  simp
/-
**Set.Finite.toFinset_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : 
t.Finite) (h : (s \ t).Finite),   h.toFinset = hs.toFinset \ ht.toFinset
参数：hs : s.Finite；ht : t.Finite；h : (s \ t).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_sdiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s \ t).Finite) : h.toFinset = hs.toFinset \ ht.toFinset := by
  ext
  simp

@[deprecated (since := "2026-06-03")] alias toFinset_diff := toFinset_sdiff

open scoped symmDiff in
/-
**Set.Finite.toFinset_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : 
t.Finite) (h : (symmDiff s t).Finite),   h.toFinset = symmDiff hs.toFinset ht.to
Finset
参数：hs : s.Finite；ht : t.Finite；h : (symmDiff s t).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_symmDiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∆ t).Finite) : h.toFinset = hs.toFinset ∆ ht.toFinset := by
  ext
  simp [mem_symmDiff, Finset.mem_symmDiff]
/-
**Set.Finite.toFinset_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} [inst : DecidableEq α] [inst_1 : Fintype α] (hs
 : s.Finite) (h : sᶜ.Finite),   h.toFinset = hs.toFinsetᶜ
参数：hs : s.Finite；h : sᶜ.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_compl [DecidableEq α] [Fintype α] (hs : s.Finite) (h : sᶜ.Finite) :
    h.toFinset = hs.toFinsetᶜ := by
  ext
  simp
/-
**Set.Finite.toFinset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [inst : Fintype α] (h : Set.univ.Finite), h.toFinset = Fins
et.univ
参数：h : Set.univ.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.toFinset_univ`：toFinset_univ [Fintype α] [Fintype (Set.univ : Set α)
] : (Set.univ : Set α).toFinset = Finset.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem toFinset_univ [Fintype α] (h : (Set.univ : Set α).Finite) :
    h.toFinset = Finset.univ := by
  simp

@[simp]
/-
**Set.Finite.toFinset_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} {h : s.Finite}, h.toFinset = ∅ ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_eq_empty`：toFinset_eq_empty [Fintype s] : s.toFinset = ∅ ↔ 
s = ∅
-/
protected theorem toFinset_eq_empty {h : s.Finite} : h.toFinset = ∅ ↔ s = ∅ :=
  @toFinset_eq_empty _ _ h.fintype
/-
**Set.Finite.toFinset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} (h : ∅.Finite), h.toFinset = ∅
参数：h : ∅.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem toFinset_empty (h : (∅ : Set α).Finite) : h.toFinset = ∅ := by
  simp

@[simp]
/-
**Set.Finite.toFinset_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} [inst : Fintype α] {h : s.Finite}, h.toFinset =
 Finset.univ ↔ s = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_eq_univ`：toFinset_eq_univ [Fintype α] [Fintype s] : s.toFin
set = Finset.univ ↔ s = univ
-/
protected theorem toFinset_eq_univ [Fintype α] {h : s.Finite} :
    h.toFinset = Finset.univ ↔ s = univ :=
  @toFinset_eq_univ _ _ _ h.fintype
/-
**Set.Finite.toFinset_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} [inst : DecidableEq β] (f : α → β)
 (hs : s.Finite) (h : (f '' s).Finite),   h.toFinset = Finset.image f hs.toFinse
t
参数：f : α → β；hs : s.Finite；h : (f '' s).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_image [DecidableEq β] (f : α → β) (hs : s.Finite) (h : (f '' s).Finite) :
    h.toFinset = hs.toFinset.image f := by
  ext
  simp
/-
**Set.Finite.toFinset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : DecidableEq α] [inst_1 : Fintype β] (f
 : β → α) (h : (Set.range f).Finite),   h.toFinset = Finset.image f Finset.univ
参数：f : β → α；h : (Set.range f).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) (h : (range f).Finite) :
    h.toFinset = Finset.univ.image f := by
  ext
  simp

@[simp]
/-
**Set.Finite.toFinset_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} (h : s.Finite), h.toFinset.Nontrivial ↔ s.Nontr
ivial
参数：h : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nontrivial.eq_1`：∀ {α : Type u_1} (s : Finset α), s.Nontrivial = 
(↑s).Nontrivial
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem toFinset_nontrivial (h : s.Finite) : h.toFinset.Nontrivial ↔ s.Nontrivial := by
  rw [Finset.Nontrivial, h.coe_toFinset]

end Finite

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

/-
**Set.fintypeUniv** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeUniv [Fintype α] : Fintype (@univ α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance fintypeUniv [Fintype α] : Fintype (@univ α) :=
  Fintype.ofEquiv α (Equiv.Set.univ α).symm

-- Redeclared with appropriate keys
/-
**Set.fintypeTop** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeTop [Fintype α] : Fintype (⊤ : Set α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance fintypeTop [Fintype α] : Fintype (⊤ : Set α) := inferInstanceAs (Fintype (univ : Set α))

/-- If `(Set.univ : Set α)` is finite then `α` is a finite type. -/
@[instance_reducible]
/-
**Set.fintypeOfFiniteUniv** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeOfFiniteUniv (H : (univ (α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(Set.univ : Set α)` is finite then `α` is a finite type.
-/
noncomputable def fintypeOfFiniteUniv (H : (univ (α := α)).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.fintype (Equiv.Set.univ _)
/-
**Set.fintypeUnion** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Finty
pe (s union t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s ∪ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∪ t.toFinset) <| by simp
/-
**Set.fintypeSep** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeSep (s : Set α) (p : α -> Prop) [Fintype s] [DecidablePred p] : Fin
type ({ a in s | p a } : Set α)
参数：s : Set α；p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSep (s : Set α) (p : α → Prop) [Fintype s] [DecidablePred p] :
    Fintype ({ a ∈ s | p a } : Set α) :=
  Fintype.ofFinset {a ∈ s.toFinset | p a} <| by simp
/-
**Set.fintypeInter** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeInter (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t] : Finty
pe (s inter t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeInter (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∩ t.toFinset) <| by simp

/-- A `Fintype` instance for set intersection where the left set has a `Fintype` instance. -/
/-
**Set.fintypeInterOfLeft** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeInterOfLeft (s t : Set α) [Fintype s] [DecidablePred (· in t)] : Fi
ntype (s inter t : Set α)
参数：s t : Set α；· in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` instance for set intersection where the left set has a `Fintype` ins
tance.
-/
instance fintypeInterOfLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset {a ∈ s.toFinset | a ∈ t} <| by simp

/-- A `Fintype` instance for set intersection where the right set has a `Fintype` instance. -/
/-
**Set.fintypeInterOfRight** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeInterOfRight (s t : Set α) [Fintype t] [DecidablePred (· in s)] : F
intype (s inter t : Set α)
参数：s t : Set α；· in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` instance for set intersection where the right set has a `Fintype` in
stance.
-/
instance fintypeInterOfRight (s t : Set α) [Fintype t] [DecidablePred (· ∈ s)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset {a ∈ t.toFinset | a ∈ s} <| by simp [and_comm]

/-- A `Fintype` structure on a set defines a `Fintype` structure on its subset. -/
@[instance_reducible]
/-
**Set.fintypeSubset** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· in t)]
 (h : t subseteq s) : Fintype t
参数：s : Set α；· in t；h : t subseteq s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` structure on a set defines a `Fintype` structure on its subset.
-/
def fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· ∈ t)] (h : t ⊆ s) :
    Fintype t := by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft
/-
**Set.fintypeDiff** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeDiff [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintyp
e (s \ t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeDiff [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s \ t : Set α) :=
  Fintype.ofFinset (s.toFinset \ t.toFinset) <| by simp
/-
**Set.fintypeDiffLeft** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeDiffLeft (s t : Set α) [Fintype s] [DecidablePred (· in t)] : Finty
pe (s \ t : Set α)
参数：s t : Set α；· in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeDiffLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s \ t : Set α) :=
  Set.fintypeSep s (· ∈ tᶜ)
/-
**Set.fintypeEmpty** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeEmpty : Fintype (∅ : Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeEmpty : Fintype (∅ : Set α) :=
  Fintype.ofFinset ∅ <| by simp
/-
**Set.fintypeSingleton** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeSingleton (a : α) : Fintype ({a} : Set α)
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeSingleton (a : α) : Fintype ({a} : Set α) :=
  Fintype.ofFinset {a} <| by simp

/-- A `Fintype` instance for inserting an element into a `Set` using the
corresponding `insert` function on `Finset`. This requires `DecidableEq α`.
There is also `Set.fintypeInsert'` when `a ∈ s` is decidable. -/
/-
**Set.fintypeInsert** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeInsert (a : α) (s : Set α) [DecidableEq α] [Fintype s] : Fintype (i
nsert a s : Set α)
参数：a : α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` instance for inserting an element into a `Set` using the
corresponding `insert` function on `Finset`. This requires `DecidableEq α`.
There is also `Set.fintypeInsert'` when `a ∈ s` is decidable.
-/
instance fintypeInsert (a : α) (s : Set α) [DecidableEq α] [Fintype s] :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset (insert a s.toFinset) <| by simp

set_option backward.isDefEq.respectTransparency false in
/-- A `Fintype` structure on `insert a s` when inserting a new element. -/
@[instance_reducible]
/-
**Set.fintypeInsertOfNotMem** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) : Fintyp
e (insert a s : Set α)
参数：s : Set α；h : a ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` structure on `insert a s` when inserting a new element.
-/
def fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.nodup.cons (by simp [h])⟩ <| by simp

/-- A `Fintype` structure on `insert a s` when inserting a pre-existing element. -/
@[instance_reducible]
/-
**Set.fintypeInsertOfMem** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeInsertOfMem {a : α} (s : Set α) [Fintype s] (h : a in s) : Fintype 
(insert a s : Set α)
参数：s : Set α；h : a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Fintype` structure on `insert a s` when inserting a pre-existing element.
-/
def fintypeInsertOfMem {a : α} (s : Set α) [Fintype s] (h : a ∈ s) : Fintype (insert a s : Set α) :=
  Fintype.ofFinset s.toFinset <| by simp [h]

/-- The `Set.fintypeInsert` instance requires decidable equality, but when `a ∈ s`
is decidable for this particular `a` we can still get a `Fintype` instance by using
`Set.fintypeInsertOfNotMem` or `Set.fintypeInsertOfMem`.

This instance pre-dates `Set.fintypeInsert`, and it is less efficient.
When `Set.decidableMemOfFintype` is made a local instance, then this instance would
override `Set.fintypeInsert` if not for the fact that its priority has been
adjusted. See Note [lower instance priority]. -/
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Set.fintypeInsert` instance requires decidable equality, but when `a ∈ s`
is decidable for this particular `a` we can still get a `Fintype` instance by us
ing
`Set.fintypeInsertOfNotMem` or `Set.fintypeInsertOfMem`.

This instance pre-dates `Set.fintypeInsert`, and it is less efficient.
When `Set.decidableMemOfFintype` is made a local instance, then this instance wo
uld
override `Set.fintypeInsert` if not for the fact that its priority has been
adjusted. See Note [lower instance priority].
-/
instance (priority := 100) fintypeInsert' (a : α) (s : Set α) [Decidable <| a ∈ s] [Fintype s] :
    Fintype (insert a s : Set α) :=
  if h : a ∈ s then fintypeInsertOfMem s h else fintypeInsertOfNotMem s h
/-
**Set.fintypeImage** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeImage [DecidableEq β] (s : Set α) (f : α -> β) [Fintype s] : Fintyp
e (f '' s)
参数：s : Set α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeImage [DecidableEq β] (s : Set α) (f : α → β) [Fintype s] : Fintype (f '' s) :=
  Fintype.ofFinset (s.toFinset.image f) <| by simp

/-- If a function `f` has a partial inverse `g` and the image of `s` under `f` is a set with
a `Fintype` instance, then `s` has a `Fintype` structure as well. -/
@[instance_reducible]
/-
**Set.fintypeOfFintypeImage** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：fintypeOfFintypeImage (s : Set α) {f : α -> β} {g} (I : IsPartialInv f g) 
[Fintype (f '' s)] : Fintype s
参数：s : Set α；I : IsPartialInv f g；f '' s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` has a partial inverse `g` and the image of `s` under `f` is a 
set with
a `Fintype` instance, then `s` has a `Fintype` structure as well.
-/
def fintypeOfFintypeImage (s : Set α) {f : α → β} {g} (I : IsPartialInv f g) [Fintype (f '' s)] :
    Fintype s :=
  Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g <| injective_of_isPartialInv_right I⟩
    (by simp [I.eq])
/-
**Set.fintypeMap** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeMap {α β} [DecidableEq β] : forall (s : Set α) (f : α -> β) [Fintyp
e s], Fintype (f <$> s)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeMap {α β} [DecidableEq β] :
    ∀ (s : Set α) (f : α → β) [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage
/-
**Set.fintypeLTNat** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeLTNat (n : Nat) : Fintype { i | i < n }
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeLTNat (n : ℕ) : Fintype { i | i < n } :=
  Fintype.ofFinset (Finset.range n) <| by simp
/-
**Set.fintypeLENat** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeLENat (n : Nat) : Fintype { i | i <= n }
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeLENat (n : ℕ) : Fintype { i | i ≤ n } := by
  simpa [Nat.lt_succ_iff] using Set.fintypeLTNat (n + 1)

/-- This is not an instance so that it does not conflict with the one
in `Mathlib/Order/Interval/Finset/Defs.lean`. -/
@[instance_reducible]
/-
**Set.Nat.fintypeIio** 是 Mathlib 中的一个定义，位于命名空间 `Set.Nat`。
形式化陈述：(n : ℕ) → Fintype ↑(Set.Iio n)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance so that it does not conflict with the one
in `Mathlib/Order/Interval/Finset/Defs.lean`.
-/
def Nat.fintypeIio (n : ℕ) : Fintype (Iio n) :=
  Set.fintypeLTNat n
/-
**Set.fintypeMemFinset** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：fintypeMemFinset (s : Finset α) : Fintype { a | a in s }
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fintypeMemFinset (s : Finset α) : Fintype { a | a ∈ s } :=
  Finset.fintypeCoeSort s

end FintypeInstances

end Set

/-! ### Finset -/

namespace Finset

/-- Gives a `Set.Finite` for the `Finset` coerced to a `Set`.
This is a wrapper around `Set.toFinite`. -/
@[simp]
/-
**Finset.finite_toSet** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：finite_toSet (s : Finset α) : (s : Set α).Finite
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Gives a `Set.Finite` for the `Finset` coerced to a `Set`.
This is a wrapper around `Set.toFinite`.
-/
theorem finite_toSet (s : Finset α) : (s : Set α).Finite :=
  Set.toFinite _
/-
**Finset.finite_toSet_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：finite_toSet_toFinset (s : Finset α) : s.finite_toSet.toFinset = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
-/
theorem finite_toSet_toFinset (s : Finset α) : s.finite_toSet.toFinset = s := by
  rw [toFinite_toFinset, toFinset_coe]

/-- This is a kind of induction principle. See `Finset.induction` for the usual induction principle
for finsets. -/
/-
**Finset.** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a kind of induction principle. See `Finset.induction` for the usual indu
ction principle
for finsets.
-/
lemma «forall» {p : Finset α → Prop} :
    (∀ s, p s) ↔ ∀ (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp h s hs := h _
  mpr h s := by simpa using h s s.finite_toSet
/-
**Finset.** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {p : Finset α → Prop} :
    (∃ s, p s) ↔ ∃ (s : Set α) (hs : s.Finite), p hs.toFinset where
  mp := fun ⟨s, hs⟩ ↦ ⟨s, s.finite_toSet, by simpa⟩
  mpr := fun ⟨s, hs, hs'⟩ ↦ ⟨hs.toFinset, hs'⟩
/-
**Finset.mem_range_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_range_coe_iff {s : Set α} : s in Set.range ((↑) : Finset α -> Set α) ↔
 s.Finite where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mem_range_coe_iff {s : Set α} : s ∈ Set.range ((↑) : Finset α → Set α) ↔ s.Finite where
  mp := by
    rintro ⟨t, rfl⟩
    simp
  mpr hs := ⟨hs.toFinset, by simp⟩

end Finset

namespace Multiset

@[simp]
/-
**Multiset.finite_toSet** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：finite_toSet (s : Multiset α) : { x | x in s }.Finite
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem finite_toSet (s : Multiset α) : { x | x ∈ s }.Finite := by
  classical simpa only [← Multiset.mem_toFinset] using! s.toFinset.finite_toSet

@[simp]
/-
**Multiset.finite_toSet_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：finite_toSet_toFinset [DecidableEq α] (s : Multiset α) : s.finite_toSet.to
Finset = s.toFinset
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Multiset.finite_toSet`：finite_toSet (s : Multiset α) : { x | x in s }.Fi
nite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finite_toSet_toFinset [DecidableEq α] (s : Multiset α) :
    s.finite_toSet.toFinset = s.toFinset := by
  ext x
  simp

end Multiset

@[simp]
/-
**List.finite_toSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.finite_toSet (l : List α) : { x | x in l }.Finite
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.finite_toSet`：finite_toSet (s : Multiset α) : { x | x in s }.Fi
nite
-/
theorem List.finite_toSet (l : List α) : { x | x ∈ l }.Finite :=
  (show Multiset α from ⟦l⟧).finite_toSet

/-- `Finset α` is order isomorphic to the type of finite sets in `α`. -/
/-
**OrderIso.finsetSetFinite** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：{α : Type u} → Finset α ≃o { s // s.Finite }
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
`Finset α` is order isomorphic to the type of finite sets in `α`.
-/
@[simps] noncomputable def OrderIso.finsetSetFinite : Finset α ≃o {s : Set α // s.Finite} where
  toFun s := ⟨s, s.finite_toSet⟩
  invFun s := s.2.toFinset
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := .rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedLT {s : Set α // s.Finite} :=
  OrderIso.finsetSetFinite.symm.toOrderEmbedding.wellFoundedLT

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

/-
**Finite.Set.** 是 Mathlib 中的一个示例，位于命名空间 `Finite.Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {s : Set α} [Finite α] : Finite s :=
  inferInstance
/-
**Finite.Set.** 是 Mathlib 中的一个示例，位于命名空间 `Finite.Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Finite (∅ : Set α) :=
  inferInstance
/-
**Finite.Set.** 是 Mathlib 中的一个示例，位于命名空间 `Finite.Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (a : α) : Finite ({a} : Set α) :=
  inferInstance
/-
**Finite.Set.finite_union** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s union t : Set
 α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s ∪ t : Set α) := by
  cases nonempty_fintype s
  cases nonempty_fintype t
  classical
  infer_instance
/-
**Finite.Set.finite_sep** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_sep (s : Set α) (p : α -> Prop) [Finite s] : Finite ({ a in s | p a
 } : Set α)
参数：s : Set α；p : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance finite_sep (s : Set α) (p : α → Prop) [Finite s] : Finite ({ a ∈ s | p a } : Set α) := by
  cases nonempty_fintype s
  classical
  infer_instance
/-
**Finite.Set.subset** 是 Mathlib 中的一个定理，位于命名空间 `Finite.Set`。
形式化陈述：∀ {α : Type u} (s : Set α) {t : Set α} [Finite ↑s], t ⊆ s → Finite ↑t
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sep_eq_of_subset`：sep_eq_of_subset (h : s subseteq t) : { x in t | x
 in s } = s
-/
protected theorem subset (s : Set α) {t : Set α} [Finite s] (h : t ⊆ s) : Finite t := by
  rw [← sep_eq_of_subset h]
  infer_instance
/-
**Finite.Set.finite_inter_of_right** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_inter_of_right (s t : Set α) [Finite t] : Finite (s inter t : Set α
)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.Set.subset`：∀ {α : Type u} (s : Set α) {t : Set α} [Finite ↑s], t
 ⊆ s → Finite ↑t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
instance finite_inter_of_right (s t : Set α) [Finite t] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset t inter_subset_right
/-
**Finite.Set.finite_inter_of_left** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_inter_of_left (s t : Set α) [Finite s] : Finite (s inter t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.Set.subset`：∀ {α : Type u} (s : Set α) {t : Set α} [Finite ↑s], t
 ⊆ s → Finite ↑t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
instance finite_inter_of_left (s t : Set α) [Finite s] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset s inter_subset_left
/-
**Finite.Set.finite_diff** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α)
参数：s t : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.Set.subset`：∀ {α : Type u} (s : Set α) {t : Set α} [Finite ↑s], t
 ⊆ s → Finite ↑t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
instance finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α) :=
  Finite.Set.subset s sdiff_subset
/-
**Finite.Set.finite_insert** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α)
参数：a : α；s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α) :=
  Finite.Set.finite_union {a} s
/-
**Finite.Set.finite_image** 是 Mathlib 中的一个实例，位于命名空间 `Finite.Set`。
形式化陈述：finite_image (s : Set α) (f : α -> β) [Finite s] : Finite (f '' s)
参数：s : Set α；f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance finite_image (s : Set α) (f : α → β) [Finite s] : Finite (f '' s) := by
  cases nonempty_fintype s
  classical
  infer_instance

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/

section SetFiniteConstructors
variable {s t u : Set α} {a : α}

@[nontriviality]
/-
**Set.Finite.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [Subsingleton α] (s : Set α), s.Finite
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
-/
theorem Finite.of_subsingleton [Subsingleton α] (s : Set α) : s.Finite :=
  s.toFinite
/-
**Set.finite_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} [Finite α], Set.univ.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
@[simp] theorem finite_univ [Finite α] : (@univ α).Finite := Set.toFinite _
/-
**Set.finite_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_univ_iff : (@univ α).Finite ↔ Finite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
-/
theorem finite_univ_iff : (@univ α).Finite ↔ Finite α := (Equiv.Set.univ α).finite_iff

alias ⟨_root_.Finite.of_finite_univ, _⟩ := finite_univ_iff
/-
**Set.Finite.subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α}, t ⊆ s → t.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Finite.Set.subset`：∀ {α : Type u} (s : Set α) {t : Set α} [Finite ↑s], t
 ⊆ s → Finite ↑t
-/
theorem Finite.subset {s : Set α} (hs : s.Finite) {t : Set α} (ht : t ⊆ s) : t.Finite := by
  have := hs.to_subtype
  exact Finite.Set.subset _ ht
/-
**Set.Finite.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s ∪ t).Finite
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.eq_1`：∀ {α : Type u} (s : Set α), s.Finite = Finite ↑s
-/
theorem Finite.union (hs : s.Finite) (ht : t.Finite) : (s ∪ t).Finite := by
  rw [Set.Finite] at hs ht
  apply toFinite
/-
**Set.Finite.finite_of_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → sᶜ.Finite → Finite α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
theorem Finite.finite_of_compl {s : Set α} (hs : s.Finite) (hsc : sᶜ.Finite) : Finite α := by
  rw [← finite_univ_iff, ← union_compl_self s]
  exact hs.union hsc
/-
**Set.Finite.sup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s ⊔ t).Finite
参数：s ⊔ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
theorem Finite.sup {s t : Set α} : s.Finite → t.Finite → (s ⊔ t).Finite :=
  Finite.union
/-
**Set.Finite.sep** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (p : α → Prop), {a | a ∈ s ∧ p a}
.Finite
参数：p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.sep_subset`：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x 
} subseteq s
-/
theorem Finite.sep {s : Set α} (hs : s.Finite) (p : α → Prop) : { a ∈ s | p a }.Finite :=
  hs.subset <| sep_subset _ _
/-
**Set.Finite.inter_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : Set α), (s ∩ t).Finite
参数：t : Set α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem Finite.inter_of_left {s : Set α} (hs : s.Finite) (t : Set α) : (s ∩ t).Finite :=
  hs.subset inter_subset_left
/-
**Set.Finite.inter_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : Set α), (t ∩ s).Finite
参数：t : Set α；t ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem Finite.inter_of_right {s : Set α} (hs : s.Finite) (t : Set α) : (t ∩ s).Finite :=
  hs.subset inter_subset_right
/-
**Set.Finite.inf_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : Set α), (s ⊓ t).Finite
参数：t : Set α；s ⊓ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
-/
theorem Finite.inf_of_left {s : Set α} (h : s.Finite) (t : Set α) : (s ⊓ t).Finite :=
  h.inter_of_left t
/-
**Set.Finite.inf_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : Set α), (t ⊓ s).Finite
参数：t : Set α；t ⊓ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.inter_of_right`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t :
 Set α), (t ∩ s).Finite
-/
theorem Finite.inf_of_right {s : Set α} (h : s.Finite) (t : Set α) : (t ⊓ s).Finite :=
  h.inter_of_right t
/-
**Set.Infinite.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
-/
protected lemma Infinite.mono {s t : Set α} (h : s ⊆ t) : s.Infinite → t.Infinite :=
  mt fun ht ↦ ht.subset h
/-
**Set.Finite.sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finite
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
@[simp] theorem Finite.sdiff (hs : s.Finite) : (s \ t).Finite := hs.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Finite.diff := Finite.sdiff
/-
**Set.Finite.of_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, (s \ t).Finite → t.Finite → s.Finite
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.subset_sdiff_union`：subset_sdiff_union (s t : Set α) : s subseteq s 
\ t union t
-/
theorem Finite.of_sdiff {s t : Set α} (hd : (s \ t).Finite) (ht : t.Finite) : s.Finite :=
  (hd.union ht).subset <| subset_sdiff_union _ _

@[deprecated (since := "2026-06-03")] alias Finite.of_diff := Finite.of_sdiff

@[simp]
/-
**Set.Finite.symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (symmDiff s t).Finite
参数：symmDiff s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
-/
lemma Finite.symmDiff (hs : s.Finite) (ht : t.Finite) : (s ∆ t).Finite := hs.sdiff.union ht.sdiff
/-
**Set.Finite.symmDiff_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s t u : Set α}, (symmDiff s t).Finite → ((symmDiff s u).Fi
nite ↔ (symmDiff t u).Finite)
参数：symmDiff s t；(symmDiff s u).Finite ↔ (symmDiff t u).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `symmDiff_triangle`：symmDiff_triangle : a ∆ c <= a ∆ b ⊔ b ∆ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
-/
lemma Finite.symmDiff_congr (hst : (s ∆ t).Finite) : (s ∆ u).Finite ↔ (t ∆ u).Finite where
  mp hsu := (hst.union hsu).subset (symmDiff_comm s t ▸ symmDiff_triangle ..)
  mpr htu := (hst.union htu).subset (symmDiff_triangle ..)

@[simp, grind .]
/-
**Set.finite_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_empty : (∅ : Set α).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_empty : (∅ : Set α).Finite :=
  toFinite _
/-
**Set.Infinite.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Infinite.nonempty {s : Set α} (h : s.Infinite) : s.Nonempty :=
  nonempty_iff_ne_empty.2 <| by
    rintro rfl
    exact h finite_empty

@[simp]
/-
**Set.finite_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_singleton (a : α) : ({a} : Set α).Finite
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_singleton (a : α) : ({a} : Set α).Finite :=
  toFinite _
/-
**Set.Finite.insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (insert a s).Finite
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
protected theorem Finite.insert (a : α) {s : Set α} (hs : s.Finite) : (insert a s).Finite :=
  (finite_singleton a).union hs
/-
**Set.finite_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s : Set α} {a : α}, (insert a s).Finite ↔ s.Finite
参数：insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
-/
@[simp] lemma finite_insert : (insert a s).Finite ↔ s.Finite where
  mp hs := hs.subset <| subset_insert ..
  mpr := .insert _
/-
**Set.Finite.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s.Finite → (f '' s).F
inite
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
theorem Finite.image {s : Set α} (f : α → β) (hs : s.Finite) : (f '' s).Finite := by
  have := hs.to_subtype
  apply toFinite
/-
**Set.Finite.of_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β} (f : α → β), Set.SurjO
n f s t → s.Finite → t.Finite
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
lemma Finite.of_surjOn {s : Set α} {t : Set β} (f : α → β) (hf : SurjOn f s t) (hs : s.Finite) :
    t.Finite := (hs.image _).subset hf
/-
**Set.Finite.map** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α β : Type u_1} {s : Set α} (f : α → β), s.Finite → (f <$> s).Finite
参数：f : α → β；f <$> s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem Finite.map {α β} {s : Set α} : ∀ f : α → β, s.Finite → (f <$> s).Finite :=
  Finite.image
/-
**Set.Finite.of_finite_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} {f : α → β}, (f '' s).Finite → Set
.InjOn f s → s.Finite
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Set.BijOn.bijective`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Se
t β} {f : α → β} (h : Set.BijOn f s t),   Function.Bijective (Set.MapsTo.restric
t f s t ⋯…
-/
theorem Finite.of_finite_image {s : Set α} {f : α → β} (h : (f '' s).Finite) (hi : Set.InjOn f s) :
    s.Finite :=
  have := h.to_subtype
  .of_injective _ hi.bijOn_image.bijective.injective
/-
**Set.Finite.of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set α} {t : Set β}, Set.MapsT
o f s t → Set.InjOn f s → t.Finite → s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem Finite.of_injOn {f : α → β} {s : Set α} {t : Set β} (hm : MapsTo f s t) (hi : InjOn f s)
    (ht : t.Finite) : s.Finite :=
  .of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi
/-
**Set.BijOn.finite_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.BijOn`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set α} {t : Set β}, Set.BijOn
 f s t → (s.Finite ↔ t.Finite)
参数：s.Finite ↔ t.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_surjOn`：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β
} (f : α → β), Set.SurjOn f s t → s.Finite → t.Finite
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Finite.of_injOn`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set α}
 {t : Set β}, Set.MapsTo f s t → Set.InjOn f s → t.Finite → s.Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem BijOn.finite_iff_finite {f : α → β} {s : Set α} {t : Set β} (h : BijOn f s t) :
    s.Finite ↔ t.Finite :=
  ⟨fun h1 ↦ h1.of_surjOn _ h.2.2, fun h1 ↦ h1.of_injOn h.1 h.2.1⟩

section preimage
variable {f : α → β} {s : Set β}

/-
**Set.finite_of_finite_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_of_finite_preimage (h : (f ⁻¹' s).Finite) (hs : s subseteq range f)
 : s.Finite
参数：h : (f ⁻¹' s).Finite；hs : s subseteq range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem finite_of_finite_preimage (h : (f ⁻¹' s).Finite) (hs : s ⊆ range f) : s.Finite := by
  rw [← image_preimage_eq_of_subset hs]
  exact Finite.image f h
/-
**Set.Finite.of_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}, (f ⁻¹' s).Finite → Fu
nction.Surjective f → s.Finite
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
-/
theorem Finite.of_preimage (h : (f ⁻¹' s).Finite) (hf : Surjective f) : s.Finite :=
  hf.image_preimage s ▸ h.image _
/-
**Set.Finite.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}, Set.InjOn f (f ⁻¹' s)
 → s.Finite → (f ⁻¹' s).Finite
参数：f ⁻¹' s；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem Finite.preimage (I : Set.InjOn f (f ⁻¹' s)) (h : s.Finite) : (f ⁻¹' s).Finite :=
  (h.subset (image_preimage_subset f s)).of_finite_image I
/-
**Set.Infinite.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}, s.Infinite → s ⊆ Set.
range f → (f ⁻¹' s).Infinite
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_of_finite_preimage`：finite_of_finite_preimage (h : (f ⁻¹' s).
Finite) (hs : s subseteq range f) : s.Finite
-/
protected lemma Infinite.preimage (hs : s.Infinite) (hf : s ⊆ range f) : (f ⁻¹' s).Infinite :=
  fun h ↦ hs <| finite_of_finite_preimage h hf
/-
**Set.Infinite.preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}, (s ∩ Set.range f).Inf
inite → (f ⁻¹' s).Infinite
参数：s ∩ Set.range f；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.Infinite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set 
β}, s.Infinite → s ⊆ Set.range f → (f ⁻¹' s).Infinite
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma Infinite.preimage' (hs : (s ∩ range f).Infinite) : (f ⁻¹' s).Infinite :=
  (hs.preimage inter_subset_right).mono <| preimage_mono inter_subset_left
/-
**Set.Finite.preimage_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set β} (f : α ↪ β), s.Finite → (⇑f ⁻¹' s)
.Finite
参数：f : α ↪ β；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem Finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.Finite) : (f ⁻¹' s).Finite :=
  h.preimage fun _ _ _ _ h' => f.injective h'

end preimage

/-
**Set.finite_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_lt_nat (n : Nat) : Set.Finite { i | i < n }
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_lt_nat (n : ℕ) : Set.Finite { i | i < n } :=
  toFinite _
/-
**Set.finite_le_nat** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_le_nat (n : ℕ) : Set.Finite { i | i ≤ n } :=
  toFinite _

section MapsTo

variable {s : Set α} {f : α → α}

/-
**Set.Finite.surjOn_iff_bijOn_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} {f : α → α}, s.Finite → Set.MapsTo f s s → (Set
.SurjOn f s s ↔ Set.BijOn f s s)
参数：Set.SurjOn f s s ↔ Set.BijOn f s s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.MapsTo.restrict_inj`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Injective (Set.MapsTo.re
strict f s t …
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Set.MapsTo.restrict_surjective_iff`：∀ {α : Type u_1} {β : Type u_2} {s :
 Set α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Surjective (S
et.MapsTo.restrict f s t…
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
-/
theorem Finite.surjOn_iff_bijOn_of_mapsTo (hs : s.Finite) (hm : MapsTo f s s) :
    SurjOn f s s ↔ BijOn f s s := by
  refine ⟨fun h ↦ ⟨hm, ?_, h⟩, BijOn.surjOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_inj.mp (Finite.injective_iff_surjective.mpr <| hm.restrict_surjective_iff.mpr h)
/-
**Set.Finite.injOn_iff_bijOn_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} {f : α → α}, s.Finite → Set.MapsTo f s s → (Set
.InjOn f s ↔ Set.BijOn f s s)
参数：Set.InjOn f s ↔ Set.BijOn f s s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.MapsTo.restrict_surjective_iff`：∀ {α : Type u_1} {β : Type u_2} {s :
 Set α} {t : Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Surjective (S
et.MapsTo.restrict f s t…
· 使用定理 `Finite.injective_iff_surjective`：injective_iff_surjective {f : α -> α} :
 Injective f ↔ Surjective f
· 使用定理 `Set.MapsTo.restrict_inj`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} (h : Set.MapsTo f s t),   Function.Injective (Set.MapsTo.re
strict f s t …
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
-/
theorem Finite.injOn_iff_bijOn_of_mapsTo (hs : s.Finite) (hm : MapsTo f s s) :
    InjOn f s ↔ BijOn f s s := by
  refine ⟨fun h ↦ ⟨hm, h, ?_⟩, BijOn.injOn⟩
  have : Finite s := finite_coe_iff.mpr hs
  exact hm.restrict_surjective_iff.mp (Finite.injective_iff_surjective.mp <| hm.restrict_inj.mpr h)

end MapsTo

/-
**Set.finite_mem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_mem_finset (s : Finset α) : { a | a in s }.Finite
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finite_mem_finset (s : Finset α) : { a | a ∈ s }.Finite :=
  toFinite _
/-
**Set.Subsingleton.finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.Finite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem Subsingleton.finite {s : Set α} (h : s.Subsingleton) : s.Finite :=
  h.induction_on finite_empty finite_singleton
/-
**Set.Infinite.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nontrivial
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subsingleton_iff`：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Non
trivial
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
-/
theorem Infinite.nontrivial {s : Set α} (hs : s.Infinite) : s.Nontrivial :=
  not_subsingleton_iff.1 <| mt Subsingleton.finite hs
/-
**Set.finite_preimage_inl_and_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_preimage_inl_and_inr {s : Set (α oplus β)} : (Sum.inl ⁻¹' s).Finite
 ∧ (Sum.inr ⁻¹' s).Finite ↔ s.Finite
参数：α oplus β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.image_preimage_inl_union_image_preimage_inr`：image_preimage_inl_unio
n_image_preimage_inr (s : Set (α oplus β)) : Sum.inl '' Sum.inl ⁻¹' s union Sum.
inr '' Sum.inr ⁻¹' s = s
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem finite_preimage_inl_and_inr {s : Set (α ⊕ β)} :
    (Sum.inl ⁻¹' s).Finite ∧ (Sum.inr ⁻¹' s).Finite ↔ s.Finite :=
  ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.preimage Sum.inl_injective.injOn, h.preimage Sum.inr_injective.injOn⟩⟩
/-
**Set.exists_finite_iff_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_finite_iff_finset {p : Set α -> Prop} : (exists s : Set α, s.Finite
 ∧ p s) ↔ exists s : Finset α, p ↑s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem exists_finite_iff_finset {p : Set α → Prop} :
    (∃ s : Set α, s.Finite ∧ p s) ↔ ∃ s : Finset α, p ↑s :=
  ⟨fun ⟨_, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩
/-
**Set.exists_subset_image_finite_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_subset_image_finite_and {f : α -> β} {s : Set α} {p : Set β -> Prop
} : (exists t subseteq f '' s, t.Finite ∧ p t) ↔ exists t subseteq s, t.Finite ∧
 p (f '' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_subset_image_finite_and {f : α → β} {s : Set α} {p : Set β → Prop} :
    (∃ t ⊆ f '' s, t.Finite ∧ p t) ↔ ∃ t ⊆ s, t.Finite ∧ p (f '' t) := by
  classical
  simp_rw [@and_comm ((_ : Set _) ⊆ _), and_assoc, exists_finite_iff_finset, @and_comm (p _),
    Finset.subset_set_image_iff]
  aesop
/-
**Set.finite_range_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_range_ite {p : α -> Prop} [DecidablePred p] {f g : α -> β} (hf : (r
ange f).Finite) (hg : (range g).Finite) : (range fun x => if p x then f x else g
 x).Finite
参数：hf : (range f).Finite；hg : (range g).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.range_ite_subset`：range_ite_subset {p : α -> Prop} [DecidablePred p]
 {f g : α -> β} : (range fun x => if p x then f x else g x) subseteq range f uni
on range g
-/
theorem finite_range_ite {p : α → Prop} [DecidablePred p] {f g : α → β} (hf : (range f).Finite)
    (hg : (range g).Finite) : (range fun x => if p x then f x else g x).Finite :=
  (hf.union hg).subset range_ite_subset
/-
**Set.finite_range_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_range_const {c : β} : (range fun _ : α => c).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Set.range_const_subset`：range_const_subset {c : α} : (range fun _ : ι =>
 c) subseteq {c}
-/
theorem finite_range_const {c : β} : (range fun _ : α => c).Finite :=
  (finite_singleton c).subset range_const_subset

end SetFiniteConstructors

/-! ### Properties -/

/-
**Set.Finite.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Set.Finite`。
形式化陈述：{α : Type u} → Inhabited { s // s.Finite }
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite

--- 原说明 ---
### Properties
-/
instance Finite.inhabited : Inhabited { s : Set α // s.Finite } :=
  ⟨⟨∅, finite_empty⟩⟩

@[simp]
/-
**Set.finite_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_union {s t : Set α} : (s union t).Finite ↔ s.Finite ∧ t.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
theorem finite_union {s t : Set α} : (s ∪ t).Finite ↔ s.Finite ∧ t.Finite :=
  ⟨fun h => ⟨h.subset subset_union_left, h.subset subset_union_right⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩
/-
**Set.finite_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_image_iff {s : Set α} {f : α -> β} (hi : InjOn f s) : (f '' s).Fini
te ↔ s.Finite
参数：hi : InjOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem finite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) : (f '' s).Finite ↔ s.Finite :=
  ⟨fun h => h.of_finite_image hi, Finite.image _⟩
/-
**Set.finite_range_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：finite_range_iff {f : α -> β} (hf : f.Injective) : (range f).Finite ↔ Fini
te α
参数：hf : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
lemma finite_range_iff {f : α → β} (hf : f.Injective) : (range f).Finite ↔ Finite α := by
  simpa [finite_univ_iff] using finite_image_iff (s := univ) hf.injOn
/-
**Set.univ_finite_iff_nonempty_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Finty
pe α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Fintype α) :=
  ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩

-- `simp`-normal form is `Set.toFinset_singleton`.
/-
**Set.Finite.toFinset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {a : α} (ha : optParam {a}.Finite ⋯), ha.toFinset = {a}
参数：ha : optParam {a}.Finite ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
-/
theorem Finite.toFinset_singleton {a : α} (ha : ({a} : Set α).Finite := finite_singleton _) :
    ha.toFinset = {a} :=
  Set.toFinite_toFinset _

@[simp]
/-
**Set.Finite.toFinset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {s : Set α} {a : α} (hs : (insert a 
s).Finite), hs.toFinset = insert a ⋯.toFinset
参数：hs : (insert a s).Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finite.toFinset_insert [DecidableEq α] {s : Set α} {a : α} (hs : (insert a s).Finite) :
    hs.toFinset = insert a (hs.subset <| subset_insert _ _).toFinset :=
  Finset.ext <| by simp
/-
**Set.Finite.toFinset_insert'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [inst : DecidableEq α] {a : α} {s : Set α} (hs : s.Finite),
 ⋯.toFinset = insert a hs.toFinset
参数：hs : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_insert`：∀ {α : Type u} [inst : DecidableEq α] {s : S
et α} {a : α} (hs : (insert a s).Finite), hs.toFinset = insert a ⋯.toFinset
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
-/
theorem Finite.toFinset_insert' [DecidableEq α] {a : α} {s : Set α} (hs : s.Finite) :
    (hs.insert a).toFinset = insert a hs.toFinset :=
  Finite.toFinset_insert _
/-
**Set.finite_option** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_option {s : Set (Option α)} : s.Finite ↔ { x : α | some x in s }.Fi
nite
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage_embedding`：∀ {α : Type u} {β : Type v} {s : Set β} (
f : α ↪ β), s.Finite → (⇑f ⁻¹' s).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem finite_option {s : Set (Option α)} : s.Finite ↔ { x : α | some x ∈ s }.Finite :=
  ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).subset fun x =>
      x.casesOn (fun _ => Or.inl rfl) fun _ hx => Or.inr <| mem_image_of_mem _ hx⟩

/-- Induction principle for finite sets: To prove a property `motive` of a finite set `s`, it's
enough to prove for the empty set and to prove that `motive t → motive ({a} ∪ t)` for all `t`.

See also `Set.Finite.induction_on_subset` for the version requiring to check
`motive t → motive ({a} ∪ t)` only for `t ⊆ s`. -/
@[elab_as_elim]
/-
**Set.Finite.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {motive : (s : Set α) → s.Finite → Prop} (s : Set α) (hs : 
s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉ s → ∀ (hs : s.Finite), mot
ive s hs → motive (insert a s) ⋯) → motive s hs
参数：s : Set α；s : Set α；hs : s.Finite；∀ {a : α} {s : Set α}, a ∉ s → ∀ (hs : s.Fi
nite), motive s hs → motive (insert a s) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Induction principle for finite sets: To prove a property `motive` of a finite se
t `s`, it's
enough to prove for the empty set and to prove that `motive t → motive ({a} ∪ t)
` for all `t`.

See also `Set.Finite.induction_on_subset` for the version requiring to check
`motive t → motive ({a} ∪ t)` only for `t ⊆ s`.
-/
theorem Finite.induction_on {motive : ∀ s : Set α, s.Finite → Prop} (s : Set α) (hs : s.Finite)
    (empty : motive ∅ finite_empty)
    (insert : ∀ {a s}, a ∉ s →
      ∀ hs : Set.Finite s, motive s hs → motive (insert a s) (hs.insert a)) :
    motive s hs := by
  lift s to Finset α using hs
  induction s using Finset.cons_induction_on with
  | empty => simpa
  | cons a s ha ih => simpa using @insert a s ha (Set.toFinite _) (ih _)

/-- Induction principle for finite sets: To prove a property `C` of a finite set `s`, it's enough
to prove for the empty set and to prove that `C t → C ({a} ∪ t)` for all `t ⊆ s`.

This is analogous to `Finset.induction_on'`. See also `Set.Finite.induction_on` for the version
requiring `motive t → motive ({a} ∪ t)` for all `t`. -/
@[elab_as_elim]
/-
**Set.Finite.induction_on_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {motive : (s : Set α) → s.Finite → Prop} (s : Set α) (hs : 
s.Finite),   motive ∅ ⋯ →     (∀ {a : α} {t : Set α}, a ∈ s → ∀ (hts : t ⊆ s), a
 ∉ t → motive t ⋯ → motive (insert a t) ⋯) → motive s hs
参数：s : Set α；s : Set α；hs : s.Finite；∀ {a : α} {t : Set α}, a ∈ s → ∀ (hts : t ⊆
 s), a ∉ t → motive t ⋯ → motive (insert a t) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.insert`：∀ {α : Type u} (a : α) {s : Set α}, s.Finite → (inser
t a s).Finite
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
Induction principle for finite sets: To prove a property `C` of a finite set `s`
, it's enough
to prove for the empty set and to prove that `C t → C ({a} ∪ t)` for all `t ⊆ s`
.

This is analogous to `Finset.induction_on'`. See also `Set.Finite.induction_on` 
for the version
requiring `motive t → motive ({a} ∪ t)` for all `t`.
-/
theorem Finite.induction_on_subset {motive : ∀ s : Set α, s.Finite → Prop} (s : Set α)
    (hs : s.Finite) (empty : motive ∅ finite_empty)
    (insert : ∀ {a t}, a ∈ s → ∀ hts : t ⊆ s, a ∉ t → motive t (hs.subset hts) →
      motive (insert a t) ((hs.subset hts).insert a)) : motive s hs := by
  refine Set.Finite.induction_on (motive := fun t _ => ∀ hts : t ⊆ s, motive t (hs.subset hts)) s hs
    (fun _ => empty) ?_ .rfl
  intro a s has _ hCs haS
  rw [insert_subset_iff] at haS
  exact insert haS.1 haS.2 has (hCs haS.2)

section

attribute [local instance] Nat.fintypeIio

/-- If `P` is some relation between terms of `γ` and sets in `γ`, such that every finite set
`t : Set γ` has some `c : γ` related to it, then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets are totally bounded.)
-/
/-
**Set.seq_of_forall_finite_exists** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：seq_of_forall_finite_exists {γ : Type*} {P : γ -> Set γ -> Prop} (h : fora
ll t : Set γ, t.Finite -> exists c, P c t) : exists u : Nat -> γ, forall n, P (u
 n) (u '' Iio n)
参数：h : forall t : Set γ, t.Finite -> exists c, P c t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Nat.strongRecOn_eq`：∀ {motive : ℕ → Sort u_1} (ind : (n : ℕ) → ((m : ℕ) 
→ m < n → motive m) → motive n) (t : ℕ),   Nat.strongRecOn t ind = ind t fun m x
 => Nat.…
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Set.finite_lt_nat`：finite_lt_nat (n : Nat) : Set.Finite { i | i < n }
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `P` is some relation between terms of `γ` and sets in `γ`, such that every fi
nite set
`t : Set γ` has some `c : γ` related to it, then there is a recursively defined 
sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets are totally bounded.)
-/
theorem seq_of_forall_finite_exists {γ : Type*} {P : γ → Set γ → Prop}
    (h : ∀ t : Set γ, t.Finite → ∃ c, P c t) : ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) := by
  have : Nonempty γ := (h ∅ finite_empty).nonempty
  choose! c hc using h
  set f : (n : ℕ) → (g : (m : ℕ) → m < n → γ) → γ := fun n g => c (range fun k : Iio n => g k.1 k.2)
  set u : ℕ → γ := fun n ↦ Nat.strongRecOn n f
  refine ⟨u, fun n ↦ ?_⟩
  convert! hc (u '' Iio n) ((finite_lt_nat _).image _)
  rw [image_eq_range]
  exact Nat.strongRecOn_eq f n

end

/-! ### Cardinality -/

/-
**Set.card_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_empty : Fintype.card (∅ : Set α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Cardinality
-/
theorem card_empty : Fintype.card (∅ : Set α) = 0 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Set.card_fintypeInsertOfNotMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) : @
Fintype.card _ (fintypeInsertOfNotMem s h) = Fintype.card s + 1
参数：s : Set α；h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_cons`：nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ 
s) ↔ a ∉ s ∧ Nodup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintypeInsertOfNotMem s h) = Fintype.card s + 1 := by
  simp [Fintype.card_ofFinset]
/-
**Set.card_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s) {d : Fintype (inse
rt a s : Set α)} : @Fintype.card _ d = Fintype.card s + 1
参数：s : Set α；h : a ∉ s；insert a s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.card_fintypeInsertOfNotMem`：card_fintypeInsertOfNotMem {a : α} (s : 
Set α) [Fintype s] (h : a ∉ s) : @Fintype.card _ (fintypeInsertOfNotMem s h) = F
intype.card s + 1
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
-/
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
    {d : Fintype (insert a s : Set α)} : @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintypeInsertOfNotMem s h]; congr!
/-
**Set.card_image_of_inj_on** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_image_of_inj_on {s : Set α} [Fintype s] {f : α -> β} [Fintype (f '' s
)] (H : forall x in s, forall y in s, f x = f y -> x = y) : Fintype.card (f '' s
) = Fintype.card s
参数：f '' s；H : forall x in s, forall y in s, f x = f y -> x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_of_finset'`：card_of_finset' {p : Set α} (s : Finset α) (H :
 forall x, x in s ↔ x in p) [Fintype p] : Fintype.card p = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) : Fintype.card (f '' s) = Fintype.card s :=
  haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.toFinset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.toFinset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_toFinset.1 hx) y (mem_toFinset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun _ => mem_toFinset).symm
/-
**Set.card_image_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_image_of_injective (s : Set α) [Fintype s] {f : α -> β} [Fintype (f '
' s)] (H : Function.Injective f) : Fintype.card (f '' s) = Fintype.card s
参数：s : Set α；f '' s；H : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.card_image_of_inj_on`：card_image_of_inj_on {s : Set α} [Fintype s] {
f : α -> β} [Fintype (f '' s)] (H : forall x in s, forall y in s, f x = f y -> x
 = y) : Fintyp…
-/
theorem card_image_of_injective (s : Set α) [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : Function.Injective f) : Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on fun _ _ _ _ h => H h

@[simp]
/-
**Set.card_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_singleton (a : α) : Fintype.card ({a} : Set α) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  rfl
/-
**Set.card_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) : Fintype.c
ard s < Fintype.card t
参数：h : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_lt_of_injective_not_surjective`：card_lt_of_injective_not_su
rjective (f : α -> β) (h : Function.Injective f) (h' : ¬Function.Surjective f) :
 card α < card β
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
· 使用定理 `Set.eq_of_inclusion_surjective`：eq_of_inclusion_surjective {s t : Set α}
 {h : s subseteq t} (h_surj : Function.Surjective (inclusion h)) : s = t
-/
theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) :
    Fintype.card s < Fintype.card t :=
  Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)
/-
**Set.card_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_le_card {s t : Set α} [Fintype s] [Fintype t] (hsub : s subseteq t) :
 Fintype.card s <= Fintype.card t
参数：hsub : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem card_le_card {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t) :
    Fintype.card s ≤ Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
/-
**Set.eq_of_subset_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s su
bseteq t) (hcard : Fintype.card t <= Fintype.card s) : s = t
参数：hsub : s subseteq t；hcard : Fintype.card t <= Fintype.card s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ssubset_of_subset`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ⊆ b → a = b ∨ a ⊂ b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Set.card_lt_card`：card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h 
: s ⊂ t) : Fintype.card s < Fintype.card t
-/
theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t)
    (hcard : Fintype.card t ≤ Fintype.card s) : s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard <| not_le_of_gt <| card_lt_card h
/-
**Set.card_range_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_range_of_injective [Fintype α] {f : α -> β} (hf : Injective f) [Finty
pe (range f)] : Fintype.card (range f) = Fintype.card α
参数：hf : Injective f；range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_range_of_injective [Fintype α] {f : α → β} (hf : Injective f) [Fintype (range f)] :
    Fintype.card (range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective f hf
/-
**Set.Finite.card_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} [inst : Fintype ↑s] (h : s.Finite), h.toFinset.
card = Fintype.card ↑s
参数：h : s.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_of_finset'`：card_of_finset' {p : Set α} (s : Finset α) (H :
 forall x, x in s ↔ x in p) [Fintype p] : Fintype.card p = #s
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem Finite.card_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset.card = Fintype.card s :=
  Eq.symm <| Fintype.card_of_finset' _ fun _ ↦ h.mem_toFinset
/-
**Set.card_ne_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x != a }] : Fintype.card
 { x : α | x != a } = Fintype.card α - 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    Fintype.card { x : α | x ≠ a } = Fintype.card α - 1 := by
  have := Classical.decEq α
  rw [← toFinset_card, toFinset_ofPred, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-! ### Infinite sets -/

variable {s t : Set α}

/-
**Set.infinite_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_univ_iff : (@univ α).Infinite ↔ Infinite α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Infinite.eq_1`：∀ {α : Type u} (s : Set α), s.Infinite = ¬s.Finite
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `not_finite_iff_infinite`：not_finite_iff_infinite : ¬Finite α ↔ Infinite 
α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infinite_univ_iff : (@univ α).Infinite ↔ Infinite α := by
  rw [Set.Infinite, finite_univ_iff, not_finite_iff_infinite]
/-
**Set.infinite_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_univ [h : Infinite α] : (@univ α).Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_univ_iff`：infinite_univ_iff : (@univ α).Infinite ↔ Infinite
 α
-/
theorem infinite_univ [h : Infinite α] : (@univ α).Infinite :=
  infinite_univ_iff.2 h
/-
**Set.Infinite.exists_notMem_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite → ∃ a ∈ s, a ∉ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma Infinite.exists_notMem_finite (hs : s.Infinite) (ht : t.Finite) : ∃ a, a ∈ s ∧ a ∉ t := by
  by_contra! h; exact hs <| ht.subset h
/-
**Set.Infinite.exists_notMem_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Infinite → ∀ (t : Finset α), ∃ a ∈ s, a ∉ t
参数：t : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.exists_notMem_finite`：∀ {α : Type u} {s t : Set α}, s.Infin
ite → t.Finite → ∃ a ∈ s, a ∉ t
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma Infinite.exists_notMem_finset (hs : s.Infinite) (t : Finset α) : ∃ a ∈ s, a ∉ t :=
  hs.exists_notMem_finite t.finite_toSet

section Infinite
variable [Infinite α]

/-
**Set.Finite.exists_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α} [Infinite α], s.Finite → ∃ a, a ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma Finite.exists_notMem (hs : s.Finite) : ∃ a, a ∉ s := by
  by_contra! h; exact infinite_univ (hs.subset fun a _ ↦ h _)
/-
**Set._root_.Finset.exists_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.exists_notMem (s : Finset α) : ∃ a, a ∉ s := s.finite_toSet.exists_notMem

end Infinite

/-- Embedding of `ℕ` into an infinite set. -/
/-
**Set.Infinite.natEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Set.Infinite`。
形式化陈述：{α : Type u} → (s : Set α) → s.Infinite → ℕ ↪ ↑s
参数：s : Set α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s

--- 原说明 ---
Embedding of `ℕ` into an infinite set.
-/
noncomputable def Infinite.natEmbedding (s : Set α) (h : s.Infinite) : ℕ ↪ s :=
  h.to_subtype.natEmbedding
/-
**Set.Infinite.exists_subset_card_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Infinite → ∀ (n : ℕ), ∃ t, ↑t ⊆ s ∧ t.card =
 n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Infinite.exists_subset_card_eq {s : Set α} (hs : s.Infinite) (n : ℕ) :
    ∃ t : Finset α, ↑t ⊆ s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩
/-
**Set.infinite_of_finite_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Inf
inite
参数：hs : sᶜ.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_union_self`：compl_union_self (s : Set α) : sᶜ union s = univ
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
theorem infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Infinite := fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)
/-
**Set.Finite.infinite_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [Infinite α] {s : Set α}, s.Finite → sᶜ.Infinite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
-/
theorem Finite.infinite_compl [Infinite α] {s : Set α} (hs : s.Finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ (α := α) (by simpa using hs.union h)
/-
**Set.Infinite.sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite → (s \ t).Infinite
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_sdiff`：∀ {α : Type u} {s t : Set α}, (s \ t).Finite → t.Fi
nite → s.Finite
-/
theorem Infinite.sdiff {s t : Set α} (hs : s.Infinite) (ht : t.Finite) :
    (s \ t).Infinite := fun h => hs <| h.of_sdiff ht

@[deprecated (since := "2026-06-03")] alias Infinite.diff := Infinite.sdiff
/-
**Set.Infinite.inter_of_finite_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u_1} {s t : Set α}, s.Infinite → (s \ t).Finite → (s ∩ t).Infi
nite
参数：s \ t；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_sdiff_right_self`：sdiff_sdiff_right_self : x \ (x \ y) = x ⊓ y
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
-/
lemma Infinite.inter_of_finite_sdiff {α : Type*} {s t : Set α} (hs : s.Infinite)
    (ht : (s \ t).Finite) : (s ∩ t).Infinite := by
  simpa using hs.sdiff ht

@[deprecated (since := "2026-06-03")]
alias Infinite.inter_of_finite_diff := Infinite.inter_of_finite_sdiff

@[simp]
/-
**Set.infinite_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_union {s t : Set α} : (s union t).Infinite ↔ s.Infinite ∨ t.Infin
ite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem infinite_union {s t : Set α} : (s ∪ t).Infinite ↔ s.Infinite ∨ t.Infinite := by
  simp only [Set.Infinite, finite_union, not_and_or]
/-
**Set.Infinite.of_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinite`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) {s : Set α}, (f '' s).Infinite → s
.Infinite
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem Infinite.of_image (f : α → β) {s : Set α} (hs : (f '' s).Infinite) : s.Infinite :=
  mt (Finite.image f) hs
/-
**Set.infinite_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_image_iff {s : Set α} {f : α -> β} (hi : InjOn f s) : (f '' s).In
finite ↔ s.Infinite
参数：hi : InjOn f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
-/
theorem infinite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) :
    (f '' s).Infinite ↔ s.Infinite :=
  not_congr <| finite_image_iff hi
/-
**Set.infinite_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_range_iff {f : α -> β} (hf : Injective f) : (range f).Infinite ↔ 
Infinite α
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Set.finite_range_iff`：finite_range_iff {f : α -> β} (hf : f.Injective) :
 (range f).Finite ↔ Finite α
-/
theorem infinite_range_iff {f : α → β} (hf : Injective f) : (range f).Infinite ↔ Infinite α := by
  simpa using (finite_range_iff hf).not

protected alias ⟨_, Infinite.image⟩ := infinite_image_iff
/-
**Set.infinite_of_injOn_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_of_injOn_mapsTo {s : Set α} {t : Set β} {f : α -> β} (hi : InjOn 
f s) (hm : MapsTo f s t) (hs : s.Infinite) : t.Infinite
参数：hi : InjOn f s；hm : MapsTo f s t；hs : s.Infinite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_image_iff`：infinite_image_iff {s : Set α} {f : α -> β} (hi 
: InjOn f s) : (f '' s).Infinite ↔ s.Infinite
-/
theorem infinite_of_injOn_mapsTo {s : Set α} {t : Set β} {f : α → β} (hi : InjOn f s)
    (hm : MapsTo f s t) (hs : s.Infinite) : t.Infinite :=
  ((infinite_image_iff hi).2 hs).mono (mapsTo_iff_image_subset.mp hm)
/-
**Set.Infinite.exists_ne_map_eq_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinit
e`。
形式化陈述：∀ {α : Type u} {β : Type v} {s : Set α} {t : Set β} {f : α → β},   s.Infin
ite → Set.MapsTo f s t → t.Finite → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Set.infinite_of_injOn_mapsTo`：infinite_of_injOn_mapsTo {s : Set α} {t : 
Set β} {f : α -> β} (hi : InjOn f s) (hm : MapsTo f s t) (hs : s.Infinite) : t.I
nfinite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
-/
theorem Infinite.exists_ne_map_eq_of_mapsTo {s : Set α} {t : Set β} {f : α → β} (hs : s.Infinite)
    (hf : MapsTo f s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  contrapose! ht
  exact infinite_of_injOn_mapsTo (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs
/-
**Set.infinite_range_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_range_of_injective [Infinite α] {f : α -> β} (hi : Injective f) :
 (range f).Infinite
参数：hi : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.infinite_image_iff`：infinite_image_iff {s : Set α} {f : α -> β} (hi 
: InjOn f s) : (f '' s).Infinite ↔ s.Infinite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
-/
theorem infinite_range_of_injective [Infinite α] {f : α → β} (hi : Injective f) :
    (range f).Infinite := by
  rw [← image_univ, infinite_image_iff hi.injOn]
  exact infinite_univ
/-
**Set.infinite_of_injective_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α -> β} (hi
 : Injective f) (hf : forall x : α, f x in s) : s.Infinite
参数：hi : Injective f；hf : forall x : α, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
-/
theorem infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α → β} (hi : Injective f)
    (hf : ∀ x : α, f x ∈ s) : s.Infinite := by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

set_option backward.isDefEq.respectTransparency false in
/-
**Set.not_injOn_infinite_finite_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_injOn_infinite_finite_image {f : α -> β} {s : Set α} (h_inf : s.Infini
te) (h_fin : (f '' s).Finite) : ¬InjOn f s
参数：h_inf : s.Infinite；h_fin : (f '' s).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `not_injective_infinite_finite`：not_injective_infinite_finite {α β} [Infi
nite α] [Finite β] (f : α -> β) : ¬Injective f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
-/
theorem not_injOn_infinite_finite_image {f : α → β} {s : Set α} (h_inf : s.Infinite)
    (h_fin : (f '' s).Finite) : ¬InjOn f s := by
  have : Finite (f '' s) := finite_coe_iff.mpr h_fin
  have : Infinite s := infinite_coe_iff.mpr h_inf
  have h := not_injective_infinite_finite
            ((f '' s).codRestrict (s.domRestrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose h
  rwa [injective_codRestrict, ← injOn_iff_injective]
/-
**Set.finite_range_findGreatest** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finite_range_findGreatest {P : α -> Nat -> Prop} [forall x, DecidablePred 
(P x)] {b : Nat} : (range fun x => Nat.findGreatest (P x) b).Finite
参数：P x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用引理 `Nat.findGreatest_le`：findGreatest_le (n : Nat) : Nat.findGreatest P n <=
 n
-/
theorem finite_range_findGreatest {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    (range fun x => Nat.findGreatest (P x) b).Finite :=
  (finite_le_nat b).subset <| range_subset_iff.2 fun _ => Nat.findGreatest_le _

end Set

namespace Finset

/-
**Finset.exists_card_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_card_eq [Infinite α] : forall n : Nat, exists s : Finset α, s.card 
= n | 0 => ⟨∅, card_empty⟩ | n + 1 => by classical obtain ⟨s, rfl⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_card_eq [Infinite α] : ∀ n : ℕ, ∃ s : Finset α, s.card = n
  | 0 => ⟨∅, card_empty⟩
  | n + 1 => by
    classical
    obtain ⟨s, rfl⟩ := exists_card_eq n
    obtain ⟨a, ha⟩ := s.exists_notMem
    exact ⟨insert a s, card_insert_of_notMem ha⟩

/-- `Finset` version of `Set.SurjOn.exists_subset_injOn_image_eq`. -/
/-
**Finset.exists_subset_injOn_image_eq_of_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t`。
形式化陈述：exists_subset_injOn_image_eq_of_surjOn [DecidableEq β] {f : α -> β} (s : S
et α) (t : Finset β) (hfs : s.SurjOn f t) : exists u : Finset α, ↑u subseteq s ∧
 Set.InjOn f u ∧ u.image f = t
参数：s : Set α；t : Finset β；hfs : s.SurjOn f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.exists_subset_injOn_image_eq`：∀ {α : Type u_1} {β : Type u_2}
 {s : Set α} {t : Set β} {f : α → β},   Set.SurjOn f s t → ∃ u ⊆ s, Set.InjOn f 
u ∧ f '' u = t
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s

--- 原说明 ---
`Finset` version of `Set.SurjOn.exists_subset_injOn_image_eq`.
-/
lemma exists_subset_injOn_image_eq_of_surjOn [DecidableEq β] {f : α → β}
    (s : Set α) (t : Finset β) (hfs : s.SurjOn f t) :
    ∃ u : Finset α, ↑u ⊆ s ∧ Set.InjOn f u ∧ u.image f = t := by
  obtain ⟨u, hus, hf, himg⟩ := hfs.exists_subset_injOn_image_eq
  refine ⟨(Finite.of_finite_image (by simp [himg]) hf).toFinset, by simpa, by simpa, ?_⟩
  simpa [← Finset.coe_inj]

end Finset

section LinearOrder
variable [LinearOrder α] {s : Set α}

/-- If a linear order does not contain any triple of elements `x < y < z`, then this type
is finite. -/
/-
**Finite.of_forall_not_lt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finite.of_forall_not_lt_lt (h : forall ⦃x y z : α⦄, x < y -> y < z -> Fals
e) : Finite α
参数：h : forall ⦃x y z : α⦄, x < y -> y < z -> False。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `eq_or_eq_or_eq_of_forall_not_lt_lt`：eq_or_eq_or_eq_of_forall_not_lt_lt [
LinearOrder α] (h : forall ⦃x y z : α⦄, x < y -> y < z -> False) (x y z : α) : x
 = y ∨ y = z ∨ x = z

--- 原说明 ---
If a linear order does not contain any triple of elements `x < y < z`, then this
 type
is finite.
-/
lemma Finite.of_forall_not_lt_lt (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) : Finite α := by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine @Finite.of_fintype α ⟨{x, y}, fun z => ?_⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y

/-- If a set `s` does not contain any triple of elements `x < y < z`, then `s` is finite. -/
/-
**Set.finite_of_forall_not_lt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.finite_of_forall_not_lt_lt (h : forall x in s, forall y in s, forall z
 in s, x < y -> y < z -> False) : Set.Finite s
参数：h : forall x in s, forall y in s, forall z in s, x < y -> y < z -> False。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `Finite.of_forall_not_lt_lt`：Finite.of_forall_not_lt_lt (h : forall ⦃x y 
z : α⦄, x < y -> y < z -> False) : Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If a set `s` does not contain any triple of elements `x < y < z`, then `s` is fi
nite.
-/
lemma Set.finite_of_forall_not_lt_lt (h : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x < y → y < z → False) :
    Set.Finite s :=
  @Set.toFinite _ s <| Finite.of_forall_not_lt_lt <| by simpa only [SetCoe.forall'] using! h

end LinearOrder

