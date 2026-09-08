/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Order.PropInstances
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Attr.Register

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `Set X := X → Prop`. Note that this function need not
be decidable. The definition is in the module `Mathlib/Data/Set/Defs.lean`.

This file provides some basic definitions related to sets and functions not present in the
definitions file, as well as extra lemmas for functions defined in the definitions file and
`Mathlib/Data/Set/Operations.lean` (empty set, univ, union, intersection, insert, singleton and
powerset).

Note that a set is a term, not a type. There is a coercion from `Set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the directory `Mathlib/SetTheory/ZFC/`, which contains an encoding of ZFC set theory in
Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : Set α` and `s₁ s₂ : Set α` are subsets of `α`

-  `t : Set β` is a subset of `β`.

Definitions in the file:

* `Nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Implementation notes

* `s.Nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
  the `s.Nonempty` dot notation can be used.

* For `s : Set α`, do not use `Subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, union, intersection, insert, singleton, powerset
-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t : Set α}

/-
**Set.mem_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u}, Function.Injective Membership.mem
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
protected theorem mem_injective : Injective (Membership.mem : Set α → α → Prop) := injective_id
/-
**Set.mem_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u}, Function.Surjective Membership.mem
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
protected theorem mem_surjective : Surjective (Membership.mem : Set α → α → Prop) := surjective_id
/-
**Set.mem_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u}, Function.Bijective Membership.mem
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
protected theorem mem_bijective : Bijective (Membership.mem : Set α → α → Prop) := bijective_id
/-
**Set.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instDistribLattice : DistribLattice (Set α) where __ : DistribLattice (α -
> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice : DistribLattice (Set α) where
  __ : DistribLattice (α → Prop) := inferInstance
  le := (· ≤ ·)
  lt := fun s t => s ⊆ t ∧ ¬t ⊆ s
  sup := (· ∪ ·)
  inf := (· ∩ ·)
/-
**Set.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instBoundedOrder : BoundedOrder (Set α) where __ : BoundedOrder (α -> Prop
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder : BoundedOrder (Set α) where
  __ : BoundedOrder (α → Prop) := inferInstance
  bot := ∅
  top := univ

@[simp]
/-
**Set.top_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：top_eq_univ : (⊤ : Set α) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl

@[simp]
/-
**Set.bot_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：bot_eq_empty : (⊥ : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl

@[simp]
/-
**Set.sup_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sup_eq_union : ((· ⊔ ·) : Set α -> Set α -> Set α) = (· union ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_eq_union : ((· ⊔ ·) : Set α → Set α → Set α) = (· ∪ ·) :=
  rfl

@[simp]
/-
**Set.inf_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inf_eq_inter : ((· ⊓ ·) : Set α -> Set α -> Set α) = (· inter ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_eq_inter : ((· ⊓ ·) : Set α → Set α → Set α) = (· ∩ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Set.le_eq_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_eq_subset : ((· <= ·) : Set α -> Set α -> Prop) = (· subseteq ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_eq_subset : ((· ≤ ·) : Set α → Set α → Prop) = (· ⊆ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Set.lt_eq_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：lt_eq_ssubset : ((· < ·) : Set α -> Set α -> Prop) = (· ⊂ ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_eq_ssubset : ((· < ·) : Set α → Set α → Prop) = (· ⊂ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Set.le_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_iff_subset : s <= t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff_subset : s ≤ t ↔ s ⊆ t :=
  Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Set.lt_iff_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：lt_iff_ssubset : s < t ↔ s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_ssubset : s < t ↔ s ⊂ t :=
  Iff.rfl

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LE.le.subset, _root_.HasSubset.Subset.le⟩ := le_iff_subset

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LT.lt.ssubset, _root_.HasSSubset.SSubset.lt⟩ := lt_iff_ssubset
/-
**Set.PiSetCoe.canLift** 是 Mathlib 中的一个定理，位于命名空间 `Set.PiSetCoe`。
形式化陈述：∀ (ι : Type u) (α : ι → Type v) [∀ (i : ι), Nonempty (α i)] (s : Set ι),  
 CanLift ((i : ↑s) → α ↑i) ((i : ι) → α i) (fun f i => f ↑i) fun x => True
参数：ι : Type u；α : ι → Type v；i : ι；α i；s : Set ι；(i : ↑s) → α ↑i；(i : ι) → α i；f
un f i => f ↑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PiSetCoe.canLift (ι : Type u) (α : ι → Type v) [∀ i, Nonempty (α i)] (s : Set ι) :
    CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)
/-
**Set.PiSetCoe.canLift'** 是 Mathlib 中的一个定理，位于命名空间 `Set.PiSetCoe`。
形式化陈述：∀ (ι : Type u) (α : Type v) [Nonempty α] (s : Set ι), CanLift (↑s → α) (ι 
→ α) (fun f i => f ↑i) fun x => True
参数：ι : Type u；α : Type v；s : Set ι；↑s → α；ι → α；fun f i => f ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PiSetCoe.canLift`：∀ (ι : Type u) (α : ι → Type v) [∀ (i : ι), Nonemp
ty (α i)] (s : Set ι),   CanLift ((i : ↑s) → α ↑i) ((i : ι) → α i) (fun f i => f
 ↑i) fun x…
-/
instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [Nonempty α] (s : Set ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSetCoe.canLift ι (fun _ => α) s

end Set

section SetCoe

variable {α : Type u}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : Set α) : CoeTC s α := ⟨fun x => x.1⟩
/-
**Set.coe_eq_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.coe_eq_subtype (s : Set α) : ↥s = { x // x in s }
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x ∈ s } :=
  rfl
/-
**Set.coe_ofPred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p x }
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.coe_ofPred (p : α → Prop) : ↥{ x | p x } = { x // p x } :=
  rfl

@[deprecated (since := "2026-07-09")] alias Set.coe_setOf := Set.coe_ofPred
/-
**SetCoe.forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s, p x) ↔ forall (
x) (h : x in s), p ⟨x, h⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ (x) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
/-
**SetCoe.exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetCoe.exists {s : Set α} {p : s -> Prop} : (exists x : s, p x) ↔ exists (
x : _) (h : x in s), p ⟨x, h⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
-/
theorem SetCoe.exists {s : Set α} {p : s → Prop} :
    (∃ x : s, p x) ↔ ∃ (x : _) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
/-
**SetCoe.exists'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetCoe.exists' {s : Set α} {p : forall x, x in s -> Prop} : (exists (x : _
) (h : x in s), p x h) ↔ exists x : s, p x.1 x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SetCoe.exists`：SetCoe.exists {s : Set α} {p : s -> Prop} : (exists x : s
, p x) ↔ exists (x : _) (h : x in s), p ⟨x, h⟩
-/
theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∃ (x : _) (h : x ∈ s), p x h) ↔ ∃ x : s, p x.1 x.2 :=
  (@SetCoe.exists _ _ fun x => p x.1 x.2).symm
/-
**SetCoe.forall'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetCoe.forall' {s : Set α} {p : forall x, x in s -> Prop} : (forall (x) (h
 : x in s), p x h) ↔ forall x : s, p x.1 x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
-/
theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∀ (x) (h : x ∈ s), p x h) ↔ ∀ x : s, p x.1 x.2 :=
  (@SetCoe.forall _ _ fun x => p x.1 x.2).symm

@[simp]
/-
**set_coe_cast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {s t : Set α} (H' : s = t) (H : ↑s = ↑t) (x : ↑s), cast H x
 = ⟨↑x, ⋯⟩
参数：H' : s = t；H : ↑s = ↑t；x : ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem set_coe_cast :
    ∀ {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | _, _, rfl, _, _ => rfl
/-
**SetCoe.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem SetCoe.ext {s : Set α} {a b : s} : (a : α) = b → a = b :=
  Subtype.ext
/-
**SetCoe.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
-/
theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl

end SetCoe

/-- See also `Subtype.prop` -/
/-
**Subtype.mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
参数：p : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
See also `Subtype.prop`
-/
theorem Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.prop

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Set α) :=
  ⟨∅⟩

@[trans]
/-
**Set.mem_of_mem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x in s) (h : s subseteq t
) : x in t
参数：hx : x in s；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx
/-
**Set.ofPred_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_injective : Function.Injective (@ofPred α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem ofPred_injective : Function.Injective (@ofPred α) := injective_id

@[deprecated (since := "2026-07-09")] alias setOf_injective := ofPred_injective
/-
**Set.ofPred_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_inj {p q : α -> Prop} : { x | p x } = { x | q x } ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofPred_inj {p q : α → Prop} : { x | p x } = { x | q x } ↔ p = q := Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_inj := ofPred_inj

/-! ### Lemmas about `mem` and `ofPred` -/

/-
**Set.ofPred_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_bijective : Bijective (ofPred : (α -> Prop) -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)

--- 原说明 ---
### Lemmas about `mem` and `ofPred`
-/
theorem ofPred_bijective : Bijective (ofPred : (α → Prop) → Set α) :=
  bijective_id

@[deprecated (since := "2026-07-09")] alias setOf_bijective := ofPred_bijective
/-
**Set.subset_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_ofPred {p : α -> Prop} {s : Set α} : s subseteq ofPred p ↔ forall x
, x in s -> p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_ofPred {p : α → Prop} {s : Set α} : s ⊆ ofPred p ↔ ∀ x, x ∈ s → p x :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias subset_setOf := subset_ofPred
/-
**Set.ofPred_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_subset {p : α -> Prop} {s : Set α} : ofPred p subseteq s ↔ forall x
, p x -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofPred_subset {p : α → Prop} {s : Set α} : ofPred p ⊆ s ↔ ∀ x, p x → x ∈ s :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset := ofPred_subset

@[simp]
/-
**Set.ofPred_subset_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_subset_ofPred {p q : α -> Prop} : { a | p a } subseteq { a | q a } 
↔ forall a, p a -> q a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofPred_subset_ofPred {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset_setOf := ofPred_subset_ofPred

@[gcongr]
alias ⟨_, ofPred_subset_ofPred_of_imp⟩ := ofPred_subset_ofPred

@[deprecated (since := "2026-07-09")]
alias setOf_subset_setOf_of_imp := ofPred_subset_ofPred_of_imp
/-
**Set.ofPred_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_and {p q : α -> Prop} : { a | p a ∧ q a } = { a | p a } inter { a |
 q a }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofPred_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_and := ofPred_and
/-
**Set.ofPred_or** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_or {p q : α -> Prop} : { a | p a ∨ q a } = { a | p a } union { a | 
q a }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofPred_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_or := ofPred_or

/-! ### Subset and strict subset relations -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
@[grind =]
/-
**Set.subset_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_def : (s subseteq t) = forall x, x in s -> x in t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

@[grind =]
/-
**Set.ssubset_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_def : (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬t ⊆ s) :=
  rfl

@[refl]
/-
**Set.Subset.refl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subset`。
形式化陈述：∀ {α : Type u} (a : Set α), a ⊆ a
参数：a : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subset.refl (a : Set α) : a ⊆ a := fun _ => id
/-
**Set.Subset.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subset`。
形式化陈述：∀ {α : Type u} {s : Set α}, s ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem Subset.rfl {s : Set α} : s ⊆ s :=
  Subset.refl s

@[trans]
/-
**Set.Subset.trans** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subset`。
形式化陈述：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c := fun _ h => bc <| ab h

@[trans]
/-
**Set.mem_of_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y in s) : x in s
参数：hx : x = y；h : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
  hx.symm ▸ h
/-
**Set.Subset.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subset`。
形式化陈述：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩
/-
**Set.Subset.antisymm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subset`。
形式化陈述：∀ {α : Type u} {a b : Set α}, a = b ↔ a ⊆ b ∧ b ⊆ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
-/
theorem Subset.antisymm_iff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩

-- an alternative name
/-
**Set.eq_of_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_subset_of_subset {a b : Set α} : a subseteq b -> b subseteq a -> a =
 b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
-/
theorem eq_of_subset_of_subset {a b : Set α} : a ⊆ b → b ⊆ a → a = b :=
  Subset.antisymm
/-
**Set.mem_of_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
  @h _
/-
**Set.notMem_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
-/
theorem notMem_subset (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| mem_of_subset_of_mem h
/-
**Set.subset_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_iff_notMem : s subseteq t ↔ forall ⦃a⦄, a ∉ t -> a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subset_iff_notMem : s ⊆ t ↔ ∀ ⦃a⦄, a ∉ t → a ∉ s := by
  simp only [subset_def, not_imp_not]
/-
**Set.not_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_subset : ¬s ⊆ t ↔ ∃ a ∈ s, a ∉ t := by
  simp only [subset_def, not_forall, exists_prop]
/-
**Set.not_univ_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_univ_subset : ¬univ subseteq s ↔ exists a, a ∉ s
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_univ_subset : ¬univ ⊆ s ↔ ∃ a, a ∉ s := by
  simp [not_subset]

@[deprecated not_univ_subset (since := "2026-03-12")]
/-
**Set.not_top_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_top_subset : ¬⊤ subseteq s ↔ exists a, a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.not_univ_subset`：not_univ_subset : ¬univ subseteq s ↔ exists a, a ∉ 
s
-/
theorem not_top_subset : ¬⊤ ⊆ s ↔ ∃ a, a ∉ s :=
  not_univ_subset
/-
**Set.eq_of_forall_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_of_forall_subset_iff (h : forall u, s subseteq u ↔ t subseteq u) : s = 
t
参数：h : forall u, s subseteq u ↔ t subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
-/
lemma eq_of_forall_subset_iff (h : ∀ u, s ⊆ u ↔ t ⊆ u) : s = t := eq_of_forall_ge_iff h

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/

/-
**Set.eq_or_ssubset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s ⊆ t → s = t ∨ s ⊂ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b

--- 原说明 ---
### Definition of strict subsets `s ⊂ t` and basic properties.
-/
protected theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h
/-
**Set.exists_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exists x in t, x ∉ s
参数：h : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset.1 h.2
/-
**Set.ssubset_iff_subset_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s ⊂ t ↔ s ⊆ t ∧ s ≠ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
-/
protected theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne (Set α) _ s t
/-
**Set.ssubset_iff_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_iff_of_subset {s t : Set α} (h : s subseteq t) : s ⊂ t ↔ exists x 
in t, x ∉ s
参数：h : s subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
-/
theorem ssubset_iff_of_subset {s t : Set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
  ⟨exists_of_ssubset, fun ⟨_, hxt, hxs⟩ => ⟨h, fun h => hxs <| h hxt⟩⟩
/-
**Set.ssubset_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s subseteq t ∧ exists x in t, x
 ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_of_subset`：ssubset_iff_of_subset {s t : Set α} (h : s su
bseteq t) : s ⊂ t ↔ exists x in t, x ∉ s
-/
theorem ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ ∃ x ∈ t, x ∉ s :=
  ⟨fun h ↦ ⟨h.le, Set.exists_of_ssubset h⟩, fun ⟨h1, h2⟩ ↦ (Set.ssubset_iff_of_subset h1).mpr h2⟩
/-
**Set.ssubset_of_ssubset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s₁ s₂ s₃ : Set α}, s₁ ⊂ s₂ → s₂ ⊆ s₃ → s₁ ⊂ s₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
    (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩
/-
**Set.ssubset_of_subset_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s₁ s₂ s₃ : Set α}, s₁ ⊆ s₂ → s₂ ⊂ s₃ → s₁ ⊂ s₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊆ s₂)
    (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩
/-
**Set.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_empty (x : α) : x ∉ (∅ : Set α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_empty (x : α) : x ∉ (∅ : Set α) :=
  id
/-
**Set.not_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_notMem : ¬a ∉ s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem not_notMem : ¬a ∉ s ↔ a ∈ s :=
  not_not

/-! ### Non-empty sets -/

/-
**Set.nonempty_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a

--- 原说明 ---
### Non-empty sets
-/
theorem nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort
/-
**Set.nonempty_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_def : s.Nonempty ↔ exists x, x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_def : s.Nonempty ↔ ∃ x, x ∈ s :=
  Iff.rfl
/-
**Set.nonempty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_mem {x} (h : x in s) : s.Nonempty
参数：h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_of_mem {x} (h : x ∈ s) : s.Nonempty :=
  ⟨x, h⟩
/-
**Set.Nonempty.not_subset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nonempty → ¬s ⊆ ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.not_subset_empty : s.Nonempty → ¬s ⊆ ∅
  | ⟨_, hx⟩, hs => hs hx

/-- Extract a witness from `s.Nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `Classical.choice` axiom. -/
/-
**Set.Nonempty.some** 是 Mathlib 中的一个定义，位于命名空间 `Set.Nonempty`。
形式化陈述：{α : Type u} → {s : Set α} → s.Nonempty → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract a witness from `s.Nonempty`. This function might be used instead of case
 analysis
on the argument. Note that it makes a proof depend on the `Classical.choice` axi
om.
-/
protected noncomputable def Nonempty.some (h : s.Nonempty) : α :=
  Classical.choose h
/-
**Set.Nonempty.some_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.some ∈ s
参数：h : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem Nonempty.some_mem (h : s.Nonempty) : h.some ∈ s :=
  Classical.choose_spec h
/-
**Set.Nonempty.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
@[gcongr] theorem Nonempty.mono (ht : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  hs.imp ht
/-
**Set.nonempty_of_not_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_not_subset (h : ¬s subseteq t) : (s \ t).Nonempty
参数：h : ¬s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
-/
theorem nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩
/-
**Set.nonempty_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty
参数：ht : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_not_subset`：nonempty_of_not_subset (h : ¬s subseteq t) :
 (s \ t).Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2
/-
**Set.Nonempty.of_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s t : Set α}, (s \ t).Nonempty → s.Nonempty
参数：s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Nonempty.of_sdiff (h : (s \ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

@[deprecated (since := "2026-06-03")] alias Nonempty.of_diff := Nonempty.of_sdiff
/-
**Set.nonempty_of_ssubset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty
参数：ht : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_sdiff`：∀ {α : Type u} {s t : Set α}, (s \ t).Nonempty → 
s.Nonempty
· 使用定理 `Set.nonempty_of_ssubset`：nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).None
mpty
-/
theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty :=
  (nonempty_of_ssubset ht).of_sdiff
/-
**Set.Nonempty.inl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s.Nonempty → (s ∪ t).Nonempty
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
theorem Nonempty.inl (hs : s.Nonempty) : (s ∪ t).Nonempty :=
  hs.imp fun _ => Or.inl
/-
**Set.Nonempty.inr** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s t : Set α}, t.Nonempty → (s ∪ t).Nonempty
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
theorem Nonempty.inr (ht : t.Nonempty) : (s ∪ t).Nonempty :=
  ht.imp fun _ => Or.inr

@[simp]
/-
**Set.union_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_nonempty : (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_or`：∀ {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) ↔ (∃ x, p
 x) ∨ ∃ x, q x
-/
theorem union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  exists_or
/-
**Set.Nonempty.left** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → s.Nonempty
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Nonempty.left (h : (s ∩ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left
/-
**Set.Nonempty.right** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → t.Nonempty
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nonempty.right (h : (s ∩ t).Nonempty) : t.Nonempty :=
  h.imp fun _ => And.right
/-
**Set.inter_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_nonempty : (s inter t).Nonempty ↔ exists x, x in s ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inter_nonempty : (s ∩ t).Nonempty ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Iff.rfl
/-
**Set.inter_nonempty_iff_exists_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_nonempty_iff_exists_left : (s inter t).Nonempty ↔ exists x in s, x i
n t
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
theorem inter_nonempty_iff_exists_left : (s ∩ t).Nonempty ↔ ∃ x ∈ s, x ∈ t := by
  simp_rw [inter_nonempty]
/-
**Set.inter_nonempty_iff_exists_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_nonempty_iff_exists_right : (s inter t).Nonempty ↔ exists x in t, x 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, and_comm]
/-
**Set.nonempty_iff_univ_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]
/-
**Set.univ_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem univ_nonempty : ∀ [Nonempty α], (univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩
/-
**Set.Nonempty.to_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
-/
theorem Nonempty.to_subtype : s.Nonempty → Nonempty (↥s) :=
  nonempty_subtype.2
/-
**Set.Nonempty.to_type** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.to_type : s.Nonempty → Nonempty α := fun ⟨x, _⟩ => ⟨x⟩
/-
**Set.univ.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set.univ`。
形式化陈述：∀ {α : Type u} [Nonempty α], Nonempty ↑Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
-/
instance univ.nonempty [Nonempty α] : Nonempty (↥(Set.univ : Set α)) :=
  Set.univ_nonempty.to_subtype

-- Redeclare for refined keys
-- `Nonempty (@Subtype _ (@Membership.mem _ (Set _) _ (@Top.top (Set _) _)))`
/-
**Set.instNonemptyTop** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instNonemptyTop [Nonempty α] : Nonempty (⊤ : Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonemptyTop [Nonempty α] : Nonempty (⊤ : Set α) :=
  inferInstanceAs (Nonempty (univ : Set α))
/-
**Set.Nonempty.of_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α} [Nonempty ↑s], s.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
-/
theorem Nonempty.of_subtype [Nonempty (↥s)] : s.Nonempty := nonempty_subtype.mp ‹_›

/-! ### Lemmas about the empty set -/

/-
**Set.empty_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_def : (∅ : Set α) = { _x : α | False }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about the empty set
-/
theorem empty_def : (∅ : Set α) = { _x : α | False } :=
  rfl

@[simp, grind =, push]
/-
**Set.mem_empty_iff_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_empty_iff_false (x : α) : x in (∅ : Set α) ↔ False
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  Iff.rfl

@[simp, grind =]
/-
**Set.ofPred_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_false : { _a : α | False } = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofPred_false : { _a : α | False } = ∅ :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_false := ofPred_false
/-
**Set.ofPred_bot** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u}, {_x | ⊥} = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofPred_bot : { _x : α | ⊥ } = ∅ := rfl

@[deprecated (since := "2026-07-09")]
alias setOf_bot := ofPred_bot

@[simp]
/-
**Set.empty_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_subset (s : Set α) : ∅ subseteq s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  nofun

@[simp, grind =]
/-
**Set.subset_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.Subset.antisymm_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ a ⊆ b ∧ b
 ⊆ a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ s = ∅ :=
  (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm
/-
**Set.eq_empty_iff_forall_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_iff_forall_notMem {s : Set α} : s = ∅ ↔ forall x, x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
-/
theorem eq_empty_iff_forall_notMem {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  subset_empty_iff.symm
/-
**Set.eq_empty_of_forall_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_of_forall_notMem (h : forall x, x ∉ s) : s = ∅
参数：h : forall x, x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
-/
theorem eq_empty_of_forall_notMem (h : ∀ x, x ∉ s) : s = ∅ :=
  subset_empty_iff.1 h
/-
**Set.eq_empty_of_subset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_of_subset_empty {s : Set α} : s subseteq ∅ -> s = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
-/
theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ :=
  subset_empty_iff.1

/-- See also `Set.nonempty_iff_ne_empty`. -/
@[push]
/-
**Set.not_nonempty_iff_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `Set.nonempty_iff_ne_empty`.
-/
theorem not_nonempty_iff_eq_empty : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_notMem]

/-- See also `Set.not_nonempty_iff_eq_empty`. -/
@[push ←]
/-
**Set.nonempty_iff_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅

--- 原说明 ---
See also `Set.not_nonempty_iff_eq_empty`.
-/
theorem nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty.not_right

/-- Variant of `nonempty_iff_ne_empty` used by `push Not`. -/
@[push ←]
/-
**Set.nonempty_iff_empty_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iff_empty_ne : s.Nonempty ↔ ∅ != s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
Variant of `nonempty_iff_ne_empty` used by `push Not`.
-/
theorem nonempty_iff_empty_ne : s.Nonempty ↔ ∅ ≠ s :=
  nonempty_iff_ne_empty.trans ne_comm

/-- See also `nonempty_iff_ne_empty'`. -/
/-
**Set.not_nonempty_iff_eq_empty'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_nonempty_iff_eq_empty' : ¬Nonempty s ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `nonempty_iff_ne_empty'`.
-/
theorem not_nonempty_iff_eq_empty' : ¬Nonempty s ↔ s = ∅ := by
  rw [nonempty_subtype, not_exists, eq_empty_iff_forall_notMem]

/-- See also `not_nonempty_iff_eq_empty'`. -/
/-
**Set.nonempty_iff_ne_empty'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_iff_ne_empty' : Nonempty s ↔ s != ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `Set.not_nonempty_iff_eq_empty'`：not_nonempty_iff_eq_empty' : ¬Nonempty s
 ↔ s = ∅

--- 原说明 ---
See also `not_nonempty_iff_eq_empty'`.
-/
theorem nonempty_iff_ne_empty' : Nonempty s ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty'.not_right

alias ⟨Nonempty.ne_empty, _⟩ := nonempty_iff_ne_empty

@[simp]
/-
**Set.not_nonempty_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_nonempty_empty : ¬(∅ : Set α).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun ⟨_, hx⟩ => hx

@[simp]
/-
**Set.isEmpty_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = ∅ :=
  not_iff_not.1 <| by simpa using! nonempty_iff_ne_empty
/-
**Set.eq_empty_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s = ∅ := by
  simpa using ‹IsEmpty s›

/-- There is exactly one set of a type that is empty. -/
/-
**Set.uniqueEmpty** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：uniqueEmpty [IsEmpty α] : Unique (Set α) where uniq _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is exactly one set of a type that is empty.
-/
instance uniqueEmpty [IsEmpty α] : Unique (Set α) where
  uniq _ := eq_empty_of_isEmpty _
/-
**Set.eq_empty_or_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 nonempty_iff_ne_empty.2
/-
**Set.subset_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_eq_empty {s t : Set α} (h : t subseteq s) (e : s = ∅) : t = ∅
参数：h : t subseteq s；e : s = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
-/
theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1 <| e ▸ h
/-
**Set.forall_mem_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_mem_empty {p : α -> Prop} : (forall x in (∅ : Set α), p x) ↔ True
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_true_intro`：∀ {a : Prop}, a → (a ↔ True)
-/
theorem forall_mem_empty {p : α → Prop} : (∀ x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun _ => False.elim
/-
**Set.Nonempty.forall_const** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Nonempty → ∀ {p : Prop}, (∀ x ∈ s, p) ↔ p
参数：∀ x ∈ s, p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.forall_const (h : s.Nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h ↦ h x hx, fun h _ _ ↦ h⟩

@[simp]
/-
**Set.forall_mem_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_mem_const {p : Prop} [Nonempty s] : (forall x in s, p) ↔ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.forall_const`：∀ {α : Type u} {s : Set α}, s.Nonempty → ∀ {p
 : Prop}, (∀ x ∈ s, p) ↔ p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
-/
theorem forall_mem_const {p : Prop} [Nonempty s] : (∀ x ∈ s, p) ↔ p :=
  (nonempty_coe_sort.mp ‹_›).forall_const
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type u) : IsEmpty.{u + 1} (↥(∅ : Set α)) :=
  ⟨fun x => x.2⟩

@[simp]
/-
**Set.empty_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_ssubset : ∅ ⊂ s ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

/-!

### Universal set.

In Lean `@univ α` (or `univ : Set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp, grind =]
/-
**Set.ofPred_true** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_true : { _x : α | True } = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Universal set.

In Lean `@univ α` (or `univ : Set α`) is the set that contains all elements of t
ype `α`.
Mathematically it is the same as `α` but it has a different type.
-/
theorem ofPred_true : { _x : α | True } = univ :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_true := ofPred_true
/-
**Set.ofPred_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u}, {_x | ⊤} = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofPred_top : { _x : α | ⊤ } = univ := rfl

@[deprecated (since := "2026-07-09")]
alias setOf_top := ofPred_top

@[simp]
/-
**Set.univ_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `trivial`：True
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
theorem univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩
/-
**Set.empty_ne_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_ne_univ [Nonempty α] : (∅ : Set α) != univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isEmpty_of_nonempty`：not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsE
mpty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem empty_ne_univ [Nonempty α] : (∅ : Set α) ≠ univ := fun e =>
  not_isEmpty_of_nonempty α <| univ_eq_empty_iff.1 e.symm

@[simp, grind ←]
/-
**Set.subset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_univ (s : Set α) : s subseteq univ
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem subset_univ (s : Set α) : s ⊆ univ := fun _ _ => trivial

@[simp, grind =]
/-
**Set.univ_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_subset_iff {s : Set α} : univ subseteq s ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff
/-
**Set.eq_univ_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_univ_iff_forall {s : Set α} : s = univ ↔ forall x, x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `trivial`：True
-/
theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun _ => imp_iff_right trivial
/-
**Set.eq_univ_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_univ_of_forall {s : Set α} : (forall x, x in s) -> s = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2
/-
**Set.Nonempty.eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u} {s : Set α} [Subsingleton α], s.Nonempty → s = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
/-
**Set.eq_univ_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_univ_of_subset {s t : Set α} (h : s subseteq t) (hs : s = univ) : t = u
niv
参数：h : s subseteq t；hs : s = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_univ_subset`：∀ {α : Type u} {s : Set α}, Set.univ ⊆ s → s
 = Set.univ
-/
theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset <| (hs ▸ h : univ ⊆ t)
/-
**Set.exists_mem_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ (α : Type u_1) [Nonempty α], ∃ x, x ∈ Set.univ
参数：α : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem exists_mem_of_nonempty (α) : ∀ [Nonempty α], ∃ x : α, x ∈ (univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩
/-
**Set.ne_univ_iff_exists_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ne_univ_iff_exists_notMem {α : Type*} (s : Set α) : s != univ ↔ exists a, 
a ∉ s
参数：s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ne_univ_iff_exists_notMem {α : Type*} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s := by
  rw [← not_forall, ← eq_univ_iff_forall]
/-
**Set.not_subset_iff_exists_mem_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：not_subset_iff_exists_mem_notMem {α : Type*} {s t : Set α} : ¬s subseteq t
 ↔ exists x, x in s ∧ x ∉ t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_subset_iff_exists_mem_notMem {α : Type*} {s t : Set α} :
    ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t := by simp [subset_def]
/-
**Set.univ_unique** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_unique [Unique α] : @Set.univ α = {default}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `trivial`：True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem univ_unique [Unique α] : @Set.univ α = {default} :=
  Set.ext fun x => iff_of_true trivial <| Subsingleton.elim x default
/-
**Set.ssubset_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_univ_iff : s ⊂ univ ↔ s != univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem ssubset_univ_iff : s ⊂ univ ↔ s ≠ univ :=
  lt_top_iff_ne_top
/-
**Set.ssubset_univ_iff_nonempty_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_univ_iff_nonempty_compl : s ⊂ univ ↔ sᶜ.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ssubset_def`：ssubset_def : (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s)
· 使用定理 `Set.not_univ_subset`：not_univ_subset : ¬univ subseteq s ↔ exists a, a ∉ 
s
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ssubset_univ_iff_nonempty_compl : s ⊂ univ ↔ sᶜ.Nonempty := by
  rw [ssubset_def, Set.not_univ_subset, Set.nonempty_def]
  simp

alias ⟨_, Nonempty.ssubset_univ⟩ := ssubset_univ_iff_nonempty_compl
/-
**Set.compl_ssubset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_ssubset_univ : sᶜ ⊂ univ ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ssubset_def`：ssubset_def : (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s)
· 使用定理 `Set.not_univ_subset`：not_univ_subset : ¬univ subseteq s ↔ exists a, a ∉ 
s
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compl_ssubset_univ : sᶜ ⊂ univ ↔ s.Nonempty := by
  rw [ssubset_def, Set.not_univ_subset, Set.nonempty_def]
  simp

alias ⟨_, Nonempty.compl_ssubset_univ⟩ := compl_ssubset_univ
/-
**Set.nontrivial_of_nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_ne_univ`：empty_ne_univ [Nonempty α] : (∅ : Set α) != univ
-/
instance nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α) :=
  ⟨⟨∅, univ, empty_ne_univ⟩⟩

/-! ### Lemmas about union -/

/-
**Set.union_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_def {s₁ s₂ : Set α} : s₁ union s₂ = { a | a in s₁ ∨ a in s₂ }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about union
-/
theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ } :=
  rfl
/-
**Set.mem_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_union_left {x : α} {a : Set α} (b : Set α) : x in a -> x in a union b
参数：b : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x ∈ a → x ∈ a ∪ b :=
  Or.inl
/-
**Set.mem_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_union_right {x : α} {b : Set α} (a : Set α) : x in b -> x in a union b
参数：a : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x ∈ b → x ∈ a ∪ b :=
  Or.inr
/-
**Set.mem_or_mem_of_mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x in a union b) : x in 
a ∨ x in b
参数：H : x in a union b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b :=
  H
/-
**Set.MemUnion.elim** 是 Mathlib 中的一个定理，位于命名空间 `Set.MemUnion`。
形式化陈述：∀ {α : Type u} {x : α} {a b : Set α} {P : Prop}, x ∈ a ∪ b → (x ∈ a → P) →
 (x ∈ b → P) → P
参数：x ∈ a → P；x ∈ b → P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem MemUnion.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P)
    (H₃ : x ∈ b → P) : P :=
  Or.elim H₁ H₂ H₃

@[simp, grind =, push]
/-
**Set.mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a ∨ x in b
参数：x : α；a b : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  Iff.rfl

@[simp]
/-
**Set.union_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_self (a : Set α) : a union a = a
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_self_iff`：∀ {a : Prop}, a ∨ a ↔ a
-/
theorem union_self (a : Set α) : a ∪ a = a :=
  ext fun _ => or_self_iff

@[simp]
/-
**Set.union_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_empty (a : Set α) : a union ∅ = a
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  ext fun _ => iff_of_eq (or_false _)

@[simp]
/-
**Set.empty_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_union (a : Set α) : ∅ union a = a
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  ext fun _ => iff_of_eq (false_or _)
/-
**Set.union_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_comm (a b : Set α) : a union b = b union a
参数：a b : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem union_comm (a b : Set α) : a ∪ b = b ∪ a :=
  ext fun _ => or_comm
/-
**Set.union_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_assoc (a b c : Set α) : a union b union c = a union (b union c)
参数：a b c : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
-/
theorem union_assoc (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext fun _ => or_assoc
/-
**Set.union_isAssoc** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：union_isAssoc : Std.Associative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
-/
instance union_isAssoc : Std.Associative (α := Set α) (· ∪ ·) :=
  ⟨union_assoc⟩
/-
**Set.union_isComm** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：union_isComm : Std.Commutative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
instance union_isComm : Std.Commutative (α := Set α) (· ∪ ·) :=
  ⟨union_comm⟩
/-
**Set.union_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_left_comm (s₁ s₂ s₃ : Set α) : s₁ union (s₂ union s₃) = s₂ union (s₁
 union s₃)
参数：s₁ s₂ s₃ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_left_comm`：∀ {a b c : Prop}, a ∨ b ∨ c ↔ b ∨ a ∨ c
-/
theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext fun _ => or_left_comm
/-
**Set.union_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_right_comm (s₁ s₂ s₃ : Set α) : s₁ union s₂ union s₃ = s₁ union s₃ u
nion s₂
参数：s₁ s₂ s₃ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `or_right_comm`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b
-/
theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext fun _ => or_right_comm

@[simp]
/-
**Set.union_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_left {s t : Set α} : s union t = s ↔ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
theorem union_eq_left {s t : Set α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left

@[simp]
/-
**Set.union_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_right {s t : Set α} : s union t = t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
theorem union_eq_right {s t : Set α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right
/-
**Set.union_eq_self_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_self_of_subset_left {s t : Set α} (h : s subseteq t) : s union t 
= t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
-/
theorem union_eq_self_of_subset_left {s t : Set α} (h : s ⊆ t) : s ∪ t = t :=
  union_eq_right.mpr h
/-
**Set.union_eq_self_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_self_of_subset_right {s t : Set α} (h : t subseteq s) : s union t
 = s
参数：h : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_left`：union_eq_left {s t : Set α} : s union t = s ↔ t subse
teq s
-/
theorem union_eq_self_of_subset_right {s t : Set α} (h : t ⊆ s) : s ∪ t = s :=
  union_eq_left.mpr h

@[simp]
/-
**Set.subset_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_union_left {s t : Set α} : s subseteq s union t
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_union_left {s t : Set α} : s ⊆ s ∪ t := fun _ => Or.inl

@[simp]
/-
**Set.subset_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_union_right {s t : Set α} : t subseteq s union t
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_union_right {s t : Set α} : t ⊆ s ∪ t := fun _ => Or.inr
/-
**Set.union_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_subset {s t r : Set α} (sr : s subseteq r) (tr : t subseteq r) : s u
nion t subseteq r
参数：sr : s subseteq r；tr : t subseteq r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_subset {s t r : Set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r := fun _ =>
  Or.rec (@sr _) (@tr _)

@[simp]
/-
**Set.union_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_subset_iff {s t u : Set α} : s union t subseteq u ↔ s subseteq u ∧ t
 subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
-/
theorem union_subset_iff {s t u : Set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (forall_congr' fun _ => or_imp).trans forall_and

@[gcongr]
/-
**Set.union_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq s₂) (h₂ : t₁ su
bseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
参数：h₁ : s₁ subseteq s₂；h₂ : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) :
    s₁ ∪ t₁ ⊆ s₂ ∪ t₂ :=
  sup_le_sup h₁ h₂
/-
**Set.union_subset_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ subseteq s₂) : s₁ unio
n t subseteq s₂ union t
参数：t；h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
/-
**Set.union_subset_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ subseteq t₂) : s unio
n t₁ subseteq s union t₂
参数：s；h : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
/-
**Set.subset_union_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_union_of_subset_left {s t : Set α} (h : s subseteq t) (u : Set α) :
 s subseteq t union u
参数：h : s subseteq t；u : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  h.trans subset_union_left
/-
**Set.subset_union_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_union_of_subset_right {s u : Set α} (h : s subseteq u) (t : Set α) 
: s subseteq t union u
参数：h : s subseteq u；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  h.trans subset_union_right
/-
**Set.union_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_congr_left (ht : t subseteq s union u) (hu : u subseteq s union t) :
 s union t = s union u
参数：ht : t subseteq s union u；hu : u subseteq s union t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_congr_left`：sup_congr_left (hb : b <= a ⊔ c) (hc : c <= a ⊔ b) : a ⊔
 b = a ⊔ c
-/
theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ∪ u :=
  sup_congr_left ht hu
/-
**Set.union_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_congr_right (hs : s subseteq t union u) (ht : t subseteq s union u) 
: s union u = t union u
参数：hs : s subseteq t union u；ht : t subseteq s union u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_congr_right`：sup_congr_right (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a
 ⊔ c = b ⊔ c
-/
theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht
/-
**Set.union_eq_union_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_union_iff_left : s union t = s union u ↔ t subseteq s union u ∧ u
 subseteq s union t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_sup_iff_left`：sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b <= a ⊔ c ∧ 
c <= a ⊔ b
-/
theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left
/-
**Set.union_eq_union_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_eq_union_iff_right : s union u = t union u ↔ s subseteq t union u ∧ 
t subseteq s union u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_sup_iff_right`：sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a <= b ⊔ c 
∧ b <= a ⊔ c
-/
theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right

@[simp]
/-
**Set.union_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_empty_iff {s t : Set α} : s union t = ∅ ↔ s = ∅ ∧ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
-/
theorem union_empty_iff {s t : Set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := by
  simp only [← subset_empty_iff]
  exact union_subset_iff

@[simp]
/-
**Set.union_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_univ (s : Set α) : s union univ = univ
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_top_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTo
p α] (a : α), a ⊔ ⊤ = ⊤
-/
theorem union_univ (s : Set α) : s ∪ univ = univ := sup_top_eq _

@[simp]
/-
**Set.univ_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_union (s : Set α) : univ union s = univ
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊔ a = ⊤
-/
theorem univ_union (s : Set α) : univ ∪ s = univ := top_sup_eq _

@[simp]
/-
**Set.ssubset_union_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_union_left_iff : s ⊂ s union t ↔ ¬ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_lt_sup`：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
-/
theorem ssubset_union_left_iff : s ⊂ s ∪ t ↔ ¬ t ⊆ s :=
  left_lt_sup

@[simp]
/-
**Set.ssubset_union_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_union_right_iff : t ⊂ s union t ↔ ¬ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_lt_sup`：right_lt_sup : b < a ⊔ b ↔ ¬a <= b
-/
theorem ssubset_union_right_iff : t ⊂ s ∪ t ↔ ¬ s ⊆ t :=
  right_lt_sup

/-! ### Lemmas about intersection -/

/-
**Set.inter_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_def {s₁ s₂ : Set α} : s₁ inter s₂ = { a | a in s₁ ∧ a in s₂ }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about intersection
-/
theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ } :=
  rfl

@[simp, mfld_simps, grind =, push]
/-
**Set.mem_inter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_inter_iff (x : α) (a b : Set α) : x in a inter b ↔ x in a ∧ x in b
参数：x : α；a b : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  Iff.rfl
/-
**Set.mem_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in b) : x in a inter
 b
参数：ha : x in a；hb : x in b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_inter {x : α} {a b : Set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
  ⟨ha, hb⟩
/-
**Set.mem_of_mem_inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_inter_left {x : α} {a b : Set α} (h : x in a inter b) : x in a
参数：h : x in a inter b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ a :=
  h.left
/-
**Set.mem_of_mem_inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_inter_right {x : α} {a b : Set α} (h : x in a inter b) : x in b
参数：h : x in a inter b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ b :=
  h.right

@[simp]
/-
**Set.inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_self (a : Set α) : a inter a = a
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
-/
theorem inter_self (a : Set α) : a ∩ a = a :=
  ext fun _ => and_self_iff

@[simp]
/-
**Set.inter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_empty (a : Set α) : a inter ∅ = ∅
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  ext fun _ => iff_of_eq (and_false _)

@[simp]
/-
**Set.empty_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_inter (a : Set α) : ∅ inter a = ∅
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  ext fun _ => iff_of_eq (false_and _)
/-
**Set.inter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_comm (a b : Set α) : a inter b = b inter a
参数：a b : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a :=
  ext fun _ => and_comm
/-
**Set.inter_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_assoc (a b c : Set α) : a inter b inter c = a inter (b inter c)
参数：a b c : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
-/
theorem inter_assoc (a b c : Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext fun _ => and_assoc
/-
**Set.inter_isAssoc** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：inter_isAssoc : Std.Associative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
-/
instance inter_isAssoc : Std.Associative (α := Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩
/-
**Set.inter_isComm** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：inter_isComm : Std.Commutative (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
instance inter_isComm : Std.Commutative (α := Set α) (· ∩ ·) :=
  ⟨inter_comm⟩
/-
**Set.inter_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ inter s₃) = s₂ inter (s₁
 inter s₃)
参数：s₁ s₂ s₃ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
-/
theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => and_left_comm
/-
**Set.inter_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ inter s₃ = s₁ inter s₃ i
nter s₂
参数：s₁ s₂ s₃ : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_right_comm`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b
-/
theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => and_right_comm

@[simp, mfld_simps]
/-
**Set.inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset_left {s t : Set α} : s inter t subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem inter_subset_left {s t : Set α} : s ∩ t ⊆ s := fun _ => And.left

@[simp]
/-
**Set.inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset_right {s t : Set α} : s inter t subseteq t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inter_subset_right {s t : Set α} : s ∩ t ⊆ t := fun _ => And.right
/-
**Set.subset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_inter {s t r : Set α} (rs : r subseteq s) (rt : r subseteq t) : r s
ubseteq s inter t
参数：rs : r subseteq s；rt : r subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_inter {s t r : Set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t := fun _ h =>
  ⟨rs h, rt h⟩

@[simp]
/-
**Set.subset_inter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_inter_iff {s t r : Set α} : r subseteq s inter t ↔ r subseteq s ∧ r
 subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_and`：∀ {b c : Prop} {α : Sort u_1}, (∀ (a : α), b ∧ c) ↔ (∀ (a : α),
 b) ∧ ∀ (a : α), c
· 使用定理 `forall_and`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (x : α), p x ∧ q x) ↔ 
(∀ (x : α), p x) ∧ ∀ (x : α), q x
-/
theorem subset_inter_iff {s t r : Set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  (forall_congr' fun _ => imp_and).trans forall_and
/-
**Set.inter_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
@[simp] lemma inter_eq_left : s ∩ t = s ↔ s ⊆ t := inf_eq_left
/-
**Set.inter_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
@[simp] lemma inter_eq_right : s ∩ t = t ↔ t ⊆ s := inf_eq_right
/-
**Set.left_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, s = s ∩ t ↔ s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_eq_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a = a ⊓
 b ↔ a ≤ b
-/
@[simp] lemma left_eq_inter : s = s ∩ t ↔ s ⊆ t := left_eq_inf
/-
**Set.right_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, t = s ∩ t ↔ t ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_eq_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b = a 
⊓ b ↔ b ≤ a
-/
@[simp] lemma right_eq_inter : t = s ∩ t ↔ t ⊆ s := right_eq_inf
/-
**Set.inter_eq_self_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_eq_self_of_subset_left {s t : Set α} : s subseteq t -> s inter t = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
-/
theorem inter_eq_self_of_subset_left {s t : Set α} : s ⊆ t → s ∩ t = s :=
  inter_eq_left.mpr
/-
**Set.inter_eq_self_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_eq_self_of_subset_right {s t : Set α} : t subseteq s -> s inter t = 
t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
-/
theorem inter_eq_self_of_subset_right {s t : Set α} : t ⊆ s → s ∩ t = t :=
  inter_eq_right.mpr
/-
**Set.inter_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_congr_left (ht : s inter u subseteq t) (hu : s inter t subseteq u) :
 s inter t = s inter u
参数：ht : s inter u subseteq t；hu : s inter t subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_congr_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}, a 
⊓ c ≤ b → a ⊓ b ≤ c → a ⊓ b = a ⊓ c
-/
theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu
/-
**Set.inter_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_congr_right (hs : t inter u subseteq s) (ht : s inter u subseteq t) 
: s inter u = t inter u
参数：hs : t inter u subseteq s；ht : s inter u subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_congr_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}, b
 ⊓ c ≤ a → a ⊓ c ≤ b → a ⊓ c = b ⊓ c
-/
theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht
/-
**Set.inter_eq_inter_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_eq_inter_iff_left : s inter t = s inter u ↔ s inter u subseteq t ∧ s
 inter t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_inf_iff_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α
}, a ⊓ b = a ⊓ c ↔ a ⊓ c ≤ b ∧ a ⊓ b ≤ c
-/
theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left
/-
**Set.inter_eq_inter_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_eq_inter_iff_right : s inter u = t inter u ↔ t inter u subseteq s ∧ 
s inter u subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_inf_iff_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : 
α}, a ⊓ c = b ⊓ c ↔ b ⊓ c ≤ a ∧ a ⊓ c ≤ b
-/
theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right

@[simp, mfld_simps]
/-
**Set.inter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_univ (a : Set α) : a inter univ = a
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
theorem inter_univ (a : Set α) : a ∩ univ = a := inf_top_eq _

@[simp, mfld_simps]
/-
**Set.univ_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_inter (a : Set α) : univ inter a = a
参数：a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
-/
theorem univ_inter (a : Set α) : univ ∩ a = a := top_inf_eq _

@[gcongr]
/-
**Set.inter_subset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq t₁) (h₂ : s₂ su
bseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
参数：h₁ : s₁ subseteq t₁；h₂ : s₂ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
-/
theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
    s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
  inf_le_inf h₁ h₂
/-
**Set.inter_subset_inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset_inter_left {s t : Set α} (u : Set α) (H : s subseteq t) : s i
nter u subseteq t inter u
参数：u : Set α；H : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H Subset.rfl
/-
**Set.inter_subset_inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_subset_inter_right {s t : Set α} (u : Set α) (H : s subseteq t) : u 
inter s subseteq u inter t
参数：u : Set α；H : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter Subset.rfl H
/-
**Set.union_inter_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_inter_cancel_left {s t : Set α} : (s union t) inter s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right subset_union_left
/-
**Set.union_inter_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_inter_cancel_right {s t : Set α} : (s union t) inter t = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right subset_union_right
/-
**Set.inter_ofPred_eq_sep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_ofPred_eq_sep (s : Set α) (p : α -> Prop) : s inter {a | p a} = {a i
n s | p a}
参数：s : Set α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_ofPred_eq_sep (s : Set α) (p : α → Prop) : s ∩ {a | p a} = {a ∈ s | p a} :=
  rfl

@[deprecated (since := "2026-07-09")]
alias inter_setOf_eq_sep := inter_ofPred_eq_sep
/-
**Set.ofPred_inter_eq_sep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_inter_eq_sep (p : α -> Prop) (s : Set α) : {a | p a} inter s = {a i
n s | p a}
参数：p : α -> Prop；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem ofPred_inter_eq_sep (p : α → Prop) (s : Set α) : {a | p a} ∩ s = {a ∈ s | p a} :=
  inter_comm _ _

@[deprecated (since := "2026-07-09")] alias setOf_inter_eq_sep := ofPred_inter_eq_sep
/-
**Set.sep_eq_inter_sep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_eq_inter_sep {α : Type*} {s t : Set α} {p : α -> Prop} (hst : s subset
eq t) : {x in s | p x} = s inter {x in t | p x}
参数：hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_ofPred_eq_sep`：inter_ofPred_eq_sep (s : Set α) (p : α -> Prop)
 : s inter {a | p a} = {a in s | p a}
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_eq_inter`：∀ {α : Type u} {s t : Set α}, s = s ∩ t ↔ s ⊆ t
-/
theorem sep_eq_inter_sep {α : Type*} {s t : Set α} {p : α → Prop} (hst : s ⊆ t) :
    {x ∈ s | p x} = s ∩ {x ∈ t | p x} := by
  rw [← inter_ofPred_eq_sep s p, ← inter_ofPred_eq_sep t p,
    ← inter_assoc, ← left_eq_inter.mpr hst]

@[simp]
/-
**Set.inter_ssubset_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_ssubset_right_iff : s inter t ⊂ t ↔ ¬ t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_lt_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
< b ↔ ¬b ≤ a
-/
theorem inter_ssubset_right_iff : s ∩ t ⊂ t ↔ ¬ t ⊆ s :=
  inf_lt_right

@[simp]
/-
**Set.inter_ssubset_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_ssubset_left_iff : s inter t ⊂ s ↔ ¬ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_lt_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b <
 a ↔ ¬a ≤ b
-/
theorem inter_ssubset_left_iff : s ∩ t ⊂ s ↔ ¬ s ⊆ t :=
  inf_lt_left

/-! ### Distributivity laws -/

/-
**Set.inter_union_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_union_distrib_left (s t u : Set α) : s inter (t union u) = s inter t
 union s inter u
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c

--- 原说明 ---
### Distributivity laws
-/
theorem inter_union_distrib_left (s t u : Set α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left _ _ _
/-
**Set.union_inter_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_inter_distrib_right (s t u : Set α) : (s union t) inter u = s inter 
u union t inter u
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
-/
theorem union_inter_distrib_right (s t u : Set α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right _ _ _
/-
**Set.union_inter_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_inter_distrib_left (s t u : Set α) : s union t inter u = (s union t)
 inter (s union u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
theorem union_inter_distrib_left (s t u : Set α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left _ _ _
/-
**Set.inter_union_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_union_distrib_right (s t u : Set α) : s inter t union u = (s union u
) inter (t union u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-/
theorem inter_union_distrib_right (s t u : Set α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right _ _ _
/-
**Set.union_union_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_union_distrib_left (s t u : Set α) : s union (t union u) = s union t
 union (s union u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_distrib_left`：sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a
 ⊔ b ⊔ (a ⊔ c)
-/
theorem union_union_distrib_left (s t u : Set α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _
/-
**Set.union_union_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_union_distrib_right (s t u : Set α) : s union t union u = s union u 
union (t union u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_distrib_right`：sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a
 ⊔ c ⊔ (b ⊔ c)
-/
theorem union_union_distrib_right (s t u : Set α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _
/-
**Set.inter_inter_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_inter_distrib_left (s t u : Set α) : s inter (t inter u) = s inter t
 inter (s inter u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_inf_distrib_left`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : 
α), a ⊓ (b ⊓ c) = a ⊓ b ⊓ (a ⊓ c)
-/
theorem inter_inter_distrib_left (s t u : Set α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _
/-
**Set.inter_inter_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_inter_distrib_right (s t u : Set α) : s inter t inter u = s inter u 
inter (t inter u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_inf_distrib_right`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c :
 α), a ⊓ b ⊓ c = a ⊓ c ⊓ (b ⊓ c)
-/
theorem inter_inter_distrib_right (s t u : Set α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _
/-
**Set.union_union_union_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_union_union_comm (s t u v : Set α) : s union t union (u union v) = s
 union u union (t union v)
参数：s t u v : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
-/
theorem union_union_union_comm (s t u v : Set α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _
/-
**Set.inter_inter_inter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_inter_inter_comm (s t u v : Set α) : s inter t inter (u inter v) = s
 inter u inter (t inter v)
参数：s t u v : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_inf_inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c d : α)
, a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d)
-/
theorem inter_inter_inter_comm (s t u v : Set α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

section Sep

variable {p q : α → Prop} {x : α}

/-
**Set.mem_sep** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_sep (xs : x in s) (px : p x) : x in { x in s | p x }
参数：xs : x in s；px : p x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_sep (xs : x ∈ s) (px : p x) : x ∈ { x ∈ s | p x } :=
  ⟨xs, px⟩

@[simp]
/-
**Set.sep_mem_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_mem_eq : { x in s | x in t } = s inter t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sep_mem_eq : { x ∈ s | x ∈ t } = s ∩ t :=
  rfl

@[simp]
/-
**Set.mem_sep_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_sep_iff : x in { x in s | p x } ↔ x in s ∧ p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sep_iff : x ∈ { x ∈ s | p x } ↔ x ∈ s ∧ p x :=
  Iff.rfl
/-
**Set.sep_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_ext_iff : { x in s | p x } = { x in s | q x } ↔ forall x in s, p x ↔ q
 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sep_ext_iff : { x ∈ s | p x } = { x ∈ s | q x } ↔ ∀ x ∈ s, p x ↔ q x := by
  simp_rw [Set.ext_iff, mem_sep_iff, and_congr_right_iff]
/-
**Set.sep_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_eq_of_subset (h : s subseteq t) : { x in t | x in s } = s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
-/
theorem sep_eq_of_subset (h : s ⊆ t) : { x ∈ t | x ∈ s } = s :=
  inter_eq_self_of_subset_right h

@[simp]
/-
**Set.sep_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x } subseteq s
参数：s : Set α；p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sep_subset (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ s := fun _ => And.left
/-
**Set.sep_subset_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_subset_ofPred (s : Set α) (p : α -> Prop) : { x in s | p x } subseteq 
{ x | p x }
参数：s : Set α；p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sep_subset_ofPred (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ { x | p x } :=
  fun _ => And.right

@[deprecated (since := "2026-07-09")]
alias sep_subset_setOf := sep_subset_ofPred

@[simp]
/-
**Set.sep_eq_self_iff_mem_true** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_eq_self_iff_mem_true : { x in s | p x } = s ↔ forall x in s, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sep_eq_self_iff_mem_true : { x ∈ s | p x } = s ↔ ∀ x ∈ s, p x := by
  simp_rw [Set.ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp]
/-
**Set.sep_eq_empty_iff_mem_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_eq_empty_iff_mem_false : { x in s | p x } = ∅ ↔ forall x in s, ¬p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sep_eq_empty_iff_mem_false : { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x := by
  simp_rw [Set.ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]
/-
**Set.sep_true** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_true : { x in s | True } = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem sep_true : { x ∈ s | True } = s :=
  inter_univ s
/-
**Set.sep_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_false : { x in s | False } = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
-/
theorem sep_false : { x ∈ s | False } = ∅ :=
  inter_empty s
/-
**Set.sep_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_empty (p : α -> Prop) : { x in (∅ : Set α) | p x } = ∅
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_inter`：empty_inter (a : Set α) : ∅ inter a = ∅
-/
theorem sep_empty (p : α → Prop) : { x ∈ (∅ : Set α) | p x } = ∅ :=
  empty_inter {x | p x}
/-
**Set.sep_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem sep_univ : { x ∈ (univ : Set α) | p x } = { x | p x } :=
  univ_inter {x | p x}

@[simp]
/-
**Set.sep_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_union : { x | (x in s ∨ x in t) ∧ p x } = { x in s | p x } union { x i
n t | p x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
-/
theorem sep_union : { x | (x ∈ s ∨ x ∈ t) ∧ p x } = { x ∈ s | p x } ∪ { x ∈ t | p x } :=
  union_inter_distrib_right { x | x ∈ s } { x | x ∈ t } {x | p x}

@[simp]
/-
**Set.sep_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_inter : { x | (x in s ∧ x in t) ∧ p x } = { x in s | p x } inter { x i
n t | p x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_inter_distrib_right`：inter_inter_distrib_right (s t u : Set α)
 : s inter t inter u = s inter u inter (t inter u)
-/
theorem sep_inter : { x | (x ∈ s ∧ x ∈ t) ∧ p x } = { x ∈ s | p x } ∩ { x ∈ t | p x } :=
  inter_inter_distrib_right s t {x | p x}

@[simp]
/-
**Set.sep_and** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_and : { x in s | p x ∧ q x } = { x in s | p x } inter { x in s | q x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_inter_distrib_left`：inter_inter_distrib_left (s t u : Set α) :
 s inter (t inter u) = s inter t inter (s inter u)
-/
theorem sep_and : { x ∈ s | p x ∧ q x } = { x ∈ s | p x } ∩ { x ∈ s | q x } :=
  inter_inter_distrib_left s {x | p x} {x | q x}

@[simp]
/-
**Set.sep_or** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_or : { x in s | p x ∨ q x } = { x in s | p x } union { x in s | q x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
-/
theorem sep_or : { x ∈ s | p x ∨ q x } = { x ∈ s | p x } ∪ { x ∈ s | q x } :=
  inter_union_distrib_left s {x | p x} {x | q x}

@[simp]
/-
**Set.sep_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sep_ofPred : { x in { y | p y } | q x } = { x | p x ∧ q x }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sep_ofPred : { x ∈ { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl

@[deprecated (since := "2026-07-09")]
alias sep_setOf := sep_ofPred

end Sep

/-! ### Powerset -/

/-
**Set.mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_powerset {x s : Set α} (h : x subseteq s) : x in 𝒫 s
参数：h : x subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Powerset
-/
theorem mem_powerset {x s : Set α} (h : x ⊆ s) : x ∈ 𝒫 s := @h
/-
**Set.subset_of_mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_of_mem_powerset {x s : Set α} (h : x in 𝒫 s) : x subseteq s
参数：h : x in 𝒫 s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_of_mem_powerset {x s : Set α} (h : x ∈ 𝒫 s) : x ⊆ s := @h

@[simp, grind =, push]
/-
**Set.mem_powerset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_powerset_iff (x s : Set α) : x in 𝒫 s ↔ x subseteq s
参数：x s : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_powerset_iff (x s : Set α) : x ∈ 𝒫 s ↔ x ⊆ s :=
  Iff.rfl
/-
**Set.powerset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_inter (s t : Set α) : 𝒫 (s inter t) = 𝒫 s inter 𝒫 t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
-/
theorem powerset_inter (s t : Set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext fun _ => subset_inter_iff

@[simp]
/-
**Set.powerset_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_mono : 𝒫 s subseteq 𝒫 t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  ⟨fun h => @h _ (fun _ h => h), fun h _ hu _ ha => h (hu ha)⟩
/-
**Set.monotone_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_powerset : Monotone (powerset : Set α -> Set (Set α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.powerset_mono`：powerset_mono : 𝒫 s subseteq 𝒫 t ↔ s subseteq t
-/
theorem monotone_powerset : Monotone (powerset : Set α → Set (Set α)) := fun _ _ => powerset_mono.2

@[simp]
/-
**Set.powerset_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_nonempty : (𝒫 s).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, fun _ h => empty_subset s h⟩

@[simp]
/-
**Set.powerset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_empty : 𝒫 (∅ : Set α) = {∅}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
-/
theorem powerset_empty : 𝒫 (∅ : Set α) = {∅} :=
  ext fun _ => subset_empty_iff

@[simp]
/-
**Set.powerset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_univ : 𝒫 (univ : Set α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem powerset_univ : 𝒫 (univ : Set α) = univ :=
  eq_univ_of_forall subset_univ

/-! ### Sets defined as an if-then-else -/

/-
**Set.mem_dite_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_dite_univ_right (p : Prop) [Decidable p] (t : p -> Set α) (x : α) : (x
 in if h : p then t h else univ) ↔ forall h : p, x in t h
参数：p : Prop；t : p -> Set α；x : α。
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Sets defined as an if-then-else
-/
theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else univ) ↔ ∀ h : p, x ∈ t h := by
  simp [mem_dite]

@[simp]
/-
**Set.mem_ite_univ_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) : x in ite
 p t Set.univ ↔ p -> x in t
参数：p : Prop；t : Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_dite_univ_right`：mem_dite_univ_right (p : Prop) [Decidable p] (t
 : p -> Set α) (x : α) : (x in if h : p then t h else univ) ↔ forall h : p, x in
 t h
-/
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t Set.univ ↔ p → x ∈ t :=
  mem_dite_univ_right p (fun _ => t) x
/-
**Set.mem_dite_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p -> Set α) (x : α) : (x
 in if h : p then univ else t h) ↔ forall h : ¬p, x in t h
参数：p : Prop；t : ¬p -> Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then univ else t h) ↔ ∀ h : ¬p, x ∈ t h := by
  split_ifs <;> simp_all

@[simp]
/-
**Set.mem_ite_univ_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) : x in ite 
p Set.univ t ↔ ¬p -> x in t
参数：p : Prop；t : Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_dite_univ_left`：mem_dite_univ_left (p : Prop) [Decidable p] (t :
 ¬p -> Set α) (x : α) : (x in if h : p then univ else t h) ↔ forall h : ¬p, x in
 t h
-/
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p Set.univ t ↔ ¬p → x ∈ t :=
  mem_dite_univ_left p (fun _ => t) x
/-
**Set.mem_dite_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_dite_empty_right (p : Prop) [Decidable p] (t : p -> Set α) (x : α) : (
x in if h : p then t h else ∅) ↔ exists h : p, x in t h
参数：p : Prop；t : p -> Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_dite_empty_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else ∅) ↔ ∃ h : p, x ∈ t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false, not_not]
  exact ⟨fun h => ⟨h.2, h.1 h.2⟩, fun ⟨h₁, h₂⟩ => ⟨fun _ => h₂, h₁⟩⟩

@[simp]
/-
**Set.mem_ite_empty_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) : x in it
e p t ∅ ↔ p ∧ x in t
参数：p : Prop；t : Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_dite_empty_right`：mem_dite_empty_right (p : Prop) [Decidable p] 
(t : p -> Set α) (x : α) : (x in if h : p then t h else ∅) ↔ exists h : p, x in 
t h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t ∅ ↔ p ∧ x ∈ t :=
  (mem_dite_empty_right p (fun _ => t) x).trans (by simp)
/-
**Set.mem_dite_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p -> Set α) (x : α) : (
x in if h : p then ∅ else t h) ↔ exists h : ¬p, x in t h
参数：p : Prop；t : ¬p -> Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then ∅ else t h) ↔ ∃ h : ¬p, x ∈ t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun ⟨h₁, h₂⟩ => ⟨fun h => h₁ h, fun _ => h₂⟩⟩

@[simp]
/-
**Set.mem_ite_empty_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) : x in ite
 p ∅ t ↔ ¬p ∧ x in t
参数：p : Prop；t : Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_dite_empty_left`：mem_dite_empty_left (p : Prop) [Decidable p] (t
 : ¬p -> Set α) (x : α) : (x in if h : p then ∅ else t h) ↔ exists h : ¬p, x in 
t h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p ∅ t ↔ ¬p ∧ x ∈ t :=
  (mem_dite_empty_left p (fun _ => t) x).trans (by simp)

end Set

open Set

namespace Function

variable {α : Type*} {β : Type*}

/-
**Function.Injective.nonempty_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inje
ctive`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : Set α → Set β},   Function.Injective 
f → f ∅ = ∅ → ∀ {s : Set α}, (f s).Nonempty ↔ s.Nonempty
参数：f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Injective.nonempty_apply_iff {f : Set α → Set β} (hf : Injective f) (h2 : f ∅ = ∅)
    {s : Set α} : (f s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, ← h2, nonempty_iff_ne_empty, hf.ne_iff]

end Function

namespace Subsingleton

variable {α : Type*} [Subsingleton α]

/-
**Subsingleton.eq_univ_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：eq_univ_of_nonempty {s : Set α} : s.Nonempty -> s = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty → s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

@[elab_as_elim]
/-
**Subsingleton.set_cases** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：set_cases {p : Set α -> Prop} (h0 : p ∅) (h1 : p univ) (s) : p s
参数：h0 : p ∅；h1 : p univ；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.eq_univ_of_nonempty`：eq_univ_of_nonempty {s : Set α} : s.No
nempty -> s = univ
-/
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1
/-
**Subsingleton.mem_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Subsingleton`。
形式化陈述：mem_iff_nonempty {α : Type*} [Subsingleton α] {s : Set α} {x : α} : x in s
 ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem mem_iff_nonempty {α : Type*} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩

end Subsingleton

/-! ### Decidability instances for sets -/

namespace Set

variable {α : Type u} (s t : Set α) (a b : α)

/-
**Set.decidableSdiff** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableSdiff [Decidable (a in s)] [Decidable (a in t)] : Decidable (a in
 s \ t)
参数：a in s；a in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableSdiff [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s \ t) :=
  inferInstanceAs (Decidable (a ∈ s ∧ a ∉ t))
/-
**Set.decidableInter** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableInter [Decidable (a in s)] [Decidable (a in t)] : Decidable (a in
 s inter t)
参数：a in s；a in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableInter [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∩ t) :=
  inferInstanceAs (Decidable (a ∈ s ∧ a ∈ t))
/-
**Set.decidableUnion** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableUnion [Decidable (a in s)] [Decidable (a in t)] : Decidable (a in
 s union t)
参数：a in s；a in t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableUnion [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∪ t) :=
  inferInstanceAs (Decidable (a ∈ s ∨ a ∈ t))
/-
**Set.decidableCompl** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableCompl [Decidable (a in s)] : Decidable (a in sᶜ)
参数：a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableCompl [Decidable (a ∈ s)] : Decidable (a ∈ sᶜ) :=
  inferInstanceAs (Decidable (a ∉ s))
/-
**Set.decidableEmptyset** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableEmptyset : Decidable (a in (∅ : Set α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEmptyset : Decidable (a ∈ (∅ : Set α)) := Decidable.isFalse (by simp)
/-
**Set.decidableUniv** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableUniv : Decidable (a in univ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableUniv : Decidable (a ∈ univ) := Decidable.isTrue (by simp)
/-
**Set.decidableInsert** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableInsert [Decidable (a = b)] [Decidable (a in s)] : Decidable (a in
 insert b s)
参数：a = b；a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableInsert [Decidable (a = b)] [Decidable (a ∈ s)] : Decidable (a ∈ insert b s) :=
  inferInstanceAs (Decidable (_ ∨ _))
/-
**Set.decidableSetOf** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableSetOf (p : α -> Prop) [Decidable (p a)] : Decidable (a in { a | p
 a })
参数：p : α -> Prop；p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableSetOf (p : α → Prop) [Decidable (p a)] : Decidable (a ∈ { a | p a }) := by
  assumption

/-- `Set α` almost never has decidable equality.
In fact, for an inhabited type `α`, `Set α` has decidable equality iff
all propositions are decidable. We add a global instance that `Set α` has decidable equality,
coming from the choice axiom, so that we don't have to provide `[DecidableEq (Set α)]` arguments
in lemma statements. -/
/-
**Set.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableEq : DecidableEq (Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set α` almost never has decidable equality.
In fact, for an inhabited type `α`, `Set α` has decidable equality iff
all propositions are decidable. We add a global instance that `Set α` has decida
ble equality,
coming from the choice axiom, so that we don't have to provide `[DecidableEq (Se
t α)]` arguments
in lemma statements.
-/
noncomputable instance decidableEq : DecidableEq (Set α) := Classical.typeDecidableEq (Set α)

end Set

variable {α : Type*} {s t u : Set α}

namespace Equiv

/-- Given a predicate `p : α → Prop`, produces an equivalence between
  `Set {a : α // p a}` and `{s : Set α // ∀ a ∈ s, p a}`. -/
/-
**Equiv.setSubtypeComm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → (p : α → Prop) → Set { a // p a } ≃ { s // ∀ a ∈ s, p a }
参数：p : α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `p : α → Prop`, produces an equivalence between
  `Set {a : α // p a}` and `{s : Set α // ∀ a ∈ s, p a}`.
-/
protected def setSubtypeComm (p : α → Prop) :
    Set {a : α // p a} ≃ {s : Set α // ∀ a ∈ s, p a} where
  toFun s := ⟨{a | ∃ h : p a, ⟨a, h⟩ ∈ s}, fun _ h ↦ h.1⟩
  invFun s := {a | a.val ∈ s.val}
  left_inv s := by ext a; exact ⟨fun h ↦ h.2, fun h ↦ ⟨a.property, h⟩⟩
  right_inv s := by ext; exact ⟨fun h ↦ h.2, fun h ↦ ⟨s.property _ h, h⟩⟩

@[simp]
/-
**Equiv.setSubtypeComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) (s : Set { a // p a }), (Equiv.setSubtypeC
omm p) s = ⟨{a | ∃ (h : p a), ⟨a, h⟩ ∈ s}, ⋯⟩
参数：p : α → Prop；s : Set { a // p a }；Equiv.setSubtypeComm p；h : p a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma setSubtypeComm_apply (p : α → Prop) (s : Set {a // p a}) :
    (Equiv.setSubtypeComm p) s = ⟨{a | ∃ h : p a, ⟨a, h⟩ ∈ s}, fun _ h ↦ h.1⟩ :=
  rfl

@[simp]
/-
**Equiv.setSubtypeComm_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) (s : { s // ∀ a ∈ s, p a }), (Equiv.setSub
typeComm p).symm s = {a | ↑a ∈ ↑s}
参数：p : α → Prop；s : { s // ∀ a ∈ s, p a }；Equiv.setSubtypeComm p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
protected lemma setSubtypeComm_symm_apply (p : α → Prop) (s : {s // ∀ a ∈ s, p a}) :
    (Equiv.setSubtypeComm p).symm s = {a | a.val ∈ s.val} :=
  rfl

end Equiv

