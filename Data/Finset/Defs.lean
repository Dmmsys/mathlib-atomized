/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Finite sets

Terms of type `Finset α` are one way of talking about finite subsets of `α` in Mathlib.
Below, `Finset α` is defined as a structure with 2 fields:

  1. `val` is a `Multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `List` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `Multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

  1. `∑ i ∈ (s : Finset α), f i`;
  2. `∏ i ∈ (s : Finset α), f i`.

Lean refers to these operations as big operators.
More information can be found in `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`.

Finsets are directly used to define fintypes in Lean.
A `Fintype α` instance for a type `α` consists of a universal `Finset α` containing every term of
`α`, called `univ`. See `Mathlib/Data/Fintype/Basic.lean`.

`Finset.card`, the size of a finset is defined in `Mathlib/Data/Finset/Card.lean`.
This is then used to define `Fintype.card`, the size of a type.

## File structure

This file defines the `Finset` type and the membership and subset relations between finsets.
Most constructions involving `Finset`s have been split off to their own files.

## Main definitions

* `Finset`: Defines a type for the finite subsets of `α`.
  Constructing a `Finset` requires two pieces of data: `val`, a `Multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `a ∈ (s : Finset α)` is defined through coercion to `Set α`.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset DirectedSystem CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

/-- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
@[use_set_notation_for_order, to_dual_dont_translate]
/-
**Finset** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements.
-/
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α
  /-- `val` contains no duplicates -/
  nodup : Nodup val
/-
**Multiset.canLiftFinset** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiset.canLiftFinset {α} : CanLift (Multiset α) (Finset α) Finset.val Mu
ltiset.Nodup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiset.canLiftFinset {α} : CanLift (Multiset α) (Finset α) Finset.val Multiset.Nodup :=
  ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩

namespace Finset

/-
**Finset.eq_of_veq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t
  | ⟨s, _⟩, ⟨t, _⟩, h => by cases h; rfl
/-
**Finset.val_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_injective : Injective (val : Finset α -> Multiset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
-/
theorem val_injective : Injective (val : Finset α → Multiset α) := fun _ _ => eq_of_veq

@[simp]
/-
**Finset.val_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
-/
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  val_injective.eq_iff
/-
**Finset.decidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → DecidableEq (Finset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
-/
instance decidableEq [DecidableEq α] : DecidableEq (Finset α)
  | _, _ => decidable_of_iff _ val_inj

/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a finset to a set in the natural way.
-/
instance : SetLike (Finset α) α where
  coe s := {a | a ∈ s.1}
  coe_injective s₁ s₂ h := (val_inj.symm.trans <| s₁.nodup.ext s₂.nodup).2 <| Set.ext_iff.mp h
/-
**Finset.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl

-- If https://github.com/leanprover/lean4/issues/2678 is resolved-
-- this can be changed back to an `Iff`, but for now we would like `dsimp` to use it.
@[simp, grind =]
/-
**Finset.mem_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_val {a : α} {s : Finset α} : (a in s.1) = (a in s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_val {a : α} {s : Finset α} : (a ∈ s.1) = (a ∈ s) := rfl

@[simp, grind =]
/-
**Finset.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_mk {a : α} {s nd} : a in @Finset.mk α s nd ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl
/-
**Finset.decidableMem** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a in
 s)
参数：a : α；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _
/-
**Finset.forall_mem_not_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α}, (∀ b ∈ s, ¬a = b) ↔ a ∉ s
参数：∀ b ∈ s, ¬a = b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forall_mem_not_eq {s : Finset α} {a : α} : (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by grind
/-
**Finset.forall_mem_not_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {a : α}, (∀ b ∈ s, ¬b = a) ↔ a ∉ s
参数：∀ b ∈ s, ¬b = a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forall_mem_not_eq' {s : Finset α} {a : α} : (∀ b ∈ s, ¬ b = a) ↔ a ∉ s := by grind
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Finset α) := .ofSetLike (Finset α) α

@[norm_cast, grind =]
/-
**Finset.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in (s : Finset α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ (s : Finset α) :=
  Iff.rfl

@[simp]
/-
**Finset.setOfPred_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：setOfPred_mem {α} {s : Finset α} : { a | a in s } = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setOfPred_mem {α} {s : Finset α} : { a | a ∈ s } = s :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem := setOfPred_mem
/-
**Finset.coe_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_mem {s : Finset α} (x : (s : Set α)) : ↑x in s
参数：x : (s : Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_mem {s : Finset α} (x : (s : Set α)) : ↑x ∈ s :=
  x.2
/-
**Finset.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x
参数：x : (s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
-/
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _
/-
**Finset.decidableMem'** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a in (s 
: Set α))
参数：a : α；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ (s : Set α)) :=
  s.decidableMem _

/-! ### extensionality -/

@[ext, grind ext]
/-
**Finset.ext** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s₁ = s₂
参数：h : forall a, a in s₁ ↔ a in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
### extensionality
-/
theorem ext {s₁ s₂ : Finset α} (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) : s₁ = s₂ :=
  SetLike.ext h

@[norm_cast]
/-
**Finset.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  SetLike.coe_set_eq

@[grind inj]
/-
**Finset.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_injective {α} : Injective ((↑) : Finset α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
-/
theorem coe_injective {α} : Injective ((↑) : Finset α → Set α) := fun _s _t => coe_inj.1

/-! ### type coercion -/


/-
**Finset.forall_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_4} (s : Finset α) (p : ↥s → Prop), (∀ (x : ↥s), p x) ↔ ∀ (x 
: α) (h : x ∈ s), p ⟨x, h⟩
参数：s : Finset α；p : ↥s → Prop；∀ (x : ↥s), p x；x : α；h : x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩

--- 原说明 ---
### type coercion
-/
protected theorem forall_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∀ x : s, p x) ↔ ∀ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
/-
**Finset.exists_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_4} (s : Finset α) (p : ↥s → Prop), (∃ x, p x) ↔ ∃ x, ∃ (h : 
x ∈ s), p ⟨x, h⟩
参数：s : Finset α；p : ↥s → Prop；∃ x, p x；h : x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
-/
protected theorem exists_coe {α : Type*} (s : Finset α) (p : s → Prop) :
    (∃ x : s, p x) ↔ ∃ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
/-
**Finset.PiFinsetCoe.canLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset.PiFinsetCoe`。
形式化陈述：∀ (ι : Type u_4) (α : ι → Type u_5) [_ne : ∀ (i : ι), Nonempty (α i)] (s :
 Finset ι),   CanLift ((i : ↥s) → α ↑i) ((i : ι) → α i) (fun f i => f ↑i) fun x 
=> True
参数：ι : Type u_4；α : ι → Type u_5；i : ι；α i；s : Finset ι；(i : ↥s) → α ↑i；(i : ι) 
→ α i；fun f i => f ↑i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance PiFinsetCoe.canLift (ι : Type*) (α : ι → Type*) [_ne : ∀ i, Nonempty (α i)]
    (s : Finset ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)
/-
**Finset.PiFinsetCoe.canLift'** 是 Mathlib 中的一个定理，位于命名空间 `Finset.PiFinsetCoe`。
形式化陈述：∀ (ι : Type u_4) (α : Type u_5) [_ne : Nonempty α] (s : Finset ι),   CanLi
ft (↥s → α) (ι → α) (fun f i => f ↑i) fun x => True
参数：ι : Type u_4；α : Type u_5；s : Finset ι；↥s → α；ι → α；fun f i => f ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.PiFinsetCoe.canLift`：∀ (ι : Type u_4) (α : ι → Type u_5) [_ne : ∀
 (i : ι), Nonempty (α i)] (s : Finset ι),   CanLift ((i : ↥s) → α ↑i) ((i : ι) →
 α i) (fun f i =…
-/
instance PiFinsetCoe.canLift' (ι α : Type*) [_ne : Nonempty α] (s : Finset ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiFinsetCoe.canLift ι (fun _ => α) s
/-
**Finset.FinsetCoe.canLift** 是 Mathlib 中的一个定理，位于命名空间 `Finset.FinsetCoe`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), CanLift α (↥s) Subtype.val fun a => a ∈ s
参数：s : Finset α；↥s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance FinsetCoe.canLift (s : Finset α) : CanLift α s (↑) fun a => a ∈ s where
  prf a ha := ⟨⟨a, ha⟩, rfl⟩

@[norm_cast]
/-
**Finset.coe_sort_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl

/-! ### Subset and strict subset relations -/


section Subset

variable {s t : Finset α}

@[deprecated "This is now a syntactic identity" (since := "2026-05-24")]
/-
**Finset.subset_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_of_le : s <= t -> s subseteq t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_of_le : s ≤ t → s ⊆ t := id
/-
**Finset.subset_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_def : s subseteq t ↔ s.1 subseteq t.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_def : s ⊆ t ↔ s.1 ⊆ t.1 :=
  Iff.rfl
/-
**Finset.ssubset_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_def : s ⊂ t ↔ s subseteq t ∧ ¬t subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬t ⊆ s :=
  Iff.rfl
/-
**Finset.Subset.refl** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Subset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α), s ⊆ s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Subset.refl`：∀ {α : Type u_1} (s : Multiset α), s ⊆ s
-/
theorem Subset.refl (s : Finset α) : s ⊆ s :=
  Multiset.Subset.refl _
/-
**Finset.Subset.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Subset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
protected theorem Subset.rfl {s : Finset α} : s ⊆ s :=
  Subset.refl _
/-
**Finset.subset_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, s = t → s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
protected theorem subset_of_eq {s t : Finset α} (h : s = t) : s ⊆ t :=
  h ▸ Subset.refl _
/-
**Finset.Subset.trans** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Subset`。
形式化陈述：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Subset.trans`：∀ {α : Type u_1} {s t u : Multiset α}, s ⊆ t → t 
⊆ u → s ⊆ u
-/
theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  Multiset.Subset.trans
/-
**Finset.Superset.trans** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Superset`。
形式化陈述：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
-/
theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ := fun h' h =>
  Subset.trans h h'
/-
**Finset.mem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ subseteq s₂ -> a in s₁ -> a 
in s₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_subset`：mem_of_subset {s t : Multiset α} {a : α} (h : s 
subseteq t) : a in s -> a in t
-/
theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  Multiset.mem_of_subset
/-
**Finset.notMem_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_mono {s t : Finset α} (h : s subseteq t) {a : α} : a ∉ t -> a ∉ s
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem notMem_mono {s t : Finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s :=
  mt <| @h _

alias not_mem_subset := notMem_mono
/-
**Finset.Subset.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Subset`。
形式化陈述：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
-/
theorem Subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun a => ⟨@H₁ a, @H₂ a⟩

@[grind =]
/-
**Finset.subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_iff {s₁ s₂ : Finset α} : s₁ subseteq s₂ ↔ forall ⦃x⦄, x in s₁ -> x 
in s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl
/-
**Finset.subset_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_iff_notMem : s subseteq t ↔ forall ⦃a⦄, a ∉ t -> a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subset_iff_notMem : s ⊆ t ↔ ∀ ⦃a⦄, a ∉ t → a ∉ s := by
  simp only [subset_iff, not_imp_not]

@[norm_cast, gcongr]
/-
**Finset.coe_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq s₂ ↔ s₁ subseteq s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊆ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl

@[simp]
/-
**Finset.val_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ subseteq s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ :=
  le_iff_subset s₁.2
/-
**Finset.Subset.antisymm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Subset`。
形式化陈述：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
-/
theorem Subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iff
/-
**Finset.not_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_subset : ¬s subseteq t ↔ exists x in s, x ∉ t
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_subset : ¬s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by simp only [← coe_subset, Set.not_subset, mem_coe]

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Finset.le_eq_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_eq_subset : ((· <= ·) : Finset α -> Finset α -> Prop) = (· subseteq ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_eq_subset : ((· ≤ ·) : Finset α → Finset α → Prop) = (· ⊆ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Finset.lt_eq_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lt_eq_subset : ((· < ·) : Finset α -> Finset α -> Prop) = (· ⊂ ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_eq_subset : ((· < ·) : Finset α → Finset α → Prop) = (· ⊂ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Finset.le_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_iff_subset {s₁ s₂ : Finset α} : s₁ <= s₂ ↔ s₁ subseteq s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/-
**Finset.lt_iff_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl

@[norm_cast]
/-
**Finset.coe_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ := by
  simp

@[simp]
/-
**Finset.val_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Finset.val_le_iff`：val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ sub
seteq s₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff <| not_congr val_le_iff
/-
**Finset.val_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：val_strictMono : StrictMono (val : Finset α -> Multiset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_lt_iff`：val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
-/
lemma val_strictMono : StrictMono (val : Finset α → Multiset α) := fun _ _ ↦ val_lt_iff.2

@[grind =]
/-
**Finset.ssubset_iff_subset_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s subseteq t ∧ s != t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
-/
theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne _ _ s t
/-
**Finset.ssubset_iff_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ subseteq s₂) : s₁ ⊂ s₂ ↔ 
exists x in s₂, x ∉ s₁
参数：h : s₁ subseteq s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ssubset_iff_of_subset`：ssubset_iff_of_subset {s t : Set α} (h : s su
bseteq t) : s ⊂ t ↔ exists x in t, x ∉ s
-/
theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
  Set.ssubset_iff_of_subset h
/-
**Finset.ssubset_of_ssubset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s
₃ : s₂ subseteq s₃) : s₁ ⊂ s₃
参数：hs₁s₂ : s₁ ⊂ s₂；hs₂s₃ : s₂ subseteq s₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ssubset_of_ssubset_of_subset`：∀ {α : Type u} {s₁ s₂ s₃ : Set α}, s₁ 
⊂ s₂ → s₂ ⊆ s₃ → s₁ ⊂ s₃
-/
theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃
/-
**Finset.ssubset_of_subset_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ subseteq s₂
) (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃
参数：hs₁s₂ : s₁ subseteq s₂；hs₂s₃ : s₂ ⊂ s₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ssubset_of_subset_of_ssubset`：∀ {α : Type u} {s₁ s₂ s₃ : Set α}, s₁ 
⊆ s₂ → s₂ ⊂ s₃ → s₁ ⊂ s₃
-/
theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃
/-
**Finset.exists_of_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : exists x in s₂, x ∉ s
₁
参数：h : s₁ ⊂ s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
-/
theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : ∃ x ∈ s₂, x ∉ s₁ :=
  Set.exists_of_ssubset h
/-
**Finset.isWellFounded_ssubset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：isWellFounded_ssubset : IsWellFounded (Finset α) (· ⊂ ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.isWellFounded`：Subrelation.isWellFounded (r : α -> α -> Prop
) [IsWellFounded α r] {s : α -> α -> Prop} (h : Subrelation s r) : IsWellFounded
 α s
· 使用定理 `instIsWellFoundedInvImage`：∀ {α : Type u} {β : Type v} (r : α → α → Prop
) [IsWellFounded α r] (f : β → α), IsWellFounded β (InvImage r f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.val_lt_iff`：val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
-/
instance isWellFounded_ssubset : IsWellFounded (Finset α) (· ⊂ ·) :=
  Subrelation.isWellFounded (InvImage _ _) val_lt_iff.2
/-
**Finset.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：wellFoundedLT : WellFoundedLT (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance wellFoundedLT : WellFoundedLT (Finset α) :=
  Finset.isWellFounded_ssubset

end Subset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Order embedding from `Finset α` to `Set α` -/


/-- Coercion to `Set α` as an `OrderEmbedding`. -/
/-
**Finset.coeEmb** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：coeEmb : Finset α ↪o Set α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂

--- 原说明 ---
Coercion to `Set α` as an `OrderEmbedding`.
-/
def coeEmb : Finset α ↪o Set α :=
  ⟨⟨(↑), coe_injective⟩, coe_subset⟩

@[simp]
/-
**Finset.coe_coeEmb** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_coeEmb : ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α -> Set α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeEmb : ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α → Set α) :=
  rfl

/-! ### Assorted results

These results can be defined using the current imports, but deserve to be given a nicer home.
-/

section DecidablePiExists

variable {s : Finset α}

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.decidableDforallFinset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableDforallFinset {p : forall a in s, Prop} [_hp : forall (a) (h : a 
in s), Decidable (p a h)] : Decidable (forall (a) (h : a in s), p a h)
参数：a；h : a in s；p a h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableDforallFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset
/-
**Finset.instDecidableRelSubset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instDecidableRelSubset [DecidableEq α] : DecidableRel (α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRelSubset [DecidableEq α] : DecidableRel (α := Finset α) (· ⊆ ·) :=
  fun _ _ ↦ decidableDforallFinset
/-
**Finset.instDecidableRelSSubset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instDecidableRelSSubset [DecidableEq α] : DecidableRel (α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRelSSubset [DecidableEq α] : DecidableRel (α := Finset α) (· ⊂ ·) :=
  fun _ _ ↦ instDecidableAnd
/-
**Finset.instDecidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instDecidableLE [DecidableEq α] : DecidableLE (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableLE [DecidableEq α] : DecidableLE (Finset α) :=
  instDecidableRelSubset
/-
**Finset.instDecidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instDecidableLT [DecidableEq α] : DecidableLT (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableLT [DecidableEq α] : DecidableLT (Finset α) :=
  instDecidableRelSSubset

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.decidableDExistsFinset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableDExistsFinset {p : forall a in s, Prop} [_hp : forall (a) (h : a 
in s), Decidable (p a h)] : Decidable (exists (a : _) (h : a in s), p a h)
参数：a；h : a in s；p a h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableDExistsFinset {p : ∀ a ∈ s, Prop} [_hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∃ (a : _) (h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset
/-
**Finset.decidableExistsAndFinset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableExistsAndFinset {p : α -> Prop} [_hp : forall (a), Decidable (p a
)] : Decidable (exists a in s, p a)
参数：a；p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableExistsAndFinset {p : α → Prop} [_hp : ∀ (a), Decidable (p a)] :
    Decidable (∃ a ∈ s, p a) :=
  decidable_of_iff (∃ (a : _) (_ : a ∈ s), p a) (by simp)
/-
**Finset.decidableExistsAndFinsetCoe** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableExistsAndFinsetCoe {p : α -> Prop} [DecidablePred p] : Decidable 
(exists a in (s : Set α), p a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableExistsAndFinsetCoe {p : α → Prop} [DecidablePred p] :
    Decidable (∃ a ∈ (s : Set α), p a) := decidableExistsAndFinset

/-- decidable equality for functions whose domain is bounded by finsets -/
/-
**Finset.decidableEqPiFinset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableEqPiFinset {β : α -> Type*} [_h : forall a, DecidableEq (β a)] : 
DecidableEq (forall a in s, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
decidable equality for functions whose domain is bounded by finsets
-/
instance decidableEqPiFinset {β : α → Type*} [_h : ∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ s, β a) :=
  Multiset.decidableEqPiMultiset

end DecidablePiExists

end Finset

namespace List

variable [DecidableEq α] {a : α} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}

/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidablePred (· ∈ t)] : Decidable (Set.MapsTo f s t) :=
  inferInstanceAs (Decidable (∀ x ∈ s, f x ∈ t))
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq β] : Decidable (Set.SurjOn f s t') :=
  inferInstanceAs (Decidable (∀ x ∈ t', ∃ y ∈ s, f y = x))

end List

namespace Finset

section Pairwise

variable {s : Finset α}

/-
**Finset.pairwise_subtype_iff_pairwise_finset'** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
形式化陈述：pairwise_subtype_iff_pairwise_finset' (r : β -> β -> Prop) (f : α -> β) : 
Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f)
参数：r : β -> β -> Prop；f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pairwise_subtype_iff_pairwise_set`：pairwise_subtype_iff_pairwise_set (s 
: Set α) (r : α -> α -> Prop) : (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pair
wise r
-/
theorem pairwise_subtype_iff_pairwise_finset' (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f) :=
  pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)
/-
**Finset.pairwise_subtype_iff_pairwise_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：pairwise_subtype_iff_pairwise_finset (r : α -> α -> Prop) : Pairwise (r on
 fun x : s => x) ↔ (s : Set α).Pairwise r
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pairwise_subtype_iff_pairwise_finset'`：pairwise_subtype_iff_pairw
ise_finset' (r : β -> β -> Prop) (f : α -> β) : Pairwise (r on fun x : s => f x)
 ↔ (s : Set α).Pairwise (r on f)
-/
theorem pairwise_subtype_iff_pairwise_finset (r : α → α → Prop) :
    Pairwise (r on fun x : s => x) ↔ (s : Set α).Pairwise r :=
  pairwise_subtype_iff_pairwise_finset' r id

end Pairwise

end Finset

