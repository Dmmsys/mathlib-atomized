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
/--
Definition of `Finset` / `Finset` 的定义

English:
structure Finset
  parameters: (α : Type*)
  axioms and operations (2):
    - val : Multiset α
    - nodup : Nodup val

中文:
结构 Finset
  参数: (α : 类型)
  公理与运算 (2 个):
    - val : Multiset α
    - nodup : Nodup val
-/
structure Finset (α : Type*) where
  /-- The underlying multiset -/
  val : Multiset α
  /-- `val` contains no duplicates -/
  nodup : Nodup val

/--
Instance `Multiset.canLiftFinset` / 实例 `Multiset.canLiftFinset`

English:
instance Multiset.canLiftFinset
  signature: {α}
  body: ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩

中文:
实例 Multiset.canLiftFinset
  签名: {α}
  定义体: ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩
-/
instance Multiset.canLiftFinset {α} : CanLift (Multiset α) (Finset α) Finset.val Multiset.Nodup :=
  ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩

namespace Finset

/--
theorem `eq_of_veq` / 定理 `eq_of_veq`

English:
theorem eq_of_veq
  statement: forall {s t : Finset α}, s.1 = t.1 -> s = t

中文:
定理 eq_of_veq
  结论: 对任意 {s t : Finset α}, s.1 = t.1 -> s = t
-/
theorem eq_of_veq : forall {s t : Finset α}, s.1 = t.1 -> s = t
  | ⟨s, _⟩, ⟨t, _⟩, h => by cases h; rfl

/--
theorem `val_injective` / 定理 `val_injective`

English:
theorem val_injective
  statement: Injective (val : Finset α -> Multiset α)
  proof: fun _ _ => eq_of_veq

@[simp]

中文:
定理 val_injective
  结论: Injective (val : Finset α -> Multiset α)
  证明: fun _ _ => eq_of_veq

@[simp]

Depends on / 依赖: eq_of_veq
-/
theorem val_injective : Injective (val : Finset α -> Multiset α) := fun _ _ => eq_of_veq

@[simp]
/--
theorem `val_inj` / 定理 `val_inj`

English:
theorem val_inj
  given: {s t : Finset α}
  statement: s.1 = t.1 ↔ s = t
  proof: val_injective.eq_iff

中文:
定理 val_inj
  条件: {s t : Finset α}
  结论: s.1 = t.1 ↔ s = t
  证明: val_injective.eq_iff

Depends on / 依赖: eq_iff, val_injective, val_injective.eq_iff
-/
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  val_injective.eq_iff

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: [DecidableEq α]

中文:
实例 decidableEq
  签名: [DecidableEq α]
-/
instance decidableEq [DecidableEq α] : DecidableEq (Finset α)
  | _, _ => decidable_of_iff _ val_inj

/-! ### set coercion -/

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Finset α) α
  body: {a | a in s.1}
coe_injective s₁ s₂ h := (val_inj.symm.trans <| s₁.nodup.ext s₂.nodup).2 Set.ext_iff.mp h

中文:
实例 :
  签名: SetLike (Finset α) α
  定义体: {a | a in s.1}
coe_injective s₁ s₂ h := (val_inj.symm.trans <| s₁.nodup.ext s₂.nodup).2 Set.ext_iff.mp h
-/
instance : SetLike (Finset α) α where
  coe s := {a | a in s.1}
coe_injective s₁ s₂ h := (val_inj.symm.trans <| s₁.nodup.ext s₂.nodup).2 Set.ext_iff.mp h

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  given: {a : α} {s : Finset α}
  statement: a in s ↔ a in s.1
  proof: Iff.rfl

中文:
定理 mem_def
  条件: {a : α} {s : Finset α}
  结论: a in s ↔ a in s.1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1 :=
  Iff.rfl

-- If https://github.com/leanprover/lean4/issues/2678 is resolved-
-- this can be changed back to an `Iff`, but for now we would like `dsimp` to use it.
@[simp, grind =]
/--
theorem `mem_val` / 定理 `mem_val`

English:
theorem mem_val
  given: {a : α} {s : Finset α}
  statement: (a in s.1) = (a in s)
  proof: rfl

@[simp, grind =]

中文:
定理 mem_val
  条件: {a : α} {s : Finset α}
  结论: (a in s.1) = (a in s)
  证明: rfl

@[simp, grind =]
-/
theorem mem_val {a : α} {s : Finset α} : (a in s.1) = (a in s) := rfl

@[simp, grind =]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {a : α} {s nd}
  statement: a in @Finset.mk α s nd ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: {a : α} {s nd}
  结论: a in @Finset.mk α s nd ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {a : α} {s nd} : a in @Finset.mk α s nd ↔ a in s :=
  Iff.rfl

/--
Instance `decidableMem` / 实例 `decidableMem`

English:
instance decidableMem
  signature: [_h : DecidableEq α] (a : α) (s : Finset α)
  body: Multiset.decidableMem _ _

中文:
实例 decidableMem
  签名: [_h : DecidableEq α] (a : α) (s : Finset α)
  定义体: Multiset.decidableMem _ _

Depends on / 依赖: Multiset, Multiset.decidableMem, decidableMem
-/
instance decidableMem [_h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a in s) :=
  Multiset.decidableMem _ _

/--
lemma `forall_mem_not_eq` / 引理 `forall_mem_not_eq`

English:
lemma forall_mem_not_eq
  given: {s : Finset α} {a : α}
  statement: (forall b in s, ¬ a = b) ↔ a ∉ s
  proof: by grind

中文:
引理 forall_mem_not_eq
  条件: {s : Finset α} {a : α}
  结论: (对任意 b in s, ¬ a = b) ↔ a ∉ s
  证明: by grind
-/
@[simp] lemma forall_mem_not_eq {s : Finset α} {a : α} : (forall b in s, ¬ a = b) ↔ a ∉ s := by grind
/--
lemma `forall_mem_not_eq'` / 引理 `forall_mem_not_eq'`

English:
lemma forall_mem_not_eq'
  given: {s : Finset α} {a : α}
  statement: (forall b in s, ¬ b = a) ↔ a ∉ s
  proof: by grind

中文:
引理 forall_mem_not_eq'
  条件: {s : Finset α} {a : α}
  结论: (对任意 b in s, ¬ b = a) ↔ a ∉ s
  证明: by grind
-/
@[simp] lemma forall_mem_not_eq' {s : Finset α} {a : α} : (forall b in s, ¬ b = a) ↔ a ∉ s := by grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Finset α)
  body: .ofSetLike (Finset α) α

@[norm_cast, grind =]

中文:
实例 :
  签名: PartialOrder (Finset α)
  定义体: .ofSetLike (Finset α) α

@[norm_cast, grind =]

Depends on / 依赖: Finset, ofSetLike
-/
instance : PartialOrder (Finset α) := .ofSetLike (Finset α) α

@[norm_cast, grind =]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {a : α} {s : Finset α}
  statement: a in (s : Set α) ↔ a in (s : Finset α)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_coe
  条件: {a : α} {s : Finset α}
  结论: a in (s : Set α) ↔ a in (s : Finset α)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in (s : Finset α) :=
  Iff.rfl

@[simp]
/--
theorem `setOfPred_mem` / 定理 `setOfPred_mem`

English:
theorem setOfPred_mem
  given: {α} {s : Finset α}
  statement: { a | a in s } = s
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem := setOfPred_mem

中文:
定理 setOfPred_mem
  条件: {α} {s : Finset α}
  结论: { a | a in s } = s
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem := setOfPred_mem
-/
theorem setOfPred_mem {α} {s : Finset α} : { a | a in s } = s :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem := setOfPred_mem

/--
theorem `coe_mem` / 定理 `coe_mem`

English:
theorem coe_mem
  given: {s : Finset α} (x : (s : Set α))
  statement: ↑x in s
  proof: x.2

中文:
定理 coe_mem
  条件: {s : Finset α} (x : (s : Set α))
  结论: ↑x in s
  证明: x.2
-/
theorem coe_mem {s : Finset α} (x : (s : Set α)) : ↑x in s :=
  x.2

/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {s : Finset α} (x : (s : Set α)) {h}
  statement: (⟨x, h⟩ : (s : Set α)) = x
  proof: Subtype.coe_eta _ _

中文:
定理 mk_coe
  条件: {s : Finset α} (x : (s : Set α)) {h}
  结论: (⟨x, h⟩ : (s : Set α)) = x
  证明: Subtype.coe_eta _ _

Depends on / 依赖: Subtype, Subtype.coe_eta, coe_eta
-/
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _

/--
Instance `decidableMem'` / 实例 `decidableMem'`

English:
instance decidableMem'
  signature: [DecidableEq α] (a : α) (s : Finset α)
  body: s.decidableMem _

中文:
实例 decidableMem'
  签名: [DecidableEq α] (a : α) (s : Finset α)
  定义体: s.decidableMem _

Depends on / 依赖: decidableMem, s.decidableMem
-/
instance decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a in (s : Set α)) :=
  s.decidableMem _

/-! ### extensionality -/

@[ext, grind ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂)
  statement: s₁ = s₂
  proof: SetLike.ext h

@[norm_cast]

中文:
定理 ext
  条件: {s₁ s₂ : Finset α} (h : 对任意 a, a in s₁ ↔ a in s₂)
  结论: s₁ = s₂
  证明: SetLike.ext h

@[norm_cast]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s₁ = s₂ :=
  SetLike.ext h

@[norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {s₁ s₂ : Finset α}
  statement: (s₁ : Set α) = s₂ ↔ s₁ = s₂
  proof: SetLike.coe_set_eq

@[grind inj]

中文:
定理 coe_inj
  条件: {s₁ s₂ : Finset α}
  结论: (s₁ : Set α) = s₂ ↔ s₁ = s₂
  证明: SetLike.coe_set_eq

@[grind inj]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  SetLike.coe_set_eq

@[grind inj]
/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  given: {α}
  statement: Injective ((↑) : Finset α -> Set α)
  proof: fun _s _t => coe_inj.1

中文:
定理 coe_injective
  条件: {α}
  结论: Injective ((↑) : Finset α -> Set α)
  证明: fun _s _t => coe_inj.1

Depends on / 依赖: coe_inj
-/
theorem coe_injective {α} : Injective ((↑) : Finset α -> Set α) := fun _s _t => coe_inj.1



/--
theorem `forall_coe` / 定理 `forall_coe`

English:
theorem forall_coe
  given: {α : Type*} (s : Finset α) (p : s -> Prop)
  proof: Subtype.forall

中文:
定理 forall_coe
  条件: {α : 类型} (s : Finset α) (p : s -> 命题)
  证明: Subtype.forall
-/
protected theorem forall_coe {α : Type*} (s : Finset α) (p : s -> Prop) :
    (forall x : s, p x) ↔ forall (x : α) (h : x in s), p ⟨x, h⟩ :=
  Subtype.forall

/--
theorem `exists_coe` / 定理 `exists_coe`

English:
theorem exists_coe
  given: {α : Type*} (s : Finset α) (p : s -> Prop)
  proof: Subtype.exists

中文:
定理 exists_coe
  条件: {α : 类型} (s : Finset α) (p : s -> 命题)
  证明: Subtype.exists
-/
protected theorem exists_coe {α : Type*} (s : Finset α) (p : s -> Prop) :
    (exists x : s, p x) ↔ exists (x : α) (h : x in s), p ⟨x, h⟩ :=
  Subtype.exists

/--
Instance `PiFinsetCoe.canLift` / 实例 `PiFinsetCoe.canLift`

English:
instance PiFinsetCoe.canLift
  signature: (ι : Type*) (α : ι -> Type*) [_ne : forall i, Nonempty (α i)]
  body: PiSubtype.canLift ι α (· in s)

中文:
实例 PiFinsetCoe.canLift
  签名: (ι : 类型) (α : ι -> 类型) [_ne : 对任意 i, Nonempty (α i)]
  定义体: PiSubtype.canLift ι α (· in s)

Depends on / 依赖: PiSubtype, PiSubtype.canLift, canLift
-/
instance PiFinsetCoe.canLift (ι : Type*) (α : ι -> Type*) [_ne : forall i, Nonempty (α i)]
    (s : Finset ι) : CanLift (forall i : s, α i) (forall i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· in s)

/--
Instance `PiFinsetCoe.canLift'` / 实例 `PiFinsetCoe.canLift'`

English:
instance PiFinsetCoe.canLift'
  signature: (ι α : Type*) [_ne : Nonempty α] (s : Finset ι)
  body: PiFinsetCoe.canLift ι (fun _ => α) s

中文:
实例 PiFinsetCoe.canLift'
  签名: (ι α : 类型) [_ne : Nonempty α] (s : Finset ι)
  定义体: PiFinsetCoe.canLift ι (fun _ => α) s

Depends on / 依赖: PiFinsetCoe, PiFinsetCoe.canLift, canLift
-/
instance PiFinsetCoe.canLift' (ι α : Type*) [_ne : Nonempty α] (s : Finset ι) :
    CanLift (s -> α) (ι -> α) (fun f i => f i) fun _ => True :=
  PiFinsetCoe.canLift ι (fun _ => α) s

/--
Instance `FinsetCoe.canLift` / 实例 `FinsetCoe.canLift`

English:
instance FinsetCoe.canLift
  signature: (s : Finset α)
  body: ⟨⟨a, ha⟩, rfl⟩

@[norm_cast]

中文:
实例 FinsetCoe.canLift
  签名: (s : Finset α)
  定义体: ⟨⟨a, ha⟩, rfl⟩

@[norm_cast]
-/
instance FinsetCoe.canLift (s : Finset α) : CanLift α s (↑) fun a => a in s where
  prf a ha := ⟨⟨a, ha⟩, rfl⟩

@[norm_cast]
/--
theorem `coe_sort_coe` / 定理 `coe_sort_coe`

English:
theorem coe_sort_coe
  given: (s : Finset α)
  statement: ((s : Set α) : Sort _) = s
  proof: rfl

中文:
定理 coe_sort_coe
  条件: (s : Finset α)
  结论: ((s : Set α) : Sort _) = s
  证明: rfl
-/
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl

/-! ### Subset and strict subset relations -/


section Subset

variable {s t : Finset α}

@[deprecated "This is now a syntactic identity" (since := "2026-05-24")]
/--
theorem `subset_of_le` / 定理 `subset_of_le`

English:
theorem subset_of_le
  statement: s <= t -> s subseteq t
  proof: id

中文:
定理 subset_of_le
  结论: s <= t -> s subseteq t
  证明: id
-/
theorem subset_of_le : s <= t -> s subseteq t := id

/--
theorem `subset_def` / 定理 `subset_def`

English:
theorem subset_def
  statement: s subseteq t ↔ s.1 subseteq t.1
  proof: Iff.rfl

中文:
定理 subset_def
  结论: s subseteq t ↔ s.1 subseteq t.1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subset_def : s subseteq t ↔ s.1 subseteq t.1 :=
  Iff.rfl

/--
theorem `ssubset_def` / 定理 `ssubset_def`

English:
theorem ssubset_def
  statement: s ⊂ t ↔ s subseteq t ∧ ¬t subseteq s
  proof: Iff.rfl

中文:
定理 ssubset_def
  结论: s ⊂ t ↔ s subseteq t ∧ ¬t subseteq s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ssubset_def : s ⊂ t ↔ s subseteq t ∧ ¬t subseteq s :=
  Iff.rfl

/--
theorem `Subset.refl` / 定理 `Subset.refl`

English:
theorem Subset.refl
  given: (s : Finset α)
  statement: s subseteq s
  proof: Multiset.Subset.refl _

中文:
定理 Subset.refl
  条件: (s : Finset α)
  结论: s subseteq s
  证明: Multiset.Subset.refl _

Depends on / 依赖: Multiset, Multiset.Subset.refl, Subset
-/
theorem Subset.refl (s : Finset α) : s subseteq s :=
  Multiset.Subset.refl _

/--
theorem `Subset.rfl` / 定理 `Subset.rfl`

English:
theorem Subset.rfl
  given: {s : Finset α}
  statement: s subseteq s
  proof: Subset.refl _

中文:
定理 Subset.rfl
  条件: {s : Finset α}
  结论: s subseteq s
  证明: Subset.refl _
-/
protected theorem Subset.rfl {s : Finset α} : s subseteq s :=
  Subset.refl _

/--
theorem `subset_of_eq` / 定理 `subset_of_eq`

English:
theorem subset_of_eq
  given: {s t : Finset α} (h : s = t)
  statement: s subseteq t
  proof: h ▸ Subset.refl _

中文:
定理 subset_of_eq
  条件: {s t : Finset α} (h : s = t)
  结论: s subseteq t
  证明: h ▸ Subset.refl _
-/
protected theorem subset_of_eq {s t : Finset α} (h : s = t) : s subseteq t :=
  h ▸ Subset.refl _

/--
theorem `Subset.trans` / 定理 `Subset.trans`

English:
theorem Subset.trans
  given: {s₁ s₂ s₃ : Finset α}
  statement: s₁ subseteq s₂ -> s₂ subseteq s₃ -> s₁ subseteq s₃
  proof: Multiset.Subset.trans

中文:
定理 Subset.trans
  条件: {s₁ s₂ s₃ : Finset α}
  结论: s₁ subseteq s₂ -> s₂ subseteq s₃ -> s₁ subseteq s₃
  证明: Multiset.Subset.trans

Depends on / 依赖: Multiset, Multiset.Subset.trans, Subset
-/
theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ subseteq s₂ -> s₂ subseteq s₃ -> s₁ subseteq s₃ :=
  Multiset.Subset.trans

/--
theorem `Superset.trans` / 定理 `Superset.trans`

English:
theorem Superset.trans
  given: {s₁ s₂ s₃ : Finset α}
  statement: s₁ ⊇ s₂ -> s₂ ⊇ s₃ -> s₁ ⊇ s₃
  proof: fun h' h =>
  Subset.trans h h'

中文:
定理 Superset.trans
  条件: {s₁ s₂ s₃ : Finset α}
  结论: s₁ ⊇ s₂ -> s₂ ⊇ s₃ -> s₁ ⊇ s₃
  证明: fun h' h =>
  Subset.trans h h'
-/
theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ -> s₂ ⊇ s₃ -> s₁ ⊇ s₃ := fun h' h =>
  Subset.trans h h'

/--
theorem `mem_of_subset` / 定理 `mem_of_subset`

English:
theorem mem_of_subset
  given: {s₁ s₂ : Finset α} {a : α}
  statement: s₁ subseteq s₂ -> a in s₁ -> a in s₂
  proof: Multiset.mem_of_subset

中文:
定理 mem_of_subset
  条件: {s₁ s₂ : Finset α} {a : α}
  结论: s₁ subseteq s₂ -> a in s₁ -> a in s₂
  证明: Multiset.mem_of_subset

Depends on / 依赖: Multiset, Multiset.mem_of_subset, mem_of_subset
-/
theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ subseteq s₂ -> a in s₁ -> a in s₂ :=
  Multiset.mem_of_subset

/--
theorem `notMem_mono` / 定理 `notMem_mono`

English:
theorem notMem_mono
  given: {s t : Finset α} (h : s subseteq t) {a : α}
  statement: a ∉ t -> a ∉ s
  proof: mt @h _

alias not_mem_subset := notMem_mono

中文:
定理 notMem_mono
  条件: {s t : Finset α} (h : s subseteq t) {a : α}
  结论: a ∉ t -> a ∉ s
  证明: mt @h _

alias not_mem_subset := notMem_mono
-/
theorem notMem_mono {s t : Finset α} (h : s subseteq t) {a : α} : a ∉ t -> a ∉ s :=
mt @h _

alias not_mem_subset := notMem_mono

/--
theorem `Subset.antisymm` / 定理 `Subset.antisymm`

English:
theorem Subset.antisymm
  given: {s₁ s₂ : Finset α} (H₁ : s₁ subseteq s₂) (H₂ : s₂ subseteq s₁)
  statement: s₁ = s₂
  proof: ext fun a => ⟨@H₁ a, @H₂ a⟩

@[grind =]

中文:
定理 Subset.antisymm
  条件: {s₁ s₂ : Finset α} (H₁ : s₁ subseteq s₂) (H₂ : s₂ subseteq s₁)
  结论: s₁ = s₂
  证明: ext fun a => ⟨@H₁ a, @H₂ a⟩

@[grind =]
-/
theorem Subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ subseteq s₂) (H₂ : s₂ subseteq s₁) : s₁ = s₂ :=
  ext fun a => ⟨@H₁ a, @H₂ a⟩

@[grind =]
/--
theorem `subset_iff` / 定理 `subset_iff`

English:
theorem subset_iff
  given: {s₁ s₂ : Finset α}
  statement: s₁ subseteq s₂ ↔ forall ⦃x⦄, x in s₁ -> x in s₂
  proof: Iff.rfl

中文:
定理 subset_iff
  条件: {s₁ s₂ : Finset α}
  结论: s₁ subseteq s₂ ↔ 对任意 ⦃x⦄, x in s₁ -> x in s₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subset_iff {s₁ s₂ : Finset α} : s₁ subseteq s₂ ↔ forall ⦃x⦄, x in s₁ -> x in s₂ :=
  Iff.rfl

/--
theorem `subset_iff_notMem` / 定理 `subset_iff_notMem`

English:
theorem subset_iff_notMem
  statement: s subseteq t ↔ forall ⦃a⦄, a ∉ t -> a ∉ s
  proof: by
  simp only [subset_iff, not_imp_not]

@[norm_cast, gcongr]

中文:
定理 subset_iff_notMem
  结论: s subseteq t ↔ 对任意 ⦃a⦄, a ∉ t -> a ∉ s
  证明: by
  simp only [subset_iff, not_imp_not]

@[norm_cast, gcongr]

Depends on / 依赖: not_imp_not, subset_iff
-/
theorem subset_iff_notMem : s subseteq t ↔ forall ⦃a⦄, a ∉ t -> a ∉ s := by
  simp only [subset_iff, not_imp_not]

@[norm_cast, gcongr]
/--
theorem `coe_subset` / 定理 `coe_subset`

English:
theorem coe_subset
  given: {s₁ s₂ : Finset α}
  statement: (s₁ : Set α) subseteq s₂ ↔ s₁ subseteq s₂
  proof: Iff.rfl

@[simp]

中文:
定理 coe_subset
  条件: {s₁ s₂ : Finset α}
  结论: (s₁ : Set α) subseteq s₂ ↔ s₁ subseteq s₂
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq s₂ ↔ s₁ subseteq s₂ :=
  Iff.rfl

@[simp]
/--
theorem `val_le_iff` / 定理 `val_le_iff`

English:
theorem val_le_iff
  given: {s₁ s₂ : Finset α}
  statement: s₁.1 <= s₂.1 ↔ s₁ subseteq s₂
  proof: le_iff_subset s₁.2

中文:
定理 val_le_iff
  条件: {s₁ s₂ : Finset α}
  结论: s₁.1 <= s₂.1 ↔ s₁ subseteq s₂
  证明: le_iff_subset s₁.2

Depends on / 依赖: le_iff_subset
-/
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 <= s₂.1 ↔ s₁ subseteq s₂ :=
  le_iff_subset s₁.2

/--
theorem `Subset.antisymm_iff` / 定理 `Subset.antisymm_iff`

English:
theorem Subset.antisymm_iff
  given: {s₁ s₂ : Finset α}
  statement: s₁ = s₂ ↔ s₁ subseteq s₂ ∧ s₂ subseteq s₁
  proof: le_antisymm_iff

中文:
定理 Subset.antisymm_iff
  条件: {s₁ s₂ : Finset α}
  结论: s₁ = s₂ ↔ s₁ subseteq s₂ ∧ s₂ subseteq s₁
  证明: le_antisymm_iff

Depends on / 依赖: le_antisymm_iff
-/
theorem Subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ subseteq s₂ ∧ s₂ subseteq s₁ :=
  le_antisymm_iff

/--
theorem `not_subset` / 定理 `not_subset`

English:
theorem not_subset
  statement: ¬s subseteq t ↔ exists x in s, x ∉ t
  proof: by simp only [← coe_subset, Set.not_subset, mem_coe]

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 not_subset
  结论: ¬s subseteq t ↔ 存在 x in s, x ∉ t
  证明: by simp only [← coe_subset, Set.not_subset, mem_coe]

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

Depends on / 依赖: Set.not_subset, coe_subset, mem_coe, not_subset
-/
theorem not_subset : ¬s subseteq t ↔ exists x in s, x ∉ t := by simp only [← coe_subset, Set.not_subset, mem_coe]

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `le_eq_subset` / 定理 `le_eq_subset`

English:
theorem le_eq_subset
  statement: ((· <= ·) : Finset α -> Finset α -> Prop) = (· subseteq ·)
  proof: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 le_eq_subset
  结论: ((· <= ·) : Finset α -> Finset α -> 命题) = (· subseteq ·)
  证明: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
-/
theorem le_eq_subset : ((· <= ·) : Finset α -> Finset α -> Prop) = (· subseteq ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `lt_eq_subset` / 定理 `lt_eq_subset`

English:
theorem lt_eq_subset
  statement: ((· < ·) : Finset α -> Finset α -> Prop) = (· ⊂ ·)
  proof: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 lt_eq_subset
  结论: ((· < ·) : Finset α -> Finset α -> 命题) = (· ⊂ ·)
  证明: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
-/
theorem lt_eq_subset : ((· < ·) : Finset α -> Finset α -> Prop) = (· ⊂ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `le_iff_subset` / 定理 `le_iff_subset`

English:
theorem le_iff_subset
  given: {s₁ s₂ : Finset α}
  statement: s₁ <= s₂ ↔ s₁ subseteq s₂
  proof: Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 le_iff_subset
  条件: {s₁ s₂ : Finset α}
  结论: s₁ <= s₂ ↔ s₁ subseteq s₂
  证明: Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

Depends on / 依赖: Iff.rfl
-/
theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ <= s₂ ↔ s₁ subseteq s₂ :=
  Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `lt_iff_ssubset` / 定理 `lt_iff_ssubset`

English:
theorem lt_iff_ssubset
  given: {s₁ s₂ : Finset α}
  statement: s₁ < s₂ ↔ s₁ ⊂ s₂
  proof: Iff.rfl

@[norm_cast]

中文:
定理 lt_iff_ssubset
  条件: {s₁ s₂ : Finset α}
  结论: s₁ < s₂ ↔ s₁ ⊂ s₂
  证明: Iff.rfl

@[norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl

@[norm_cast]
/--
theorem `coe_ssubset` / 定理 `coe_ssubset`

English:
theorem coe_ssubset
  given: {s₁ s₂ : Finset α}
  statement: (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂
  proof: by
  simp

@[simp]

中文:
定理 coe_ssubset
  条件: {s₁ s₂ : Finset α}
  结论: (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂
  证明: by
  simp

@[simp]
-/
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ := by
  simp

@[simp]
/--
theorem `val_lt_iff` / 定理 `val_lt_iff`

English:
theorem val_lt_iff
  given: {s₁ s₂ : Finset α}
  statement: s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
  proof: and_congr val_le_iff not_congr val_le_iff

中文:
定理 val_lt_iff
  条件: {s₁ s₂ : Finset α}
  结论: s₁.1 < s₂.1 ↔ s₁ ⊂ s₂
  证明: and_congr val_le_iff not_congr val_le_iff

Depends on / 依赖: and_congr, not_congr, val_le_iff
-/
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
and_congr val_le_iff not_congr val_le_iff

/--
lemma `val_strictMono` / 引理 `val_strictMono`

English:
lemma val_strictMono
  statement: StrictMono (val : Finset α -> Multiset α)
  proof: fun _ _ => val_lt_iff.2

@[grind =]

中文:
引理 val_strictMono
  结论: StrictMono (val : Finset α -> Multiset α)
  证明: fun _ _ => val_lt_iff.2

@[grind =]

Depends on / 依赖: val_lt_iff
-/
lemma val_strictMono : StrictMono (val : Finset α -> Multiset α) := fun _ _ => val_lt_iff.2

@[grind =]
/--
theorem `ssubset_iff_subset_ne` / 定理 `ssubset_iff_subset_ne`

English:
theorem ssubset_iff_subset_ne
  given: {s t : Finset α}
  statement: s ⊂ t ↔ s subseteq t ∧ s != t
  proof: @lt_iff_le_and_ne _ _ s t

中文:
定理 ssubset_iff_subset_ne
  条件: {s t : Finset α}
  结论: s ⊂ t ↔ s subseteq t ∧ s != t
  证明: @lt_iff_le_and_ne _ _ s t

Depends on / 依赖: lt_iff_le_and_ne
-/
theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s subseteq t ∧ s != t :=
  @lt_iff_le_and_ne _ _ s t

/--
theorem `ssubset_iff_of_subset` / 定理 `ssubset_iff_of_subset`

English:
theorem ssubset_iff_of_subset
  given: {s₁ s₂ : Finset α} (h : s₁ subseteq s₂)
  statement: s₁ ⊂ s₂ ↔ exists x in s₂, x ∉ s₁
  proof: Set.ssubset_iff_of_subset h

中文:
定理 ssubset_iff_of_subset
  条件: {s₁ s₂ : Finset α} (h : s₁ subseteq s₂)
  结论: s₁ ⊂ s₂ ↔ 存在 x in s₂, x ∉ s₁
  证明: Set.ssubset_iff_of_subset h

Depends on / 依赖: Set.ssubset_iff_of_subset, ssubset_iff_of_subset
-/
theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ subseteq s₂) : s₁ ⊂ s₂ ↔ exists x in s₂, x ∉ s₁ :=
  Set.ssubset_iff_of_subset h

/--
theorem `ssubset_of_ssubset_of_subset` / 定理 `ssubset_of_ssubset_of_subset`

English:
theorem ssubset_of_ssubset_of_subset
  given: {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ subseteq s₃)
  proof: Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

中文:
定理 ssubset_of_ssubset_of_subset
  条件: {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ subseteq s₃)
  证明: Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

Depends on / 依赖: Set.ssubset_of_ssubset_of_subset, ssubset_of_ssubset_of_subset
-/
theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ subseteq s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

/--
theorem `ssubset_of_subset_of_ssubset` / 定理 `ssubset_of_subset_of_ssubset`

English:
theorem ssubset_of_subset_of_ssubset
  given: {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ subseteq s₂) (hs₂s₃ : s₂ ⊂ s₃)
  proof: Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

中文:
定理 ssubset_of_subset_of_ssubset
  条件: {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ subseteq s₂) (hs₂s₃ : s₂ ⊂ s₃)
  证明: Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

Depends on / 依赖: Set.ssubset_of_subset_of_ssubset, ssubset_of_subset_of_ssubset
-/
theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ subseteq s₂) (hs₂s₃ : s₂ ⊂ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

/--
theorem `exists_of_ssubset` / 定理 `exists_of_ssubset`

English:
theorem exists_of_ssubset
  given: {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂)
  statement: exists x in s₂, x ∉ s₁
  proof: Set.exists_of_ssubset h

中文:
定理 exists_of_ssubset
  条件: {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂)
  结论: 存在 x in s₂, x ∉ s₁
  证明: Set.exists_of_ssubset h

Depends on / 依赖: Set.exists_of_ssubset, exists_of_ssubset
-/
theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : exists x in s₂, x ∉ s₁ :=
  Set.exists_of_ssubset h

/--
Instance `isWellFounded_ssubset` / 实例 `isWellFounded_ssubset`

English:
instance isWellFounded_ssubset
  signature: : IsWellFounded (Finset α) (· ⊂ ·)
  body: Subrelation.isWellFounded (InvImage _ _) val_lt_iff.2

中文:
实例 isWellFounded_ssubset
  签名: : IsWellFounded (Finset α) (· ⊂ ·)
  定义体: Subrelation.isWellFounded (InvImage _ _) val_lt_iff.2

Depends on / 依赖: InvImage, Subrelation, Subrelation.isWellFounded, isWellFounded, val_lt_iff
-/
instance isWellFounded_ssubset : IsWellFounded (Finset α) (· ⊂ ·) :=
  Subrelation.isWellFounded (InvImage _ _) val_lt_iff.2

/--
Instance `wellFoundedLT` / 实例 `wellFoundedLT`

English:
instance wellFoundedLT
  signature: : WellFoundedLT (Finset α)
  body: Finset.isWellFounded_ssubset

中文:
实例 wellFoundedLT
  签名: : WellFoundedLT (Finset α)
  定义体: Finset.isWellFounded_ssubset

Depends on / 依赖: Finset, Finset.isWellFounded_ssubset, isWellFounded_ssubset
-/
instance wellFoundedLT : WellFoundedLT (Finset α) :=
  Finset.isWellFounded_ssubset

end Subset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Order embedding from `Finset α` to `Set α` -/


/--
Definition of `coeEmb` / `coeEmb` 的定义

English:
definition coeEmb
  signature: : Finset α ↪o Set α
  body: ⟨⟨(↑), coe_injective⟩, coe_subset⟩

@[simp]

中文:
定义 coeEmb
  签名: : Finset α ↪o Set α
  定义体: ⟨⟨(↑), coe_injective⟩, coe_subset⟩

@[simp]

Depends on / 依赖: coe_injective, coe_subset
-/
def coeEmb : Finset α ↪o Set α :=
  ⟨⟨(↑), coe_injective⟩, coe_subset⟩

@[simp]
/--
theorem `coe_coeEmb` / 定理 `coe_coeEmb`

English:
theorem coe_coeEmb
  statement: ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α -> Set α)
  proof: rfl

中文:
定理 coe_coeEmb
  结论: ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α -> Set α)
  证明: rfl
-/
theorem coe_coeEmb : ⇑(coeEmb : Finset α ↪o Set α) = ((↑) : Finset α -> Set α) :=
  rfl

/-! ### Assorted results

These results can be defined using the current imports, but deserve to be given a nicer home.
-/

section DecidablePiExists

variable {s : Finset α}

set_option backward.isDefEq.respectTransparency false in
/--
Instance `decidableDforallFinset` / 实例 `decidableDforallFinset`

English:
instance decidableDforallFinset
  signature: {p : forall a in s, Prop} [_hp : forall (a) (h : a in s), Decidable (p a h)]
  body: Multiset.decidableDforallMultiset

中文:
实例 decidableDforallFinset
  签名: {p : 对任意 a in s, 命题} [_hp : 对任意 (a) (h : a in s), Decidable (p a h)]
  定义体: Multiset.decidableDforallMultiset

Depends on / 依赖: Multiset, Multiset.decidableDforallMultiset, decidableDforallMultiset
-/
instance decidableDforallFinset {p : forall a in s, Prop} [_hp : forall (a) (h : a in s), Decidable (p a h)] :
    Decidable (forall (a) (h : a in s), p a h) :=
  Multiset.decidableDforallMultiset

/--
Instance `instDecidableRelSubset` / 实例 `instDecidableRelSubset`

English:
instance instDecidableRelSubset
  signature: [DecidableEq α]
  body: fun _ _ => decidableDforallFinset

中文:
实例 instDecidableRelSubset
  签名: [DecidableEq α]
  定义体: fun _ _ => decidableDforallFinset

Depends on / 依赖: Finset, subseteq
-/
instance instDecidableRelSubset [DecidableEq α] : DecidableRel (α := Finset α) (· subseteq ·) :=
  fun _ _ => decidableDforallFinset

/--
Instance `instDecidableRelSSubset` / 实例 `instDecidableRelSSubset`

English:
instance instDecidableRelSSubset
  signature: [DecidableEq α]
  body: fun _ _ => instDecidableAnd

中文:
实例 instDecidableRelSSubset
  签名: [DecidableEq α]
  定义体: fun _ _ => instDecidableAnd

Depends on / 依赖: Finset
-/
instance instDecidableRelSSubset [DecidableEq α] : DecidableRel (α := Finset α) (· ⊂ ·) :=
  fun _ _ => instDecidableAnd

/--
Instance `instDecidableLE` / 实例 `instDecidableLE`

English:
instance instDecidableLE
  signature: [DecidableEq α]
  body: instDecidableRelSubset

中文:
实例 instDecidableLE
  签名: [DecidableEq α]
  定义体: instDecidableRelSubset

Depends on / 依赖: instDecidableRelSubset
-/
instance instDecidableLE [DecidableEq α] : DecidableLE (Finset α) :=
  instDecidableRelSubset

/--
Instance `instDecidableLT` / 实例 `instDecidableLT`

English:
instance instDecidableLT
  signature: [DecidableEq α]
  body: instDecidableRelSSubset

中文:
实例 instDecidableLT
  签名: [DecidableEq α]
  定义体: instDecidableRelSSubset

Depends on / 依赖: instDecidableRelSSubset
-/
instance instDecidableLT [DecidableEq α] : DecidableLT (Finset α) :=
  instDecidableRelSSubset

set_option backward.isDefEq.respectTransparency false in
/--
Instance `decidableDExistsFinset` / 实例 `decidableDExistsFinset`

English:
instance decidableDExistsFinset
  signature: {p : forall a in s, Prop} [_hp : forall (a) (h : a in s), Decidable (p a h)]
  body: Multiset.decidableDexistsMultiset

中文:
实例 decidableDExistsFinset
  签名: {p : 对任意 a in s, 命题} [_hp : 对任意 (a) (h : a in s), Decidable (p a h)]
  定义体: Multiset.decidableDexistsMultiset

Depends on / 依赖: Multiset, Multiset.decidableDexistsMultiset, decidableDexistsMultiset
-/
instance decidableDExistsFinset {p : forall a in s, Prop} [_hp : forall (a) (h : a in s), Decidable (p a h)] :
    Decidable (exists (a : _) (h : a in s), p a h) :=
  Multiset.decidableDexistsMultiset

/--
Instance `decidableExistsAndFinset` / 实例 `decidableExistsAndFinset`

English:
instance decidableExistsAndFinset
  signature: {p : α -> Prop} [_hp : forall (a), Decidable (p a)]
  body: decidable_of_iff (exists (a : _) (_ : a in s), p a) (by simp)

中文:
实例 decidableExistsAndFinset
  签名: {p : α -> 命题} [_hp : 对任意 (a), Decidable (p a)]
  定义体: decidable_of_iff (exists (a : _) (_ : a in s), p a) (by simp)

Depends on / 依赖: decidable_of_iff
-/
instance decidableExistsAndFinset {p : α -> Prop} [_hp : forall (a), Decidable (p a)] :
    Decidable (exists a in s, p a) :=
  decidable_of_iff (exists (a : _) (_ : a in s), p a) (by simp)

/--
Instance `decidableExistsAndFinsetCoe` / 实例 `decidableExistsAndFinsetCoe`

English:
instance decidableExistsAndFinsetCoe
  signature: {p : α -> Prop} [DecidablePred p]
  body: decidableExistsAndFinset

中文:
实例 decidableExistsAndFinsetCoe
  签名: {p : α -> 命题} [DecidablePred p]
  定义体: decidableExistsAndFinset

Depends on / 依赖: decidableExistsAndFinset
-/
instance decidableExistsAndFinsetCoe {p : α -> Prop} [DecidablePred p] :
    Decidable (exists a in (s : Set α), p a) := decidableExistsAndFinset

/--
Instance `decidableEqPiFinset` / 实例 `decidableEqPiFinset`

English:
instance decidableEqPiFinset
  signature: {β : α -> Type*} [_h : forall a, DecidableEq (β a)]
  body: Multiset.decidableEqPiMultiset

中文:
实例 decidableEqPiFinset
  签名: {β : α -> 类型} [_h : 对任意 a, DecidableEq (β a)]
  定义体: Multiset.decidableEqPiMultiset

Depends on / 依赖: Multiset, Multiset.decidableEqPiMultiset, decidableEqPiMultiset
-/
instance decidableEqPiFinset {β : α -> Type*} [_h : forall a, DecidableEq (β a)] :
    DecidableEq (forall a in s, β a) :=
  Multiset.decidableEqPiMultiset

end DecidablePiExists

end Finset

namespace List

variable [DecidableEq α] {a : α} {f : α -> β} {s : Finset α} {t : Set β} {t' : Finset β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidablePred
  signature: (· in t)] : Decidable (Set.MapsTo f s t)
  body: inferInstanceAs (Decidable (forall x in s, f x in t))

中文:
实例 [DecidablePred
  签名: (· in t)] : Decidable (Set.MapsTo f s t)
  定义体: inferInstanceAs (Decidable (forall x in s, f x in t))

Depends on / 依赖: Decidable
-/
instance [DecidablePred (· in t)] : Decidable (Set.MapsTo f s t) :=
  inferInstanceAs (Decidable (forall x in s, f x in t))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: β] : Decidable (Set.SurjOn f s t')
  body: inferInstanceAs (Decidable (forall x in t', exists y in s, f y = x))

中文:
实例 [DecidableEq
  签名: β] : Decidable (Set.SurjOn f s t')
  定义体: inferInstanceAs (Decidable (forall x in t', exists y in s, f y = x))

Depends on / 依赖: Decidable
-/
instance [DecidableEq β] : Decidable (Set.SurjOn f s t') :=
  inferInstanceAs (Decidable (forall x in t', exists y in s, f y = x))

end List

namespace Finset

section Pairwise

variable {s : Finset α}

/--
theorem `pairwise_subtype_iff_pairwise_finset'` / 定理 `pairwise_subtype_iff_pairwise_finset'`

English:
theorem pairwise_subtype_iff_pairwise_finset'
  given: (r : β -> β -> Prop) (f : α -> β)
  proof: pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)

中文:
定理 pairwise_subtype_iff_pairwise_finset'
  条件: (r : β -> β -> 命题) (f : α -> β)
  证明: pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)

Depends on / 依赖: pairwise_subtype_iff_pairwise_set
-/
theorem pairwise_subtype_iff_pairwise_finset' (r : β -> β -> Prop) (f : α -> β) :
    Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f) :=
  pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)

/--
theorem `pairwise_subtype_iff_pairwise_finset` / 定理 `pairwise_subtype_iff_pairwise_finset`

English:
theorem pairwise_subtype_iff_pairwise_finset
  given: (r : α -> α -> Prop)
  proof: pairwise_subtype_iff_pairwise_finset' r id

中文:
定理 pairwise_subtype_iff_pairwise_finset
  条件: (r : α -> α -> 命题)
  证明: pairwise_subtype_iff_pairwise_finset' r id

Depends on / 依赖: pairwise_subtype_iff_pairwise_finset
-/
theorem pairwise_subtype_iff_pairwise_finset (r : α -> α -> Prop) :
    Pairwise (r on fun x : s => x) ↔ (s : Set α).Pairwise r :=
  pairwise_subtype_iff_pairwise_finset' r id

end Pairwise

end Finset
