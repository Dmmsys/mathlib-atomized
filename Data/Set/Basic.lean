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

- `f : α → β` is a function,

- `s : Set α` and `s₁ s₂ : Set α` are subsets of `α`

- `t : Set β` is a subset of `β`.

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

/--
theorem `mem_injective` / 定理 `mem_injective`

English:
theorem mem_injective
  statement: Injective (Membership.mem : Set α -> α -> Prop)
  proof: injective_id

中文:
定理 mem_injective
  结论: Injective (Membership.mem : Set α -> α -> 命题)
  证明: injective_id
-/
protected theorem mem_injective : Injective (Membership.mem : Set α -> α -> Prop) := injective_id
/--
theorem `mem_surjective` / 定理 `mem_surjective`

English:
theorem mem_surjective
  statement: Surjective (Membership.mem : Set α -> α -> Prop)
  proof: surjective_id

中文:
定理 mem_surjective
  结论: Surjective (Membership.mem : Set α -> α -> 命题)
  证明: surjective_id
-/
protected theorem mem_surjective : Surjective (Membership.mem : Set α -> α -> Prop) := surjective_id
/--
theorem `mem_bijective` / 定理 `mem_bijective`

English:
theorem mem_bijective
  statement: Bijective (Membership.mem : Set α -> α -> Prop)
  proof: bijective_id

中文:
定理 mem_bijective
  结论: Bijective (Membership.mem : Set α -> α -> 命题)
  证明: bijective_id
-/
protected theorem mem_bijective : Bijective (Membership.mem : Set α -> α -> Prop) := bijective_id

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: : DistribLattice (Set α) where
  body: inferInstance
  le := (· <= ·)
  lt := fun s t => s subseteq t ∧ ¬t subseteq s
  sup := (· union ·)
  inf := (· inter ·)

中文:
实例 instDistribLattice
  签名: : DistribLattice (Set α) where
  定义体: inferInstance
  le := (· <= ·)
  lt := fun s t => s subseteq t ∧ ¬t subseteq s
  sup := (· union ·)
  inf := (· inter ·)
-/
instance instDistribLattice : DistribLattice (Set α) where
  __ : DistribLattice (α -> Prop) := inferInstance
  le := (· <= ·)
  lt := fun s t => s subseteq t ∧ ¬t subseteq s
  sup := (· union ·)
  inf := (· inter ·)

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: : BoundedOrder (Set α) where
  body: inferInstance
  bot := ∅
  top := univ

@[simp]

中文:
实例 instBoundedOrder
  签名: : BoundedOrder (Set α) where
  定义体: inferInstance
  bot := ∅
  top := univ

@[simp]
-/
instance instBoundedOrder : BoundedOrder (Set α) where
  __ : BoundedOrder (α -> Prop) := inferInstance
  bot := ∅
  top := univ

@[simp]
/--
theorem `top_eq_univ` / 定理 `top_eq_univ`

English:
theorem top_eq_univ
  statement: (⊤ : Set α) = univ
  proof: rfl

@[simp]

中文:
定理 top_eq_univ
  结论: (⊤ : Set α) = univ
  证明: rfl

@[simp]
-/
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl

@[simp]
/--
theorem `bot_eq_empty` / 定理 `bot_eq_empty`

English:
theorem bot_eq_empty
  statement: (⊥ : Set α) = ∅
  proof: rfl

@[simp]

中文:
定理 bot_eq_empty
  结论: (⊥ : Set α) = ∅
  证明: rfl

@[simp]
-/
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl

@[simp]
/--
theorem `sup_eq_union` / 定理 `sup_eq_union`

English:
theorem sup_eq_union
  statement: ((· ⊔ ·) : Set α -> Set α -> Set α) = (· union ·)
  proof: rfl

@[simp]

中文:
定理 sup_eq_union
  结论: ((· ⊔ ·) : Set α -> Set α -> Set α) = (· union ·)
  证明: rfl

@[simp]
-/
theorem sup_eq_union : ((· ⊔ ·) : Set α -> Set α -> Set α) = (· union ·) :=
  rfl

@[simp]
/--
theorem `inf_eq_inter` / 定理 `inf_eq_inter`

English:
theorem inf_eq_inter
  statement: ((· ⊓ ·) : Set α -> Set α -> Set α) = (· inter ·)
  proof: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 inf_eq_inter
  结论: ((· ⊓ ·) : Set α -> Set α -> Set α) = (· inter ·)
  证明: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
-/
theorem inf_eq_inter : ((· ⊓ ·) : Set α -> Set α -> Set α) = (· inter ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `le_eq_subset` / 定理 `le_eq_subset`

English:
theorem le_eq_subset
  statement: ((· <= ·) : Set α -> Set α -> Prop) = (· subseteq ·)
  proof: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 le_eq_subset
  结论: ((· <= ·) : Set α -> Set α -> 命题) = (· subseteq ·)
  证明: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
-/
theorem le_eq_subset : ((· <= ·) : Set α -> Set α -> Prop) = (· subseteq ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `lt_eq_ssubset` / 定理 `lt_eq_ssubset`

English:
theorem lt_eq_ssubset
  statement: ((· < ·) : Set α -> Set α -> Prop) = (· ⊂ ·)
  proof: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 lt_eq_ssubset
  结论: ((· < ·) : Set α -> Set α -> 命题) = (· ⊂ ·)
  证明: rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
-/
theorem lt_eq_ssubset : ((· < ·) : Set α -> Set α -> Prop) = (· ⊂ ·) :=
  rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `le_iff_subset` / 定理 `le_iff_subset`

English:
theorem le_iff_subset
  statement: s <= t ↔ s subseteq t
  proof: Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

中文:
定理 le_iff_subset
  结论: s <= t ↔ s subseteq t
  证明: Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]

Depends on / 依赖: Iff.rfl
-/
theorem le_iff_subset : s <= t ↔ s subseteq t :=
  Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-05-24"), nolint synTaut]
/--
theorem `lt_iff_ssubset` / 定理 `lt_iff_ssubset`

English:
theorem lt_iff_ssubset
  statement: s < t ↔ s ⊂ t
  proof: Iff.rfl

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LE.le.subset, _root_.HasSubset.Subset.le⟩ := le_iff_subset

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LT.lt.ssubset, _root_.HasSSubset.SSubset.lt⟩ := lt_iff_ss

中文:
定理 lt_iff_ssubset
  结论: s < t ↔ s ⊂ t
  证明: Iff.rfl

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LE.le.subset, _root_.HasSubset.Subset.le⟩ := le_iff_subset

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LT.lt.ssubset, _root_.HasSSubset.SSubset.lt⟩ := lt_iff_ss

Depends on / 依赖: Iff.rfl
-/
theorem lt_iff_ssubset : s < t ↔ s ⊂ t :=
  Iff.rfl

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LE.le.subset, _root_.HasSubset.Subset.le⟩ := le_iff_subset

@[deprecated "this is now a syntactic identity" (since := "2026-05-24")]
alias ⟨_root_.LT.lt.ssubset, _root_.HasSSubset.SSubset.lt⟩ := lt_iff_ssubset

/--
Instance `PiSetCoe.canLift` / 实例 `PiSetCoe.canLift`

English:
instance PiSetCoe.canLift
  signature: (ι : Type u) (α : ι -> Type v) [forall i, Nonempty (α i)] (s : Set ι)
  body: PiSubtype.canLift ι α (· in s)

中文:
实例 PiSetCoe.canLift
  签名: (ι : 类型u) (α : ι -> 类型v) [对任意 i, Nonempty (α i)] (s : Set ι)
  定义体: PiSubtype.canLift ι α (· in s)

Depends on / 依赖: PiSubtype, PiSubtype.canLift, canLift
-/
instance PiSetCoe.canLift (ι : Type u) (α : ι -> Type v) [forall i, Nonempty (α i)] (s : Set ι) :
    CanLift (forall i : s, α i) (forall i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· in s)

/--
Instance `PiSetCoe.canLift'` / 实例 `PiSetCoe.canLift'`

English:
instance PiSetCoe.canLift'
  signature: (ι : Type u) (α : Type v) [Nonempty α] (s : Set ι)
  body: PiSetCoe.canLift ι (fun _ => α) s

中文:
实例 PiSetCoe.canLift'
  签名: (ι : 类型u) (α : 类型v) [Nonempty α] (s : Set ι)
  定义体: PiSetCoe.canLift ι (fun _ => α) s

Depends on / 依赖: PiSetCoe, PiSetCoe.canLift, canLift
-/
instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [Nonempty α] (s : Set ι) :
    CanLift (s -> α) (ι -> α) (fun f i => f i) fun _ => True :=
  PiSetCoe.canLift ι (fun _ => α) s

end Set

section SetCoe

variable {α : Type u}

instance (s : Set α) : CoeTC s α := ⟨fun x => x.1⟩

/--
theorem `Set.coe_eq_subtype` / 定理 `Set.coe_eq_subtype`

English:
theorem Set.coe_eq_subtype
  given: (s : Set α)
  statement: ↥s = { x // x in s }
  proof: rfl

中文:
定理 Set.coe_eq_subtype
  条件: (s : Set α)
  结论: ↥s = { x // x in s }
  证明: rfl
-/
theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x in s } :=
  rfl

/--
theorem `Set.coe_ofPred` / 定理 `Set.coe_ofPred`

English:
theorem Set.coe_ofPred
  given: (p : α -> Prop)
  statement: ↥{ x | p x } = { x // p x }
  proof: rfl

@[deprecated (since := "2026-07-09")] alias Set.coe_setOf := Set.coe_ofPred

中文:
定理 Set.coe_ofPred
  条件: (p : α -> 命题)
  结论: ↥{ x | p x } = { x // p x }
  证明: rfl

@[deprecated (since := "2026-07-09")] alias Set.coe_setOf := Set.coe_ofPred
-/
theorem Set.coe_ofPred (p : α -> Prop) : ↥{ x | p x } = { x // p x } :=
  rfl

@[deprecated (since := "2026-07-09")] alias Set.coe_setOf := Set.coe_ofPred

/--
theorem `SetCoe.forall` / 定理 `SetCoe.forall`

English:
theorem SetCoe.forall
  given: {s : Set α} {p : s -> Prop}
  statement: (forall x : s, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
  proof: Subtype.forall

中文:
定理 SetCoe.forall
  条件: {s : Set α} {p : s -> 命题}
  结论: (对任意 x : s, p x) ↔ 对任意 (x) (h : x in s), p ⟨x, h⟩
  证明: Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall
-/
theorem SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩ :=
  Subtype.forall

/--
theorem `SetCoe.exists` / 定理 `SetCoe.exists`

English:
theorem SetCoe.exists
  given: {s : Set α} {p : s -> Prop}
  proof: Subtype.exists

中文:
定理 SetCoe.exists
  条件: {s : Set α} {p : s -> 命题}
  证明: Subtype.exists

Depends on / 依赖: Subtype, Subtype.exists
-/
theorem SetCoe.exists {s : Set α} {p : s -> Prop} :
    (exists x : s, p x) ↔ exists (x : _) (h : x in s), p ⟨x, h⟩ :=
  Subtype.exists

/--
theorem `SetCoe.exists'` / 定理 `SetCoe.exists'`

English:
theorem SetCoe.exists'
  given: {s : Set α} {p : forall x, x in s -> Prop}
  proof: (@SetCoe.exists _ _ fun x => p x.1 x.2).symm

中文:
定理 SetCoe.exists'
  条件: {s : Set α} {p : 对任意 x, x in s -> 命题}
  证明: (@SetCoe.exists _ _ fun x => p x.1 x.2).symm

Depends on / 依赖: SetCoe, SetCoe.exists
-/
theorem SetCoe.exists' {s : Set α} {p : forall x, x in s -> Prop} :
    (exists (x : _) (h : x in s), p x h) ↔ exists x : s, p x.1 x.2 :=
  (@SetCoe.exists _ _ fun x => p x.1 x.2).symm

/--
theorem `SetCoe.forall'` / 定理 `SetCoe.forall'`

English:
theorem SetCoe.forall'
  given: {s : Set α} {p : forall x, x in s -> Prop}
  proof: (@SetCoe.forall _ _ fun x => p x.1 x.2).symm

@[simp]

中文:
定理 SetCoe.forall'
  条件: {s : Set α} {p : 对任意 x, x in s -> 命题}
  证明: (@SetCoe.forall _ _ fun x => p x.1 x.2).symm

@[simp]

Depends on / 依赖: SetCoe, SetCoe.forall
-/
theorem SetCoe.forall' {s : Set α} {p : forall x, x in s -> Prop} :
    (forall (x) (h : x in s), p x h) ↔ forall x : s, p x.1 x.2 :=
  (@SetCoe.forall _ _ fun x => p x.1 x.2).symm

@[simp]
/--
theorem `set_coe_cast` / 定理 `set_coe_cast`

English:
theorem set_coe_cast

中文:
定理 set_coe_cast
-/
theorem set_coe_cast :
    forall {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | _, _, rfl, _, _ => rfl

/--
theorem `SetCoe.ext` / 定理 `SetCoe.ext`

English:
theorem SetCoe.ext
  given: {s : Set α} {a b : s}
  statement: (a : α) = b -> a = b
  proof: Subtype.ext

中文:
定理 SetCoe.ext
  条件: {s : Set α} {a b : s}
  结论: (a : α) = b -> a = b
  证明: Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b :=
  Subtype.ext

/--
theorem `SetCoe.ext_iff` / 定理 `SetCoe.ext_iff`

English:
theorem SetCoe.ext_iff
  given: {s : Set α} {a b : s}
  statement: (↑a : α) = ↑b ↔ a = b
  proof: Iff.intro SetCoe.ext fun h => h ▸ rfl

中文:
定理 SetCoe.ext_iff
  条件: {s : Set α} {a b : s}
  结论: (↑a : α) = ↑b ↔ a = b
  证明: Iff.intro SetCoe.ext fun h => h ▸ rfl

Depends on / 依赖: Iff.intro, SetCoe, SetCoe.ext
-/
theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl

end SetCoe

/--
theorem `Subtype.mem` / 定理 `Subtype.mem`

English:
theorem Subtype.mem
  given: {α : Type*} {s : Set α} (p : s)
  statement: (p : α) in s
  proof: p.prop

中文:
定理 Subtype.mem
  条件: {α : 类型} {s : Set α} (p : s)
  结论: (p : α) in s
  证明: p.prop

Depends on / 依赖: p.prop
-/
theorem Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s :=
  p.prop

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Set α)
  body: ⟨∅⟩

@[trans]

中文:
实例 :
  签名: Inhabited (Set α)
  定义体: ⟨∅⟩

@[trans]
-/
instance : Inhabited (Set α) :=
  ⟨∅⟩

@[trans]
/--
theorem `mem_of_mem_of_subset` / 定理 `mem_of_mem_of_subset`

English:
theorem mem_of_mem_of_subset
  given: {x : α} {s t : Set α} (hx : x in s) (h : s subseteq t)
  statement: x in t
  proof: h hx

中文:
定理 mem_of_mem_of_subset
  条件: {x : α} {s t : Set α} (hx : x in s) (h : s subseteq t)
  结论: x in t
  证明: h hx

Depends on / 依赖: NormedAddCommGroup, Shrink, hf.small
-/
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x in s) (h : s subseteq t) : x in t :=
  h hx

/--
theorem `ofPred_injective` / 定理 `ofPred_injective`

English:
theorem ofPred_injective
  statement: Function.Injective (@ofPred α)
  proof: injective_id

@[deprecated (since := "2026-07-09")] alias setOf_injective := ofPred_injective

中文:
定理 ofPred_injective
  结论: Function.Injective (@ofPred α)
  证明: injective_id

@[deprecated (since := "2026-07-09")] alias setOf_injective := ofPred_injective

Depends on / 依赖: NormedSpace, Shrink, hf.small, injective_id
-/
theorem ofPred_injective : Function.Injective (@ofPred α) := injective_id

@[deprecated (since := "2026-07-09")] alias setOf_injective := ofPred_injective

/--
theorem `ofPred_inj` / 定理 `ofPred_inj`

English:
theorem ofPred_inj
  given: {p q : α -> Prop}
  statement: { x | p x } = { x | q x } ↔ p = q
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_inj := ofPred_inj

中文:
定理 ofPred_inj
  条件: {p q : α -> 命题}
  结论: { x | p x } = { x | q x } ↔ p = q
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_inj := ofPred_inj

Depends on / 依赖: Iff.rfl
-/
theorem ofPred_inj {p q : α -> Prop} : { x | p x } = { x | q x } ↔ p = q := Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_inj := ofPred_inj


/--
theorem `ofPred_bijective` / 定理 `ofPred_bijective`

English:
theorem ofPred_bijective
  statement: Bijective (ofPred : (α -> Prop) -> Set α)
  proof: bijective_id

@[deprecated (since := "2026-07-09")] alias setOf_bijective := ofPred_bijective

中文:
定理 ofPred_bijective
  结论: Bijective (ofPred : (α -> 命题) -> Set α)
  证明: bijective_id

@[deprecated (since := "2026-07-09")] alias setOf_bijective := ofPred_bijective

Depends on / 依赖: bijective_id
-/
theorem ofPred_bijective : Bijective (ofPred : (α -> Prop) -> Set α) :=
  bijective_id

@[deprecated (since := "2026-07-09")] alias setOf_bijective := ofPred_bijective

/--
theorem `subset_ofPred` / 定理 `subset_ofPred`

English:
theorem subset_ofPred
  given: {p : α -> Prop} {s : Set α}
  statement: s subseteq ofPred p ↔ forall x, x in s -> p x
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias subset_setOf := subset_ofPred

中文:
定理 subset_ofPred
  条件: {p : α -> 命题} {s : Set α}
  结论: s subseteq ofPred p ↔ 对任意 x, x in s -> p x
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias subset_setOf := subset_ofPred

Depends on / 依赖: Iff.rfl
-/
theorem subset_ofPred {p : α -> Prop} {s : Set α} : s subseteq ofPred p ↔ forall x, x in s -> p x :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias subset_setOf := subset_ofPred

/--
theorem `ofPred_subset` / 定理 `ofPred_subset`

English:
theorem ofPred_subset
  given: {p : α -> Prop} {s : Set α}
  statement: ofPred p subseteq s ↔ forall x, p x -> x in s
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset := ofPred_subset

@[simp]

中文:
定理 ofPred_subset
  条件: {p : α -> 命题} {s : Set α}
  结论: ofPred p subseteq s ↔ 对任意 x, p x -> x in s
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset := ofPred_subset

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofPred_subset {p : α -> Prop} {s : Set α} : ofPred p subseteq s ↔ forall x, p x -> x in s :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset := ofPred_subset

@[simp]
/--
theorem `ofPred_subset_ofPred` / 定理 `ofPred_subset_ofPred`

English:
theorem ofPred_subset_ofPred
  given: {p q : α -> Prop}
  statement: { a | p a } subseteq { a | q a } ↔ forall a, p a -> q a
  proof: Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset_setOf := ofPred_subset_ofPred

@[gcongr]
alias ⟨_, ofPred_subset_ofPred_of_imp⟩ := ofPred_subset_ofPred

@[deprecated (since := "2026-07-09")]
alias setOf_subset_setOf_of_imp := ofPred_subset_ofPred_of_imp

中文:
定理 ofPred_subset_ofPred
  条件: {p q : α -> 命题}
  结论: { a | p a } subseteq { a | q a } ↔ 对任意 a, p a -> q a
  证明: Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset_setOf := ofPred_subset_ofPred

@[gcongr]
alias ⟨_, ofPred_subset_ofPred_of_imp⟩ := ofPred_subset_ofPred

@[deprecated (since := "2026-07-09")]
alias setOf_subset_setOf_of_imp := ofPred_subset_ofPred_of_imp

Depends on / 依赖: Iff.rfl
-/
theorem ofPred_subset_ofPred {p q : α -> Prop} : { a | p a } subseteq { a | q a } ↔ forall a, p a -> q a :=
  Iff.rfl

@[deprecated (since := "2026-07-09")] alias setOf_subset_setOf := ofPred_subset_ofPred

@[gcongr]
alias ⟨_, ofPred_subset_ofPred_of_imp⟩ := ofPred_subset_ofPred

@[deprecated (since := "2026-07-09")]
alias setOf_subset_setOf_of_imp := ofPred_subset_ofPred_of_imp

/--
theorem `ofPred_and` / 定理 `ofPred_and`

English:
theorem ofPred_and
  given: {p q : α -> Prop}
  statement: { a | p a ∧ q a } = { a | p a } inter { a | q a }
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_and := ofPred_and

中文:
定理 ofPred_and
  条件: {p q : α -> 命题}
  结论: { a | p a ∧ q a } = { a | p a } inter { a | q a }
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_and := ofPred_and
-/
theorem ofPred_and {p q : α -> Prop} : { a | p a ∧ q a } = { a | p a } inter { a | q a } :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_and := ofPred_and

/--
theorem `ofPred_or` / 定理 `ofPred_or`

English:
theorem ofPred_or
  given: {p q : α -> Prop}
  statement: { a | p a ∨ q a } = { a | p a } union { a | q a }
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_or := ofPred_or

中文:
定理 ofPred_or
  条件: {p q : α -> 命题}
  结论: { a | p a ∨ q a } = { a | p a } union { a | q a }
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_or := ofPred_or
-/
theorem ofPred_or {p q : α -> Prop} : { a | p a ∨ q a } = { a | p a } union { a | q a } :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_or := ofPred_or

/-! ### Subset and strict subset relations -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
@[grind =]
/--
theorem `subset_def` / 定理 `subset_def`

English:
theorem subset_def
  statement: (s subseteq t) = forall x, x in s -> x in t
  proof: rfl

@[grind =]

中文:
定理 subset_def
  结论: (s subseteq t) = 对任意 x, x in s -> x in t
  证明: rfl

@[grind =]
-/
theorem subset_def : (s subseteq t) = forall x, x in s -> x in t :=
  rfl

@[grind =]
/--
theorem `ssubset_def` / 定理 `ssubset_def`

English:
theorem ssubset_def
  statement: (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s)
  proof: rfl

@[refl]

中文:
定理 ssubset_def
  结论: (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s)
  证明: rfl

@[refl]
-/
theorem ssubset_def : (s ⊂ t) = (s subseteq t ∧ ¬t subseteq s) :=
  rfl

@[refl]
/--
theorem `Subset.refl` / 定理 `Subset.refl`

English:
theorem Subset.refl
  given: (a : Set α)
  statement: a subseteq a
  proof: fun _ => id

中文:
定理 Subset.refl
  条件: (a : Set α)
  结论: a subseteq a
  证明: fun _ => id
-/
theorem Subset.refl (a : Set α) : a subseteq a := fun _ => id

/--
theorem `Subset.rfl` / 定理 `Subset.rfl`

English:
theorem Subset.rfl
  given: {s : Set α}
  statement: s subseteq s
  proof: Subset.refl s

@[trans]

中文:
定理 Subset.rfl
  条件: {s : Set α}
  结论: s subseteq s
  证明: Subset.refl s

@[trans]

Depends on / 依赖: Subset, Subset.refl
-/
theorem Subset.rfl {s : Set α} : s subseteq s :=
  Subset.refl s

@[trans]
/--
theorem `Subset.trans` / 定理 `Subset.trans`

English:
theorem Subset.trans
  given: {a b c : Set α} (ab : a subseteq b) (bc : b subseteq c)
  statement: a subseteq c
  proof: fun _ h => bc ab h

@[trans]

中文:
定理 Subset.trans
  条件: {a b c : Set α} (ab : a subseteq b) (bc : b subseteq c)
  结论: a subseteq c
  证明: fun _ h => bc ab h

@[trans]
-/
theorem Subset.trans {a b c : Set α} (ab : a subseteq b) (bc : b subseteq c) : a subseteq c := fun _ h => bc ab h

@[trans]
/--
theorem `mem_of_eq_of_mem` / 定理 `mem_of_eq_of_mem`

English:
theorem mem_of_eq_of_mem
  given: {x y : α} {s : Set α} (hx : x = y) (h : y in s)
  statement: x in s
  proof: hx.symm ▸ h

中文:
定理 mem_of_eq_of_mem
  条件: {x y : α} {s : Set α} (hx : x = y) (h : y in s)
  结论: x in s
  证明: hx.symm ▸ h

Depends on / 依赖: hx.symm
-/
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y in s) : x in s :=
  hx.symm ▸ h

/--
theorem `Subset.antisymm` / 定理 `Subset.antisymm`

English:
theorem Subset.antisymm
  given: {a b : Set α} (h₁ : a subseteq b) (h₂ : b subseteq a)
  statement: a = b
  proof: Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩

中文:
定理 Subset.antisymm
  条件: {a b : Set α} (h₁ : a subseteq b) (h₂ : b subseteq a)
  结论: a = b
  证明: Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩
-/
theorem Subset.antisymm {a b : Set α} (h₁ : a subseteq b) (h₂ : b subseteq a) : a = b :=
  Set.ext fun _ => ⟨@h₁ _, @h₂ _⟩

/--
theorem `Subset.antisymm_iff` / 定理 `Subset.antisymm_iff`

English:
theorem Subset.antisymm_iff
  given: {a b : Set α}
  statement: a = b ↔ a subseteq b ∧ b subseteq a
  proof: ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩

中文:
定理 Subset.antisymm_iff
  条件: {a b : Set α}
  结论: a = b ↔ a subseteq b ∧ b subseteq a
  证明: ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩
-/
theorem Subset.antisymm_iff {a b : Set α} : a = b ↔ a subseteq b ∧ b subseteq a :=
  ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩

-- an alternative name
/--
theorem `eq_of_subset_of_subset` / 定理 `eq_of_subset_of_subset`

English:
theorem eq_of_subset_of_subset
  given: {a b : Set α}
  statement: a subseteq b -> b subseteq a -> a = b
  proof: Subset.antisymm

中文:
定理 eq_of_subset_of_subset
  条件: {a b : Set α}
  结论: a subseteq b -> b subseteq a -> a = b
  证明: Subset.antisymm

Depends on / 依赖: Subset, Subset.antisymm, antisymm
-/
theorem eq_of_subset_of_subset {a b : Set α} : a subseteq b -> b subseteq a -> a = b :=
  Subset.antisymm

/--
theorem `mem_of_subset_of_mem` / 定理 `mem_of_subset_of_mem`

English:
theorem mem_of_subset_of_mem
  given: {s₁ s₂ : Set α} {a : α} (h : s₁ subseteq s₂)
  statement: a in s₁ -> a in s₂
  proof: @h _

中文:
定理 mem_of_subset_of_mem
  条件: {s₁ s₂ : Set α} {a : α} (h : s₁ subseteq s₂)
  结论: a in s₁ -> a in s₂
  证明: @h _
-/
@[gcongr] theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ subseteq s₂) : a in s₁ -> a in s₂ :=
  @h _

/--
theorem `notMem_subset` / 定理 `notMem_subset`

English:
theorem notMem_subset
  given: (h : s subseteq t)
  statement: a ∉ t -> a ∉ s
  proof: mt mem_of_subset_of_mem h

中文:
定理 notMem_subset
  条件: (h : s subseteq t)
  结论: a ∉ t -> a ∉ s
  证明: mt mem_of_subset_of_mem h

Depends on / 依赖: mem_of_subset_of_mem
-/
theorem notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s :=
mt mem_of_subset_of_mem h

/--
theorem `subset_iff_notMem` / 定理 `subset_iff_notMem`

English:
theorem subset_iff_notMem
  statement: s subseteq t ↔ forall ⦃a⦄, a ∉ t -> a ∉ s
  proof: by
  simp only [subset_def, not_imp_not]

中文:
定理 subset_iff_notMem
  结论: s subseteq t ↔ 对任意 ⦃a⦄, a ∉ t -> a ∉ s
  证明: by
  simp only [subset_def, not_imp_not]

Depends on / 依赖: not_imp_not, subset_def
-/
theorem subset_iff_notMem : s subseteq t ↔ forall ⦃a⦄, a ∉ t -> a ∉ s := by
  simp only [subset_def, not_imp_not]

/--
theorem `not_subset` / 定理 `not_subset`

English:
theorem not_subset
  statement: ¬s subseteq t ↔ exists a in s, a ∉ t
  proof: by
  simp only [subset_def, not_forall, exists_prop]

中文:
定理 not_subset
  结论: ¬s subseteq t ↔ 存在 a in s, a ∉ t
  证明: by
  simp only [subset_def, not_forall, exists_prop]

Depends on / 依赖: exists_prop, not_forall, subset_def
-/
theorem not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t := by
  simp only [subset_def, not_forall, exists_prop]

/--
theorem `not_univ_subset` / 定理 `not_univ_subset`

English:
theorem not_univ_subset
  statement: ¬univ subseteq s ↔ exists a, a ∉ s
  proof: by
  simp [not_subset]

@[deprecated not_univ_subset (since := "2026-03-12")]

中文:
定理 not_univ_subset
  结论: ¬univ subseteq s ↔ 存在 a, a ∉ s
  证明: by
  simp [not_subset]

@[deprecated not_univ_subset (since := "2026-03-12")]

Depends on / 依赖: not_subset
-/
theorem not_univ_subset : ¬univ subseteq s ↔ exists a, a ∉ s := by
  simp [not_subset]

@[deprecated not_univ_subset (since := "2026-03-12")]
/--
theorem `not_top_subset` / 定理 `not_top_subset`

English:
theorem not_top_subset
  statement: ¬⊤ subseteq s ↔ exists a, a ∉ s
  proof: not_univ_subset

中文:
定理 not_top_subset
  结论: ¬⊤ subseteq s ↔ 存在 a, a ∉ s
  证明: not_univ_subset

Depends on / 依赖: not_univ_subset
-/
theorem not_top_subset : ¬⊤ subseteq s ↔ exists a, a ∉ s :=
  not_univ_subset

/--
lemma `eq_of_forall_subset_iff` / 引理 `eq_of_forall_subset_iff`

English:
lemma eq_of_forall_subset_iff
  given: (h : forall u, s subseteq u ↔ t subseteq u)
  statement: s = t
  proof: eq_of_forall_ge_iff h

中文:
引理 eq_of_forall_subset_iff
  条件: (h : 对任意 u, s subseteq u ↔ t subseteq u)
  结论: s = t
  证明: eq_of_forall_ge_iff h

Depends on / 依赖: eq_of_forall_ge_iff
-/
lemma eq_of_forall_subset_iff (h : forall u, s subseteq u ↔ t subseteq u) : s = t := eq_of_forall_ge_iff h


/--
theorem `eq_or_ssubset_of_subset` / 定理 `eq_or_ssubset_of_subset`

English:
theorem eq_or_ssubset_of_subset
  given: (h : s subseteq t)
  statement: s = t ∨ s ⊂ t
  proof: eq_or_lt_of_le h

中文:
定理 eq_or_ssubset_of_subset
  条件: (h : s subseteq t)
  结论: s = t ∨ s ⊂ t
  证明: eq_or_lt_of_le h
-/
protected theorem eq_or_ssubset_of_subset (h : s subseteq t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h

/--
theorem `exists_of_ssubset` / 定理 `exists_of_ssubset`

English:
theorem exists_of_ssubset
  given: {s t : Set α} (h : s ⊂ t)
  statement: exists x in t, x ∉ s
  proof: not_subset.1 h.2

中文:
定理 exists_of_ssubset
  条件: {s t : Set α} (h : s ⊂ t)
  结论: 存在 x in t, x ∉ s
  证明: not_subset.1 h.2

Depends on / 依赖: not_subset
-/
theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exists x in t, x ∉ s :=
  not_subset.1 h.2

/--
theorem `ssubset_iff_subset_ne` / 定理 `ssubset_iff_subset_ne`

English:
theorem ssubset_iff_subset_ne
  given: {s t : Set α}
  statement: s ⊂ t ↔ s subseteq t ∧ s != t
  proof: @lt_iff_le_and_ne (Set α) _ s t

中文:
定理 ssubset_iff_subset_ne
  条件: {s t : Set α}
  结论: s ⊂ t ↔ s subseteq t ∧ s != t
  证明: @lt_iff_le_and_ne (Set α) _ s t
-/
protected theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s subseteq t ∧ s != t :=
  @lt_iff_le_and_ne (Set α) _ s t

/--
theorem `ssubset_iff_of_subset` / 定理 `ssubset_iff_of_subset`

English:
theorem ssubset_iff_of_subset
  given: {s t : Set α} (h : s subseteq t)
  statement: s ⊂ t ↔ exists x in t, x ∉ s
  proof: ⟨exists_of_ssubset, fun ⟨_, hxt, hxs⟩ => ⟨h, fun h => hxs h hxt⟩⟩

中文:
定理 ssubset_iff_of_subset
  条件: {s t : Set α} (h : s subseteq t)
  结论: s ⊂ t ↔ 存在 x in t, x ∉ s
  证明: ⟨exists_of_ssubset, fun ⟨_, hxt, hxs⟩ => ⟨h, fun h => hxs h hxt⟩⟩

Depends on / 依赖: exists_of_ssubset
-/
theorem ssubset_iff_of_subset {s t : Set α} (h : s subseteq t) : s ⊂ t ↔ exists x in t, x ∉ s :=
⟨exists_of_ssubset, fun ⟨_, hxt, hxs⟩ => ⟨h, fun h => hxs h hxt⟩⟩

/--
theorem `ssubset_iff_exists` / 定理 `ssubset_iff_exists`

English:
theorem ssubset_iff_exists
  given: {s t : Set α}
  statement: s ⊂ t ↔ s subseteq t ∧ exists x in t, x ∉ s
  proof: ⟨fun h => ⟨h.le, Set.exists_of_ssubset h⟩, fun ⟨h1, h2⟩ => (Set.ssubset_iff_of_subset h1).mpr h2⟩

中文:
定理 ssubset_iff_exists
  条件: {s t : Set α}
  结论: s ⊂ t ↔ s subseteq t ∧ 存在 x in t, x ∉ s
  证明: ⟨fun h => ⟨h.le, Set.exists_of_ssubset h⟩, fun ⟨h1, h2⟩ => (Set.ssubset_iff_of_subset h1).mpr h2⟩

Depends on / 依赖: Set.exists_of_ssubset, Set.ssubset_iff_of_subset, exists_of_ssubset, h.le, ssubset_iff_of_subset
-/
theorem ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s subseteq t ∧ exists x in t, x ∉ s :=
  ⟨fun h => ⟨h.le, Set.exists_of_ssubset h⟩, fun ⟨h1, h2⟩ => (Set.ssubset_iff_of_subset h1).mpr h2⟩

/--
theorem `ssubset_of_ssubset_of_subset` / 定理 `ssubset_of_ssubset_of_subset`

English:
theorem ssubset_of_ssubset_of_subset
  statement: {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
  proof: ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩

中文:
定理 ssubset_of_ssubset_of_subset
  结论: {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
  证明: ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩
-/
protected theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
    (hs₂s₃ : s₂ subseteq s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩

/--
theorem `ssubset_of_subset_of_ssubset` / 定理 `ssubset_of_subset_of_ssubset`

English:
theorem ssubset_of_subset_of_ssubset
  statement: {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ subseteq s₂)
  proof: ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩

中文:
定理 ssubset_of_subset_of_ssubset
  结论: {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ subseteq s₂)
  证明: ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩
-/
protected theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ subseteq s₂)
    (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩

/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (x : α)
  statement: x ∉ (∅ : Set α)
  proof: id

中文:
定理 notMem_empty
  条件: (x : α)
  结论: x ∉ (∅ : Set α)
  证明: id
-/
theorem notMem_empty (x : α) : x ∉ (∅ : Set α) :=
  id

/--
theorem `not_notMem` / 定理 `not_notMem`

English:
theorem not_notMem
  statement: ¬a ∉ s ↔ a in s
  proof: not_not

中文:
定理 not_notMem
  结论: ¬a ∉ s ↔ a in s
  证明: not_not

Depends on / 依赖: not_not
-/
theorem not_notMem : ¬a ∉ s ↔ a in s :=
  not_not


/--
theorem `nonempty_coe_sort` / 定理 `nonempty_coe_sort`

English:
theorem nonempty_coe_sort
  given: {s : Set α}
  statement: Nonempty ↥s ↔ s.Nonempty
  proof: nonempty_subtype

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

中文:
定理 nonempty_coe_sort
  条件: {s : Set α}
  结论: Nonempty ↥s ↔ s.Nonempty
  证明: nonempty_subtype

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

Depends on / 依赖: nonempty_subtype
-/
theorem nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

/--
theorem `nonempty_def` / 定理 `nonempty_def`

English:
theorem nonempty_def
  statement: s.Nonempty ↔ exists x, x in s
  proof: Iff.rfl

中文:
定理 nonempty_def
  结论: s.Nonempty ↔ 存在 x, x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem nonempty_def : s.Nonempty ↔ exists x, x in s :=
  Iff.rfl

/--
theorem `nonempty_of_mem` / 定理 `nonempty_of_mem`

English:
theorem nonempty_of_mem
  given: {x} (h : x in s)
  statement: s.Nonempty
  proof: ⟨x, h⟩

中文:
定理 nonempty_of_mem
  条件: {x} (h : x in s)
  结论: s.Nonempty
  证明: ⟨x, h⟩
-/
theorem nonempty_of_mem {x} (h : x in s) : s.Nonempty :=
  ⟨x, h⟩

/--
theorem `Nonempty.not_subset_empty` / 定理 `Nonempty.not_subset_empty`

English:
theorem Nonempty.not_subset_empty
  statement: s.Nonempty -> ¬s subseteq ∅

中文:
定理 Nonempty.not_subset_empty
  结论: s.Nonempty -> ¬s subseteq ∅

Depends on / 依赖: Classical, Classical.choose
-/
theorem Nonempty.not_subset_empty : s.Nonempty -> ¬s subseteq ∅
  | ⟨_, hx⟩, hs => hs hx

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Nonempty.some (h : s.Nonempty)
  body: Classical.choose h

中文:
定义 noncomputable
  签名: def Nonempty.some (h : s.Nonempty)
  定义体: Classical.choose h
-/
protected noncomputable def Nonempty.some (h : s.Nonempty) : α :=
  Classical.choose h

/--
theorem `Nonempty.some_mem` / 定理 `Nonempty.some_mem`

English:
theorem Nonempty.some_mem
  given: (h : s.Nonempty)
  statement: h.some in s
  proof: Classical.choose_spec h

中文:
定理 Nonempty.some_mem
  条件: (h : s.Nonempty)
  结论: h.some in s
  证明: Classical.choose_spec h
-/
protected theorem Nonempty.some_mem (h : s.Nonempty) : h.some in s :=
  Classical.choose_spec h

/--
theorem `Nonempty.mono` / 定理 `Nonempty.mono`

English:
theorem Nonempty.mono
  given: (ht : s subseteq t) (hs : s.Nonempty)
  statement: t.Nonempty
  proof: hs.imp ht

中文:
定理 Nonempty.mono
  条件: (ht : s subseteq t) (hs : s.Nonempty)
  结论: t.Nonempty
  证明: hs.imp ht
-/
@[gcongr] theorem Nonempty.mono (ht : s subseteq t) (hs : s.Nonempty) : t.Nonempty :=
  hs.imp ht

/--
theorem `nonempty_of_not_subset` / 定理 `nonempty_of_not_subset`

English:
theorem nonempty_of_not_subset
  given: (h : ¬s subseteq t)
  statement: (s \ t).Nonempty
  proof: let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩

中文:
定理 nonempty_of_not_subset
  条件: (h : ¬s subseteq t)
  结论: (s \ t).Nonempty
  证明: let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩

Depends on / 依赖: not_subset
-/
theorem nonempty_of_not_subset (h : ¬s subseteq t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩

/--
theorem `nonempty_of_ssubset` / 定理 `nonempty_of_ssubset`

English:
theorem nonempty_of_ssubset
  given: (ht : s ⊂ t)
  statement: (t \ s).Nonempty
  proof: nonempty_of_not_subset ht.2

中文:
定理 nonempty_of_ssubset
  条件: (ht : s ⊂ t)
  结论: (t \ s).Nonempty
  证明: nonempty_of_not_subset ht.2

Depends on / 依赖: nonempty_of_not_subset
-/
theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2

/--
theorem `Nonempty.of_sdiff` / 定理 `Nonempty.of_sdiff`

English:
theorem Nonempty.of_sdiff
  given: (h : (s \ t).Nonempty)
  statement: s.Nonempty
  proof: h.imp fun _ => And.left

@[deprecated (since := "2026-06-03")] alias Nonempty.of_diff := Nonempty.of_sdiff

中文:
定理 Nonempty.of_sdiff
  条件: (h : (s \ t).Nonempty)
  结论: s.Nonempty
  证明: h.imp fun _ => And.left

@[deprecated (since := "2026-06-03")] alias Nonempty.of_diff := Nonempty.of_sdiff

Depends on / 依赖: And.left, h.imp
-/
theorem Nonempty.of_sdiff (h : (s \ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

@[deprecated (since := "2026-06-03")] alias Nonempty.of_diff := Nonempty.of_sdiff

/--
theorem `nonempty_of_ssubset'` / 定理 `nonempty_of_ssubset'`

English:
theorem nonempty_of_ssubset'
  given: (ht : s ⊂ t)
  statement: t.Nonempty
  proof: (nonempty_of_ssubset ht).of_sdiff

中文:
定理 nonempty_of_ssubset'
  条件: (ht : s ⊂ t)
  结论: t.Nonempty
  证明: (nonempty_of_ssubset ht).of_sdiff

Depends on / 依赖: nonempty_of_ssubset, of_sdiff
-/
theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty :=
  (nonempty_of_ssubset ht).of_sdiff

/--
theorem `Nonempty.inl` / 定理 `Nonempty.inl`

English:
theorem Nonempty.inl
  given: (hs : s.Nonempty)
  statement: (s union t).Nonempty
  proof: hs.imp fun _ => Or.inl

中文:
定理 Nonempty.inl
  条件: (hs : s.Nonempty)
  结论: (s union t).Nonempty
  证明: hs.imp fun _ => Or.inl
-/
theorem Nonempty.inl (hs : s.Nonempty) : (s union t).Nonempty :=
  hs.imp fun _ => Or.inl

/--
theorem `Nonempty.inr` / 定理 `Nonempty.inr`

English:
theorem Nonempty.inr
  given: (ht : t.Nonempty)
  statement: (s union t).Nonempty
  proof: ht.imp fun _ => Or.inr

@[simp]

中文:
定理 Nonempty.inr
  条件: (ht : t.Nonempty)
  结论: (s union t).Nonempty
  证明: ht.imp fun _ => Or.inr

@[simp]
-/
theorem Nonempty.inr (ht : t.Nonempty) : (s union t).Nonempty :=
  ht.imp fun _ => Or.inr

@[simp]
/--
theorem `union_nonempty` / 定理 `union_nonempty`

English:
theorem union_nonempty
  statement: (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty
  proof: exists_or

中文:
定理 union_nonempty
  结论: (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty
  证明: exists_or

Depends on / 依赖: exists_or
-/
theorem union_nonempty : (s union t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  exists_or

/--
theorem `Nonempty.left` / 定理 `Nonempty.left`

English:
theorem Nonempty.left
  given: (h : (s inter t).Nonempty)
  statement: s.Nonempty
  proof: h.imp fun _ => And.left

中文:
定理 Nonempty.left
  条件: (h : (s inter t).Nonempty)
  结论: s.Nonempty
  证明: h.imp fun _ => And.left

Depends on / 依赖: And.left, h.imp
-/
theorem Nonempty.left (h : (s inter t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

/--
theorem `Nonempty.right` / 定理 `Nonempty.right`

English:
theorem Nonempty.right
  given: (h : (s inter t).Nonempty)
  statement: t.Nonempty
  proof: h.imp fun _ => And.right

中文:
定理 Nonempty.right
  条件: (h : (s inter t).Nonempty)
  结论: t.Nonempty
  证明: h.imp fun _ => And.right

Depends on / 依赖: And.right, h.imp
-/
theorem Nonempty.right (h : (s inter t).Nonempty) : t.Nonempty :=
  h.imp fun _ => And.right

/--
theorem `inter_nonempty` / 定理 `inter_nonempty`

English:
theorem inter_nonempty
  statement: (s inter t).Nonempty ↔ exists x, x in s ∧ x in t
  proof: Iff.rfl

中文:
定理 inter_nonempty
  结论: (s inter t).Nonempty ↔ 存在 x, x in s ∧ x in t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem inter_nonempty : (s inter t).Nonempty ↔ exists x, x in s ∧ x in t :=
  Iff.rfl

/--
theorem `inter_nonempty_iff_exists_left` / 定理 `inter_nonempty_iff_exists_left`

English:
theorem inter_nonempty_iff_exists_left
  statement: (s inter t).Nonempty ↔ exists x in s, x in t
  proof: by
  simp_rw [inter_nonempty]

中文:
定理 inter_nonempty_iff_exists_left
  结论: (s inter t).Nonempty ↔ 存在 x in s, x in t
  证明: by
  simp_rw [inter_nonempty]

Depends on / 依赖: inter_nonempty, simp_rw
-/
theorem inter_nonempty_iff_exists_left : (s inter t).Nonempty ↔ exists x in s, x in t := by
  simp_rw [inter_nonempty]

/--
theorem `inter_nonempty_iff_exists_right` / 定理 `inter_nonempty_iff_exists_right`

English:
theorem inter_nonempty_iff_exists_right
  statement: (s inter t).Nonempty ↔ exists x in t, x in s
  proof: by
  simp_rw [inter_nonempty, and_comm]

中文:
定理 inter_nonempty_iff_exists_right
  结论: (s inter t).Nonempty ↔ 存在 x in t, x in s
  证明: by
  simp_rw [inter_nonempty, and_comm]

Depends on / 依赖: and_comm, inter_nonempty, simp_rw
-/
theorem inter_nonempty_iff_exists_right : (s inter t).Nonempty ↔ exists x in t, x in s := by
  simp_rw [inter_nonempty, and_comm]

/--
theorem `nonempty_iff_univ_nonempty` / 定理 `nonempty_iff_univ_nonempty`

English:
theorem nonempty_iff_univ_nonempty
  statement: Nonempty α ↔ (univ : Set α).Nonempty
  proof: ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]

中文:
定理 nonempty_iff_univ_nonempty
  结论: Nonempty α ↔ (univ : Set α).Nonempty
  证明: ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]
-/
theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]
/--
theorem `univ_nonempty` / 定理 `univ_nonempty`

English:
theorem univ_nonempty
  statement: forall [Nonempty α], (univ : Set α).Nonempty

中文:
定理 univ_nonempty
  结论: 对任意 [Nonempty α], (univ : Set α).Nonempty
-/
theorem univ_nonempty : forall [Nonempty α], (univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩

/--
theorem `Nonempty.to_subtype` / 定理 `Nonempty.to_subtype`

English:
theorem Nonempty.to_subtype
  statement: s.Nonempty -> Nonempty (↥s)
  proof: nonempty_subtype.2

中文:
定理 Nonempty.to_subtype
  结论: s.Nonempty -> Nonempty (↥s)
  证明: nonempty_subtype.2
-/
theorem Nonempty.to_subtype : s.Nonempty -> Nonempty (↥s) :=
  nonempty_subtype.2

/--
theorem `Nonempty.to_type` / 定理 `Nonempty.to_type`

English:
theorem Nonempty.to_type
  statement: s.Nonempty -> Nonempty α
  proof: fun ⟨x, _⟩ => ⟨x⟩

中文:
定理 Nonempty.to_type
  结论: s.Nonempty -> Nonempty α
  证明: fun ⟨x, _⟩ => ⟨x⟩
-/
theorem Nonempty.to_type : s.Nonempty -> Nonempty α := fun ⟨x, _⟩ => ⟨x⟩

/--
Instance `univ.nonempty` / 实例 `univ.nonempty`

English:
instance univ.nonempty
  signature: [Nonempty α]
  body: Set.univ_nonempty.to_subtype

中文:
实例 univ.nonempty
  签名: [Nonempty α]
  定义体: Set.univ_nonempty.to_subtype

Depends on / 依赖: Set.univ_nonempty.to_subtype, to_subtype, univ_nonempty
-/
instance univ.nonempty [Nonempty α] : Nonempty (↥(Set.univ : Set α)) :=
  Set.univ_nonempty.to_subtype

-- Redeclare for refined keys
-- `Nonempty (@Subtype _ (@Membership.mem _ (Set _) _ (@Top.top (Set _) _)))`
/--
Instance `instNonemptyTop` / 实例 `instNonemptyTop`

English:
instance instNonemptyTop
  signature: [Nonempty α]
  body: inferInstanceAs (Nonempty (univ : Set α))

中文:
实例 instNonemptyTop
  签名: [Nonempty α]
  定义体: inferInstanceAs (Nonempty (univ : Set α))

Depends on / 依赖: Nonempty
-/
instance instNonemptyTop [Nonempty α] : Nonempty (⊤ : Set α) :=
  inferInstanceAs (Nonempty (univ : Set α))

/--
theorem `Nonempty.of_subtype` / 定理 `Nonempty.of_subtype`

English:
theorem Nonempty.of_subtype
  given: [Nonempty (↥s)]
  statement: s.Nonempty
  proof: nonempty_subtype.mp ‹_›

中文:
定理 Nonempty.of_subtype
  条件: [Nonempty (↥s)]
  结论: s.Nonempty
  证明: nonempty_subtype.mp ‹_›

Depends on / 依赖: nonempty_subtype, nonempty_subtype.mp
-/
theorem Nonempty.of_subtype [Nonempty (↥s)] : s.Nonempty := nonempty_subtype.mp ‹_›


/--
theorem `empty_def` / 定理 `empty_def`

English:
theorem empty_def
  statement: (∅ : Set α) = { _x : α | False }
  proof: rfl

@[simp, grind =, push]

中文:
定理 empty_def
  结论: (∅ : Set α) = { _x : α | False }
  证明: rfl

@[simp, grind =, push]
-/
theorem empty_def : (∅ : Set α) = { _x : α | False } :=
  rfl

@[simp, grind =, push]
/--
theorem `mem_empty_iff_false` / 定理 `mem_empty_iff_false`

English:
theorem mem_empty_iff_false
  given: (x : α)
  statement: x in (∅ : Set α) ↔ False
  proof: Iff.rfl

@[simp, grind =]

中文:
定理 mem_empty_iff_false
  条件: (x : α)
  结论: x in (∅ : Set α) ↔ False
  证明: Iff.rfl

@[simp, grind =]

Depends on / 依赖: Iff.rfl
-/
theorem mem_empty_iff_false (x : α) : x in (∅ : Set α) ↔ False :=
  Iff.rfl

@[simp, grind =]
/--
theorem `ofPred_false` / 定理 `ofPred_false`

English:
theorem ofPred_false
  statement: { _a : α | False } = ∅
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_false := ofPred_false

中文:
定理 ofPred_false
  结论: { _a : α | False } = ∅
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_false := ofPred_false
-/
theorem ofPred_false : { _a : α | False } = ∅ :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_false := ofPred_false

/--
theorem `ofPred_bot` / 定理 `ofPred_bot`

English:
theorem ofPred_bot
  statement: { _x : α | ⊥ } = ∅
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias setOf_bot := ofPred_bot

@[simp]

中文:
定理 ofPred_bot
  结论: { _x : α | ⊥ } = ∅
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias setOf_bot := ofPred_bot

@[simp]
-/
@[simp] theorem ofPred_bot : { _x : α | ⊥ } = ∅ := rfl

@[deprecated (since := "2026-07-09")]
alias setOf_bot := ofPred_bot

@[simp]
/--
theorem `empty_subset` / 定理 `empty_subset`

English:
theorem empty_subset
  given: (s : Set α)
  statement: ∅ subseteq s
  proof: nofun

@[simp, grind =]

中文:
定理 empty_subset
  条件: (s : Set α)
  结论: ∅ subseteq s
  证明: nofun

@[simp, grind =]
-/
theorem empty_subset (s : Set α) : ∅ subseteq s :=
  nofun

@[simp, grind =]
/--
theorem `subset_empty_iff` / 定理 `subset_empty_iff`

English:
theorem subset_empty_iff
  given: {s : Set α}
  statement: s subseteq ∅ ↔ s = ∅
  proof: (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm

中文:
定理 subset_empty_iff
  条件: {s : Set α}
  结论: s subseteq ∅ ↔ s = ∅
  证明: (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm

Depends on / 依赖: Subset, Subset.antisymm_iff.trans, and_iff_left, antisymm_iff, empty_subset
-/
theorem subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = ∅ :=
  (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm

/--
theorem `eq_empty_iff_forall_notMem` / 定理 `eq_empty_iff_forall_notMem`

English:
theorem eq_empty_iff_forall_notMem
  given: {s : Set α}
  statement: s = ∅ ↔ forall x, x ∉ s
  proof: subset_empty_iff.symm

中文:
定理 eq_empty_iff_forall_notMem
  条件: {s : Set α}
  结论: s = ∅ ↔ 对任意 x, x ∉ s
  证明: subset_empty_iff.symm

Depends on / 依赖: subset_empty_iff, subset_empty_iff.symm
-/
theorem eq_empty_iff_forall_notMem {s : Set α} : s = ∅ ↔ forall x, x ∉ s :=
  subset_empty_iff.symm

/--
theorem `eq_empty_of_forall_notMem` / 定理 `eq_empty_of_forall_notMem`

English:
theorem eq_empty_of_forall_notMem
  given: (h : forall x, x ∉ s)
  statement: s = ∅
  proof: subset_empty_iff.1 h

中文:
定理 eq_empty_of_forall_notMem
  条件: (h : 对任意 x, x ∉ s)
  结论: s = ∅
  证明: subset_empty_iff.1 h

Depends on / 依赖: subset_empty_iff
-/
theorem eq_empty_of_forall_notMem (h : forall x, x ∉ s) : s = ∅ :=
  subset_empty_iff.1 h

/--
theorem `eq_empty_of_subset_empty` / 定理 `eq_empty_of_subset_empty`

English:
theorem eq_empty_of_subset_empty
  given: {s : Set α}
  statement: s subseteq ∅ -> s = ∅
  proof: subset_empty_iff.1

中文:
定理 eq_empty_of_subset_empty
  条件: {s : Set α}
  结论: s subseteq ∅ -> s = ∅
  证明: subset_empty_iff.1

Depends on / 依赖: subset_empty_iff
-/
theorem eq_empty_of_subset_empty {s : Set α} : s subseteq ∅ -> s = ∅ :=
  subset_empty_iff.1

/-- See also `Set.nonempty_iff_ne_empty`. -/
@[push]
/--
theorem `not_nonempty_iff_eq_empty` / 定理 `not_nonempty_iff_eq_empty`

English:
theorem not_nonempty_iff_eq_empty
  statement: ¬s.Nonempty ↔ s = ∅
  proof: by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_notMem]

中文:
定理 not_nonempty_iff_eq_empty
  结论: ¬s.Nonempty ↔ s = ∅
  证明: by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_notMem]

Depends on / 依赖: Nonempty, Set.Nonempty, eq_empty_iff_forall_notMem, not_exists
-/
theorem not_nonempty_iff_eq_empty : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, not_exists, eq_empty_iff_forall_notMem]

/-- See also `Set.not_nonempty_iff_eq_empty`. -/
@[push ←]
/--
theorem `nonempty_iff_ne_empty` / 定理 `nonempty_iff_ne_empty`

English:
theorem nonempty_iff_ne_empty
  statement: s.Nonempty ↔ s != ∅
  proof: not_nonempty_iff_eq_empty.not_right

中文:
定理 nonempty_iff_ne_empty
  结论: s.Nonempty ↔ s != ∅
  证明: not_nonempty_iff_eq_empty.not_right

Depends on / 依赖: not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.not_right, not_right
-/
theorem nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅ :=
  not_nonempty_iff_eq_empty.not_right

/-- Variant of `nonempty_iff_ne_empty` used by `push Not`. -/
@[push ←]
/--
theorem `nonempty_iff_empty_ne` / 定理 `nonempty_iff_empty_ne`

English:
theorem nonempty_iff_empty_ne
  statement: s.Nonempty ↔ ∅ != s
  proof: nonempty_iff_ne_empty.trans ne_comm

中文:
定理 nonempty_iff_empty_ne
  结论: s.Nonempty ↔ ∅ != s
  证明: nonempty_iff_ne_empty.trans ne_comm

Depends on / 依赖: ne_comm, nonempty_iff_ne_empty, nonempty_iff_ne_empty.trans
-/
theorem nonempty_iff_empty_ne : s.Nonempty ↔ ∅ != s :=
  nonempty_iff_ne_empty.trans ne_comm

/--
theorem `not_nonempty_iff_eq_empty'` / 定理 `not_nonempty_iff_eq_empty'`

English:
theorem not_nonempty_iff_eq_empty'
  statement: ¬Nonempty s ↔ s = ∅
  proof: by
  rw [nonempty_subtype]; rw [not_exists]; rw [eq_empty_iff_forall_notMem]

中文:
定理 not_nonempty_iff_eq_empty'
  结论: ¬Nonempty s ↔ s = ∅
  证明: by
  rw [nonempty_subtype]; rw [not_exists]; rw [eq_empty_iff_forall_notMem]

Depends on / 依赖: eq_empty_iff_forall_notMem, nonempty_subtype, not_exists
-/
theorem not_nonempty_iff_eq_empty' : ¬Nonempty s ↔ s = ∅ := by
  rw [nonempty_subtype]; rw [not_exists]; rw [eq_empty_iff_forall_notMem]

/--
theorem `nonempty_iff_ne_empty'` / 定理 `nonempty_iff_ne_empty'`

English:
theorem nonempty_iff_ne_empty'
  statement: Nonempty s ↔ s != ∅
  proof: not_nonempty_iff_eq_empty'.not_right

alias ⟨Nonempty.ne_empty, _⟩ := nonempty_iff_ne_empty

@[simp]

中文:
定理 nonempty_iff_ne_empty'
  结论: Nonempty s ↔ s != ∅
  证明: not_nonempty_iff_eq_empty'.not_right

alias ⟨Nonempty.ne_empty, _⟩ := nonempty_iff_ne_empty

@[simp]

Depends on / 依赖: not_nonempty_iff_eq_empty, not_right
-/
theorem nonempty_iff_ne_empty' : Nonempty s ↔ s != ∅ :=
  not_nonempty_iff_eq_empty'.not_right

alias ⟨Nonempty.ne_empty, _⟩ := nonempty_iff_ne_empty

@[simp]
/--
theorem `not_nonempty_empty` / 定理 `not_nonempty_empty`

English:
theorem not_nonempty_empty
  statement: ¬(∅ : Set α).Nonempty
  proof: fun ⟨_, hx⟩ => hx

@[simp]

中文:
定理 not_nonempty_empty
  结论: ¬(∅ : Set α).Nonempty
  证明: fun ⟨_, hx⟩ => hx

@[simp]
-/
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun ⟨_, hx⟩ => hx

@[simp]
/--
theorem `isEmpty_coe_sort` / 定理 `isEmpty_coe_sort`

English:
theorem isEmpty_coe_sort
  given: {s : Set α}
  statement: IsEmpty (↥s) ↔ s = ∅
  proof: not_iff_not.1 by simpa using! nonempty_iff_ne_empty

中文:
定理 isEmpty_coe_sort
  条件: {s : Set α}
  结论: IsEmpty (↥s) ↔ s = ∅
  证明: not_iff_not.1 by simpa using! nonempty_iff_ne_empty

Depends on / 依赖: nonempty_iff_ne_empty, not_iff_not
-/
theorem isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = ∅ :=
not_iff_not.1 by simpa using! nonempty_iff_ne_empty

/--
lemma `eq_empty_of_isEmpty` / 引理 `eq_empty_of_isEmpty`

English:
lemma eq_empty_of_isEmpty
  given: (s : Set α) [IsEmpty s]
  statement: s = ∅
  proof: by
  simpa using ‹IsEmpty s›

中文:
引理 eq_empty_of_isEmpty
  条件: (s : Set α) [IsEmpty s]
  结论: s = ∅
  证明: by
  simpa using ‹IsEmpty s›

Depends on / 依赖: IsEmpty
-/
lemma eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s = ∅ := by
  simpa using ‹IsEmpty s›

/--
Instance `uniqueEmpty` / 实例 `uniqueEmpty`

English:
instance uniqueEmpty
  signature: [IsEmpty α]
  body: eq_empty_of_isEmpty _

中文:
实例 uniqueEmpty
  签名: [IsEmpty α]
  定义体: eq_empty_of_isEmpty _

Depends on / 依赖: eq_empty_of_isEmpty
-/
instance uniqueEmpty [IsEmpty α] : Unique (Set α) where
  uniq _ := eq_empty_of_isEmpty _

/--
theorem `eq_empty_or_nonempty` / 定理 `eq_empty_or_nonempty`

English:
theorem eq_empty_or_nonempty
  given: (s : Set α)
  statement: s = ∅ ∨ s.Nonempty
  proof: or_iff_not_imp_left.2 nonempty_iff_ne_empty.2

中文:
定理 eq_empty_or_nonempty
  条件: (s : Set α)
  结论: s = ∅ ∨ s.Nonempty
  证明: or_iff_not_imp_left.2 nonempty_iff_ne_empty.2

Depends on / 依赖: nonempty_iff_ne_empty, or_iff_not_imp_left
-/
theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 nonempty_iff_ne_empty.2

/--
theorem `subset_eq_empty` / 定理 `subset_eq_empty`

English:
theorem subset_eq_empty
  given: {s t : Set α} (h : t subseteq s) (e : s = ∅)
  statement: t = ∅
  proof: subset_empty_iff.1 e ▸ h

中文:
定理 subset_eq_empty
  条件: {s t : Set α} (h : t subseteq s) (e : s = ∅)
  结论: t = ∅
  证明: subset_empty_iff.1 e ▸ h

Depends on / 依赖: subset_empty_iff
-/
theorem subset_eq_empty {s t : Set α} (h : t subseteq s) (e : s = ∅) : t = ∅ :=
subset_empty_iff.1 e ▸ h

/--
theorem `forall_mem_empty` / 定理 `forall_mem_empty`

English:
theorem forall_mem_empty
  given: {p : α -> Prop}
  statement: (forall x in (∅ : Set α), p x) ↔ True
  proof: iff_true_intro fun _ => False.elim

中文:
定理 forall_mem_empty
  条件: {p : α -> 命题}
  结论: (对任意 x in (∅ : Set α), p x) ↔ True
  证明: iff_true_intro fun _ => False.elim

Depends on / 依赖: False.elim, iff_true_intro
-/
theorem forall_mem_empty {p : α -> Prop} : (forall x in (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun _ => False.elim

/--
theorem `Nonempty.forall_const` / 定理 `Nonempty.forall_const`

English:
theorem Nonempty.forall_const
  given: (h : s.Nonempty) {p : Prop}
  statement: (forall x in s, p) ↔ p
  proof: let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]

中文:
定理 Nonempty.forall_const
  条件: (h : s.Nonempty) {p : 命题}
  结论: (对任意 x in s, p) ↔ p
  证明: let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]
-/
theorem Nonempty.forall_const (h : s.Nonempty) {p : Prop} : (forall x in s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]
/--
theorem `forall_mem_const` / 定理 `forall_mem_const`

English:
theorem forall_mem_const
  given: {p : Prop} [Nonempty s]
  statement: (forall x in s, p) ↔ p
  proof: (nonempty_coe_sort.mp ‹_›).forall_const

中文:
定理 forall_mem_const
  条件: {p : 命题} [Nonempty s]
  结论: (对任意 x in s, p) ↔ p
  证明: (nonempty_coe_sort.mp ‹_›).forall_const

Depends on / 依赖: forall_const, nonempty_coe_sort, nonempty_coe_sort.mp
-/
theorem forall_mem_const {p : Prop} [Nonempty s] : (forall x in s, p) ↔ p :=
  (nonempty_coe_sort.mp ‹_›).forall_const

instance (α : Type u) : IsEmpty.{u + 1} (↥(∅ : Set α)) :=
  ⟨fun x => x.2⟩

@[simp]
/--
theorem `empty_ssubset` / 定理 `empty_ssubset`

English:
theorem empty_ssubset
  statement: ∅ ⊂ s ↔ s.Nonempty
  proof: (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

中文:
定理 empty_ssubset
  结论: ∅ ⊂ s ↔ s.Nonempty
  证明: (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

Depends on / 依赖: bot_lt_iff_ne_bot, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
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
/--
theorem `ofPred_true` / 定理 `ofPred_true`

English:
theorem ofPred_true
  statement: { _x : α | True } = univ
  proof: rfl

@[deprecated (since := "2026-07-09")] alias setOf_true := ofPred_true

中文:
定理 ofPred_true
  结论: { _x : α | True } = univ
  证明: rfl

@[deprecated (since := "2026-07-09")] alias setOf_true := ofPred_true
-/
theorem ofPred_true : { _x : α | True } = univ :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_true := ofPred_true

/--
theorem `ofPred_top` / 定理 `ofPred_top`

English:
theorem ofPred_top
  statement: { _x : α | ⊤ } = univ
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias setOf_top := ofPred_top

@[simp]

中文:
定理 ofPred_top
  结论: { _x : α | ⊤ } = univ
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias setOf_top := ofPred_top

@[simp]
-/
@[simp] theorem ofPred_top : { _x : α | ⊤ } = univ := rfl

@[deprecated (since := "2026-07-09")]
alias setOf_top := ofPred_top

@[simp]
/--
theorem `univ_eq_empty_iff` / 定理 `univ_eq_empty_iff`

English:
theorem univ_eq_empty_iff
  statement: (univ : Set α) = ∅ ↔ IsEmpty α
  proof: eq_empty_iff_forall_notMem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩

中文:
定理 univ_eq_empty_iff
  结论: (univ : Set α) = ∅ ↔ IsEmpty α
  证明: eq_empty_iff_forall_notMem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩

Depends on / 依赖: IsEmpty, IsEmpty.false, eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem.trans
-/
theorem univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩

/--
theorem `empty_ne_univ` / 定理 `empty_ne_univ`

English:
theorem empty_ne_univ
  given: [Nonempty α]
  statement: (∅ : Set α) != univ
  proof: fun e =>
not_isEmpty_of_nonempty α univ_eq_empty_iff.1 e.symm

@[simp, grind ←]

中文:
定理 empty_ne_univ
  条件: [Nonempty α]
  结论: (∅ : Set α) != univ
  证明: fun e =>
not_isEmpty_of_nonempty α univ_eq_empty_iff.1 e.symm

@[simp, grind ←]
-/
theorem empty_ne_univ [Nonempty α] : (∅ : Set α) != univ := fun e =>
not_isEmpty_of_nonempty α univ_eq_empty_iff.1 e.symm

@[simp, grind ←]
/--
theorem `subset_univ` / 定理 `subset_univ`

English:
theorem subset_univ
  given: (s : Set α)
  statement: s subseteq univ
  proof: fun _ _ => trivial

@[simp, grind =]

中文:
定理 subset_univ
  条件: (s : Set α)
  结论: s subseteq univ
  证明: fun _ _ => trivial

@[simp, grind =]
-/
theorem subset_univ (s : Set α) : s subseteq univ := fun _ _ => trivial

@[simp, grind =]
/--
theorem `univ_subset_iff` / 定理 `univ_subset_iff`

English:
theorem univ_subset_iff
  given: {s : Set α}
  statement: univ subseteq s ↔ s = univ
  proof: @top_le_iff _ _ _ s

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff

中文:
定理 univ_subset_iff
  条件: {s : Set α}
  结论: univ subseteq s ↔ s = univ
  证明: @top_le_iff _ _ _ s

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff

Depends on / 依赖: top_le_iff
-/
theorem univ_subset_iff {s : Set α} : univ subseteq s ↔ s = univ :=
  @top_le_iff _ _ _ s

alias ⟨eq_univ_of_univ_subset, _⟩ := univ_subset_iff

/--
theorem `eq_univ_iff_forall` / 定理 `eq_univ_iff_forall`

English:
theorem eq_univ_iff_forall
  given: {s : Set α}
  statement: s = univ ↔ forall x, x in s
  proof: univ_subset_iff.symm.trans forall_congr' fun _ => imp_iff_right trivial

中文:
定理 eq_univ_iff_forall
  条件: {s : Set α}
  结论: s = univ ↔ 对任意 x, x in s
  证明: univ_subset_iff.symm.trans forall_congr' fun _ => imp_iff_right trivial

Depends on / 依赖: forall_congr, imp_iff_right, univ_subset_iff, univ_subset_iff.symm.trans
-/
theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ forall x, x in s :=
univ_subset_iff.symm.trans forall_congr' fun _ => imp_iff_right trivial

/--
theorem `eq_univ_of_forall` / 定理 `eq_univ_of_forall`

English:
theorem eq_univ_of_forall
  given: {s : Set α}
  statement: (forall x, x in s) -> s = univ
  proof: eq_univ_iff_forall.2

中文:
定理 eq_univ_of_forall
  条件: {s : Set α}
  结论: (对任意 x, x in s) -> s = univ
  证明: eq_univ_iff_forall.2

Depends on / 依赖: eq_univ_iff_forall
-/
theorem eq_univ_of_forall {s : Set α} : (forall x, x in s) -> s = univ :=
  eq_univ_iff_forall.2

/--
theorem `Nonempty.eq_univ` / 定理 `Nonempty.eq_univ`

English:
theorem Nonempty.eq_univ
  given: [Subsingleton α]
  statement: s.Nonempty -> s = univ
  proof: by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

中文:
定理 Nonempty.eq_univ
  条件: [Subsingleton α]
  结论: s.Nonempty -> s = univ
  证明: by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

Depends on / 依赖: LieGroup, LieGroup.of_le, h.out, of_le
-/
theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty -> s = univ := by
  rintro ⟨x, hx⟩
  exact eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

/--
theorem `eq_univ_of_subset` / 定理 `eq_univ_of_subset`

English:
theorem eq_univ_of_subset
  given: {s t : Set α} (h : s subseteq t) (hs : s = univ)
  statement: t = univ
  proof: eq_univ_of_univ_subset (hs ▸ h : univ subseteq t)

中文:
定理 eq_univ_of_subset
  条件: {s t : Set α} (h : s subseteq t) (hs : s = univ)
  结论: t = univ
  证明: eq_univ_of_univ_subset (hs ▸ h : univ subseteq t)

Depends on / 依赖: LieGroup, LieGroup.of_le, eq_univ_of_univ_subset, le_top, of_le, subseteq
-/
theorem eq_univ_of_subset {s t : Set α} (h : s subseteq t) (hs : s = univ) : t = univ :=
eq_univ_of_univ_subset (hs ▸ h : univ subseteq t)

/--
theorem `exists_mem_of_nonempty` / 定理 `exists_mem_of_nonempty`

English:
theorem exists_mem_of_nonempty
  given: (α)
  statement: forall [Nonempty α], exists x : α, x in (univ : Set α)

中文:
定理 exists_mem_of_nonempty
  条件: (α)
  结论: 对任意 [Nonempty α], 存在 x : α, x in (univ : Set α)
-/
theorem exists_mem_of_nonempty (α) : forall [Nonempty α], exists x : α, x in (univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩

/--
theorem `ne_univ_iff_exists_notMem` / 定理 `ne_univ_iff_exists_notMem`

English:
theorem ne_univ_iff_exists_notMem
  given: {α : Type*} (s : Set α)
  statement: s != univ ↔ exists a, a ∉ s
  proof: by
  rw [← not_forall]; rw [← eq_univ_iff_forall]

中文:
定理 ne_univ_iff_exists_notMem
  条件: {α : 类型} (s : Set α)
  结论: s != univ ↔ 存在 a, a ∉ s
  证明: by
  rw [← not_forall]; rw [← eq_univ_iff_forall]

Depends on / 依赖: eq_univ_iff_forall, not_forall
-/
theorem ne_univ_iff_exists_notMem {α : Type*} (s : Set α) : s != univ ↔ exists a, a ∉ s := by
  rw [← not_forall]; rw [← eq_univ_iff_forall]

/--
theorem `not_subset_iff_exists_mem_notMem` / 定理 `not_subset_iff_exists_mem_notMem`

English:
theorem not_subset_iff_exists_mem_notMem
  given: {α : Type*} {s t : Set α}
  proof: by simp [subset_def]

中文:
定理 not_subset_iff_exists_mem_notMem
  条件: {α : 类型} {s t : Set α}
  证明: by simp [subset_def]

Depends on / 依赖: subset_def
-/
theorem not_subset_iff_exists_mem_notMem {α : Type*} {s t : Set α} :
    ¬s subseteq t ↔ exists x, x in s ∧ x ∉ t := by simp [subset_def]

/--
theorem `univ_unique` / 定理 `univ_unique`

English:
theorem univ_unique
  given: [Unique α]
  statement: @Set.univ α = {default}
  proof: Set.ext fun x => iff_of_true trivial Subsingleton.elim x default

中文:
定理 univ_unique
  条件: [Unique α]
  结论: @Set.univ α = {default}
  证明: Set.ext fun x => iff_of_true trivial Subsingleton.elim x default

Depends on / 依赖: Set.ext, Subsingleton, Subsingleton.elim, iff_of_true
-/
theorem univ_unique [Unique α] : @Set.univ α = {default} :=
Set.ext fun x => iff_of_true trivial Subsingleton.elim x default

/--
theorem `ssubset_univ_iff` / 定理 `ssubset_univ_iff`

English:
theorem ssubset_univ_iff
  statement: s ⊂ univ ↔ s != univ
  proof: lt_top_iff_ne_top

中文:
定理 ssubset_univ_iff
  结论: s ⊂ univ ↔ s != univ
  证明: lt_top_iff_ne_top

Depends on / 依赖: lt_top_iff_ne_top
-/
theorem ssubset_univ_iff : s ⊂ univ ↔ s != univ :=
  lt_top_iff_ne_top

/--
theorem `ssubset_univ_iff_nonempty_compl` / 定理 `ssubset_univ_iff_nonempty_compl`

English:
theorem ssubset_univ_iff_nonempty_compl
  statement: s ⊂ univ ↔ sᶜ.Nonempty
  proof: by
  rw [ssubset_def]; rw [Set.not_univ_subset]; rw [Set.nonempty_def]
  simp

alias ⟨_, Nonempty.ssubset_univ⟩ := ssubset_univ_iff_nonempty_compl

中文:
定理 ssubset_univ_iff_nonempty_compl
  结论: s ⊂ univ ↔ sᶜ.Nonempty
  证明: by
  rw [ssubset_def]; rw [Set.not_univ_subset]; rw [Set.nonempty_def]
  simp

alias ⟨_, Nonempty.ssubset_univ⟩ := ssubset_univ_iff_nonempty_compl

Depends on / 依赖: Set.nonempty_def, Set.not_univ_subset, nonempty_def, not_univ_subset, ssubset_def
-/
theorem ssubset_univ_iff_nonempty_compl : s ⊂ univ ↔ sᶜ.Nonempty := by
  rw [ssubset_def]; rw [Set.not_univ_subset]; rw [Set.nonempty_def]
  simp

alias ⟨_, Nonempty.ssubset_univ⟩ := ssubset_univ_iff_nonempty_compl

/--
theorem `compl_ssubset_univ` / 定理 `compl_ssubset_univ`

English:
theorem compl_ssubset_univ
  statement: sᶜ ⊂ univ ↔ s.Nonempty
  proof: by
  rw [ssubset_def]; rw [Set.not_univ_subset]; rw [Set.nonempty_def]
  simp

alias ⟨_, Nonempty.compl_ssubset_univ⟩ := compl_ssubset_univ

中文:
定理 compl_ssubset_univ
  结论: sᶜ ⊂ univ ↔ s.Nonempty
  证明: by
  rw [ssubset_def]; rw [Set.not_univ_subset]; rw [Set.nonempty_def]
  simp

alias ⟨_, Nonempty.compl_ssubset_univ⟩ := compl_ssubset_univ

Depends on / 依赖: Set.nonempty_def, Set.not_univ_subset, nonempty_def, not_univ_subset, ssubset_def
-/
theorem compl_ssubset_univ : sᶜ ⊂ univ ↔ s.Nonempty := by
  rw [ssubset_def]; rw [Set.not_univ_subset]; rw [Set.nonempty_def]
  simp

alias ⟨_, Nonempty.compl_ssubset_univ⟩ := compl_ssubset_univ

/--
Instance `nontrivial_of_nonempty` / 实例 `nontrivial_of_nonempty`

English:
instance nontrivial_of_nonempty
  signature: [Nonempty α]
  body: ⟨⟨∅, univ, empty_ne_univ⟩⟩

中文:
实例 nontrivial_of_nonempty
  签名: [Nonempty α]
  定义体: ⟨⟨∅, univ, empty_ne_univ⟩⟩

Depends on / 依赖: empty_ne_univ
-/
instance nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α) :=
  ⟨⟨∅, univ, empty_ne_univ⟩⟩


/--
theorem `union_def` / 定理 `union_def`

English:
theorem union_def
  given: {s₁ s₂ : Set α}
  statement: s₁ union s₂ = { a | a in s₁ ∨ a in s₂ }
  proof: rfl

中文:
定理 union_def
  条件: {s₁ s₂ : Set α}
  结论: s₁ union s₂ = { a | a in s₁ ∨ a in s₂ }
  证明: rfl
-/
theorem union_def {s₁ s₂ : Set α} : s₁ union s₂ = { a | a in s₁ ∨ a in s₂ } :=
  rfl

/--
theorem `mem_union_left` / 定理 `mem_union_left`

English:
theorem mem_union_left
  given: {x : α} {a : Set α} (b : Set α)
  statement: x in a -> x in a union b
  proof: Or.inl

中文:
定理 mem_union_left
  条件: {x : α} {a : Set α} (b : Set α)
  结论: x in a -> x in a union b
  证明: Or.inl

Depends on / 依赖: Or.inl
-/
theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x in a -> x in a union b :=
  Or.inl

/--
theorem `mem_union_right` / 定理 `mem_union_right`

English:
theorem mem_union_right
  given: {x : α} {b : Set α} (a : Set α)
  statement: x in b -> x in a union b
  proof: Or.inr

中文:
定理 mem_union_right
  条件: {x : α} {b : Set α} (a : Set α)
  结论: x in b -> x in a union b
  证明: Or.inr

Depends on / 依赖: Or.inr
-/
theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x in b -> x in a union b :=
  Or.inr

/--
theorem `mem_or_mem_of_mem_union` / 定理 `mem_or_mem_of_mem_union`

English:
theorem mem_or_mem_of_mem_union
  given: {x : α} {a b : Set α} (H : x in a union b)
  statement: x in a ∨ x in b
  proof: H

中文:
定理 mem_or_mem_of_mem_union
  条件: {x : α} {a b : Set α} (H : x in a union b)
  结论: x in a ∨ x in b
  证明: H
-/
theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x in a union b) : x in a ∨ x in b :=
  H

/--
theorem `MemUnion.elim` / 定理 `MemUnion.elim`

English:
theorem MemUnion.elim
  statement: {x : α} {a b : Set α} {P : Prop} (H₁ : x in a union b) (H₂ : x in a -> P)
  proof: Or.elim H₁ H₂ H₃

@[simp, grind =, push]

中文:
定理 MemUnion.elim
  结论: {x : α} {a b : Set α} {P : 命题} (H₁ : x in a union b) (H₂ : x in a -> P)
  证明: Or.elim H₁ H₂ H₃

@[simp, grind =, push]

Depends on / 依赖: Or.elim
-/
theorem MemUnion.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x in a union b) (H₂ : x in a -> P)
    (H₃ : x in b -> P) : P :=
  Or.elim H₁ H₂ H₃

@[simp, grind =, push]
/--
theorem `mem_union` / 定理 `mem_union`

English:
theorem mem_union
  given: (x : α) (a b : Set α)
  statement: x in a union b ↔ x in a ∨ x in b
  proof: Iff.rfl

@[simp]

中文:
定理 mem_union
  条件: (x : α) (a b : Set α)
  结论: x in a union b ↔ x in a ∨ x in b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a ∨ x in b :=
  Iff.rfl

@[simp]
/--
theorem `union_self` / 定理 `union_self`

English:
theorem union_self
  given: (a : Set α)
  statement: a union a = a
  proof: ext fun _ => or_self_iff

@[simp]

中文:
定理 union_self
  条件: (a : Set α)
  结论: a union a = a
  证明: ext fun _ => or_self_iff

@[simp]

Depends on / 依赖: ContMDiffAt, Inv.inv, contDiffAt_inv, contMDiffAt_iff_contDiffAt, or_self_iff
-/
theorem union_self (a : Set α) : a union a = a :=
  ext fun _ => or_self_iff

@[simp]
/--
theorem `union_empty` / 定理 `union_empty`

English:
theorem union_empty
  given: (a : Set α)
  statement: a union ∅ = a
  proof: ext fun _ => iff_of_eq (or_false _)

@[simp]

中文:
定理 union_empty
  条件: (a : Set α)
  结论: a union ∅ = a
  证明: ext fun _ => iff_of_eq (or_false _)

@[simp]

Depends on / 依赖: h.out, iff_of_eq, of_le, or_false
-/
theorem union_empty (a : Set α) : a union ∅ = a :=
  ext fun _ => iff_of_eq (or_false _)

@[simp]
/--
theorem `empty_union` / 定理 `empty_union`

English:
theorem empty_union
  given: (a : Set α)
  statement: ∅ union a = a
  proof: ext fun _ => iff_of_eq (false_or _)

中文:
定理 empty_union
  条件: (a : Set α)
  结论: ∅ union a = a
  证明: ext fun _ => iff_of_eq (false_or _)

Depends on / 依赖: false_or, iff_of_eq, le_top, of_le
-/
theorem empty_union (a : Set α) : ∅ union a = a :=
  ext fun _ => iff_of_eq (false_or _)

/--
theorem `union_comm` / 定理 `union_comm`

English:
theorem union_comm
  given: (a b : Set α)
  statement: a union b = b union a
  proof: ext fun _ => or_comm

中文:
定理 union_comm
  条件: (a b : Set α)
  结论: a union b = b union a
  证明: ext fun _ => or_comm

Depends on / 依赖: or_comm
-/
theorem union_comm (a b : Set α) : a union b = b union a :=
  ext fun _ => or_comm

/--
theorem `union_assoc` / 定理 `union_assoc`

English:
theorem union_assoc
  given: (a b c : Set α)
  statement: a union b union c = a union (b union c)
  proof: ext fun _ => or_assoc

中文:
定理 union_assoc
  条件: (a b c : Set α)
  结论: a union b union c = a union (b union c)
  证明: ext fun _ => or_assoc

Depends on / 依赖: or_assoc
-/
theorem union_assoc (a b c : Set α) : a union b union c = a union (b union c) :=
  ext fun _ => or_assoc

/--
Instance `union_isAssoc` / 实例 `union_isAssoc`

English:
instance union_isAssoc
  signature: : Std.Associative (α := Set α) (· union ·)
  body: ⟨union_assoc⟩

中文:
实例 union_isAssoc
  签名: : Std.Associative (α := Set α) (· union ·)
  定义体: ⟨union_assoc⟩
-/
instance union_isAssoc : Std.Associative (α := Set α) (· union ·) :=
  ⟨union_assoc⟩

/--
Instance `union_isComm` / 实例 `union_isComm`

English:
instance union_isComm
  signature: : Std.Commutative (α := Set α) (· union ·)
  body: ⟨union_comm⟩

中文:
实例 union_isComm
  签名: : Std.Commutative (α := Set α) (· union ·)
  定义体: ⟨union_comm⟩
-/
instance union_isComm : Std.Commutative (α := Set α) (· union ·) :=
  ⟨union_comm⟩

/--
theorem `union_left_comm` / 定理 `union_left_comm`

English:
theorem union_left_comm
  given: (s₁ s₂ s₃ : Set α)
  statement: s₁ union (s₂ union s₃) = s₂ union (s₁ union s₃)
  proof: ext fun _ => or_left_comm

中文:
定理 union_left_comm
  条件: (s₁ s₂ s₃ : Set α)
  结论: s₁ union (s₂ union s₃) = s₂ union (s₁ union s₃)
  证明: ext fun _ => or_left_comm

Depends on / 依赖: or_left_comm
-/
theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ union (s₂ union s₃) = s₂ union (s₁ union s₃) :=
  ext fun _ => or_left_comm

/--
theorem `union_right_comm` / 定理 `union_right_comm`

English:
theorem union_right_comm
  given: (s₁ s₂ s₃ : Set α)
  statement: s₁ union s₂ union s₃ = s₁ union s₃ union s₂
  proof: ext fun _ => or_right_comm

@[simp]

中文:
定理 union_right_comm
  条件: (s₁ s₂ s₃ : Set α)
  结论: s₁ union s₂ union s₃ = s₁ union s₃ union s₂
  证明: ext fun _ => or_right_comm

@[simp]

Depends on / 依赖: or_right_comm
-/
theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ union s₂ union s₃ = s₁ union s₃ union s₂ :=
  ext fun _ => or_right_comm

@[simp]
/--
theorem `union_eq_left` / 定理 `union_eq_left`

English:
theorem union_eq_left
  given: {s t : Set α}
  statement: s union t = s ↔ t subseteq s
  proof: sup_eq_left

@[simp]

中文:
定理 union_eq_left
  条件: {s t : Set α}
  结论: s union t = s ↔ t subseteq s
  证明: sup_eq_left

@[simp]

Depends on / 依赖: sup_eq_left
-/
theorem union_eq_left {s t : Set α} : s union t = s ↔ t subseteq s :=
  sup_eq_left

@[simp]
/--
theorem `union_eq_right` / 定理 `union_eq_right`

English:
theorem union_eq_right
  given: {s t : Set α}
  statement: s union t = t ↔ s subseteq t
  proof: sup_eq_right

中文:
定理 union_eq_right
  条件: {s t : Set α}
  结论: s union t = t ↔ s subseteq t
  证明: sup_eq_right

Depends on / 依赖: sup_eq_right
-/
theorem union_eq_right {s t : Set α} : s union t = t ↔ s subseteq t :=
  sup_eq_right

/--
theorem `union_eq_self_of_subset_left` / 定理 `union_eq_self_of_subset_left`

English:
theorem union_eq_self_of_subset_left
  given: {s t : Set α} (h : s subseteq t)
  statement: s union t = t
  proof: union_eq_right.mpr h

中文:
定理 union_eq_self_of_subset_left
  条件: {s t : Set α} (h : s subseteq t)
  结论: s union t = t
  证明: union_eq_right.mpr h

Depends on / 依赖: union_eq_right, union_eq_right.mpr
-/
theorem union_eq_self_of_subset_left {s t : Set α} (h : s subseteq t) : s union t = t :=
  union_eq_right.mpr h

/--
theorem `union_eq_self_of_subset_right` / 定理 `union_eq_self_of_subset_right`

English:
theorem union_eq_self_of_subset_right
  given: {s t : Set α} (h : t subseteq s)
  statement: s union t = s
  proof: union_eq_left.mpr h

@[simp]

中文:
定理 union_eq_self_of_subset_right
  条件: {s t : Set α} (h : t subseteq s)
  结论: s union t = s
  证明: union_eq_left.mpr h

@[simp]

Depends on / 依赖: union_eq_left, union_eq_left.mpr
-/
theorem union_eq_self_of_subset_right {s t : Set α} (h : t subseteq s) : s union t = s :=
  union_eq_left.mpr h

@[simp]
/--
theorem `subset_union_left` / 定理 `subset_union_left`

English:
theorem subset_union_left
  given: {s t : Set α}
  statement: s subseteq s union t
  proof: fun _ => Or.inl

@[simp]

中文:
定理 subset_union_left
  条件: {s t : Set α}
  结论: s subseteq s union t
  证明: fun _ => Or.inl

@[simp]

Depends on / 依赖: Or.inl
-/
theorem subset_union_left {s t : Set α} : s subseteq s union t := fun _ => Or.inl

@[simp]
/--
theorem `subset_union_right` / 定理 `subset_union_right`

English:
theorem subset_union_right
  given: {s t : Set α}
  statement: t subseteq s union t
  proof: fun _ => Or.inr

中文:
定理 subset_union_right
  条件: {s t : Set α}
  结论: t subseteq s union t
  证明: fun _ => Or.inr

Depends on / 依赖: Or.inr
-/
theorem subset_union_right {s t : Set α} : t subseteq s union t := fun _ => Or.inr

/--
theorem `union_subset` / 定理 `union_subset`

English:
theorem union_subset
  given: {s t r : Set α} (sr : s subseteq r) (tr : t subseteq r)
  statement: s union t subseteq r
  proof: fun _ =>
  Or.rec (@sr _) (@tr _)

@[simp]

中文:
定理 union_subset
  条件: {s t r : Set α} (sr : s subseteq r) (tr : t subseteq r)
  结论: s union t subseteq r
  证明: fun _ =>
  Or.rec (@sr _) (@tr _)

@[simp]
-/
theorem union_subset {s t r : Set α} (sr : s subseteq r) (tr : t subseteq r) : s union t subseteq r := fun _ =>
  Or.rec (@sr _) (@tr _)

@[simp]
/--
theorem `union_subset_iff` / 定理 `union_subset_iff`

English:
theorem union_subset_iff
  given: {s t u : Set α}
  statement: s union t subseteq u ↔ s subseteq u ∧ t subseteq u
  proof: (forall_congr' fun _ => or_imp).trans forall_and

@[gcongr]

中文:
定理 union_subset_iff
  条件: {s t u : Set α}
  结论: s union t subseteq u ↔ s subseteq u ∧ t subseteq u
  证明: (forall_congr' fun _ => or_imp).trans forall_and

@[gcongr]

Depends on / 依赖: ContMDiffMul, ContMDiffMul.of_le, forall_and, forall_congr, h.out, of_le, or_imp
-/
theorem union_subset_iff {s t u : Set α} : s union t subseteq u ↔ s subseteq u ∧ t subseteq u :=
  (forall_congr' fun _ => or_imp).trans forall_and

@[gcongr]
/--
theorem `union_subset_union` / 定理 `union_subset_union`

English:
theorem union_subset_union
  given: {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq s₂) (h₂ : t₁ subseteq t₂)
  proof: sup_le_sup h₁ h₂

中文:
定理 union_subset_union
  条件: {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq s₂) (h₂ : t₁ subseteq t₂)
  证明: sup_le_sup h₁ h₂

Depends on / 依赖: ContMDiffMul, ContMDiffMul.of_le, le_top, of_le, sup_le_sup
-/
theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq s₂) (h₂ : t₁ subseteq t₂) :
    s₁ union t₁ subseteq s₂ union t₂ :=
  sup_le_sup h₁ h₂

/--
theorem `union_subset_union_left` / 定理 `union_subset_union_left`

English:
theorem union_subset_union_left
  given: {s₁ s₂ : Set α} (t) (h : s₁ subseteq s₂)
  statement: s₁ union t subseteq s₂ union t
  proof: union_subset_union h Subset.rfl

中文:
定理 union_subset_union_left
  条件: {s₁ s₂ : Set α} (t) (h : s₁ subseteq s₂)
  结论: s₁ union t subseteq s₂ union t
  证明: union_subset_union h Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, union_subset_union
-/
theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t :=
  union_subset_union h Subset.rfl

/--
theorem `union_subset_union_right` / 定理 `union_subset_union_right`

English:
theorem union_subset_union_right
  given: (s) {t₁ t₂ : Set α} (h : t₁ subseteq t₂)
  statement: s union t₁ subseteq s union t₂
  proof: union_subset_union Subset.rfl h

中文:
定理 union_subset_union_right
  条件: (s) {t₁ t₂ : Set α} (h : t₁ subseteq t₂)
  结论: s union t₁ subseteq s union t₂
  证明: union_subset_union Subset.rfl h

Depends on / 依赖: Subset, Subset.rfl, union_subset_union
-/
theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂ :=
  union_subset_union Subset.rfl h

/--
theorem `subset_union_of_subset_left` / 定理 `subset_union_of_subset_left`

English:
theorem subset_union_of_subset_left
  given: {s t : Set α} (h : s subseteq t) (u : Set α)
  statement: s subseteq t union u
  proof: h.trans subset_union_left

中文:
定理 subset_union_of_subset_left
  条件: {s t : Set α} (h : s subseteq t) (u : Set α)
  结论: s subseteq t union u
  证明: h.trans subset_union_left

Depends on / 依赖: h.trans, subset_union_left
-/
theorem subset_union_of_subset_left {s t : Set α} (h : s subseteq t) (u : Set α) : s subseteq t union u :=
  h.trans subset_union_left

/--
theorem `subset_union_of_subset_right` / 定理 `subset_union_of_subset_right`

English:
theorem subset_union_of_subset_right
  given: {s u : Set α} (h : s subseteq u) (t : Set α)
  statement: s subseteq t union u
  proof: h.trans subset_union_right

中文:
定理 subset_union_of_subset_right
  条件: {s u : Set α} (h : s subseteq u) (t : Set α)
  结论: s subseteq t union u
  证明: h.trans subset_union_right

Depends on / 依赖: h.trans, subset_union_right
-/
theorem subset_union_of_subset_right {s u : Set α} (h : s subseteq u) (t : Set α) : s subseteq t union u :=
  h.trans subset_union_right

/--
theorem `union_congr_left` / 定理 `union_congr_left`

English:
theorem union_congr_left
  given: (ht : t subseteq s union u) (hu : u subseteq s union t)
  statement: s union t = s union u
  proof: sup_congr_left ht hu

中文:
定理 union_congr_left
  条件: (ht : t subseteq s union u) (hu : u subseteq s union t)
  结论: s union t = s union u
  证明: sup_congr_left ht hu

Depends on / 依赖: sup_congr_left
-/
theorem union_congr_left (ht : t subseteq s union u) (hu : u subseteq s union t) : s union t = s union u :=
  sup_congr_left ht hu

/--
theorem `union_congr_right` / 定理 `union_congr_right`

English:
theorem union_congr_right
  given: (hs : s subseteq t union u) (ht : t subseteq s union u)
  statement: s union u = t union u
  proof: sup_congr_right hs ht

中文:
定理 union_congr_right
  条件: (hs : s subseteq t union u) (ht : t subseteq s union u)
  结论: s union u = t union u
  证明: sup_congr_right hs ht

Depends on / 依赖: sup_congr_right
-/
theorem union_congr_right (hs : s subseteq t union u) (ht : t subseteq s union u) : s union u = t union u :=
  sup_congr_right hs ht

/--
theorem `union_eq_union_iff_left` / 定理 `union_eq_union_iff_left`

English:
theorem union_eq_union_iff_left
  statement: s union t = s union u ↔ t subseteq s union u ∧ u subseteq s union t
  proof: sup_eq_sup_iff_left

中文:
定理 union_eq_union_iff_left
  结论: s union t = s union u ↔ t subseteq s union u ∧ u subseteq s union t
  证明: sup_eq_sup_iff_left

Depends on / 依赖: sup_eq_sup_iff_left
-/
theorem union_eq_union_iff_left : s union t = s union u ↔ t subseteq s union u ∧ u subseteq s union t :=
  sup_eq_sup_iff_left

/--
theorem `union_eq_union_iff_right` / 定理 `union_eq_union_iff_right`

English:
theorem union_eq_union_iff_right
  statement: s union u = t union u ↔ s subseteq t union u ∧ t subseteq s union u
  proof: sup_eq_sup_iff_right

@[simp]

中文:
定理 union_eq_union_iff_right
  结论: s union u = t union u ↔ s subseteq t union u ∧ t subseteq s union u
  证明: sup_eq_sup_iff_right

@[simp]

Depends on / 依赖: sup_eq_sup_iff_right
-/
theorem union_eq_union_iff_right : s union u = t union u ↔ s subseteq t union u ∧ t subseteq s union u :=
  sup_eq_sup_iff_right

@[simp]
/--
theorem `union_empty_iff` / 定理 `union_empty_iff`

English:
theorem union_empty_iff
  given: {s t : Set α}
  statement: s union t = ∅ ↔ s = ∅ ∧ t = ∅
  proof: by
  simp only [← subset_empty_iff]
  exact union_subset_iff

@[simp]

中文:
定理 union_empty_iff
  条件: {s t : Set α}
  结论: s union t = ∅ ↔ s = ∅ ∧ t = ∅
  证明: by
  simp only [← subset_empty_iff]
  exact union_subset_iff

@[simp]

Depends on / 依赖: subset_empty_iff, union_subset_iff
-/
theorem union_empty_iff {s t : Set α} : s union t = ∅ ↔ s = ∅ ∧ t = ∅ := by
  simp only [← subset_empty_iff]
  exact union_subset_iff

@[simp]
/--
theorem `union_univ` / 定理 `union_univ`

English:
theorem union_univ
  given: (s : Set α)
  statement: s union univ = univ
  proof: sup_top_eq _

@[simp]

中文:
定理 union_univ
  条件: (s : Set α)
  结论: s union univ = univ
  证明: sup_top_eq _

@[simp]

Depends on / 依赖: sup_top_eq
-/
theorem union_univ (s : Set α) : s union univ = univ := sup_top_eq _

@[simp]
/--
theorem `univ_union` / 定理 `univ_union`

English:
theorem univ_union
  given: (s : Set α)
  statement: univ union s = univ
  proof: top_sup_eq _

@[simp]

中文:
定理 univ_union
  条件: (s : Set α)
  结论: univ union s = univ
  证明: top_sup_eq _

@[simp]

Depends on / 依赖: top_sup_eq
-/
theorem univ_union (s : Set α) : univ union s = univ := top_sup_eq _

@[simp]
/--
theorem `ssubset_union_left_iff` / 定理 `ssubset_union_left_iff`

English:
theorem ssubset_union_left_iff
  statement: s ⊂ s union t ↔ ¬ t subseteq s
  proof: left_lt_sup

@[simp]

中文:
定理 ssubset_union_left_iff
  结论: s ⊂ s union t ↔ ¬ t subseteq s
  证明: left_lt_sup

@[simp]

Depends on / 依赖: left_lt_sup
-/
theorem ssubset_union_left_iff : s ⊂ s union t ↔ ¬ t subseteq s :=
  left_lt_sup

@[simp]
/--
theorem `ssubset_union_right_iff` / 定理 `ssubset_union_right_iff`

English:
theorem ssubset_union_right_iff
  statement: t ⊂ s union t ↔ ¬ s subseteq t
  proof: right_lt_sup

中文:
定理 ssubset_union_right_iff
  结论: t ⊂ s union t ↔ ¬ s subseteq t
  证明: right_lt_sup

Depends on / 依赖: right_lt_sup
-/
theorem ssubset_union_right_iff : t ⊂ s union t ↔ ¬ s subseteq t :=
  right_lt_sup


/--
theorem `inter_def` / 定理 `inter_def`

English:
theorem inter_def
  given: {s₁ s₂ : Set α}
  statement: s₁ inter s₂ = { a | a in s₁ ∧ a in s₂ }
  proof: rfl

@[simp, mfld_simps, grind =, push]

中文:
定理 inter_def
  条件: {s₁ s₂ : Set α}
  结论: s₁ inter s₂ = { a | a in s₁ ∧ a in s₂ }
  证明: rfl

@[simp, mfld_simps, grind =, push]
-/
theorem inter_def {s₁ s₂ : Set α} : s₁ inter s₂ = { a | a in s₁ ∧ a in s₂ } :=
  rfl

@[simp, mfld_simps, grind =, push]
/--
theorem `mem_inter_iff` / 定理 `mem_inter_iff`

English:
theorem mem_inter_iff
  given: (x : α) (a b : Set α)
  statement: x in a inter b ↔ x in a ∧ x in b
  proof: Iff.rfl

中文:
定理 mem_inter_iff
  条件: (x : α) (a b : Set α)
  结论: x in a inter b ↔ x in a ∧ x in b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inter_iff (x : α) (a b : Set α) : x in a inter b ↔ x in a ∧ x in b :=
  Iff.rfl

/--
theorem `mem_inter` / 定理 `mem_inter`

English:
theorem mem_inter
  given: {x : α} {a b : Set α} (ha : x in a) (hb : x in b)
  statement: x in a inter b
  proof: ⟨ha, hb⟩

中文:
定理 mem_inter
  条件: {x : α} {a b : Set α} (ha : x in a) (hb : x in b)
  结论: x in a inter b
  证明: ⟨ha, hb⟩
-/
theorem mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in b) : x in a inter b :=
  ⟨ha, hb⟩

/--
theorem `mem_of_mem_inter_left` / 定理 `mem_of_mem_inter_left`

English:
theorem mem_of_mem_inter_left
  given: {x : α} {a b : Set α} (h : x in a inter b)
  statement: x in a
  proof: h.left

中文:
定理 mem_of_mem_inter_left
  条件: {x : α} {a b : Set α} (h : x in a inter b)
  结论: x in a
  证明: h.left

Depends on / 依赖: h.left
-/
theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x in a inter b) : x in a :=
  h.left

/--
theorem `mem_of_mem_inter_right` / 定理 `mem_of_mem_inter_right`

English:
theorem mem_of_mem_inter_right
  given: {x : α} {a b : Set α} (h : x in a inter b)
  statement: x in b
  proof: h.right

@[simp]

中文:
定理 mem_of_mem_inter_right
  条件: {x : α} {a b : Set α} (h : x in a inter b)
  结论: x in b
  证明: h.right

@[simp]

Depends on / 依赖: h.right
-/
theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x in a inter b) : x in b :=
  h.right

@[simp]
/--
theorem `inter_self` / 定理 `inter_self`

English:
theorem inter_self
  given: (a : Set α)
  statement: a inter a = a
  proof: ext fun _ => and_self_iff

@[simp]

中文:
定理 inter_self
  条件: (a : Set α)
  结论: a inter a = a
  证明: ext fun _ => and_self_iff

@[simp]

Depends on / 依赖: and_self_iff
-/
theorem inter_self (a : Set α) : a inter a = a :=
  ext fun _ => and_self_iff

@[simp]
/--
theorem `inter_empty` / 定理 `inter_empty`

English:
theorem inter_empty
  given: (a : Set α)
  statement: a inter ∅ = ∅
  proof: ext fun _ => iff_of_eq (and_false _)

@[simp]

中文:
定理 inter_empty
  条件: (a : Set α)
  结论: a inter ∅ = ∅
  证明: ext fun _ => iff_of_eq (and_false _)

@[simp]

Depends on / 依赖: and_false, iff_of_eq
-/
theorem inter_empty (a : Set α) : a inter ∅ = ∅ :=
  ext fun _ => iff_of_eq (and_false _)

@[simp]
/--
theorem `empty_inter` / 定理 `empty_inter`

English:
theorem empty_inter
  given: (a : Set α)
  statement: ∅ inter a = ∅
  proof: ext fun _ => iff_of_eq (false_and _)

中文:
定理 empty_inter
  条件: (a : Set α)
  结论: ∅ inter a = ∅
  证明: ext fun _ => iff_of_eq (false_and _)

Depends on / 依赖: false_and, iff_of_eq
-/
theorem empty_inter (a : Set α) : ∅ inter a = ∅ :=
  ext fun _ => iff_of_eq (false_and _)

/--
theorem `inter_comm` / 定理 `inter_comm`

English:
theorem inter_comm
  given: (a b : Set α)
  statement: a inter b = b inter a
  proof: ext fun _ => and_comm

中文:
定理 inter_comm
  条件: (a b : Set α)
  结论: a inter b = b inter a
  证明: ext fun _ => and_comm

Depends on / 依赖: and_comm
-/
theorem inter_comm (a b : Set α) : a inter b = b inter a :=
  ext fun _ => and_comm

/--
theorem `inter_assoc` / 定理 `inter_assoc`

English:
theorem inter_assoc
  given: (a b c : Set α)
  statement: a inter b inter c = a inter (b inter c)
  proof: ext fun _ => and_assoc

中文:
定理 inter_assoc
  条件: (a b c : Set α)
  结论: a inter b inter c = a inter (b inter c)
  证明: ext fun _ => and_assoc

Depends on / 依赖: and_assoc
-/
theorem inter_assoc (a b c : Set α) : a inter b inter c = a inter (b inter c) :=
  ext fun _ => and_assoc

/--
Instance `inter_isAssoc` / 实例 `inter_isAssoc`

English:
instance inter_isAssoc
  signature: : Std.Associative (α := Set α) (· inter ·)
  body: ⟨inter_assoc⟩

中文:
实例 inter_isAssoc
  签名: : Std.Associative (α := Set α) (· inter ·)
  定义体: ⟨inter_assoc⟩
-/
instance inter_isAssoc : Std.Associative (α := Set α) (· inter ·) :=
  ⟨inter_assoc⟩

/--
Instance `inter_isComm` / 实例 `inter_isComm`

English:
instance inter_isComm
  signature: : Std.Commutative (α := Set α) (· inter ·)
  body: ⟨inter_comm⟩

中文:
实例 inter_isComm
  签名: : Std.Commutative (α := Set α) (· inter ·)
  定义体: ⟨inter_comm⟩
-/
instance inter_isComm : Std.Commutative (α := Set α) (· inter ·) :=
  ⟨inter_comm⟩

/--
theorem `inter_left_comm` / 定理 `inter_left_comm`

English:
theorem inter_left_comm
  given: (s₁ s₂ s₃ : Set α)
  statement: s₁ inter (s₂ inter s₃) = s₂ inter (s₁ inter s₃)
  proof: ext fun _ => and_left_comm

中文:
定理 inter_left_comm
  条件: (s₁ s₂ s₃ : Set α)
  结论: s₁ inter (s₂ inter s₃) = s₂ inter (s₁ inter s₃)
  证明: ext fun _ => and_left_comm

Depends on / 依赖: and_left_comm
-/
theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ inter s₃) = s₂ inter (s₁ inter s₃) :=
  ext fun _ => and_left_comm

/--
theorem `inter_right_comm` / 定理 `inter_right_comm`

English:
theorem inter_right_comm
  given: (s₁ s₂ s₃ : Set α)
  statement: s₁ inter s₂ inter s₃ = s₁ inter s₃ inter s₂
  proof: ext fun _ => and_right_comm

@[simp, mfld_simps]

中文:
定理 inter_right_comm
  条件: (s₁ s₂ s₃ : Set α)
  结论: s₁ inter s₂ inter s₃ = s₁ inter s₃ inter s₂
  证明: ext fun _ => and_right_comm

@[simp, mfld_simps]

Depends on / 依赖: and_right_comm
-/
theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ inter s₃ = s₁ inter s₃ inter s₂ :=
  ext fun _ => and_right_comm

@[simp, mfld_simps]
/--
theorem `inter_subset_left` / 定理 `inter_subset_left`

English:
theorem inter_subset_left
  given: {s t : Set α}
  statement: s inter t subseteq s
  proof: fun _ => And.left

@[simp]

中文:
定理 inter_subset_left
  条件: {s t : Set α}
  结论: s inter t subseteq s
  证明: fun _ => And.left

@[simp]

Depends on / 依赖: And.left
-/
theorem inter_subset_left {s t : Set α} : s inter t subseteq s := fun _ => And.left

@[simp]
/--
theorem `inter_subset_right` / 定理 `inter_subset_right`

English:
theorem inter_subset_right
  given: {s t : Set α}
  statement: s inter t subseteq t
  proof: fun _ => And.right

中文:
定理 inter_subset_right
  条件: {s t : Set α}
  结论: s inter t subseteq t
  证明: fun _ => And.right

Depends on / 依赖: And.right
-/
theorem inter_subset_right {s t : Set α} : s inter t subseteq t := fun _ => And.right

/--
theorem `subset_inter` / 定理 `subset_inter`

English:
theorem subset_inter
  given: {s t r : Set α} (rs : r subseteq s) (rt : r subseteq t)
  statement: r subseteq s inter t
  proof: fun _ h =>
  ⟨rs h, rt h⟩

@[simp]

中文:
定理 subset_inter
  条件: {s t r : Set α} (rs : r subseteq s) (rt : r subseteq t)
  结论: r subseteq s inter t
  证明: fun _ h =>
  ⟨rs h, rt h⟩

@[simp]
-/
theorem subset_inter {s t r : Set α} (rs : r subseteq s) (rt : r subseteq t) : r subseteq s inter t := fun _ h =>
  ⟨rs h, rt h⟩

@[simp]
/--
theorem `subset_inter_iff` / 定理 `subset_inter_iff`

English:
theorem subset_inter_iff
  given: {s t r : Set α}
  statement: r subseteq s inter t ↔ r subseteq s ∧ r subseteq t
  proof: (forall_congr' fun _ => imp_and).trans forall_and

中文:
定理 subset_inter_iff
  条件: {s t r : Set α}
  结论: r subseteq s inter t ↔ r subseteq s ∧ r subseteq t
  证明: (forall_congr' fun _ => imp_and).trans forall_and

Depends on / 依赖: forall_and, forall_congr, imp_and
-/
theorem subset_inter_iff {s t r : Set α} : r subseteq s inter t ↔ r subseteq s ∧ r subseteq t :=
  (forall_congr' fun _ => imp_and).trans forall_and

/--
lemma `inter_eq_left` / 引理 `inter_eq_left`

English:
lemma inter_eq_left
  statement: s inter t = s ↔ s subseteq t
  proof: inf_eq_left

中文:
引理 inter_eq_left
  结论: s inter t = s ↔ s subseteq t
  证明: inf_eq_left
-/
@[simp] lemma inter_eq_left : s inter t = s ↔ s subseteq t := inf_eq_left

/--
lemma `inter_eq_right` / 引理 `inter_eq_right`

English:
lemma inter_eq_right
  statement: s inter t = t ↔ t subseteq s
  proof: inf_eq_right

中文:
引理 inter_eq_right
  结论: s inter t = t ↔ t subseteq s
  证明: inf_eq_right
-/
@[simp] lemma inter_eq_right : s inter t = t ↔ t subseteq s := inf_eq_right

/--
lemma `left_eq_inter` / 引理 `left_eq_inter`

English:
lemma left_eq_inter
  statement: s = s inter t ↔ s subseteq t
  proof: left_eq_inf

中文:
引理 left_eq_inter
  结论: s = s inter t ↔ s subseteq t
  证明: left_eq_inf
-/
@[simp] lemma left_eq_inter : s = s inter t ↔ s subseteq t := left_eq_inf

/--
lemma `right_eq_inter` / 引理 `right_eq_inter`

English:
lemma right_eq_inter
  statement: t = s inter t ↔ t subseteq s
  proof: right_eq_inf

中文:
引理 right_eq_inter
  结论: t = s inter t ↔ t subseteq s
  证明: right_eq_inf
-/
@[simp] lemma right_eq_inter : t = s inter t ↔ t subseteq s := right_eq_inf

/--
theorem `inter_eq_self_of_subset_left` / 定理 `inter_eq_self_of_subset_left`

English:
theorem inter_eq_self_of_subset_left
  given: {s t : Set α}
  statement: s subseteq t -> s inter t = s
  proof: inter_eq_left.mpr

中文:
定理 inter_eq_self_of_subset_left
  条件: {s t : Set α}
  结论: s subseteq t -> s inter t = s
  证明: inter_eq_left.mpr

Depends on / 依赖: inter_eq_left, inter_eq_left.mpr
-/
theorem inter_eq_self_of_subset_left {s t : Set α} : s subseteq t -> s inter t = s :=
  inter_eq_left.mpr

/--
theorem `inter_eq_self_of_subset_right` / 定理 `inter_eq_self_of_subset_right`

English:
theorem inter_eq_self_of_subset_right
  given: {s t : Set α}
  statement: t subseteq s -> s inter t = t
  proof: inter_eq_right.mpr

中文:
定理 inter_eq_self_of_subset_right
  条件: {s t : Set α}
  结论: t subseteq s -> s inter t = t
  证明: inter_eq_right.mpr

Depends on / 依赖: inter_eq_right, inter_eq_right.mpr
-/
theorem inter_eq_self_of_subset_right {s t : Set α} : t subseteq s -> s inter t = t :=
  inter_eq_right.mpr

/--
theorem `inter_congr_left` / 定理 `inter_congr_left`

English:
theorem inter_congr_left
  given: (ht : s inter u subseteq t) (hu : s inter t subseteq u)
  statement: s inter t = s inter u
  proof: inf_congr_left ht hu

中文:
定理 inter_congr_left
  条件: (ht : s inter u subseteq t) (hu : s inter t subseteq u)
  结论: s inter t = s inter u
  证明: inf_congr_left ht hu

Depends on / 依赖: inf_congr_left
-/
theorem inter_congr_left (ht : s inter u subseteq t) (hu : s inter t subseteq u) : s inter t = s inter u :=
  inf_congr_left ht hu

/--
theorem `inter_congr_right` / 定理 `inter_congr_right`

English:
theorem inter_congr_right
  given: (hs : t inter u subseteq s) (ht : s inter u subseteq t)
  statement: s inter u = t inter u
  proof: inf_congr_right hs ht

中文:
定理 inter_congr_right
  条件: (hs : t inter u subseteq s) (ht : s inter u subseteq t)
  结论: s inter u = t inter u
  证明: inf_congr_right hs ht

Depends on / 依赖: inf_congr_right
-/
theorem inter_congr_right (hs : t inter u subseteq s) (ht : s inter u subseteq t) : s inter u = t inter u :=
  inf_congr_right hs ht

/--
theorem `inter_eq_inter_iff_left` / 定理 `inter_eq_inter_iff_left`

English:
theorem inter_eq_inter_iff_left
  statement: s inter t = s inter u ↔ s inter u subseteq t ∧ s inter t subseteq u
  proof: inf_eq_inf_iff_left

中文:
定理 inter_eq_inter_iff_left
  结论: s inter t = s inter u ↔ s inter u subseteq t ∧ s inter t subseteq u
  证明: inf_eq_inf_iff_left

Depends on / 依赖: inf_eq_inf_iff_left
-/
theorem inter_eq_inter_iff_left : s inter t = s inter u ↔ s inter u subseteq t ∧ s inter t subseteq u :=
  inf_eq_inf_iff_left

/--
theorem `inter_eq_inter_iff_right` / 定理 `inter_eq_inter_iff_right`

English:
theorem inter_eq_inter_iff_right
  statement: s inter u = t inter u ↔ t inter u subseteq s ∧ s inter u subseteq t
  proof: inf_eq_inf_iff_right

@[simp, mfld_simps]

中文:
定理 inter_eq_inter_iff_right
  结论: s inter u = t inter u ↔ t inter u subseteq s ∧ s inter u subseteq t
  证明: inf_eq_inf_iff_right

@[simp, mfld_simps]

Depends on / 依赖: inf_eq_inf_iff_right
-/
theorem inter_eq_inter_iff_right : s inter u = t inter u ↔ t inter u subseteq s ∧ s inter u subseteq t :=
  inf_eq_inf_iff_right

@[simp, mfld_simps]
/--
theorem `inter_univ` / 定理 `inter_univ`

English:
theorem inter_univ
  given: (a : Set α)
  statement: a inter univ = a
  proof: inf_top_eq _

@[simp, mfld_simps]

中文:
定理 inter_univ
  条件: (a : Set α)
  结论: a inter univ = a
  证明: inf_top_eq _

@[simp, mfld_simps]

Depends on / 依赖: inf_top_eq
-/
theorem inter_univ (a : Set α) : a inter univ = a := inf_top_eq _

@[simp, mfld_simps]
/--
theorem `univ_inter` / 定理 `univ_inter`

English:
theorem univ_inter
  given: (a : Set α)
  statement: univ inter a = a
  proof: top_inf_eq _

@[gcongr]

中文:
定理 univ_inter
  条件: (a : Set α)
  结论: univ inter a = a
  证明: top_inf_eq _

@[gcongr]

Depends on / 依赖: top_inf_eq
-/
theorem univ_inter (a : Set α) : univ inter a = a := top_inf_eq _

@[gcongr]
/--
theorem `inter_subset_inter` / 定理 `inter_subset_inter`

English:
theorem inter_subset_inter
  given: {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq t₁) (h₂ : s₂ subseteq t₂)
  proof: inf_le_inf h₁ h₂

中文:
定理 inter_subset_inter
  条件: {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq t₁) (h₂ : s₂ subseteq t₂)
  证明: inf_le_inf h₁ h₂

Depends on / 依赖: inf_le_inf
-/
theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ subseteq t₁) (h₂ : s₂ subseteq t₂) :
    s₁ inter s₂ subseteq t₁ inter t₂ :=
  inf_le_inf h₁ h₂

/--
theorem `inter_subset_inter_left` / 定理 `inter_subset_inter_left`

English:
theorem inter_subset_inter_left
  given: {s t : Set α} (u : Set α) (H : s subseteq t)
  statement: s inter u subseteq t inter u
  proof: inter_subset_inter H Subset.rfl

中文:
定理 inter_subset_inter_left
  条件: {s t : Set α} (u : Set α) (H : s subseteq t)
  结论: s inter u subseteq t inter u
  证明: inter_subset_inter H Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, inter_subset_inter
-/
theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s subseteq t) : s inter u subseteq t inter u :=
  inter_subset_inter H Subset.rfl

/--
theorem `inter_subset_inter_right` / 定理 `inter_subset_inter_right`

English:
theorem inter_subset_inter_right
  given: {s t : Set α} (u : Set α) (H : s subseteq t)
  statement: u inter s subseteq u inter t
  proof: inter_subset_inter Subset.rfl H

中文:
定理 inter_subset_inter_right
  条件: {s t : Set α} (u : Set α) (H : s subseteq t)
  结论: u inter s subseteq u inter t
  证明: inter_subset_inter Subset.rfl H

Depends on / 依赖: Subset, Subset.rfl, inter_subset_inter
-/
theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s subseteq t) : u inter s subseteq u inter t :=
  inter_subset_inter Subset.rfl H

/--
theorem `union_inter_cancel_left` / 定理 `union_inter_cancel_left`

English:
theorem union_inter_cancel_left
  given: {s t : Set α}
  statement: (s union t) inter s = s
  proof: inter_eq_self_of_subset_right subset_union_left

中文:
定理 union_inter_cancel_left
  条件: {s t : Set α}
  结论: (s union t) inter s = s
  证明: inter_eq_self_of_subset_right subset_union_left

Depends on / 依赖: inter_eq_self_of_subset_right, subset_union_left
-/
theorem union_inter_cancel_left {s t : Set α} : (s union t) inter s = s :=
  inter_eq_self_of_subset_right subset_union_left

/--
theorem `union_inter_cancel_right` / 定理 `union_inter_cancel_right`

English:
theorem union_inter_cancel_right
  given: {s t : Set α}
  statement: (s union t) inter t = t
  proof: inter_eq_self_of_subset_right subset_union_right

中文:
定理 union_inter_cancel_right
  条件: {s t : Set α}
  结论: (s union t) inter t = t
  证明: inter_eq_self_of_subset_right subset_union_right

Depends on / 依赖: inter_eq_self_of_subset_right, subset_union_right
-/
theorem union_inter_cancel_right {s t : Set α} : (s union t) inter t = t :=
  inter_eq_self_of_subset_right subset_union_right

/--
theorem `inter_ofPred_eq_sep` / 定理 `inter_ofPred_eq_sep`

English:
theorem inter_ofPred_eq_sep
  given: (s : Set α) (p : α -> Prop)
  statement: s inter {a | p a} = {a in s | p a}
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias inter_setOf_eq_sep := inter_ofPred_eq_sep

中文:
定理 inter_ofPred_eq_sep
  条件: (s : Set α) (p : α -> 命题)
  结论: s inter {a | p a} = {a in s | p a}
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias inter_setOf_eq_sep := inter_ofPred_eq_sep
-/
theorem inter_ofPred_eq_sep (s : Set α) (p : α -> Prop) : s inter {a | p a} = {a in s | p a} :=
  rfl

@[deprecated (since := "2026-07-09")]
alias inter_setOf_eq_sep := inter_ofPred_eq_sep

/--
theorem `ofPred_inter_eq_sep` / 定理 `ofPred_inter_eq_sep`

English:
theorem ofPred_inter_eq_sep
  given: (p : α -> Prop) (s : Set α)
  statement: {a | p a} inter s = {a in s | p a}
  proof: inter_comm _ _

@[deprecated (since := "2026-07-09")] alias setOf_inter_eq_sep := ofPred_inter_eq_sep

中文:
定理 ofPred_inter_eq_sep
  条件: (p : α -> 命题) (s : Set α)
  结论: {a | p a} inter s = {a in s | p a}
  证明: inter_comm _ _

@[deprecated (since := "2026-07-09")] alias setOf_inter_eq_sep := ofPred_inter_eq_sep

Depends on / 依赖: inter_comm
-/
theorem ofPred_inter_eq_sep (p : α -> Prop) (s : Set α) : {a | p a} inter s = {a in s | p a} :=
  inter_comm _ _

@[deprecated (since := "2026-07-09")] alias setOf_inter_eq_sep := ofPred_inter_eq_sep

/--
theorem `sep_eq_inter_sep` / 定理 `sep_eq_inter_sep`

English:
theorem sep_eq_inter_sep
  given: {α : Type*} {s t : Set α} {p : α -> Prop} (hst : s subseteq t)
  proof: by
  rw [← inter_ofPred_eq_sep s p]; rw [← inter_ofPred_eq_sep t p]; rw [← inter_assoc]; rw [← left_eq_inter.mpr hst]

@[simp]

中文:
定理 sep_eq_inter_sep
  条件: {α : 类型} {s t : Set α} {p : α -> 命题} (hst : s subseteq t)
  证明: by
  rw [← inter_ofPred_eq_sep s p]; rw [← inter_ofPred_eq_sep t p]; rw [← inter_assoc]; rw [← left_eq_inter.mpr hst]

@[simp]

Depends on / 依赖: inter_assoc, inter_ofPred_eq_sep, left_eq_inter, left_eq_inter.mpr
-/
theorem sep_eq_inter_sep {α : Type*} {s t : Set α} {p : α -> Prop} (hst : s subseteq t) :
    {x in s | p x} = s inter {x in t | p x} := by
  rw [← inter_ofPred_eq_sep s p]; rw [← inter_ofPred_eq_sep t p]; rw [← inter_assoc]; rw [← left_eq_inter.mpr hst]

@[simp]
/--
theorem `inter_ssubset_right_iff` / 定理 `inter_ssubset_right_iff`

English:
theorem inter_ssubset_right_iff
  statement: s inter t ⊂ t ↔ ¬ t subseteq s
  proof: inf_lt_right

@[simp]

中文:
定理 inter_ssubset_right_iff
  结论: s inter t ⊂ t ↔ ¬ t subseteq s
  证明: inf_lt_right

@[simp]

Depends on / 依赖: inf_lt_right
-/
theorem inter_ssubset_right_iff : s inter t ⊂ t ↔ ¬ t subseteq s :=
  inf_lt_right

@[simp]
/--
theorem `inter_ssubset_left_iff` / 定理 `inter_ssubset_left_iff`

English:
theorem inter_ssubset_left_iff
  statement: s inter t ⊂ s ↔ ¬ s subseteq t
  proof: inf_lt_left

中文:
定理 inter_ssubset_left_iff
  结论: s inter t ⊂ s ↔ ¬ s subseteq t
  证明: inf_lt_left

Depends on / 依赖: inf_lt_left
-/
theorem inter_ssubset_left_iff : s inter t ⊂ s ↔ ¬ s subseteq t :=
  inf_lt_left


/--
theorem `inter_union_distrib_left` / 定理 `inter_union_distrib_left`

English:
theorem inter_union_distrib_left
  given: (s t u : Set α)
  statement: s inter (t union u) = s inter t union s inter u
  proof: inf_sup_left _ _ _

中文:
定理 inter_union_distrib_left
  条件: (s t u : Set α)
  结论: s inter (t union u) = s inter t union s inter u
  证明: inf_sup_left _ _ _

Depends on / 依赖: inf_sup_left
-/
theorem inter_union_distrib_left (s t u : Set α) : s inter (t union u) = s inter t union s inter u :=
  inf_sup_left _ _ _

/--
theorem `union_inter_distrib_right` / 定理 `union_inter_distrib_right`

English:
theorem union_inter_distrib_right
  given: (s t u : Set α)
  statement: (s union t) inter u = s inter u union t inter u
  proof: inf_sup_right _ _ _

中文:
定理 union_inter_distrib_right
  条件: (s t u : Set α)
  结论: (s union t) inter u = s inter u union t inter u
  证明: inf_sup_right _ _ _

Depends on / 依赖: inf_sup_right
-/
theorem union_inter_distrib_right (s t u : Set α) : (s union t) inter u = s inter u union t inter u :=
  inf_sup_right _ _ _

/--
theorem `union_inter_distrib_left` / 定理 `union_inter_distrib_left`

English:
theorem union_inter_distrib_left
  given: (s t u : Set α)
  statement: s union t inter u = (s union t) inter (s union u)
  proof: sup_inf_left _ _ _

中文:
定理 union_inter_distrib_left
  条件: (s t u : Set α)
  结论: s union t inter u = (s union t) inter (s union u)
  证明: sup_inf_left _ _ _

Depends on / 依赖: sup_inf_left
-/
theorem union_inter_distrib_left (s t u : Set α) : s union t inter u = (s union t) inter (s union u) :=
  sup_inf_left _ _ _

/--
theorem `inter_union_distrib_right` / 定理 `inter_union_distrib_right`

English:
theorem inter_union_distrib_right
  given: (s t u : Set α)
  statement: s inter t union u = (s union u) inter (t union u)
  proof: sup_inf_right _ _ _

中文:
定理 inter_union_distrib_right
  条件: (s t u : Set α)
  结论: s inter t union u = (s union u) inter (t union u)
  证明: sup_inf_right _ _ _

Depends on / 依赖: sup_inf_right
-/
theorem inter_union_distrib_right (s t u : Set α) : s inter t union u = (s union u) inter (t union u) :=
  sup_inf_right _ _ _

/--
theorem `union_union_distrib_left` / 定理 `union_union_distrib_left`

English:
theorem union_union_distrib_left
  given: (s t u : Set α)
  statement: s union (t union u) = s union t union (s union u)
  proof: sup_sup_distrib_left _ _ _

中文:
定理 union_union_distrib_left
  条件: (s t u : Set α)
  结论: s union (t union u) = s union t union (s union u)
  证明: sup_sup_distrib_left _ _ _

Depends on / 依赖: sup_sup_distrib_left
-/
theorem union_union_distrib_left (s t u : Set α) : s union (t union u) = s union t union (s union u) :=
  sup_sup_distrib_left _ _ _

/--
theorem `union_union_distrib_right` / 定理 `union_union_distrib_right`

English:
theorem union_union_distrib_right
  given: (s t u : Set α)
  statement: s union t union u = s union u union (t union u)
  proof: sup_sup_distrib_right _ _ _

中文:
定理 union_union_distrib_right
  条件: (s t u : Set α)
  结论: s union t union u = s union u union (t union u)
  证明: sup_sup_distrib_right _ _ _

Depends on / 依赖: sup_sup_distrib_right
-/
theorem union_union_distrib_right (s t u : Set α) : s union t union u = s union u union (t union u) :=
  sup_sup_distrib_right _ _ _

/--
theorem `inter_inter_distrib_left` / 定理 `inter_inter_distrib_left`

English:
theorem inter_inter_distrib_left
  given: (s t u : Set α)
  statement: s inter (t inter u) = s inter t inter (s inter u)
  proof: inf_inf_distrib_left _ _ _

中文:
定理 inter_inter_distrib_left
  条件: (s t u : Set α)
  结论: s inter (t inter u) = s inter t inter (s inter u)
  证明: inf_inf_distrib_left _ _ _

Depends on / 依赖: inf_inf_distrib_left
-/
theorem inter_inter_distrib_left (s t u : Set α) : s inter (t inter u) = s inter t inter (s inter u) :=
  inf_inf_distrib_left _ _ _

/--
theorem `inter_inter_distrib_right` / 定理 `inter_inter_distrib_right`

English:
theorem inter_inter_distrib_right
  given: (s t u : Set α)
  statement: s inter t inter u = s inter u inter (t inter u)
  proof: inf_inf_distrib_right _ _ _

中文:
定理 inter_inter_distrib_right
  条件: (s t u : Set α)
  结论: s inter t inter u = s inter u inter (t inter u)
  证明: inf_inf_distrib_right _ _ _

Depends on / 依赖: inf_inf_distrib_right
-/
theorem inter_inter_distrib_right (s t u : Set α) : s inter t inter u = s inter u inter (t inter u) :=
  inf_inf_distrib_right _ _ _

/--
theorem `union_union_union_comm` / 定理 `union_union_union_comm`

English:
theorem union_union_union_comm
  given: (s t u v : Set α)
  statement: s union t union (u union v) = s union u union (t union v)
  proof: sup_sup_sup_comm _ _ _ _

中文:
定理 union_union_union_comm
  条件: (s t u v : Set α)
  结论: s union t union (u union v) = s union u union (t union v)
  证明: sup_sup_sup_comm _ _ _ _

Depends on / 依赖: sup_sup_sup_comm
-/
theorem union_union_union_comm (s t u v : Set α) : s union t union (u union v) = s union u union (t union v) :=
  sup_sup_sup_comm _ _ _ _

/--
theorem `inter_inter_inter_comm` / 定理 `inter_inter_inter_comm`

English:
theorem inter_inter_inter_comm
  given: (s t u v : Set α)
  statement: s inter t inter (u inter v) = s inter u inter (t inter v)
  proof: inf_inf_inf_comm _ _ _ _

中文:
定理 inter_inter_inter_comm
  条件: (s t u v : Set α)
  结论: s inter t inter (u inter v) = s inter u inter (t inter v)
  证明: inf_inf_inf_comm _ _ _ _

Depends on / 依赖: inf_inf_inf_comm
-/
theorem inter_inter_inter_comm (s t u v : Set α) : s inter t inter (u inter v) = s inter u inter (t inter v) :=
  inf_inf_inf_comm _ _ _ _

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

section Sep

variable {p q : α -> Prop} {x : α}

/--
theorem `mem_sep` / 定理 `mem_sep`

English:
theorem mem_sep
  given: (xs : x in s) (px : p x)
  statement: x in { x in s | p x }
  proof: ⟨xs, px⟩

@[simp]

中文:
定理 mem_sep
  条件: (xs : x in s) (px : p x)
  结论: x in { x in s | p x }
  证明: ⟨xs, px⟩

@[simp]
-/
theorem mem_sep (xs : x in s) (px : p x) : x in { x in s | p x } :=
  ⟨xs, px⟩

@[simp]
/--
theorem `sep_mem_eq` / 定理 `sep_mem_eq`

English:
theorem sep_mem_eq
  statement: { x in s | x in t } = s inter t
  proof: rfl

@[simp]

中文:
定理 sep_mem_eq
  结论: { x in s | x in t } = s inter t
  证明: rfl

@[simp]
-/
theorem sep_mem_eq : { x in s | x in t } = s inter t :=
  rfl

@[simp]
/--
theorem `mem_sep_iff` / 定理 `mem_sep_iff`

English:
theorem mem_sep_iff
  statement: x in { x in s | p x } ↔ x in s ∧ p x
  proof: Iff.rfl

中文:
定理 mem_sep_iff
  结论: x in { x in s | p x } ↔ x in s ∧ p x
  证明: Iff.rfl

Depends on / 依赖: ContMDiff, Iff.rfl, contDiff_smul, contDiff_smul.contMDiff.comp, contMDiff, contMDiff_id, contMDiff_prod_iff, contMDiff_prod_module_iff
-/
theorem mem_sep_iff : x in { x in s | p x } ↔ x in s ∧ p x :=
  Iff.rfl

/--
theorem `sep_ext_iff` / 定理 `sep_ext_iff`

English:
theorem sep_ext_iff
  statement: { x in s | p x } = { x in s | q x } ↔ forall x in s, p x ↔ q x
  proof: by
  simp_rw [Set.ext_iff, mem_sep_iff, and_congr_right_iff]

中文:
定理 sep_ext_iff
  结论: { x in s | p x } = { x in s | q x } ↔ 对任意 x in s, p x ↔ q x
  证明: by
  simp_rw [Set.ext_iff, mem_sep_iff, and_congr_right_iff]

Depends on / 依赖: ContMDiff, Set.ext_iff, and_congr_right_iff, contDiff, contMDiff, contMDiff_id, contMDiff_prod_iff, contMDiff_prod_module_iff, ext_iff, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.contDiff.contMDiff.comp, mem_sep_iff, simp_rw
-/
theorem sep_ext_iff : { x in s | p x } = { x in s | q x } ↔ forall x in s, p x ↔ q x := by
  simp_rw [Set.ext_iff, mem_sep_iff, and_congr_right_iff]

/--
theorem `sep_eq_of_subset` / 定理 `sep_eq_of_subset`

English:
theorem sep_eq_of_subset
  given: (h : s subseteq t)
  statement: { x in t | x in s } = s
  proof: inter_eq_self_of_subset_right h

@[simp]

中文:
定理 sep_eq_of_subset
  条件: (h : s subseteq t)
  结论: { x in t | x in s } = s
  证明: inter_eq_self_of_subset_right h

@[simp]

Depends on / 依赖: inter_eq_self_of_subset_right
-/
theorem sep_eq_of_subset (h : s subseteq t) : { x in t | x in s } = s :=
  inter_eq_self_of_subset_right h

@[simp]
/--
theorem `sep_subset` / 定理 `sep_subset`

English:
theorem sep_subset
  given: (s : Set α) (p : α -> Prop)
  statement: { x in s | p x } subseteq s
  proof: fun _ => And.left

中文:
定理 sep_subset
  条件: (s : Set α) (p : α -> 命题)
  结论: { x in s | p x } subseteq s
  证明: fun _ => And.left

Depends on / 依赖: And.left
-/
theorem sep_subset (s : Set α) (p : α -> Prop) : { x in s | p x } subseteq s := fun _ => And.left

/--
theorem `sep_subset_ofPred` / 定理 `sep_subset_ofPred`

English:
theorem sep_subset_ofPred
  given: (s : Set α) (p : α -> Prop)
  statement: { x in s | p x } subseteq { x | p x }
  proof: fun _ => And.right

@[deprecated (since := "2026-07-09")]
alias sep_subset_setOf := sep_subset_ofPred

@[simp]

中文:
定理 sep_subset_ofPred
  条件: (s : Set α) (p : α -> 命题)
  结论: { x in s | p x } subseteq { x | p x }
  证明: fun _ => And.right

@[deprecated (since := "2026-07-09")]
alias sep_subset_setOf := sep_subset_ofPred

@[simp]

Depends on / 依赖: And.right
-/
theorem sep_subset_ofPred (s : Set α) (p : α -> Prop) : { x in s | p x } subseteq { x | p x } :=
  fun _ => And.right

@[deprecated (since := "2026-07-09")]
alias sep_subset_setOf := sep_subset_ofPred

@[simp]
/--
theorem `sep_eq_self_iff_mem_true` / 定理 `sep_eq_self_iff_mem_true`

English:
theorem sep_eq_self_iff_mem_true
  statement: { x in s | p x } = s ↔ forall x in s, p x
  proof: by
  simp_rw [Set.ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp]

中文:
定理 sep_eq_self_iff_mem_true
  结论: { x in s | p x } = s ↔ 对任意 x in s, p x
  证明: by
  simp_rw [Set.ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp]

Depends on / 依赖: Set.ext_iff, and_iff_left_iff_imp, ext_iff, mem_sep_iff, simp_rw
-/
theorem sep_eq_self_iff_mem_true : { x in s | p x } = s ↔ forall x in s, p x := by
  simp_rw [Set.ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp]
/--
theorem `sep_eq_empty_iff_mem_false` / 定理 `sep_eq_empty_iff_mem_false`

English:
theorem sep_eq_empty_iff_mem_false
  statement: { x in s | p x } = ∅ ↔ forall x in s, ¬p x
  proof: by
  simp_rw [Set.ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]

中文:
定理 sep_eq_empty_iff_mem_false
  结论: { x in s | p x } = ∅ ↔ 对任意 x in s, ¬p x
  证明: by
  simp_rw [Set.ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]

Depends on / 依赖: Set.ext_iff, ext_iff, iff_false, mem_empty_iff_false, mem_sep_iff, not_and, simp_rw
-/
theorem sep_eq_empty_iff_mem_false : { x in s | p x } = ∅ ↔ forall x in s, ¬p x := by
  simp_rw [Set.ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]

/--
theorem `sep_true` / 定理 `sep_true`

English:
theorem sep_true
  statement: { x in s | True } = s
  proof: inter_univ s

中文:
定理 sep_true
  结论: { x in s | True } = s
  证明: inter_univ s

Depends on / 依赖: inter_univ
-/
theorem sep_true : { x in s | True } = s :=
  inter_univ s

/--
theorem `sep_false` / 定理 `sep_false`

English:
theorem sep_false
  statement: { x in s | False } = ∅
  proof: inter_empty s

中文:
定理 sep_false
  结论: { x in s | False } = ∅
  证明: inter_empty s

Depends on / 依赖: inter_empty
-/
theorem sep_false : { x in s | False } = ∅ :=
  inter_empty s

/--
theorem `sep_empty` / 定理 `sep_empty`

English:
theorem sep_empty
  given: (p : α -> Prop)
  statement: { x in (∅ : Set α) | p x } = ∅
  proof: empty_inter {x | p x}

中文:
定理 sep_empty
  条件: (p : α -> 命题)
  结论: { x in (∅ : Set α) | p x } = ∅
  证明: empty_inter {x | p x}

Depends on / 依赖: empty_inter
-/
theorem sep_empty (p : α -> Prop) : { x in (∅ : Set α) | p x } = ∅ :=
  empty_inter {x | p x}

/--
theorem `sep_univ` / 定理 `sep_univ`

English:
theorem sep_univ
  statement: { x in (univ : Set α) | p x } = { x | p x }
  proof: univ_inter {x | p x}

@[simp]

中文:
定理 sep_univ
  结论: { x in (univ : Set α) | p x } = { x | p x }
  证明: univ_inter {x | p x}

@[simp]

Depends on / 依赖: univ_inter
-/
theorem sep_univ : { x in (univ : Set α) | p x } = { x | p x } :=
  univ_inter {x | p x}

@[simp]
/--
theorem `sep_union` / 定理 `sep_union`

English:
theorem sep_union
  statement: { x | (x in s ∨ x in t) ∧ p x } = { x in s | p x } union { x in t | p x }
  proof: union_inter_distrib_right { x | x in s } { x | x in t } {x | p x}

@[simp]

中文:
定理 sep_union
  结论: { x | (x in s ∨ x in t) ∧ p x } = { x in s | p x } union { x in t | p x }
  证明: union_inter_distrib_right { x | x in s } { x | x in t } {x | p x}

@[simp]

Depends on / 依赖: union_inter_distrib_right
-/
theorem sep_union : { x | (x in s ∨ x in t) ∧ p x } = { x in s | p x } union { x in t | p x } :=
  union_inter_distrib_right { x | x in s } { x | x in t } {x | p x}

@[simp]
/--
theorem `sep_inter` / 定理 `sep_inter`

English:
theorem sep_inter
  statement: { x | (x in s ∧ x in t) ∧ p x } = { x in s | p x } inter { x in t | p x }
  proof: inter_inter_distrib_right s t {x | p x}

@[simp]

中文:
定理 sep_inter
  结论: { x | (x in s ∧ x in t) ∧ p x } = { x in s | p x } inter { x in t | p x }
  证明: inter_inter_distrib_right s t {x | p x}

@[simp]

Depends on / 依赖: inter_inter_distrib_right
-/
theorem sep_inter : { x | (x in s ∧ x in t) ∧ p x } = { x in s | p x } inter { x in t | p x } :=
  inter_inter_distrib_right s t {x | p x}

@[simp]
/--
theorem `sep_and` / 定理 `sep_and`

English:
theorem sep_and
  statement: { x in s | p x ∧ q x } = { x in s | p x } inter { x in s | q x }
  proof: inter_inter_distrib_left s {x | p x} {x | q x}

@[simp]

中文:
定理 sep_and
  结论: { x in s | p x ∧ q x } = { x in s | p x } inter { x in s | q x }
  证明: inter_inter_distrib_left s {x | p x} {x | q x}

@[simp]

Depends on / 依赖: inter_inter_distrib_left
-/
theorem sep_and : { x in s | p x ∧ q x } = { x in s | p x } inter { x in s | q x } :=
  inter_inter_distrib_left s {x | p x} {x | q x}

@[simp]
/--
theorem `sep_or` / 定理 `sep_or`

English:
theorem sep_or
  statement: { x in s | p x ∨ q x } = { x in s | p x } union { x in s | q x }
  proof: inter_union_distrib_left s {x | p x} {x | q x}

@[simp]

中文:
定理 sep_or
  结论: { x in s | p x ∨ q x } = { x in s | p x } union { x in s | q x }
  证明: inter_union_distrib_left s {x | p x} {x | q x}

@[simp]

Depends on / 依赖: inter_union_distrib_left
-/
theorem sep_or : { x in s | p x ∨ q x } = { x in s | p x } union { x in s | q x } :=
  inter_union_distrib_left s {x | p x} {x | q x}

@[simp]
/--
theorem `sep_ofPred` / 定理 `sep_ofPred`

English:
theorem sep_ofPred
  statement: { x in { y | p y } | q x } = { x | p x ∧ q x }
  proof: rfl

@[deprecated (since := "2026-07-09")]
alias sep_setOf := sep_ofPred

中文:
定理 sep_ofPred
  结论: { x in { y | p y } | q x } = { x | p x ∧ q x }
  证明: rfl

@[deprecated (since := "2026-07-09")]
alias sep_setOf := sep_ofPred
-/
theorem sep_ofPred : { x in { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl

@[deprecated (since := "2026-07-09")]
alias sep_setOf := sep_ofPred

end Sep


/--
theorem `mem_powerset` / 定理 `mem_powerset`

English:
theorem mem_powerset
  given: {x s : Set α} (h : x subseteq s)
  statement: x in 𝒫 s
  proof: @h

中文:
定理 mem_powerset
  条件: {x s : Set α} (h : x subseteq s)
  结论: x in 𝒫 s
  证明: @h
-/
theorem mem_powerset {x s : Set α} (h : x subseteq s) : x in 𝒫 s := @h

/--
theorem `subset_of_mem_powerset` / 定理 `subset_of_mem_powerset`

English:
theorem subset_of_mem_powerset
  given: {x s : Set α} (h : x in 𝒫 s)
  statement: x subseteq s
  proof: @h

@[simp, grind =, push]

中文:
定理 subset_of_mem_powerset
  条件: {x s : Set α} (h : x in 𝒫 s)
  结论: x subseteq s
  证明: @h

@[simp, grind =, push]
-/
theorem subset_of_mem_powerset {x s : Set α} (h : x in 𝒫 s) : x subseteq s := @h

@[simp, grind =, push]
/--
theorem `mem_powerset_iff` / 定理 `mem_powerset_iff`

English:
theorem mem_powerset_iff
  given: (x s : Set α)
  statement: x in 𝒫 s ↔ x subseteq s
  proof: Iff.rfl

中文:
定理 mem_powerset_iff
  条件: (x s : Set α)
  结论: x in 𝒫 s ↔ x subseteq s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_powerset_iff (x s : Set α) : x in 𝒫 s ↔ x subseteq s :=
  Iff.rfl

/--
theorem `powerset_inter` / 定理 `powerset_inter`

English:
theorem powerset_inter
  given: (s t : Set α)
  statement: 𝒫 (s inter t) = 𝒫 s inter 𝒫 t
  proof: ext fun _ => subset_inter_iff

@[simp]

中文:
定理 powerset_inter
  条件: (s t : Set α)
  结论: 𝒫 (s inter t) = 𝒫 s inter 𝒫 t
  证明: ext fun _ => subset_inter_iff

@[simp]

Depends on / 依赖: subset_inter_iff
-/
theorem powerset_inter (s t : Set α) : 𝒫 (s inter t) = 𝒫 s inter 𝒫 t :=
  ext fun _ => subset_inter_iff

@[simp]
/--
theorem `powerset_mono` / 定理 `powerset_mono`

English:
theorem powerset_mono
  statement: 𝒫 s subseteq 𝒫 t ↔ s subseteq t
  proof: ⟨fun h => @h _ (fun _ h => h), fun h _ hu _ ha => h (hu ha)⟩

中文:
定理 powerset_mono
  结论: 𝒫 s subseteq 𝒫 t ↔ s subseteq t
  证明: ⟨fun h => @h _ (fun _ h => h), fun h _ hu _ ha => h (hu ha)⟩
-/
theorem powerset_mono : 𝒫 s subseteq 𝒫 t ↔ s subseteq t :=
  ⟨fun h => @h _ (fun _ h => h), fun h _ hu _ ha => h (hu ha)⟩

/--
theorem `monotone_powerset` / 定理 `monotone_powerset`

English:
theorem monotone_powerset
  statement: Monotone (powerset : Set α -> Set (Set α))
  proof: fun _ _ => powerset_mono.2

@[simp]

中文:
定理 monotone_powerset
  结论: Monotone (powerset : Set α -> Set (Set α))
  证明: fun _ _ => powerset_mono.2

@[simp]

Depends on / 依赖: powerset_mono
-/
theorem monotone_powerset : Monotone (powerset : Set α -> Set (Set α)) := fun _ _ => powerset_mono.2

@[simp]
/--
theorem `powerset_nonempty` / 定理 `powerset_nonempty`

English:
theorem powerset_nonempty
  statement: (𝒫 s).Nonempty
  proof: ⟨∅, fun _ h => empty_subset s h⟩

@[simp]

中文:
定理 powerset_nonempty
  结论: (𝒫 s).Nonempty
  证明: ⟨∅, fun _ h => empty_subset s h⟩

@[simp]

Depends on / 依赖: empty_subset
-/
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, fun _ h => empty_subset s h⟩

@[simp]
/--
theorem `powerset_empty` / 定理 `powerset_empty`

English:
theorem powerset_empty
  statement: 𝒫 (∅ : Set α) = {∅}
  proof: ext fun _ => subset_empty_iff

@[simp]

中文:
定理 powerset_empty
  结论: 𝒫 (∅ : Set α) = {∅}
  证明: ext fun _ => subset_empty_iff

@[simp]

Depends on / 依赖: subset_empty_iff
-/
theorem powerset_empty : 𝒫 (∅ : Set α) = {∅} :=
  ext fun _ => subset_empty_iff

@[simp]
/--
theorem `powerset_univ` / 定理 `powerset_univ`

English:
theorem powerset_univ
  statement: 𝒫 (univ : Set α) = univ
  proof: eq_univ_of_forall subset_univ

中文:
定理 powerset_univ
  结论: 𝒫 (univ : Set α) = univ
  证明: eq_univ_of_forall subset_univ

Depends on / 依赖: eq_univ_of_forall, subset_univ
-/
theorem powerset_univ : 𝒫 (univ : Set α) = univ :=
  eq_univ_of_forall subset_univ


/--
theorem `mem_dite_univ_right` / 定理 `mem_dite_univ_right`

English:
theorem mem_dite_univ_right
  given: (p : Prop) [Decidable p] (t : p -> Set α) (x : α)
  proof: by
  simp [mem_dite]

@[simp]

中文:
定理 mem_dite_univ_right
  条件: (p : 命题) [Decidable p] (t : p -> Set α) (x : α)
  证明: by
  simp [mem_dite]

@[simp]

Depends on / 依赖: mem_dite
-/
theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p -> Set α) (x : α) :
    (x in if h : p then t h else univ) ↔ forall h : p, x in t h := by
  simp [mem_dite]

@[simp]
/--
theorem `mem_ite_univ_right` / 定理 `mem_ite_univ_right`

English:
theorem mem_ite_univ_right
  given: (p : Prop) [Decidable p] (t : Set α) (x : α)
  proof: mem_dite_univ_right p (fun _ => t) x

中文:
定理 mem_ite_univ_right
  条件: (p : 命题) [Decidable p] (t : Set α) (x : α)
  证明: mem_dite_univ_right p (fun _ => t) x

Depends on / 依赖: mem_dite_univ_right
-/
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x in ite p t Set.univ ↔ p -> x in t :=
  mem_dite_univ_right p (fun _ => t) x

/--
theorem `mem_dite_univ_left` / 定理 `mem_dite_univ_left`

English:
theorem mem_dite_univ_left
  given: (p : Prop) [Decidable p] (t : ¬p -> Set α) (x : α)
  proof: by
  split_ifs <;> simp_all

@[simp]

中文:
定理 mem_dite_univ_left
  条件: (p : 命题) [Decidable p] (t : ¬p -> Set α) (x : α)
  证明: by
  split_ifs <;> simp_all

@[simp]

Depends on / 依赖: split_ifs
-/
theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p -> Set α) (x : α) :
    (x in if h : p then univ else t h) ↔ forall h : ¬p, x in t h := by
  split_ifs <;> simp_all

@[simp]
/--
theorem `mem_ite_univ_left` / 定理 `mem_ite_univ_left`

English:
theorem mem_ite_univ_left
  given: (p : Prop) [Decidable p] (t : Set α) (x : α)
  proof: mem_dite_univ_left p (fun _ => t) x

中文:
定理 mem_ite_univ_left
  条件: (p : 命题) [Decidable p] (t : Set α) (x : α)
  证明: mem_dite_univ_left p (fun _ => t) x

Depends on / 依赖: mem_dite_univ_left
-/
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x in ite p Set.univ t ↔ ¬p -> x in t :=
  mem_dite_univ_left p (fun _ => t) x

/--
theorem `mem_dite_empty_right` / 定理 `mem_dite_empty_right`

English:
theorem mem_dite_empty_right
  given: (p : Prop) [Decidable p] (t : p -> Set α) (x : α)
  proof: by
  simp only [mem_dite, mem_empty_iff_false, imp_false, not_not]
  exact ⟨fun h => ⟨h.2, h.1 h.2⟩, fun ⟨h₁, h₂⟩ => ⟨fun _ => h₂, h₁⟩⟩

@[simp]

中文:
定理 mem_dite_empty_right
  条件: (p : 命题) [Decidable p] (t : p -> Set α) (x : α)
  证明: by
  simp only [mem_dite, mem_empty_iff_false, imp_false, not_not]
  exact ⟨fun h => ⟨h.2, h.1 h.2⟩, fun ⟨h₁, h₂⟩ => ⟨fun _ => h₂, h₁⟩⟩

@[simp]

Depends on / 依赖: imp_false, mem_dite, mem_empty_iff_false, not_not
-/
theorem mem_dite_empty_right (p : Prop) [Decidable p] (t : p -> Set α) (x : α) :
    (x in if h : p then t h else ∅) ↔ exists h : p, x in t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false, not_not]
  exact ⟨fun h => ⟨h.2, h.1 h.2⟩, fun ⟨h₁, h₂⟩ => ⟨fun _ => h₂, h₁⟩⟩

@[simp]
/--
theorem `mem_ite_empty_right` / 定理 `mem_ite_empty_right`

English:
theorem mem_ite_empty_right
  given: (p : Prop) [Decidable p] (t : Set α) (x : α)
  proof: (mem_dite_empty_right p (fun _ => t) x).trans (by simp)

中文:
定理 mem_ite_empty_right
  条件: (p : 命题) [Decidable p] (t : Set α) (x : α)
  证明: (mem_dite_empty_right p (fun _ => t) x).trans (by simp)

Depends on / 依赖: mem_dite_empty_right
-/
theorem mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x in ite p t ∅ ↔ p ∧ x in t :=
  (mem_dite_empty_right p (fun _ => t) x).trans (by simp)

/--
theorem `mem_dite_empty_left` / 定理 `mem_dite_empty_left`

English:
theorem mem_dite_empty_left
  given: (p : Prop) [Decidable p] (t : ¬p -> Set α) (x : α)
  proof: by
  simp only [mem_dite, mem_empty_iff_false, imp_false]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun ⟨h₁, h₂⟩ => ⟨fun h => h₁ h, fun _ => h₂⟩⟩

@[simp]

中文:
定理 mem_dite_empty_left
  条件: (p : 命题) [Decidable p] (t : ¬p -> Set α) (x : α)
  证明: by
  simp only [mem_dite, mem_empty_iff_false, imp_false]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun ⟨h₁, h₂⟩ => ⟨fun h => h₁ h, fun _ => h₂⟩⟩

@[simp]

Depends on / 依赖: imp_false, mem_dite, mem_empty_iff_false
-/
theorem mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p -> Set α) (x : α) :
    (x in if h : p then ∅ else t h) ↔ exists h : ¬p, x in t h := by
  simp only [mem_dite, mem_empty_iff_false, imp_false]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun ⟨h₁, h₂⟩ => ⟨fun h => h₁ h, fun _ => h₂⟩⟩

@[simp]
/--
theorem `mem_ite_empty_left` / 定理 `mem_ite_empty_left`

English:
theorem mem_ite_empty_left
  given: (p : Prop) [Decidable p] (t : Set α) (x : α)
  proof: (mem_dite_empty_left p (fun _ => t) x).trans (by simp)

中文:
定理 mem_ite_empty_left
  条件: (p : 命题) [Decidable p] (t : Set α) (x : α)
  证明: (mem_dite_empty_left p (fun _ => t) x).trans (by simp)

Depends on / 依赖: mem_dite_empty_left
-/
theorem mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x in ite p ∅ t ↔ ¬p ∧ x in t :=
  (mem_dite_empty_left p (fun _ => t) x).trans (by simp)

end Set

open Set

namespace Function

variable {α : Type*} {β : Type*}

/--
theorem `Injective.nonempty_apply_iff` / 定理 `Injective.nonempty_apply_iff`

English:
theorem Injective.nonempty_apply_iff
  statement: {f : Set α -> Set β} (hf : Injective f) (h2 : f ∅ = ∅)
  proof: by
  rw [nonempty_iff_ne_empty]; rw [← h2]; rw [nonempty_iff_ne_empty]; rw [hf.ne_iff]

中文:
定理 Injective.nonempty_apply_iff
  结论: {f : Set α -> Set β} (hf : Injective f) (h2 : f ∅ = ∅)
  证明: by
  rw [nonempty_iff_ne_empty]; rw [← h2]; rw [nonempty_iff_ne_empty]; rw [hf.ne_iff]

Depends on / 依赖: hf.ne_iff, ne_iff, nonempty_iff_ne_empty
-/
theorem Injective.nonempty_apply_iff {f : Set α -> Set β} (hf : Injective f) (h2 : f ∅ = ∅)
    {s : Set α} : (f s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rw [← h2]; rw [nonempty_iff_ne_empty]; rw [hf.ne_iff]

end Function

namespace Subsingleton

variable {α : Type*} [Subsingleton α]

/--
theorem `eq_univ_of_nonempty` / 定理 `eq_univ_of_nonempty`

English:
theorem eq_univ_of_nonempty
  given: {s : Set α}
  statement: s.Nonempty -> s = univ
  proof: fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

@[elab_as_elim]

中文:
定理 eq_univ_of_nonempty
  条件: {s : Set α}
  结论: s.Nonempty -> s = univ
  证明: fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

@[elab_as_elim]
-/
theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty -> s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

@[elab_as_elim]
/--
theorem `set_cases` / 定理 `set_cases`

English:
theorem set_cases
  given: {p : Set α -> Prop} (h0 : p ∅) (h1 : p univ) (s)
  statement: p s
  proof: (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1

中文:
定理 set_cases
  条件: {p : Set α -> 命题} (h0 : p ∅) (h1 : p univ) (s)
  结论: p s
  证明: (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1

Depends on / 依赖: eq_empty_or_nonempty, eq_univ_of_nonempty, h.symm, s.eq_empty_or_nonempty.elim
-/
theorem set_cases {p : Set α -> Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1

/--
theorem `mem_iff_nonempty` / 定理 `mem_iff_nonempty`

English:
theorem mem_iff_nonempty
  given: {α : Type*} [Subsingleton α] {s : Set α} {x : α}
  statement: x in s ↔ s.Nonempty
  proof: ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩

中文:
定理 mem_iff_nonempty
  条件: {α : 类型} [Subsingleton α] {s : Set α} {x : α}
  结论: x in s ↔ s.Nonempty
  证明: ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem mem_iff_nonempty {α : Type*} [Subsingleton α] {s : Set α} {x : α} : x in s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩

end Subsingleton

/-! ### Decidability instances for sets -/

namespace Set

variable {α : Type u} (s t : Set α) (a b : α)

/--
Instance `decidableSdiff` / 实例 `decidableSdiff`

English:
instance decidableSdiff
  signature: [Decidable (a in s)] [Decidable (a in t)]
  body: inferInstanceAs (Decidable (a in s ∧ a ∉ t))

中文:
实例 decidableSdiff
  签名: [Decidable (a in s)] [Decidable (a in t)]
  定义体: inferInstanceAs (Decidable (a in s ∧ a ∉ t))

Depends on / 依赖: Decidable
-/
instance decidableSdiff [Decidable (a in s)] [Decidable (a in t)] : Decidable (a in s \ t) :=
  inferInstanceAs (Decidable (a in s ∧ a ∉ t))

/--
Instance `decidableInter` / 实例 `decidableInter`

English:
instance decidableInter
  signature: [Decidable (a in s)] [Decidable (a in t)]
  body: inferInstanceAs (Decidable (a in s ∧ a in t))

中文:
实例 decidableInter
  签名: [Decidable (a in s)] [Decidable (a in t)]
  定义体: inferInstanceAs (Decidable (a in s ∧ a in t))

Depends on / 依赖: Decidable
-/
instance decidableInter [Decidable (a in s)] [Decidable (a in t)] : Decidable (a in s inter t) :=
  inferInstanceAs (Decidable (a in s ∧ a in t))

/--
Instance `decidableUnion` / 实例 `decidableUnion`

English:
instance decidableUnion
  signature: [Decidable (a in s)] [Decidable (a in t)]
  body: inferInstanceAs (Decidable (a in s ∨ a in t))

中文:
实例 decidableUnion
  签名: [Decidable (a in s)] [Decidable (a in t)]
  定义体: inferInstanceAs (Decidable (a in s ∨ a in t))

Depends on / 依赖: Decidable
-/
instance decidableUnion [Decidable (a in s)] [Decidable (a in t)] : Decidable (a in s union t) :=
  inferInstanceAs (Decidable (a in s ∨ a in t))

/--
Instance `decidableCompl` / 实例 `decidableCompl`

English:
instance decidableCompl
  signature: [Decidable (a in s)]
  body: inferInstanceAs (Decidable (a ∉ s))

中文:
实例 decidableCompl
  签名: [Decidable (a in s)]
  定义体: inferInstanceAs (Decidable (a ∉ s))

Depends on / 依赖: ContMDiffRing, ContMDiffRing.toContMDiffMul, Decidable, ModelWithCorners, toContMDiffMul
-/
instance decidableCompl [Decidable (a in s)] : Decidable (a in sᶜ) :=
  inferInstanceAs (Decidable (a ∉ s))

/--
Instance `decidableEmptyset` / 实例 `decidableEmptyset`

English:
instance decidableEmptyset
  signature: : Decidable (a in (∅ : Set α))
  body: Decidable.isFalse (by simp)

中文:
实例 decidableEmptyset
  签名: : Decidable (a in (∅ : Set α))
  定义体: Decidable.isFalse (by simp)

Depends on / 依赖: ContMDiffRing, ContMDiffRing.toLieAddGroup, Decidable, Decidable.isFalse, ModelWithCorners, isFalse, toLieAddGroup
-/
instance decidableEmptyset : Decidable (a in (∅ : Set α)) := Decidable.isFalse (by simp)

/--
Instance `decidableUniv` / 实例 `decidableUniv`

English:
instance decidableUniv
  signature: : Decidable (a in univ)
  body: Decidable.isTrue (by simp)

中文:
实例 decidableUniv
  签名: : Decidable (a in univ)
  定义体: Decidable.isTrue (by simp)

Depends on / 依赖: Decidable, Decidable.isTrue, instFieldContMDiffRing, isTrue
-/
instance decidableUniv : Decidable (a in univ) := Decidable.isTrue (by simp)

/--
Instance `decidableInsert` / 实例 `decidableInsert`

English:
instance decidableInsert
  signature: [Decidable (a = b)] [Decidable (a in s)]
  body: inferInstanceAs (Decidable (_ ∨ _))

中文:
实例 decidableInsert
  签名: [Decidable (a = b)] [Decidable (a in s)]
  定义体: inferInstanceAs (Decidable (_ ∨ _))

Depends on / 依赖: Decidable
-/
instance decidableInsert [Decidable (a = b)] [Decidable (a in s)] : Decidable (a in insert b s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/--
Instance `decidableSetOf` / 实例 `decidableSetOf`

English:
instance decidableSetOf
  signature: (p : α -> Prop) [Decidable (p a)]
  body: by
  assumption

中文:
实例 decidableSetOf
  签名: (p : α -> 命题) [Decidable (p a)]
  定义体: by
  assumption
-/
instance decidableSetOf (p : α -> Prop) [Decidable (p a)] : Decidable (a in { a | p a }) := by
  assumption

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: : DecidableEq (Set α)
  body: Classical.typeDecidableEq (Set α)

中文:
实例 decidableEq
  签名: : DecidableEq (Set α)
  定义体: Classical.typeDecidableEq (Set α)

Depends on / 依赖: Classical, Classical.typeDecidableEq, typeDecidableEq
-/
noncomputable instance decidableEq : DecidableEq (Set α) := Classical.typeDecidableEq (Set α)

end Set

variable {α : Type*} {s t u : Set α}

namespace Equiv

/--
Definition of `setSubtypeComm` / `setSubtypeComm` 的定义

English:
definition setSubtypeComm
  signature: (p : α -> Prop)
  body: ⟨{a | exists h : p a, ⟨a, h⟩ in s}, fun _ h => h.1⟩
  invFun s := {a | a.val in s.val}
  left_inv s := by ext a; exact ⟨fun h => h.2, fun h => ⟨a.property, h⟩⟩
  right_inv s := by ext; exact ⟨fun h => h.2, fun h => ⟨s.property _ h, h⟩⟩

@[simp]

中文:
定义 setSubtypeComm
  签名: (p : α -> 命题)
  定义体: ⟨{a | exists h : p a, ⟨a, h⟩ in s}, fun _ h => h.1⟩
  invFun s := {a | a.val in s.val}
  left_inv s := by ext a; exact ⟨fun h => h.2, fun h => ⟨a.property, h⟩⟩
  right_inv s := by ext; exact ⟨fun h => h.2, fun h => ⟨s.property _ h, h⟩⟩

@[simp]
-/
protected def setSubtypeComm (p : α -> Prop) :
    Set {a : α // p a} ≃ {s : Set α // forall a in s, p a} where
  toFun s := ⟨{a | exists h : p a, ⟨a, h⟩ in s}, fun _ h => h.1⟩
  invFun s := {a | a.val in s.val}
  left_inv s := by ext a; exact ⟨fun h => h.2, fun h => ⟨a.property, h⟩⟩
  right_inv s := by ext; exact ⟨fun h => h.2, fun h => ⟨s.property _ h, h⟩⟩

@[simp]
/--
lemma `setSubtypeComm_apply` / 引理 `setSubtypeComm_apply`

English:
lemma setSubtypeComm_apply
  given: (p : α -> Prop) (s : Set {a // p a})
  proof: rfl

@[simp]

中文:
引理 setSubtypeComm_apply
  条件: (p : α -> 命题) (s : Set {a // p a})
  证明: rfl

@[simp]
-/
protected lemma setSubtypeComm_apply (p : α -> Prop) (s : Set {a // p a}) :
    (Equiv.setSubtypeComm p) s = ⟨{a | exists h : p a, ⟨a, h⟩ in s}, fun _ h => h.1⟩ :=
  rfl

@[simp]
/--
lemma `setSubtypeComm_symm_apply` / 引理 `setSubtypeComm_symm_apply`

English:
lemma setSubtypeComm_symm_apply
  given: (p : α -> Prop) (s : {s // forall a in s, p a})
  proof: rfl

中文:
引理 setSubtypeComm_symm_apply
  条件: (p : α -> 命题) (s : {s // 对任意 a in s, p a})
  证明: rfl
-/
protected lemma setSubtypeComm_symm_apply (p : α -> Prop) (s : {s // forall a in s, p a}) :
    (Equiv.setSubtypeComm p).symm s = {a | a.val in s.val} :=
  rfl

end Equiv
