/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.IsNormal
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.PPWithUniv

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `Ordinal`: the type of ordinals (in a given universe)
* `Ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `Ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r ⟨o, h⟩`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `Ordinal.card o`: the cardinality of an ordinal `o`.
* `Ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `Ordinal.liftInitialSeg`.
  For a version registering that it is a principal segment embedding if `u < v`, see
  `Ordinal.liftPrincipalSeg`.
* `Ordinal.omega0` or `ω` is the order type of `ℕ`. It is called this to match `Cardinal.aleph0`
  and so that the omega function can be named `Ordinal.omega`. This definition is universe
  polymorphic: `Ordinal.omega0.{u} : Ordinal.{u}` (contrast with `ℕ : Type`, which lives in
  a specific universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
  The main properties of addition (and the other operations on ordinals) are stated and proved in
  `Mathlib/SetTheory/Ordinal/Arithmetic.lean`.
  Here, we only introduce it and prove its basic properties to deduce the fact that the order on
  ordinals is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `Cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notation

* `ω` is a notation for the first infinite ordinal in the scope `Ordinal`.
-/

@[expose] public section

assert_not_exists Module Field

noncomputable section

open Function Cardinal Set Equiv Order
open scoped Cardinal InitialSeg

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop}

/-! ### Definition of ordinals -/


/--
Definition of `WellOrder` / `WellOrder` 的定义

English:
structure WellOrder
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - α : Type u
    - r : α -> α -> Prop
    - wo : IsWellOrder α r

中文:
结构 WellOrder
  参数: : Type (u + 1) where
  公理与运算 (3 个):
    - α : 类型u
    - r : α -> α -> 命题
    - wo : IsWellOrder α r
-/
structure WellOrder : Type (u + 1) where
  /-- The underlying type of the order. -/
  α : Type u
  /-- The underlying relation of the order. -/
  r : α -> α -> Prop
  /-- The proposition that `r` is a well-ordering for `α`. -/
  wo : IsWellOrder α r

attribute [instance] WellOrder.wo

namespace WellOrder

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited WellOrder
  body: ⟨⟨PEmpty, _, (inferInstance : IsWellOrder PEmpty emptyRelation)⟩⟩

中文:
实例 inhabited
  签名: : Inhabited WellOrder
  定义体: ⟨⟨PEmpty, _, (inferInstance : IsWellOrder PEmpty emptyRelation)⟩⟩

Depends on / 依赖: IsWellOrder, PEmpty, emptyRelation
-/
instance inhabited : Inhabited WellOrder :=
  ⟨⟨PEmpty, _, (inferInstance : IsWellOrder PEmpty emptyRelation)⟩⟩

end WellOrder

/--
Instance `Ordinal.isEquivalent` / 实例 `Ordinal.isEquivalent`

English:
instance Ordinal.isEquivalent
  signature: : Setoid WellOrder where
  body: fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

中文:
实例 Ordinal.isEquivalent
  签名: : Setoid WellOrder where
  定义体: fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

Depends on / 依赖: Nonempty
-/
instance Ordinal.isEquivalent : Setoid WellOrder where
  r := fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ, wikidata Q191780]
/--
Definition of `Ordinal` / `Ordinal` 的定义

English:
definition Ordinal
  signature: : Type (u + 1)
  body: Quotient Ordinal.isEquivalent

中文:
定义 Ordinal
  签名: : Type (u + 1)
  定义体: Quotient Ordinal.isEquivalent

Depends on / 依赖: Ordinal, Ordinal.isEquivalent, Quotient, isEquivalent
-/
def Ordinal : Type (u + 1) :=
  Quotient Ordinal.isEquivalent

/-- A "canonical" type order-isomorphic to the ordinal `o`, living in the same universe. This is
defined through the axiom of choice; in particular, it has no useful def-eqs, and it is not exposed.

Use this over `Iio o` only when it is paramount to have a `Type u` rather than a `Type (u + 1)`,
and convert using

```
Ordinal.ToType.mk : Iio o → o.ToType
Ordinal.ToType.toOrd : o.ToType → Iio o
```
-/
@[no_expose]
/--
Definition of `Ordinal.ToType` / `Ordinal.ToType` 的定义

English:
definition Ordinal.ToType
  signature: (o : Ordinal.{u})
  body: o.out.α

@[no_expose]

中文:
定义 Ordinal.ToType
  签名: (o : Ordinal.{u})
  定义体: o.out.α

@[no_expose]

Depends on / 依赖: o.out
-/
def Ordinal.ToType (o : Ordinal.{u}) : Type u :=
  o.out.α

@[no_expose]
/--
Instance `linearOrder_toType` / 实例 `linearOrder_toType`

English:
instance linearOrder_toType
  signature: (o : Ordinal)
  body: @IsWellOrder.linearOrder _ o.out.r o.out.wo

中文:
实例 linearOrder_toType
  签名: (o : Ordinal)
  定义体: @IsWellOrder.linearOrder _ o.out.r o.out.wo

Depends on / 依赖: IsWellOrder, IsWellOrder.linearOrder, linearOrder, o.out.r, o.out.wo
-/
instance linearOrder_toType (o : Ordinal) : LinearOrder o.ToType :=
  @IsWellOrder.linearOrder _ o.out.r o.out.wo

/--
Instance `wellFoundedLT_toType` / 实例 `wellFoundedLT_toType`

English:
instance wellFoundedLT_toType
  signature: (o : Ordinal)
  body: o.out.wo.toIsWellFounded

中文:
实例 wellFoundedLT_toType
  签名: (o : Ordinal)
  定义体: o.out.wo.toIsWellFounded

Depends on / 依赖: o.out.wo.toIsWellFounded, toIsWellFounded
-/
instance wellFoundedLT_toType (o : Ordinal) : WellFoundedLT o.ToType :=
  o.out.wo.toIsWellFounded

/--
Instance `hasWellFounded_toType` / 实例 `hasWellFounded_toType`

English:
instance hasWellFounded_toType
  signature: (o : Ordinal)
  body: WellFoundedLT.toWellFoundedRelation

中文:
实例 hasWellFounded_toType
  签名: (o : Ordinal)
  定义体: WellFoundedLT.toWellFoundedRelation

Depends on / 依赖: WellFoundedLT, WellFoundedLT.toWellFoundedRelation, toWellFoundedRelation
-/
instance hasWellFounded_toType (o : Ordinal) : WellFoundedRelation o.ToType :=
  WellFoundedLT.toWellFoundedRelation

namespace Ordinal

@[no_expose]
noncomputable instance (o : Ordinal) : SuccOrder o.ToType :=
  .ofLinearWellFoundedLT _

/-! ### Basic properties of the order type -/

/--
Definition of `type` / `type` 的定义

English:
definition type
  signature: (r : α -> α -> Prop) [wo : IsWellOrder α r]
  body: ⟦⟨α, r, wo⟩⟧

中文:
定义 type
  签名: (r : α -> α -> 命题) [wo : IsWellOrder α r]
  定义体: ⟦⟨α, r, wo⟩⟧
-/
def type (r : α -> α -> Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧

/-- `typeLT α` is an abbreviation for the order type of the `<` relation of `α`. -/
scoped notation3 "typeLT " α:70 => @Ordinal.type α (· < ·) inferInstance

/-- info: typeLT ℕ : Ordinal.{0} -/
#guard_msgs in
#check typeLT Nat

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : Zero Ordinal
  body: ⟨type @emptyRelation PEmpty⟩

中文:
实例 zero
  签名: : Zero Ordinal
  定义体: ⟨type @emptyRelation PEmpty⟩

Depends on / 依赖: PEmpty, emptyRelation
-/
instance zero : Zero Ordinal :=
⟨type @emptyRelation PEmpty⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited Ordinal
  body: ⟨0⟩

中文:
实例 inhabited
  签名: : Inhabited Ordinal
  定义体: ⟨0⟩
-/
instance inhabited : Inhabited Ordinal :=
  ⟨0⟩

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One Ordinal
  body: ⟨type @emptyRelation PUnit⟩

@[simp]

中文:
实例 one
  签名: : One Ordinal
  定义体: ⟨type @emptyRelation PUnit⟩

@[simp]

Depends on / 依赖: emptyRelation
-/
instance one : One Ordinal :=
⟨type @emptyRelation PUnit⟩

@[simp]
/--
theorem `type_toType` / 定理 `type_toType`

English:
theorem type_toType
  given: (o : Ordinal)
  statement: typeLT o.ToType = o
  proof: o.out_eq

中文:
定理 type_toType
  条件: (o : Ordinal)
  结论: typeLT o.ToType = o
  证明: o.out_eq

Depends on / 依赖: o.out_eq, out_eq
-/
theorem type_toType (o : Ordinal) : typeLT o.ToType = o :=
  o.out_eq

/--
theorem `type_eq` / 定理 `type_eq`

English:
theorem type_eq
  given: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s]
  proof: Quotient.eq'

中文:
定理 type_eq
  条件: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r] [IsWellOrder β s]
  证明: Quotient.eq'

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem type_eq {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'

/--
theorem `_root_.RelIso.ordinalType_congr` / 定理 `_root_.RelIso.ordinalType_congr`

English:
theorem _root_.RelIso.ordinalType_congr
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: type_eq.2 ⟨h⟩

@[deprecated (since := "2026-05-25")]
alias _root_.RelIso.ordinal_type_eq := RelIso.ordinalType_congr

中文:
定理 _root_.RelIso.ordinalType_congr
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: type_eq.2 ⟨h⟩

@[deprecated (since := "2026-05-25")]
alias _root_.RelIso.ordinal_type_eq := RelIso.ordinalType_congr

Depends on / 依赖: type_eq
-/
theorem _root_.RelIso.ordinalType_congr {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩

@[deprecated (since := "2026-05-25")]
alias _root_.RelIso.ordinal_type_eq := RelIso.ordinalType_congr

/--
theorem `_root_.OrderIso.ordinalType_congr` / 定理 `_root_.OrderIso.ordinalType_congr`

English:
theorem _root_.OrderIso.ordinalType_congr
  statement: {α β} [LinearOrder α] [LinearOrder β]
  proof: h.toRelIsoLT.ordinalType_congr

中文:
定理 _root_.OrderIso.ordinalType_congr
  结论: {α β} [LinearOrder α] [LinearOrder β]
  证明: h.toRelIsoLT.ordinalType_congr

Depends on / 依赖: h.toRelIsoLT.ordinalType_congr, ordinalType_congr, toRelIsoLT
-/
theorem _root_.OrderIso.ordinalType_congr {α β} [LinearOrder α] [LinearOrder β]
    [WellFoundedLT α] [WellFoundedLT β] (h : α ≃o β) : typeLT α = typeLT β :=
  h.toRelIsoLT.ordinalType_congr

/--
theorem `type_eq_zero_of_empty` / 定理 `type_eq_zero_of_empty`

English:
theorem type_eq_zero_of_empty
  given: (r) [IsWellOrder α r] [IsEmpty α]
  statement: type r = 0
  proof: (RelIso.relIsoOfIsEmpty r _).ordinalType_congr

@[simp]

中文:
定理 type_eq_zero_of_empty
  条件: (r) [IsWellOrder α r] [IsEmpty α]
  结论: type r = 0
  证明: (RelIso.relIsoOfIsEmpty r _).ordinalType_congr

@[simp]

Depends on / 依赖: RelIso, RelIso.relIsoOfIsEmpty, ordinalType_congr, relIsoOfIsEmpty
-/
theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinalType_congr

@[simp]
/--
theorem `type_eq_zero_iff_isEmpty` / 定理 `type_eq_zero_iff_isEmpty`

English:
theorem type_eq_zero_iff_isEmpty
  given: [IsWellOrder α r]
  statement: type r = 0 ↔ IsEmpty α
  proof: by
  refine ⟨fun h => ?_, fun _ => type_eq_zero_of_empty r⟩
  let ⟨s⟩ := type_eq.1 h
  exact s.toEquiv.isEmpty

中文:
定理 type_eq_zero_iff_isEmpty
  条件: [IsWellOrder α r]
  结论: type r = 0 ↔ IsEmpty α
  证明: by
  refine ⟨fun h => ?_, fun _ => type_eq_zero_of_empty r⟩
  let ⟨s⟩ := type_eq.1 h
  exact s.toEquiv.isEmpty

Depends on / 依赖: isEmpty, s.toEquiv.isEmpty, toEquiv, type_eq, type_eq_zero_of_empty
-/
theorem type_eq_zero_iff_isEmpty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α := by
  refine ⟨fun h => ?_, fun _ => type_eq_zero_of_empty r⟩
  let ⟨s⟩ := type_eq.1 h
  exact s.toEquiv.isEmpty

/--
theorem `type_ne_zero_iff_nonempty` / 定理 `type_ne_zero_iff_nonempty`

English:
theorem type_ne_zero_iff_nonempty
  given: [IsWellOrder α r]
  statement: type r != 0 ↔ Nonempty α
  proof: by simp

中文:
定理 type_ne_zero_iff_nonempty
  条件: [IsWellOrder α r]
  结论: type r != 0 ↔ Nonempty α
  证明: by simp
-/
theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r != 0 ↔ Nonempty α := by simp

/--
theorem `type_ne_zero_of_nonempty` / 定理 `type_ne_zero_of_nonempty`

English:
theorem type_ne_zero_of_nonempty
  given: (r) [IsWellOrder α r] [h : Nonempty α]
  statement: type r != 0
  proof: type_ne_zero_iff_nonempty.2 h

中文:
定理 type_ne_zero_of_nonempty
  条件: (r) [IsWellOrder α r] [h : Nonempty α]
  结论: type r != 0
  证明: type_ne_zero_iff_nonempty.2 h

Depends on / 依赖: type_ne_zero_iff_nonempty
-/
theorem type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r != 0 :=
  type_ne_zero_iff_nonempty.2 h

/--
theorem `type_pEmpty` / 定理 `type_pEmpty`

English:
theorem type_pEmpty
  statement: type (@emptyRelation PEmpty) = 0
  proof: rfl

中文:
定理 type_pEmpty
  结论: type (@emptyRelation PEmpty) = 0
  证明: rfl
-/
theorem type_pEmpty : type (@emptyRelation PEmpty) = 0 :=
  rfl

/--
theorem `type_empty` / 定理 `type_empty`

English:
theorem type_empty
  statement: type (@emptyRelation Empty) = 0
  proof: type_eq_zero_of_empty _

中文:
定理 type_empty
  结论: type (@emptyRelation Empty) = 0
  证明: type_eq_zero_of_empty _

Depends on / 依赖: type_eq_zero_of_empty
-/
theorem type_empty : type (@emptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _

/--
theorem `type_eq_one_of_unique` / 定理 `type_eq_one_of_unique`

English:
theorem type_eq_one_of_unique
  given: (r) [IsWellOrder α r] [Nonempty α] [Subsingleton α]
  statement: type r = 1
  proof: by
  cases nonempty_unique α
  exact (RelIso.ofUniqueOfIrrefl r _).ordinalType_congr

@[simp]

中文:
定理 type_eq_one_of_unique
  条件: (r) [IsWellOrder α r] [Nonempty α] [Subsingleton α]
  结论: type r = 1
  证明: by
  cases nonempty_unique α
  exact (RelIso.ofUniqueOfIrrefl r _).ordinalType_congr

@[simp]

Depends on / 依赖: RelIso, RelIso.ofUniqueOfIrrefl, nonempty_unique, ofUniqueOfIrrefl, ordinalType_congr
-/
theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Nonempty α] [Subsingleton α] : type r = 1 := by
  cases nonempty_unique α
  exact (RelIso.ofUniqueOfIrrefl r _).ordinalType_congr

@[simp]
/--
theorem `type_eq_one_iff_unique` / 定理 `type_eq_one_iff_unique`

English:
theorem type_eq_one_iff_unique
  given: [IsWellOrder α r]
  statement: type r = 1 ↔ Nonempty (Unique α)
  proof: ⟨fun h => let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ => type_eq_one_of_unique r⟩

中文:
定理 type_eq_one_iff_unique
  条件: [IsWellOrder α r]
  结论: type r = 1 ↔ Nonempty (Unique α)
  证明: ⟨fun h => let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ => type_eq_one_of_unique r⟩

Depends on / 依赖: s.toEquiv.unique, toEquiv, type_eq, type_eq_one_of_unique, unique
-/
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h => let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ => type_eq_one_of_unique r⟩

/--
theorem `type_pUnit` / 定理 `type_pUnit`

English:
theorem type_pUnit
  statement: type (@emptyRelation PUnit) = 1
  proof: rfl

中文:
定理 type_pUnit
  结论: type (@emptyRelation PUnit) = 1
  证明: rfl
-/
theorem type_pUnit : type (@emptyRelation PUnit) = 1 :=
  rfl

/--
theorem `type_unit` / 定理 `type_unit`

English:
theorem type_unit
  statement: type (@emptyRelation Unit) = 1
  proof: rfl

@[simp]

中文:
定理 type_unit
  结论: type (@emptyRelation Unit) = 1
  证明: rfl

@[simp]
-/
theorem type_unit : type (@emptyRelation Unit) = 1 :=
  rfl

@[simp]
/--
theorem `isEmpty_toType_iff` / 定理 `isEmpty_toType_iff`

English:
theorem isEmpty_toType_iff
  given: {o : Ordinal}
  statement: IsEmpty o.ToType ↔ o = 0
  proof: by
  rw [← @type_eq_zero_iff_isEmpty o.ToType (· < ·)]; rw [type_toType]

@[deprecated (since := "2026-02-18")] alias toType_empty_iff_eq_zero := isEmpty_toType_iff

中文:
定理 isEmpty_toType_iff
  条件: {o : Ordinal}
  结论: IsEmpty o.ToType ↔ o = 0
  证明: by
  rw [← @type_eq_zero_iff_isEmpty o.ToType (· < ·)]; rw [type_toType]

@[deprecated (since := "2026-02-18")] alias toType_empty_iff_eq_zero := isEmpty_toType_iff

Depends on / 依赖: ToType, o.ToType, type_eq_zero_iff_isEmpty, type_toType
-/
theorem isEmpty_toType_iff {o : Ordinal} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero_iff_isEmpty o.ToType (· < ·)]; rw [type_toType]

@[deprecated (since := "2026-02-18")] alias toType_empty_iff_eq_zero := isEmpty_toType_iff

/--
Instance `isEmpty_toType_zero` / 实例 `isEmpty_toType_zero`

English:
instance isEmpty_toType_zero
  signature: : IsEmpty (ToType 0)
  body: isEmpty_toType_iff.2 rfl

@[simp]

中文:
实例 isEmpty_toType_zero
  签名: : IsEmpty (ToType 0)
  定义体: isEmpty_toType_iff.2 rfl

@[simp]

Depends on / 依赖: isEmpty_toType_iff
-/
instance isEmpty_toType_zero : IsEmpty (ToType 0) :=
  isEmpty_toType_iff.2 rfl

@[simp]
/--
theorem `nonempty_toType_iff` / 定理 `nonempty_toType_iff`

English:
theorem nonempty_toType_iff
  given: {o : Ordinal}
  statement: Nonempty o.ToType ↔ o != 0
  proof: by
  rw [← @type_ne_zero_iff_nonempty o.ToType (· < ·)]; rw [type_toType]

@[deprecated (since := "2026-02-18")] alias toType_nonempty_iff_ne_zero := nonempty_toType_iff

中文:
定理 nonempty_toType_iff
  条件: {o : Ordinal}
  结论: Nonempty o.ToType ↔ o != 0
  证明: by
  rw [← @type_ne_zero_iff_nonempty o.ToType (· < ·)]; rw [type_toType]

@[deprecated (since := "2026-02-18")] alias toType_nonempty_iff_ne_zero := nonempty_toType_iff

Depends on / 依赖: ToType, o.ToType, type_ne_zero_iff_nonempty, type_toType
-/
theorem nonempty_toType_iff {o : Ordinal} : Nonempty o.ToType ↔ o != 0 := by
  rw [← @type_ne_zero_iff_nonempty o.ToType (· < ·)]; rw [type_toType]

@[deprecated (since := "2026-02-18")] alias toType_nonempty_iff_ne_zero := nonempty_toType_iff

/--
Instance `instNeZeroOne` / 实例 `instNeZeroOne`

English:
instance instNeZeroOne
  signature: : NeZero (1 : Ordinal)
  body: ⟨type_ne_zero_of_nonempty _⟩

@[deprecated _root_.one_ne_zero (since := "2026-05-12")]

中文:
实例 instNeZeroOne
  签名: : NeZero (1 : Ordinal)
  定义体: ⟨type_ne_zero_of_nonempty _⟩

@[deprecated _root_.one_ne_zero (since := "2026-05-12")]

Depends on / 依赖: type_ne_zero_of_nonempty
-/
instance instNeZeroOne : NeZero (1 : Ordinal) :=
  ⟨type_ne_zero_of_nonempty _⟩

@[deprecated _root_.one_ne_zero (since := "2026-05-12")]
/--
theorem `one_ne_zero` / 定理 `one_ne_zero`

English:
theorem one_ne_zero
  statement: (1 : Ordinal) != 0
  proof: _root_.one_ne_zero

中文:
定理 one_ne_zero
  结论: (1 : Ordinal) != 0
  证明: _root_.one_ne_zero
-/
protected theorem one_ne_zero : (1 : Ordinal) != 0 :=
  _root_.one_ne_zero

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: : Nontrivial Ordinal.{u}
  body: ⟨⟨1, 0, one_ne_zero⟩⟩

中文:
实例 nontrivial
  签名: : Nontrivial Ordinal.{u}
  定义体: ⟨⟨1, 0, one_ne_zero⟩⟩

Depends on / 依赖: one_ne_zero
-/
instance nontrivial : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, one_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  statement: {motive : Ordinal -> Prop} (o : Ordinal)
  proof: Quot.inductionOn o fun ⟨α, r, _⟩ => type α r

中文:
定理 inductionOn
  结论: {motive : Ordinal -> 命题} (o : Ordinal)
  证明: Quot.inductionOn o fun ⟨α, r, _⟩ => type α r

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem inductionOn {motive : Ordinal -> Prop} (o : Ordinal)
    (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o :=
  Quot.inductionOn o fun ⟨α, r, _⟩ => type α r

/-- `Quotient.inductionOn₂` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
/--
theorem `inductionOn₂` / 定理 `inductionOn₂`

English:
theorem inductionOn₂
  statement: {motive : Ordinal -> Ordinal -> Prop} (o₁ o₂ : Ordinal)
  proof: Quotient.inductionOn₂ o₁ o₂ fun ⟨α, r, _⟩ ⟨β, s, _⟩ => type α r β s

中文:
定理 inductionOn₂
  结论: {motive : Ordinal -> Ordinal -> 命题} (o₁ o₂ : Ordinal)
  证明: Quotient.inductionOn₂ o₁ o₂ fun ⟨α, r, _⟩ ⟨β, s, _⟩ => type α r β s

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₂ {motive : Ordinal -> Ordinal -> Prop} (o₁ o₂ : Ordinal)
    (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s], motive (type r) (type s)) :
    motive o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun ⟨α, r, _⟩ ⟨β, s, _⟩ => type α r β s

/-- `Quotient.inductionOn₃` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
/--
theorem `inductionOn₃` / 定理 `inductionOn₃`

English:
theorem inductionOn₃
  statement: {motive : Ordinal -> Ordinal -> Ordinal -> Prop} (o₁ o₂ o₃ : Ordinal)
  proof: Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ => type α r β s γ t

中文:
定理 inductionOn₃
  结论: {motive : Ordinal -> Ordinal -> Ordinal -> 命题} (o₁ o₂ o₃ : Ordinal)
  证明: Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ => type α r β s γ t

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₃ {motive : Ordinal -> Ordinal -> Ordinal -> Prop} (o₁ o₂ o₃ : Ordinal)
    (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s] (γ t) [IsWellOrder γ t],
      motive (type r) (type s) (type t)) : motive o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ => type α r β s γ t

open scoped Classical in
/-- To prove a result on ordinals, it suffices to prove it for order types of well-orders. -/
@[elab_as_elim]
/--
theorem `inductionOnWellOrder` / 定理 `inductionOnWellOrder`

English:
theorem inductionOnWellOrder
  statement: {motive : Ordinal -> Prop} (o : Ordinal)
  proof: inductionOn o fun α r wo => @type α (linearOrderOfSTO r) wo.toIsWellFounded

中文:
定理 inductionOnWellOrder
  结论: {motive : Ordinal -> 命题} (o : Ordinal)
  证明: inductionOn o fun α r wo => @type α (linearOrderOfSTO r) wo.toIsWellFounded

Depends on / 依赖: inductionOn, linearOrderOfSTO, toIsWellFounded, wo.toIsWellFounded
-/
theorem inductionOnWellOrder {motive : Ordinal -> Prop} (o : Ordinal)
    (type : forall (α) [LinearOrder α] [WellFoundedLT α], motive (typeLT α)) : motive o :=
  inductionOn o fun α r wo => @type α (linearOrderOfSTO r) wo.toIsWellFounded

open scoped Classical in
/--
Definition of `liftOnWellOrder` / `liftOnWellOrder` 的定义

English:
definition liftOnWellOrder
  signature: {δ : Sort v} (o : Ordinal) (f : forall (α) [LinearOrder α] [WellFoundedLT α], δ)
  body: Quotient.liftOn o (fun w => @f w.α (linearOrderOfSTO w.r) w.wo.toIsWellFounded)
    fun w₁ w₂ h => @c
      w₁.α (linearOrderOfSTO w₁.r) w₁.wo.toIsWellFounded
      w₂.α (linearOrderOfSTO w₂.r) w₂.wo.toIsWellFounded
      (Quotient.sound h)

@[simp]

中文:
定义 liftOnWellOrder
  签名: {δ : Sort v} (o : Ordinal) (f : 对任意 (α) [LinearOrder α] [WellFoundedLT α], δ)
  定义体: Quotient.liftOn o (fun w => @f w.α (linearOrderOfSTO w.r) w.wo.toIsWellFounded)
    fun w₁ w₂ h => @c
      w₁.α (linearOrderOfSTO w₁.r) w₁.wo.toIsWellFounded
      w₂.α (linearOrderOfSTO w₂.r) w₂.wo.toIsWellFounded
      (Quotient.sound h)

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, Quotient.sound, liftOn, linearOrderOfSTO, toIsWellFounded, w.wo.toIsWellFounded, wo.toIsWellFounded
-/
def liftOnWellOrder {δ : Sort v} (o : Ordinal) (f : forall (α) [LinearOrder α] [WellFoundedLT α], δ)
    (c : forall (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β],
      typeLT α = typeLT β -> f α = f β) : δ :=
  Quotient.liftOn o (fun w => @f w.α (linearOrderOfSTO w.r) w.wo.toIsWellFounded)
    fun w₁ w₂ h => @c
      w₁.α (linearOrderOfSTO w₁.r) w₁.wo.toIsWellFounded
      w₂.α (linearOrderOfSTO w₂.r) w₂.wo.toIsWellFounded
      (Quotient.sound h)

@[simp]
/--
theorem `liftOnWellOrder_type` / 定理 `liftOnWellOrder_type`

English:
theorem liftOnWellOrder_type
  statement: {δ : Sort v} (f : forall (α) [LinearOrder α] [WellFoundedLT α], δ)
  proof: by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
  congr
  exact LinearOrder.ext_lt fun _ _ => Iff.rfl

中文:
定理 liftOnWellOrder_type
  结论: {δ : Sort v} (f : 对任意 (α) [LinearOrder α] [WellFoundedLT α], δ)
  证明: by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
  congr
  exact LinearOrder.ext_lt fun _ _ => Iff.rfl

Depends on / 依赖: Iff.rfl, LinearOrder, LinearOrder.ext_lt, Quotient, Quotient.liftOn, ext_lt, liftOn
-/
theorem liftOnWellOrder_type {δ : Sort v} (f : forall (α) [LinearOrder α] [WellFoundedLT α], δ)
    (c : forall (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β],
      typeLT α = typeLT β -> f α = f β) {γ} [LinearOrder γ] [WellFoundedLT γ] :
    liftOnWellOrder (typeLT γ) f c = f γ := by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
  congr
  exact LinearOrder.ext_lt fun _ _ => Iff.rfl

/-! ### The order on ordinals -/

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder Ordinal where
  body: Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≼i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
⟨fun ⟨h⟩ => ⟨f.symm.toInitialSeg.trans h.trans g.toInitialSeg⟩, fun ⟨h⟩ =>
⟨f.toInitialSeg.trans h.trans g.symm.toInitialSeg⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Non

中文:
实例 partialOrder
  签名: : PartialOrder Ordinal where
  定义体: Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≼i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
⟨fun ⟨h⟩ => ⟨f.symm.toInitialSeg.trans h.trans g.toInitialSeg⟩, fun ⟨h⟩ =>
⟨f.toInitialSeg.trans h.trans g.symm.toInitialSeg⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Non

Depends on / 依赖: Nonempty, PrincipalSeg, PrincipalSeg.relIsoTrans, Quot.ind, Quotient, Quotient.liftOn, f.symm, f.symm.toInitialSeg.trans, f.toInitialSeg.trans, g.symm, g.symm.toInitialSeg, g.toInitialSeg, h.trans, h.transRelIso, le_refl, propext, relIsoTrans, toInitialSeg, transRelIso
-/
instance partialOrder : PartialOrder Ordinal where
  le a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≼i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
⟨fun ⟨h⟩ => ⟨f.symm.toInitialSeg.trans h.trans g.toInitialSeg⟩, fun ⟨h⟩ =>
⟨f.toInitialSeg.trans h.trans g.symm.toInitialSeg⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≺i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
⟨fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f.symm h.transRelIso g⟩,
fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f h.transRelIso g.symm⟩⟩
  le_refl := Quot.ind fun ⟨_, _, _⟩ => ⟨InitialSeg.refl _⟩
  le_trans a b c :=
    Quotient.inductionOn₃ a b c fun _ _ _ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  lt_iff_le_not_ge a b :=
    Quotient.inductionOn₂ a b fun _ _ =>
      ⟨fun ⟨f⟩ => ⟨⟨f⟩, fun ⟨g⟩ => (f.transInitial g).irrefl⟩, fun ⟨⟨f⟩, h⟩ =>
        f.principalSumRelIso.recOn (fun g => ⟨g⟩) fun g => (h ⟨g.symm.toInitialSeg⟩).elim⟩
  le_antisymm a b :=
    Quotient.inductionOn₂ a b fun _ _ ⟨h₁⟩ ⟨h₂⟩ =>
      Quot.sound ⟨InitialSeg.antisymm h₁ h₂⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder Ordinal
  body: { (inferInstance : PartialOrder Ordinal) with
    le_total := fun a b => Quotient.inductionOn₂ a b fun ⟨_, r, _⟩ ⟨_, s, _⟩ =>
      (InitialSeg.total r s).recOn (fun f => Or.inl ⟨f⟩) fun f => Or.inr ⟨f⟩
    toDecidableLE := Classical.decRel _ }

中文:
实例 :
  签名: LinearOrder Ordinal
  定义体: { (inferInstance : PartialOrder Ordinal) with
    le_total := fun a b => Quotient.inductionOn₂ a b fun ⟨_, r, _⟩ ⟨_, s, _⟩ =>
      (InitialSeg.total r s).recOn (fun f => Or.inl ⟨f⟩) fun f => Or.inr ⟨f⟩
    toDecidableLE := Classical.decRel _ }

Depends on / 依赖: Classical, Classical.decRel, InitialSeg, InitialSeg.total, Or.inl, Or.inr, Ordinal, PartialOrder, Quotient, Quotient.inductionOn, decRel, le_total, toDecidableLE
-/
instance : LinearOrder Ordinal :=
  { (inferInstance : PartialOrder Ordinal) with
    le_total := fun a b => Quotient.inductionOn₂ a b fun ⟨_, r, _⟩ ⟨_, s, _⟩ =>
      (InitialSeg.total r s).recOn (fun f => Or.inl ⟨f⟩) fun f => Or.inr ⟨f⟩
    toDecidableLE := Classical.decRel _ }

/--
theorem `_root_.InitialSeg.ordinal_type_le` / 定理 `_root_.InitialSeg.ordinal_type_le`

English:
theorem _root_.InitialSeg.ordinal_type_le
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: ⟨h⟩

中文:
定理 _root_.InitialSeg.ordinal_type_le
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: ⟨h⟩
-/
theorem _root_.InitialSeg.ordinal_type_le {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≼i s) : type r <= type s :=
  ⟨h⟩

/--
theorem `_root_.RelEmbedding.ordinal_type_le` / 定理 `_root_.RelEmbedding.ordinal_type_le`

English:
theorem _root_.RelEmbedding.ordinal_type_le
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: ⟨h.collapse⟩

中文:
定理 _root_.RelEmbedding.ordinal_type_le
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: ⟨h.collapse⟩

Depends on / 依赖: collapse, h.collapse
-/
theorem _root_.RelEmbedding.ordinal_type_le {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ↪r s) : type r <= type s :=
  ⟨h.collapse⟩

/--
theorem `_root_.PrincipalSeg.ordinal_type_lt` / 定理 `_root_.PrincipalSeg.ordinal_type_lt`

English:
theorem _root_.PrincipalSeg.ordinal_type_lt
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: ⟨h⟩

中文:
定理 _root_.PrincipalSeg.ordinal_type_lt
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: ⟨h⟩
-/
theorem _root_.PrincipalSeg.ordinal_type_lt {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≺i s) : type r < type s :=
  ⟨h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot Ordinal
  body: 0
  bot_le o := inductionOn o fun _ r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le

@[simp]

中文:
实例 :
  签名: OrderBot Ordinal
  定义体: 0
  bot_le o := inductionOn o fun _ r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le

@[simp]
-/
instance : OrderBot Ordinal where
  bot := 0
  bot_le o := inductionOn o fun _ r _ => (InitialSeg.ofIsEmpty _ r).ordinal_type_le

@[simp]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : Ordinal) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  结论: (⊥ : Ordinal) = 0
  证明: rfl
-/
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl

/--
theorem `type_le_iff` / 定理 `type_le_iff`

English:
theorem type_le_iff
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
  proof: Iff.rfl

中文:
定理 type_le_iff
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem type_le_iff {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r <= type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl

/--
theorem `type_le_iff'` / 定理 `type_le_iff'`

English:
theorem type_le_iff'
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
  proof: ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩

中文:
定理 type_le_iff'
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r]
  证明: ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩

Depends on / 依赖: collapse, f.collapse
-/
theorem type_le_iff' {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r <= type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩

/--
theorem `type_lt_iff` / 定理 `type_lt_iff`

English:
theorem type_lt_iff
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
  proof: Iff.rfl

中文:
定理 type_lt_iff
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem type_lt_iff {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl

/--
theorem `type_set_le` / 定理 `type_set_le`

English:
theorem type_set_le
  given: [LinearOrder α] [WellFoundedLT α] (s : Set α)
  statement: typeLT s <= typeLT α
  proof: by
  rw [type_le_iff']
  refine ⟨⟨Embedding.subtype _, ?_⟩⟩
  simp

中文:
定理 type_set_le
  条件: [LinearOrder α] [WellFoundedLT α] (s : Set α)
  结论: typeLT s <= typeLT α
  证明: by
  rw [type_le_iff']
  refine ⟨⟨Embedding.subtype _, ?_⟩⟩
  simp

Depends on / 依赖: Embedding, Embedding.subtype, subtype, type_le_iff
-/
theorem type_set_le [LinearOrder α] [WellFoundedLT α] (s : Set α) : typeLT s <= typeLT α := by
  rw [type_le_iff']
  refine ⟨⟨Embedding.subtype _, ?_⟩⟩
  simp

/--
theorem `type_mono` / 定理 `type_mono`

English:
theorem type_mono
  given: [LinearOrder α] [WellFoundedLT α] {s t : Set α} (h : s subseteq t)
  proof: by
  rw [type_le_iff']
  refine ⟨⟨embeddingOfSubset _ _ h, ?_⟩⟩
  aesop

中文:
定理 type_mono
  条件: [LinearOrder α] [WellFoundedLT α] {s t : Set α} (h : s subseteq t)
  证明: by
  rw [type_le_iff']
  refine ⟨⟨embeddingOfSubset _ _ h, ?_⟩⟩
  aesop

Depends on / 依赖: embeddingOfSubset, type_le_iff
-/
theorem type_mono [LinearOrder α] [WellFoundedLT α] {s t : Set α} (h : s subseteq t) :
    typeLT s <= typeLT t := by
  rw [type_le_iff']
  refine ⟨⟨embeddingOfSubset _ _ h, ?_⟩⟩
  aesop

/-- Given two ordinals `α ≤ β`, then `initialSegToType α β` is the initial segment embedding of
`α.ToType` into `β.ToType`. -/
@[deprecated type_le_iff (since := "2026-04-12")]
/--
Definition of `initialSegToType` / `initialSegToType` 的定义

English:
definition initialSegToType
  signature: {α β : Ordinal} (h : α <= β)
  body: by
  apply Classical.choice (type_le_iff.mp _)
  rwa [type_toType, type_toType]

中文:
定义 initialSegToType
  签名: {α β : Ordinal} (h : α <= β)
  定义体: by
  apply Classical.choice (type_le_iff.mp _)
  rwa [type_toType, type_toType]

Depends on / 依赖: Classical, Classical.choice, choice, type_le_iff, type_le_iff.mp, type_toType
-/
def initialSegToType {α β : Ordinal} (h : α <= β) : α.ToType <=i β.ToType := by
  apply Classical.choice (type_le_iff.mp _)
  rwa [type_toType, type_toType]

/-- Given two ordinals `α < β`, then `principalSegToType α β` is the principal segment embedding
of `α.ToType` into `β.ToType`. -/
@[deprecated type_lt_iff (since := "2026-04-12")]
/--
Definition of `principalSegToType` / `principalSegToType` 的定义

English:
definition principalSegToType
  signature: {α β : Ordinal} (h : α < β)
  body: by
  apply Classical.choice (type_lt_iff.mp _)
  rwa [type_toType, type_toType]

中文:
定义 principalSegToType
  签名: {α β : Ordinal} (h : α < β)
  定义体: by
  apply Classical.choice (type_lt_iff.mp _)
  rwa [type_toType, type_toType]

Depends on / 依赖: Classical, Classical.choice, choice, type_lt_iff, type_lt_iff.mp, type_toType
-/
def principalSegToType {α β : Ordinal} (h : α < β) : α.ToType <i β.ToType := by
  apply Classical.choice (type_lt_iff.mp _)
  rwa [type_toType, type_toType]

/-! ### Enumerating elements in a well-order with ordinals -/

/--
Definition of `typein` / `typein` 的定义

English:
definition typein
  signature: (r : α -> α -> Prop) [IsWellOrder α r]
  body: by
  refine ⟨RelEmbedding.ofMonotone _ fun a b ha =>
    ((PrincipalSeg.ofElement r a).codRestrict _ ?_ ?_).ordinal_type_lt, type r, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc⟩
    exact trans hc ha
  · exact ha
  · rintro ⟨b, rfl⟩
    exact (PrincipalSeg.ofElement _ _).ordinal_type_lt
  · refine inductio

中文:
定义 typein
  签名: (r : α -> α -> 命题) [IsWellOrder α r]
  定义体: by
  refine ⟨RelEmbedding.ofMonotone _ fun a b ha =>
    ((PrincipalSeg.ofElement r a).codRestrict _ ?_ ?_).ordinal_type_lt, type r, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc⟩
    exact trans hc ha
  · exact ha
  · rintro ⟨b, rfl⟩
    exact (PrincipalSeg.ofElement _ _).ordinal_type_lt
  · refine inductio

Depends on / 依赖: PrincipalSeg, PrincipalSeg.ofElement, RelEmbedding, RelEmbedding.ofMonotone, codRestrict, g.subrelIso.ordinalType_congr, inductionOn, ofElement, ofMonotone, ordinalType_congr, ordinal_type_lt, subrelIso
-/
def typein (r : α -> α -> Prop) [IsWellOrder α r] : @PrincipalSeg α Ordinal.{u} r (· < ·) := by
  refine ⟨RelEmbedding.ofMonotone _ fun a b ha =>
    ((PrincipalSeg.ofElement r a).codRestrict _ ?_ ?_).ordinal_type_lt, type r, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc⟩
    exact trans hc ha
  · exact ha
  · rintro ⟨b, rfl⟩
    exact (PrincipalSeg.ofElement _ _).ordinal_type_lt
  · refine inductionOn a ?_
    rintro β s wo ⟨g⟩
    exact ⟨_, g.subrelIso.ordinalType_congr⟩

@[simp]
/--
theorem `type_subrel` / 定理 `type_subrel`

English:
theorem type_subrel
  given: (r : α -> α -> Prop) [IsWellOrder α r] (a : α)
  proof: rfl

@[simp]

中文:
定理 type_subrel
  条件: (r : α -> α -> 命题) [IsWellOrder α r] (a : α)
  证明: rfl

@[simp]
-/
theorem type_subrel (r : α -> α -> Prop) [IsWellOrder α r] (a : α) :
    type (Subrel r (r · a)) = typein r a :=
  rfl

@[simp]
/--
theorem `top_typein` / 定理 `top_typein`

English:
theorem top_typein
  given: (r : α -> α -> Prop) [IsWellOrder α r]
  statement: (typein r).top = type r
  proof: rfl

中文:
定理 top_typein
  条件: (r : α -> α -> 命题) [IsWellOrder α r]
  结论: (typein r).top = type r
  证明: rfl
-/
theorem top_typein (r : α -> α -> Prop) [IsWellOrder α r] : (typein r).top = type r :=
  rfl

/--
theorem `typein_lt_type` / 定理 `typein_lt_type`

English:
theorem typein_lt_type
  given: (r : α -> α -> Prop) [IsWellOrder α r] (a : α)
  statement: typein r a < type r
  proof: (typein r).lt_top a

中文:
定理 typein_lt_type
  条件: (r : α -> α -> 命题) [IsWellOrder α r] (a : α)
  结论: typein r a < type r
  证明: (typein r).lt_top a

Depends on / 依赖: lt_top, typein
-/
theorem typein_lt_type (r : α -> α -> Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  (typein r).lt_top a

/--
theorem `typein_lt_self` / 定理 `typein_lt_self`

English:
theorem typein_lt_self
  given: {o : Ordinal} (i : o.ToType)
  statement: typein (α := o.ToType) (· < ·) i < o
  proof: by
  simp_rw [← type_toType o]
  apply typein_lt_type

@[simp]

中文:
定理 typein_lt_self
  条件: {o : Ordinal} (i : o.ToType)
  结论: typein (α := o.ToType) (· < ·) i < o
  证明: by
  simp_rw [← type_toType o]
  apply typein_lt_type

@[simp]

Depends on / 依赖: ToType, o.ToType, simp_rw, type_toType, typein_lt_type
-/
theorem typein_lt_self {o : Ordinal} (i : o.ToType) : typein (α := o.ToType) (· < ·) i < o := by
  simp_rw [← type_toType o]
  apply typein_lt_type

@[simp]
/--
theorem `typein_top` / 定理 `typein_top`

English:
theorem typein_top
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: f.subrelIso.ordinalType_congr

@[simp]

中文:
定理 typein_top
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: f.subrelIso.ordinalType_congr

@[simp]

Depends on / 依赖: f.subrelIso.ordinalType_congr, ordinalType_congr, subrelIso
-/
theorem typein_top {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : typein s f.top = type r :=
  f.subrelIso.ordinalType_congr

@[simp]
/--
theorem `typein_lt_typein` / 定理 `typein_lt_typein`

English:
theorem typein_lt_typein
  given: (r : α -> α -> Prop) [IsWellOrder α r] {a b : α}
  proof: (typein r).map_rel_iff

@[simp]

中文:
定理 typein_lt_typein
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {a b : α}
  证明: (typein r).map_rel_iff

@[simp]

Depends on / 依赖: map_rel_iff, typein
-/
theorem typein_lt_typein (r : α -> α -> Prop) [IsWellOrder α r] {a b : α} :
    typein r a < typein r b ↔ r a b :=
  (typein r).map_rel_iff

@[simp]
/--
theorem `typein_le_typein` / 定理 `typein_le_typein`

English:
theorem typein_le_typein
  given: (r : α -> α -> Prop) [IsWellOrder α r] {a b : α}
  proof: by
  rw [← not_lt]; rw [typein_lt_typein]

中文:
定理 typein_le_typein
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {a b : α}
  证明: by
  rw [← not_lt]; rw [typein_lt_typein]

Depends on / 依赖: not_lt, typein_lt_typein
-/
theorem typein_le_typein (r : α -> α -> Prop) [IsWellOrder α r] {a b : α} :
    typein r a <= typein r b ↔ ¬r b a := by
  rw [← not_lt]; rw [typein_lt_typein]

/--
theorem `typein_injective` / 定理 `typein_injective`

English:
theorem typein_injective
  given: (r : α -> α -> Prop) [IsWellOrder α r]
  statement: Injective (typein r)
  proof: (typein r).injective

中文:
定理 typein_injective
  条件: (r : α -> α -> 命题) [IsWellOrder α r]
  结论: Injective (typein r)
  证明: (typein r).injective

Depends on / 依赖: injective, typein
-/
theorem typein_injective (r : α -> α -> Prop) [IsWellOrder α r] : Injective (typein r) :=
  (typein r).injective

/--
theorem `typein_inj` / 定理 `typein_inj`

English:
theorem typein_inj
  given: (r : α -> α -> Prop) [IsWellOrder α r] {a b}
  statement: typein r a = typein r b ↔ a = b
  proof: (typein_injective r).eq_iff

中文:
定理 typein_inj
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {a b}
  结论: typein r a = typein r b ↔ a = b
  证明: (typein_injective r).eq_iff

Depends on / 依赖: eq_iff, typein_injective
-/
theorem typein_inj (r : α -> α -> Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff

/--
theorem `mem_range_typein_iff` / 定理 `mem_range_typein_iff`

English:
theorem mem_range_typein_iff
  given: (r : α -> α -> Prop) [IsWellOrder α r] {o}
  proof: (typein r).mem_range_iff_rel

中文:
定理 mem_range_typein_iff
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {o}
  证明: (typein r).mem_range_iff_rel

Depends on / 依赖: mem_range_iff_rel, typein
-/
theorem mem_range_typein_iff (r : α -> α -> Prop) [IsWellOrder α r] {o} :
    o in Set.range (typein r) ↔ o < type r :=
  (typein r).mem_range_iff_rel

/--
theorem `typein_surj` / 定理 `typein_surj`

English:
theorem typein_surj
  given: (r : α -> α -> Prop) [IsWellOrder α r] {o} (h : o < type r)
  proof: (typein r).mem_range_of_rel_top h

中文:
定理 typein_surj
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {o} (h : o < type r)
  证明: (typein r).mem_range_of_rel_top h

Depends on / 依赖: DilationClass, DilationEquivClass, EquivLike, mem_range_of_rel_top, typein
-/
theorem typein_surj (r : α -> α -> Prop) [IsWellOrder α r] {o} (h : o < type r) :
    o in Set.range (typein r) :=
  (typein r).mem_range_of_rel_top h

/--
theorem `typein_surjOn` / 定理 `typein_surjOn`

English:
theorem typein_surjOn
  given: (r : α -> α -> Prop) [IsWellOrder α r]
  proof: (typein r).surjOn

@[simp]

中文:
定理 typein_surjOn
  条件: (r : α -> α -> 命题) [IsWellOrder α r]
  证明: (typein r).surjOn

@[simp]

Depends on / 依赖: surjOn, typein
-/
theorem typein_surjOn (r : α -> α -> Prop) [IsWellOrder α r] :
    Set.SurjOn (typein r) Set.univ (Set.Iio (type r)) :=
  (typein r).surjOn

@[simp]
/--
theorem `type_Iio_lt` / 定理 `type_Iio_lt`

English:
theorem type_Iio_lt
  given: [LinearOrder α] [WellFoundedLT α] (x : α)
  proof: rfl

中文:
定理 type_Iio_lt
  条件: [LinearOrder α] [WellFoundedLT α] (x : α)
  证明: rfl

Depends on / 依赖: LT.lt, typein
-/
theorem type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : α) :
    type (α := Iio x) LT.lt = typein LT.lt x :=
  rfl

/-- A well order `r` is order-isomorphic to the set of ordinals smaller than `type r`.
`enum r ⟨o, h⟩` is the `o`-th element of `α` ordered by `r`.

That is, `enum` maps an initial segment of the ordinals, those less than the order type of `r`, to
the elements of `α`. -/
@[simps! symm_apply_coe]
/--
Definition of `enum` / `enum` 的定义

English:
definition enum
  signature: (r : α -> α -> Prop) [IsWellOrder α r]
  body: (typein r).subrelIso

@[simp]

中文:
定义 enum
  签名: (r : α -> α -> 命题) [IsWellOrder α r]
  定义体: (typein r).subrelIso

@[simp]

Depends on / 依赖: subrelIso, typein
-/
def enum (r : α -> α -> Prop) [IsWellOrder α r] : (· < · : Iio (type r) -> Iio (type r) -> Prop) ≃r r :=
  (typein r).subrelIso

@[simp]
/--
theorem `typein_enum` / 定理 `typein_enum`

English:
theorem typein_enum
  given: (r : α -> α -> Prop) [IsWellOrder α r] {o} (h : o < type r)
  proof: (typein r).apply_subrelIso _

中文:
定理 typein_enum
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {o} (h : o < type r)
  证明: (typein r).apply_subrelIso _

Depends on / 依赖: apply_subrelIso, typein
-/
theorem typein_enum (r : α -> α -> Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r ⟨o, h⟩) = o :=
  (typein r).apply_subrelIso _

/--
theorem `enum_type` / 定理 `enum_type`

English:
theorem enum_type
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s]
  proof: (typein r).injective (typein_enum _ _).trans (typein_top _).symm

@[simp]

中文:
定理 enum_type
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r] [IsWellOrder β s]
  证明: (typein r).injective (typein_enum _ _).trans (typein_top _).symm

@[simp]

Depends on / 依赖: injective, typein, typein_enum, typein_top
-/
theorem enum_type {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : s ≺i r) {h : type s < type r} : enum r ⟨type s, h⟩ = f.top :=
(typein r).injective (typein_enum _ _).trans (typein_top _).symm

@[simp]
/--
theorem `enum_typein` / 定理 `enum_typein`

English:
theorem enum_typein
  given: (r : α -> α -> Prop) [IsWellOrder α r] (a : α)
  proof: enum_type (PrincipalSeg.ofElement r a)

中文:
定理 enum_typein
  条件: (r : α -> α -> 命题) [IsWellOrder α r] (a : α)
  证明: enum_type (PrincipalSeg.ofElement r a)

Depends on / 依赖: PrincipalSeg, PrincipalSeg.ofElement, enum_type, ofElement
-/
theorem enum_typein (r : α -> α -> Prop) [IsWellOrder α r] (a : α) :
    enum r ⟨typein r a, typein_lt_type r a⟩ = a :=
  enum_type (PrincipalSeg.ofElement r a)

/--
theorem `enum_lt_enum` / 定理 `enum_lt_enum`

English:
theorem enum_lt_enum
  given: {r : α -> α -> Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
  proof: (enum _).map_rel_iff

中文:
定理 enum_lt_enum
  条件: {r : α -> α -> 命题} [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
  证明: (enum _).map_rel_iff

Depends on / 依赖: e.symm, map_rel_iff
-/
theorem enum_lt_enum {r : α -> α -> Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    r (enum r o₁) (enum r o₂) ↔ o₁ < o₂ :=
  (enum _).map_rel_iff

/--
theorem `enum_le_enum` / 定理 `enum_le_enum`

English:
theorem enum_le_enum
  given: (r : α -> α -> Prop) [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
  proof: by
  rw [enum_lt_enum (r := r)]; rw [not_lt]

中文:
定理 enum_le_enum
  条件: (r : α -> α -> 命题) [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
  证明: by
  rw [enum_lt_enum (r := r)]; rw [not_lt]

Depends on / 依赖: enum_lt_enum, not_lt
-/
theorem enum_le_enum (r : α -> α -> Prop) [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    ¬r (enum r o₁) (enum r o₂) ↔ o₂ <= o₁ := by
  rw [enum_lt_enum (r := r)]; rw [not_lt]

-- TODO: generalize to other well-orders
@[simp]
/--
theorem `enum_le_enum'` / 定理 `enum_le_enum'`

English:
theorem enum_le_enum'
  given: (a : Ordinal) {o₁ o₂ : Iio (type (· < ·))}
  proof: by
  rw [← enum_le_enum]; rw [not_lt]

中文:
定理 enum_le_enum'
  条件: (a : Ordinal) {o₁ o₂ : Iio (type (· < ·))}
  证明: by
  rw [← enum_le_enum]; rw [not_lt]

Depends on / 依赖: ToType, a.ToType, enum_le_enum, not_lt
-/
theorem enum_le_enum' (a : Ordinal) {o₁ o₂ : Iio (type (· < ·))} :
    enum (· < ·) o₁ <= enum (α := a.ToType) (· < ·) o₂ ↔ o₁ <= o₂ := by
  rw [← enum_le_enum]; rw [not_lt]

/--
theorem `enum_inj` / 定理 `enum_inj`

English:
theorem enum_inj
  given: {r : α -> α -> Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
  proof: EmbeddingLike.apply_eq_iff_eq _

中文:
定理 enum_inj
  条件: {r : α -> α -> 命题} [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
  证明: EmbeddingLike.apply_eq_iff_eq _

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, apply_eq_iff_eq
-/
theorem enum_inj {r : α -> α -> Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    enum r o₁ = enum r o₂ ↔ o₁ = o₂ :=
  EmbeddingLike.apply_eq_iff_eq _

/--
theorem `enum_zero_le` / 定理 `enum_zero_le`

English:
theorem enum_zero_le
  given: {r : α -> α -> Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α)
  proof: by
  rw [← enum_typein r a]; rw [enum_le_enum r]
  exact bot_le (α := Ordinal)

中文:
定理 enum_zero_le
  条件: {r : α -> α -> 命题} [IsWellOrder α r] (h0 : 0 < type r) (a : α)
  证明: by
  rw [← enum_typein r a]; rw [enum_le_enum r]
  exact bot_le (α := Ordinal)

Depends on / 依赖: Ordinal, bot_le, enum_le_enum, enum_typein
-/
theorem enum_zero_le {r : α -> α -> Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) :
    ¬r a (enum r ⟨0, h0⟩) := by
  rw [← enum_typein r a]; rw [enum_le_enum r]
  exact bot_le (α := Ordinal)

/--
theorem `enum_zero_le'` / 定理 `enum_zero_le'`

English:
theorem enum_zero_le'
  given: {o : Ordinal} (h0 : 0 < o) (a : o.ToType)
  proof: by
  rw [← not_lt]
  apply enum_zero_le

中文:
定理 enum_zero_le'
  条件: {o : Ordinal} (h0 : 0 < o) (a : o.ToType)
  证明: by
  rw [← not_lt]
  apply enum_zero_le

Depends on / 依赖: ToType, enum_zero_le, not_lt, o.ToType, type_toType
-/
theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.ToType) :
    enum (α := o.ToType) (· < ·) ⟨0, type_toType _ ▸ h0⟩ <= a := by
  rw [← not_lt]
  apply enum_zero_le

set_option backward.isDefEq.respectTransparency false in
/--
theorem `relIso_enum'` / 定理 `relIso_enum'`

English:
theorem relIso_enum'
  statement: {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
  proof: by
  refine inductionOn o ?_; rintro γ t wo ⟨g⟩ ⟨h⟩
  rw [enum_type g]; rw [enum_type (g.transRelIso f)]; rfl

中文:
定理 relIso_enum'
  结论: {α β : 类型u} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r]
  证明: by
  refine inductionOn o ?_; rintro γ t wo ⟨g⟩ ⟨h⟩
  rw [enum_type g]; rw [enum_type (g.transRelIso f)]; rfl

Depends on / 依赖: enum_type, g.transRelIso, inductionOn, transRelIso
-/
theorem relIso_enum' {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) :
    forall (hr : o < type r) (hs : o < type s), f (enum r ⟨o, hr⟩) = enum s ⟨o, hs⟩ := by
  refine inductionOn o ?_; rintro γ t wo ⟨g⟩ ⟨h⟩
  rw [enum_type g]; rw [enum_type (g.transRelIso f)]; rfl

/--
theorem `relIso_enum` / 定理 `relIso_enum`

English:
theorem relIso_enum
  statement: {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
  proof: relIso_enum' _ _ _ _

中文:
定理 relIso_enum
  结论: {α β : 类型u} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r]
  证明: relIso_enum' _ _ _ _

Depends on / 依赖: relIso_enum
-/
theorem relIso_enum {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r ⟨o, hr⟩) = enum s ⟨o, hr.trans_eq (Quotient.sound ⟨f⟩)⟩ :=
  relIso_enum' _ _ _ _

/-- The order isomorphism between ordinals less than `o` and `o.ToType`. -/
@[simps! -isSimp]
/--
Definition of `ToType.mk` / `ToType.mk` 的定义

English:
definition ToType.mk
  signature: {o : Ordinal}
  body: enum (α := o.ToType) (· < ·) ⟨x.1, type_toType _ ▸ x.2⟩
  invFun x := ⟨typein (α := o.ToType) (· < ·) x, typein_lt_self x⟩
  left_inv _ := Subtype.ext (typein_enum _ _)
  right_inv _ := enum_typein _ _
  map_rel_iff' := enum_le_enum' _

中文:
定义 ToType.mk
  签名: {o : Ordinal}
  定义体: enum (α := o.ToType) (· < ·) ⟨x.1, type_toType _ ▸ x.2⟩
  invFun x := ⟨typein (α := o.ToType) (· < ·) x, typein_lt_self x⟩
  left_inv _ := Subtype.ext (typein_enum _ _)
  right_inv _ := enum_typein _ _
  map_rel_iff' := enum_le_enum' _

Depends on / 依赖: ToType, o.ToType, type_toType
-/
def ToType.mk {o : Ordinal} : Set.Iio o ≃o o.ToType where
  toFun x := enum (α := o.ToType) (· < ·) ⟨x.1, type_toType _ ▸ x.2⟩
  invFun x := ⟨typein (α := o.ToType) (· < ·) x, typein_lt_self x⟩
  left_inv _ := Subtype.ext (typein_enum _ _)
  right_inv _ := enum_typein _ _
  map_rel_iff' := enum_le_enum' _

/--
Definition of `ToType.toOrd` / `ToType.toOrd` 的定义

English:
abbreviation ToType.toOrd
  signature: {o : Ordinal} (α : o.ToType)
  body: ToType.mk.symm α

中文:
缩写 ToType.toOrd
  签名: {o : Ordinal} (α : o.ToType)
  定义体: ToType.mk.symm α

Depends on / 依赖: ToType, ToType.mk.symm
-/
abbrev ToType.toOrd {o : Ordinal} (α : o.ToType) : Set.Iio o := ToType.mk.symm α

instance (o : Ordinal) : Coe o.ToType (Set.Iio o) where
  coe := ToType.toOrd
instance (o : Ordinal) : CoeOut o.ToType Ordinal where
  coe x := x.toOrd

/--
Instance `small_Iio` / 实例 `small_Iio`

English:
instance small_Iio
  signature: (o : Ordinal.{u})
  body: ⟨_, ⟨ToType.mk.toEquiv⟩⟩

中文:
实例 small_Iio
  签名: (o : Ordinal.{u})
  定义体: ⟨_, ⟨ToType.mk.toEquiv⟩⟩

Depends on / 依赖: ToType, ToType.mk.toEquiv, toEquiv
-/
instance small_Iio (o : Ordinal.{u}) : Small.{u} (Iio o) :=
  ⟨_, ⟨ToType.mk.toEquiv⟩⟩

/--
Instance `small_Iic` / 实例 `small_Iic`

English:
instance small_Iic
  signature: (o : Ordinal.{u})
  body: by
  rw [← Iio_union_right]
  infer_instance

中文:
实例 small_Iic
  签名: (o : Ordinal.{u})
  定义体: by
  rw [← Iio_union_right]
  infer_instance

Depends on / 依赖: Iio_union_right, infer_instance
-/
instance small_Iic (o : Ordinal.{u}) : Small.{u} (Iic o) := by
  rw [← Iio_union_right]
  infer_instance

/--
Instance `small_Ico` / 实例 `small_Ico`

English:
instance small_Ico
  signature: (a b : Ordinal.{u})
  body: small_subset Ico_subset_Iio_self

中文:
实例 small_Ico
  签名: (a b : Ordinal.{u})
  定义体: small_subset Ico_subset_Iio_self

Depends on / 依赖: Ico_subset_Iio_self, small_subset
-/
instance small_Ico (a b : Ordinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
/--
Instance `small_Icc` / 实例 `small_Icc`

English:
instance small_Icc
  signature: (a b : Ordinal.{u})
  body: small_subset Icc_subset_Iic_self

中文:
实例 small_Icc
  签名: (a b : Ordinal.{u})
  定义体: small_subset Icc_subset_Iic_self

Depends on / 依赖: Icc_subset_Iic_self, small_subset
-/
instance small_Icc (a b : Ordinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
/--
Instance `small_Ioo` / 实例 `small_Ioo`

English:
instance small_Ioo
  signature: (a b : Ordinal.{u})
  body: small_subset Ioo_subset_Iio_self

中文:
实例 small_Ioo
  签名: (a b : Ordinal.{u})
  定义体: small_subset Ioo_subset_Iio_self

Depends on / 依赖: Ioo_subset_Iio_self, small_subset
-/
instance small_Ioo (a b : Ordinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self
/--
Instance `small_Ioc` / 实例 `small_Ioc`

English:
instance small_Ioc
  signature: (a b : Ordinal.{u})
  body: small_subset Ioc_subset_Iic_self

中文:
实例 small_Ioc
  签名: (a b : Ordinal.{u})
  定义体: small_subset Ioc_subset_Iic_self

Depends on / 依赖: Ioc_subset_Iic_self, small_subset
-/
instance small_Ioc (a b : Ordinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self

/-- `o.ToType` is an `OrderBot` whenever `o ≠ 0`. -/
@[instance_reducible, deprecated WellFoundedLT.toOrderBot (since := "2026-04-12")]
/--
Definition of `toTypeOrderBot` / `toTypeOrderBot` 的定义

English:
definition toTypeOrderBot
  signature: {o : Ordinal} (ho : o != 0)
  body: (enum (· < ·)) ⟨0, _⟩
  bot_le := enum_zero_le' (bot_lt_iff_ne_bot.2 ho)

@[deprecated "use `WellFoundedLT.toOrderBot` if you need an `OrderBot` instance"
(since := "2026-04-12")]

中文:
定义 toTypeOrderBot
  签名: {o : Ordinal} (ho : o != 0)
  定义体: (enum (· < ·)) ⟨0, _⟩
  bot_le := enum_zero_le' (bot_lt_iff_ne_bot.2 ho)

@[deprecated "use `WellFoundedLT.toOrderBot` if you need an `OrderBot` instance"
(since := "2026-04-12")]
-/
def toTypeOrderBot {o : Ordinal} (ho : o != 0) : OrderBot o.ToType where
  bot := (enum (· < ·)) ⟨0, _⟩
  bot_le := enum_zero_le' (bot_lt_iff_ne_bot.2 ho)

@[deprecated "use `WellFoundedLT.toOrderBot` if you need an `OrderBot` instance"
(since := "2026-04-12")]
/--
theorem `enum_zero_eq_bot` / 定理 `enum_zero_eq_bot`

English:
theorem enum_zero_eq_bot
  given: {o : Ordinal} (ho : 0 < o)
  proof: toTypeOrderBot (o := o) (by rintro rfl; simp at ho)
      (⊥ : o.ToType) :=
  rfl

中文:
定理 enum_zero_eq_bot
  条件: {o : Ordinal} (ho : 0 < o)
  证明: toTypeOrderBot (o := o) (by rintro rfl; simp at ho)
      (⊥ : o.ToType) :=
  rfl

Depends on / 依赖: ToType, o.ToType, type_toType
-/
theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (α := o.ToType) (· < ·) ⟨0, by rwa [type_toType]⟩ =
      have H := toTypeOrderBot (o := o) (by rintro rfl; simp at ho)
      (⊥ : o.ToType) :=
  rfl

/--
theorem `lt_wf` / 定理 `lt_wf`

English:
theorem lt_wf
  statement: @WellFounded Ordinal (· < ·)
  proof: wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ =>
    RelHomClass.wellFounded (enum _) wo.wf)

中文:
定理 lt_wf
  结论: @WellFounded Ordinal (· < ·)
  证明: wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ =>
    RelHomClass.wellFounded (enum _) wo.wf)

Depends on / 依赖: RelHomClass, RelHomClass.wellFounded, induction_on, wellFounded, wellFounded_iff_wellFounded_subrel, wellFounded_iff_wellFounded_subrel.mpr, wo.wf
-/
theorem lt_wf : @WellFounded Ordinal (· < ·) :=
  wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ =>
    RelHomClass.wellFounded (enum _) wo.wf)

/--
Instance `wellFoundedRelation` / 实例 `wellFoundedRelation`

English:
instance wellFoundedRelation
  signature: : WellFoundedRelation Ordinal
  body: ⟨(· < ·), lt_wf⟩

中文:
实例 wellFoundedRelation
  签名: : WellFoundedRelation Ordinal
  定义体: ⟨(· < ·), lt_wf⟩

Depends on / 依赖: lt_wf
-/
instance wellFoundedRelation : WellFoundedRelation Ordinal :=
  ⟨(· < ·), lt_wf⟩

/--
Instance `wellFoundedLT` / 实例 `wellFoundedLT`

English:
instance wellFoundedLT
  signature: : WellFoundedLT Ordinal
  body: ⟨lt_wf⟩

中文:
实例 wellFoundedLT
  签名: : WellFoundedLT Ordinal
  定义体: ⟨lt_wf⟩

Depends on / 依赖: lt_wf
-/
instance wellFoundedLT : WellFoundedLT Ordinal :=
  ⟨lt_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConditionallyCompleteLinearOrderBot Ordinal
  body: WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[deprecated WellFoundedLT.induction (since := "2026-02-27")]

中文:
实例 :
  签名: ConditionallyCompleteLinearOrderBot Ordinal
  定义体: WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[deprecated WellFoundedLT.induction (since := "2026-02-27")]

Depends on / 依赖: WellFoundedLT, WellFoundedLT.conditionallyCompleteLinearOrderBot, conditionallyCompleteLinearOrderBot
-/
instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[deprecated WellFoundedLT.induction (since := "2026-02-27")]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  given: {p : Ordinal.{u} -> Prop} (i : Ordinal.{u}) (h : forall j, (forall k, k < j -> p k) -> p j)
  proof: WellFoundedLT.induction i h

中文:
定理 induction
  条件: {p : Ordinal.{u} -> 命题} (i : Ordinal.{u}) (h : 对任意 j, (对任意 k, k < j -> p k) -> p j)
  证明: WellFoundedLT.induction i h

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction
-/
theorem induction {p : Ordinal.{u} -> Prop} (i : Ordinal.{u}) (h : forall j, (forall k, k < j -> p k) -> p j) :
    p i :=
  WellFoundedLT.induction i h

/--
theorem `typein_apply` / 定理 `typein_apply`

English:
theorem typein_apply
  statement: {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s]
  proof: by
  rw [← f.transPrincipal_apply _ a]; rw [(f.transPrincipal _).eq]

中文:
定理 typein_apply
  结论: {α β} {r : α -> α -> 命题} {s : β -> β -> 命题} [IsWellOrder α r] [IsWellOrder β s]
  证明: by
  rw [← f.transPrincipal_apply _ a]; rw [(f.transPrincipal _).eq]

Depends on / 依赖: f.transPrincipal, f.transPrincipal_apply, transPrincipal, transPrincipal_apply
-/
theorem typein_apply {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) : typein s (f a) = typein r a := by
  rw [← f.transPrincipal_apply _ a]; rw [(f.transPrincipal _).eq]

/-! ### Cardinality of ordinals -/

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: : Ordinal -> Cardinal
  body: Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩

@[simp]

中文:
定义 card
  签名: : Ordinal -> Cardinal
  定义体: Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.map, WellOrder, e.toEquiv, toEquiv
-/
def card : Ordinal -> Cardinal :=
  Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩

@[simp]
/--
theorem `card_type` / 定理 `card_type`

English:
theorem card_type
  given: (r : α -> α -> Prop) [IsWellOrder α r]
  statement: card (type r) = #α
  proof: rfl

@[simp]

中文:
定理 card_type
  条件: (r : α -> α -> 命题) [IsWellOrder α r]
  结论: card (type r) = #α
  证明: rfl

@[simp]
-/
theorem card_type (r : α -> α -> Prop) [IsWellOrder α r] : card (type r) = #α :=
  rfl

@[simp]
/--
theorem `card_typein` / 定理 `card_typein`

English:
theorem card_typein
  given: {r : α -> α -> Prop} [IsWellOrder α r] (x : α)
  proof: rfl

@[gcongr]

中文:
定理 card_typein
  条件: {r : α -> α -> 命题} [IsWellOrder α r] (x : α)
  证明: rfl

@[gcongr]
-/
theorem card_typein {r : α -> α -> Prop} [IsWellOrder α r] (x : α) :
    (typein r x).card = #{ y // r y x } :=
  rfl

@[gcongr]
/--
theorem `card_le_card` / 定理 `card_le_card`

English:
theorem card_le_card
  given: {o₁ o₂ : Ordinal}
  statement: o₁ <= o₂ -> card o₁ <= card o₂
  proof: inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

@[simp]

中文:
定理 card_le_card
  条件: {o₁ o₂ : Ordinal}
  结论: o₁ <= o₂ -> card o₁ <= card o₂
  证明: inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

@[simp]

Depends on / 依赖: inductionOn
-/
theorem card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card o₁ <= card o₂ :=
  inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

@[simp]
/--
theorem `card_zero` / 定理 `card_zero`

English:
theorem card_zero
  statement: card 0 = 0
  proof: mk_eq_zero _

@[simp]

中文:
定理 card_zero
  结论: card 0 = 0
  证明: mk_eq_zero _

@[simp]

Depends on / 依赖: mk_eq_zero
-/
theorem card_zero : card 0 = 0 := mk_eq_zero _

@[simp]
/--
theorem `card_one` / 定理 `card_one`

English:
theorem card_one
  statement: card 1 = 1
  proof: mk_eq_one _

@[simp]

中文:
定理 card_one
  结论: card 1 = 1
  证明: mk_eq_one _

@[simp]

Depends on / 依赖: mk_eq_one
-/
theorem card_one : card 1 = 1 := mk_eq_one _

@[simp]
/--
theorem `_root_.Cardinal.mk_toType` / 定理 `_root_.Cardinal.mk_toType`

English:
theorem _root_.Cardinal.mk_toType
  given: (o : Ordinal)
  statement: #o.ToType = o.card
  proof: (Ordinal.card_type _).symm.trans by rw [Ordinal.type_toType]

中文:
定理 _root_.Cardinal.mk_toType
  条件: (o : Ordinal)
  结论: #o.ToType = o.card
  证明: (Ordinal.card_type _).symm.trans by rw [Ordinal.type_toType]

Depends on / 依赖: Ordinal, Ordinal.card_type, Ordinal.type_toType, card_type, symm.trans, type_toType
-/
theorem _root_.Cardinal.mk_toType (o : Ordinal) : #o.ToType = o.card :=
(Ordinal.card_type _).symm.trans by rw [Ordinal.type_toType]

variable (r) in
/--
theorem `card_typein_min_le_mk` / 定理 `card_typein_min_le_mk`

English:
theorem card_typein_min_le_mk
  given: [IsWellOrder α r] {s : Set α} (hs : sᶜ.Nonempty)
  proof: IsWellFounded.wf.cardinalMk_subtype_lt_min_compl_le hs

中文:
定理 card_typein_min_le_mk
  条件: [IsWellOrder α r] {s : Set α} (hs : sᶜ.Nonempty)
  证明: IsWellFounded.wf.cardinalMk_subtype_lt_min_compl_le hs
-/
theorem card_typein_min_le_mk [IsWellOrder α r] {s : Set α} (hs : sᶜ.Nonempty) :
    (typein r <| IsWellFounded.wf.min (r := r) sᶜ hs).card <= #s :=
  IsWellFounded.wf.cardinalMk_subtype_lt_min_compl_le hs

/-! ### Lifting ordinals to a higher universe -/

/-- The universe lift operation for ordinals, which embeds `Ordinal.{u}` as
  a proper initial segment of `Ordinal.{v}` for `v > u`. For the initial segment version,
  see `liftInitialSeg`. -/
@[pp_with_univ]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (o : Ordinal.{v})
  body: Quotient.liftOn o (fun w => type <| ULift.down ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
⟨(RelIso.preimage Equiv.ulift r).trans f.trans (RelIso.preimage Equiv.ulift s).symm⟩

@[simp]

中文:
定义 lift
  签名: (o : Ordinal.{v})
  定义体: Quotient.liftOn o (fun w => type <| ULift.down ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
⟨(RelIso.preimage Equiv.ulift r).trans f.trans (RelIso.preimage Equiv.ulift s).symm⟩

@[simp]

Depends on / 依赖: Equiv.ulift, Quot.sound, Quotient, Quotient.liftOn, RelIso, RelIso.preimage, ULift.down, f.trans, liftOn, preimage
-/
def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  Quotient.liftOn o (fun w => type <| ULift.down ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
⟨(RelIso.preimage Equiv.ulift r).trans f.trans (RelIso.preimage Equiv.ulift s).symm⟩

@[simp]
/--
theorem `type_ulift` / 定理 `type_ulift`

English:
theorem type_ulift
  given: (r : α -> α -> Prop) [IsWellOrder α r]
  proof: rfl

@[deprecated (since := "2026-02-20")] alias type_uLift := type_ulift

@[simp]

中文:
定理 type_ulift
  条件: (r : α -> α -> 命题) [IsWellOrder α r]
  证明: rfl

@[deprecated (since := "2026-02-20")] alias type_uLift := type_ulift

@[simp]
-/
theorem type_ulift (r : α -> α -> Prop) [IsWellOrder α r] :
    type (ULift.down ⁻¹'o r) = lift.{v} (type r) :=
  rfl

@[deprecated (since := "2026-02-20")] alias type_uLift := type_ulift

@[simp]
/--
theorem `type_lt_ulift` / 定理 `type_lt_ulift`

English:
theorem type_lt_ulift
  given: [LinearOrder α] [WellFoundedLT α]
  proof: rfl

中文:
定理 type_lt_ulift
  条件: [LinearOrder α] [WellFoundedLT α]
  证明: rfl
-/
theorem type_lt_ulift [LinearOrder α] [WellFoundedLT α] :
    typeLT (ULift α) = lift.{v} (typeLT α) :=
  rfl

/--
theorem `_root_.RelIso.ordinal_lift_type_eq` / 定理 `_root_.RelIso.ordinal_lift_type_eq`

English:
theorem _root_.RelIso.ordinal_lift_type_eq
  statement: {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinalType_congr

@[simp]

中文:
定理 _root_.RelIso.ordinal_lift_type_eq
  结论: {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinalType_congr

@[simp]

Depends on / 依赖: Equiv.ulift, RelIso, RelIso.preimage, f.trans, ordinalType_congr, preimage
-/
theorem _root_.RelIso.ordinal_lift_type_eq {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) : lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinalType_congr

@[simp]
/--
theorem `type_preimage` / 定理 `type_preimage`

English:
theorem type_preimage
  given: {α β : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β ≃ α)
  proof: (RelIso.preimage f r).ordinalType_congr

@[simp]

中文:
定理 type_preimage
  条件: {α β : 类型u} (r : α -> α -> 命题) [IsWellOrder α r] (f : β ≃ α)
  证明: (RelIso.preimage f r).ordinalType_congr

@[simp]

Depends on / 依赖: RelIso, RelIso.preimage, ordinalType_congr, preimage
-/
theorem type_preimage {α β : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β ≃ α) :
    type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinalType_congr

@[simp]
/--
theorem `type_lift_preimage` / 定理 `type_lift_preimage`

English:
theorem type_lift_preimage
  statement: (r : α -> α -> Prop) [IsWellOrder α r]
  proof: (RelIso.preimage f r).ordinal_lift_type_eq

中文:
定理 type_lift_preimage
  结论: (r : α -> α -> 命题) [IsWellOrder α r]
  证明: (RelIso.preimage f r).ordinal_lift_type_eq

Depends on / 依赖: RelIso, RelIso.preimage, ordinal_lift_type_eq, preimage
-/
theorem type_lift_preimage (r : α -> α -> Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

/--
theorem `lift_umax` / 定理 `lift_umax`

English:
theorem lift_umax
  statement: lift.{max u v, u} = lift.{v, u}
  proof: funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩

中文:
定理 lift_umax
  结论: lift.{max u v, u} = lift.{v, u}
  证明: funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩

Depends on / 依赖: Equiv.ulift, Quotient, Quotient.sound, RelIso, RelIso.preimage, inductionOn, preimage
-/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩

/--
theorem `lift_id'` / 定理 `lift_id'`

English:
theorem lift_id'
  given: (a : Ordinal)
  statement: lift a = a
  proof: inductionOn a fun _ r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩

中文:
定理 lift_id'
  条件: (a : Ordinal)
  结论: lift a = a
  证明: inductionOn a fun _ r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩

Depends on / 依赖: Equiv.ulift, Quotient, Quotient.sound, RelIso, RelIso.preimage, inductionOn, preimage
-/
theorem lift_id' (a : Ordinal) : lift a = a :=
  inductionOn a fun _ r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩

/-- An ordinal lifted to the same universe equals itself. -/
@[simp]
/--
theorem `lift_id` / 定理 `lift_id`

English:
theorem lift_id
  statement: forall a, lift.{u, u} a = a
  proof: lift_id'.{u, u}

中文:
定理 lift_id
  结论: 对任意 a, lift.{u, u} a = a
  证明: lift_id'.{u, u}

Depends on / 依赖: lift_id
-/
theorem lift_id : forall a, lift.{u, u} a = a :=
  lift_id'.{u, u}

/-- An ordinal lifted to the zero universe equals itself. -/
@[simp]
/--
theorem `lift_uzero` / 定理 `lift_uzero`

English:
theorem lift_uzero
  given: (a : Ordinal.{u})
  statement: lift.{0} a = a
  proof: lift_id' a

中文:
定理 lift_uzero
  条件: (a : Ordinal.{u})
  结论: lift.{0} a = a
  证明: lift_id' a

Depends on / 依赖: lift_id
-/
theorem lift_uzero (a : Ordinal.{u}) : lift.{0} a = a :=
  lift_id' a

/--
theorem `lift_type_le` / 定理 `lift_type_le`

English:
theorem lift_type_le
  given: {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s]
  proof: by
  constructor <;> refine fun ⟨f⟩ => ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).toInitialSeg)
  · exact (RelIso.preimage Equiv.ulift r).toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).symm.toInitialSeg)

中文:
定理 lift_type_le
  条件: {α : 类型u} {β : 类型v} {r s} [IsWellOrder α r] [IsWellOrder β s]
  证明: by
  constructor <;> refine fun ⟨f⟩ => ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).toInitialSeg)
  · exact (RelIso.preimage Equiv.ulift r).toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).symm.toInitialSeg)

Depends on / 依赖: Equiv.ulift, RelIso, RelIso.preimage, f.trans, preimage, symm.toInitialSeg, symm.toInitialSeg.trans, toInitialSeg, toInitialSeg.trans
-/
theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) <= lift.{max u w} (type s) ↔ Nonempty (r ≼i s) := by
  constructor <;> refine fun ⟨f⟩ => ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).toInitialSeg)
  · exact (RelIso.preimage Equiv.ulift r).toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).symm.toInitialSeg)

/--
theorem `lift_type_eq` / 定理 `lift_type_eq`

English:
theorem lift_type_eq
  given: {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s]
  proof: by
  refine Quotient.eq'.trans ⟨?_, ?_⟩ <;> refine fun ⟨f⟩ => ⟨?_⟩
· exact (RelIso.preimage Equiv.ulift r).symm.trans f.trans (RelIso.preimage Equiv.ulift s)
· exact (RelIso.preimage Equiv.ulift r).trans f.trans (RelIso.preimage Equiv.ulift s).symm

中文:
定理 lift_type_eq
  条件: {α : 类型u} {β : 类型v} {r s} [IsWellOrder α r] [IsWellOrder β s]
  证明: by
  refine Quotient.eq'.trans ⟨?_, ?_⟩ <;> refine fun ⟨f⟩ => ⟨?_⟩
· exact (RelIso.preimage Equiv.ulift r).symm.trans f.trans (RelIso.preimage Equiv.ulift s)
· exact (RelIso.preimage Equiv.ulift r).trans f.trans (RelIso.preimage Equiv.ulift s).symm

Depends on / 依赖: Equiv.ulift, Quotient, Quotient.eq, RelIso, RelIso.preimage, f.trans, preimage, symm.trans
-/
theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) := by
  refine Quotient.eq'.trans ⟨?_, ?_⟩ <;> refine fun ⟨f⟩ => ⟨?_⟩
· exact (RelIso.preimage Equiv.ulift r).symm.trans f.trans (RelIso.preimage Equiv.ulift s)
· exact (RelIso.preimage Equiv.ulift r).trans f.trans (RelIso.preimage Equiv.ulift s).symm

/--
theorem `lift_type_lt` / 定理 `lift_type_lt`

English:
theorem lift_type_lt
  given: {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s]
  proof: by
  constructor <;> refine fun ⟨f⟩ => ⟨?_⟩
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r).symm).transInitial
      (RelIso.preimage Equiv.ulift s).toInitialSeg
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r)).transInitial
      (RelIso.preimage Equiv.ulift s).symm.toInitialSeg

@

中文:
定理 lift_type_lt
  条件: {α : 类型u} {β : 类型v} {r s} [IsWellOrder α r] [IsWellOrder β s]
  证明: by
  constructor <;> refine fun ⟨f⟩ => ⟨?_⟩
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r).symm).transInitial
      (RelIso.preimage Equiv.ulift s).toInitialSeg
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r)).transInitial
      (RelIso.preimage Equiv.ulift s).symm.toInitialSeg

@

Depends on / 依赖: Equiv.ulift, RelIso, RelIso.preimage, f.relIsoTrans, preimage, relIsoTrans, symm.toInitialSeg, toInitialSeg, transInitial
-/
theorem lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s) := by
  constructor <;> refine fun ⟨f⟩ => ⟨?_⟩
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r).symm).transInitial
      (RelIso.preimage Equiv.ulift s).toInitialSeg
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r)).transInitial
      (RelIso.preimage Equiv.ulift s).symm.toInitialSeg

@[simp]
/--
theorem `lift_le` / 定理 `lift_le`

English:
theorem lift_le
  given: {a b : Ordinal}
  statement: lift.{u, v} a <= lift.{u, v} b ↔ a <= b
  proof: inductionOn₂ a b fun α r _ β s _ => by
    rw [← lift_umax]
    exact lift_type_le.{_, _, u}

@[simp]

中文:
定理 lift_le
  条件: {a b : Ordinal}
  结论: lift.{u, v} a <= lift.{u, v} b ↔ a <= b
  证明: inductionOn₂ a b fun α r _ β s _ => by
    rw [← lift_umax]
    exact lift_type_le.{_, _, u}

@[simp]

Depends on / 依赖: lift_type_le, lift_umax
-/
theorem lift_le {a b : Ordinal} : lift.{u, v} a <= lift.{u, v} b ↔ a <= b :=
  inductionOn₂ a b fun α r _ β s _ => by
    rw [← lift_umax]
    exact lift_type_le.{_, _, u}

@[simp]
/--
theorem `lift_inj` / 定理 `lift_inj`

English:
theorem lift_inj
  given: {a b : Ordinal}
  statement: lift.{u, v} a = lift.{u, v} b ↔ a = b
  proof: by
  simp_rw [le_antisymm_iff, lift_le]

@[simp]

中文:
定理 lift_inj
  条件: {a b : Ordinal}
  结论: lift.{u, v} a = lift.{u, v} b ↔ a = b
  证明: by
  simp_rw [le_antisymm_iff, lift_le]

@[simp]

Depends on / 依赖: le_antisymm_iff, lift_le, simp_rw
-/
theorem lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v} b ↔ a = b := by
  simp_rw [le_antisymm_iff, lift_le]

@[simp]
/--
theorem `lift_lt` / 定理 `lift_lt`

English:
theorem lift_lt
  given: {a b : Ordinal}
  statement: lift.{u, v} a < lift.{u, v} b ↔ a < b
  proof: by
  simp_rw [lt_iff_le_not_ge, lift_le]

@[simp]

中文:
定理 lift_lt
  条件: {a b : Ordinal}
  结论: lift.{u, v} a < lift.{u, v} b ↔ a < b
  证明: by
  simp_rw [lt_iff_le_not_ge, lift_le]

@[simp]

Depends on / 依赖: lift_le, lt_iff_le_not_ge, simp_rw
-/
theorem lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b ↔ a < b := by
  simp_rw [lt_iff_le_not_ge, lift_le]

@[simp]
/--
theorem `lift_typein_top` / 定理 `lift_typein_top`

English:
theorem lift_typein_top
  statement: {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: f.subrelIso.ordinal_lift_type_eq

@[simp]

中文:
定理 lift_typein_top
  结论: {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: f.subrelIso.ordinal_lift_type_eq

@[simp]

Depends on / 依赖: f.subrelIso.ordinal_lift_type_eq, ordinal_lift_type_eq, subrelIso
-/
theorem lift_typein_top {r : α -> α -> Prop} {s : β -> β -> Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : lift.{u} (typein s f.top) = lift (type r) :=
  f.subrelIso.ordinal_lift_type_eq

@[simp]
/--
theorem `typein_ordinal` / 定理 `typein_ordinal`

English:
theorem typein_ordinal
  given: (o : Ordinal.{u})
  statement: typein LT.lt o = lift.{u + 1} o
  proof: by
  nth_rw 2 [← o.type_toType]
  rw [← ToType.mk.toRelIsoLT.ordinal_lift_type_eq]; rw [lift_id'.{u]; rw [u + 1}]; rw [type_Iio_lt]

中文:
定理 typein_ordinal
  条件: (o : Ordinal.{u})
  结论: typein LT.lt o = lift.{u + 1} o
  证明: by
  nth_rw 2 [← o.type_toType]
  rw [← ToType.mk.toRelIsoLT.ordinal_lift_type_eq]; rw [lift_id'.{u]; rw [u + 1}]; rw [type_Iio_lt]

Depends on / 依赖: ToType, ToType.mk.toRelIsoLT.ordinal_lift_type_eq, lift_id, nth_rw, o.type_toType, ordinal_lift_type_eq, toRelIsoLT, type_Iio_lt, type_toType
-/
theorem typein_ordinal (o : Ordinal.{u}) : typein LT.lt o = lift.{u + 1} o := by
  nth_rw 2 [← o.type_toType]
  rw [← ToType.mk.toRelIsoLT.ordinal_lift_type_eq]; rw [lift_id'.{u]; rw [u + 1}]; rw [type_Iio_lt]

/--
theorem `type_lt_Iio` / 定理 `type_lt_Iio`

English:
theorem type_lt_Iio
  given: (o : Ordinal.{u})
  statement: typeLT (Iio o) = lift.{u + 1} o
  proof: by simp

中文:
定理 type_lt_Iio
  条件: (o : Ordinal.{u})
  结论: typeLT (Iio o) = lift.{u + 1} o
  证明: by simp
-/
theorem type_lt_Iio (o : Ordinal.{u}) : typeLT (Iio o) = lift.{u + 1} o := by simp

/--
Definition of `liftInitialSeg` / `liftInitialSeg` 的定义

English:
definition liftInitialSeg
  signature: : Ordinal.{v} <=i Ordinal.{max u v}
  body: by
  refine ⟨RelEmbedding.ofMonotone lift.{u} (by simp),
    fun a b => Ordinal.inductionOn₂ a b fun α r _ β s _ h => ?_⟩
  rw [RelEmbedding.ofMonotone_coe]; rw [← lift_id'.{max u v} (type s)]; rw [← lift_umax.{v]; rw [u}]; rw [lift_type_lt] at h
  obtain ⟨f⟩ := h
  use typein r f.top
  rw [RelEmbed

中文:
定义 liftInitialSeg
  签名: : Ordinal.{v} <=i Ordinal.{max u v}
  定义体: by
  refine ⟨RelEmbedding.ofMonotone lift.{u} (by simp),
    fun a b => Ordinal.inductionOn₂ a b fun α r _ β s _ h => ?_⟩
  rw [RelEmbedding.ofMonotone_coe]; rw [← lift_id'.{max u v} (type s)]; rw [← lift_umax.{v]; rw [u}]; rw [lift_type_lt] at h
  obtain ⟨f⟩ := h
  use typein r f.top
  rw [RelEmbed

Depends on / 依赖: Ordinal, Ordinal.inductionOn, RelEmbedding, RelEmbedding.ofMonotone, RelEmbedding.ofMonotone_coe, f.top, lift_id, lift_type_lt, lift_typein_top, lift_umax, ofMonotone, ofMonotone_coe, typein
-/
def liftInitialSeg : Ordinal.{v} <=i Ordinal.{max u v} := by
  refine ⟨RelEmbedding.ofMonotone lift.{u} (by simp),
    fun a b => Ordinal.inductionOn₂ a b fun α r _ β s _ h => ?_⟩
  rw [RelEmbedding.ofMonotone_coe]; rw [← lift_id'.{max u v} (type s)]; rw [← lift_umax.{v]; rw [u}]; rw [lift_type_lt] at h
  obtain ⟨f⟩ := h
  use typein r f.top
  rw [RelEmbedding.ofMonotone_coe]; rw [← lift_umax]; rw [lift_typein_top]; rw [lift_id']

@[simp]
/--
theorem `liftInitialSeg_coe` / 定理 `liftInitialSeg_coe`

English:
theorem liftInitialSeg_coe
  statement: (liftInitialSeg.{v, u} : Ordinal -> Ordinal) = lift.{v, u}
  proof: rfl

@[simp]

中文:
定理 liftInitialSeg_coe
  结论: (liftInitialSeg.{v, u} : Ordinal -> Ordinal) = lift.{v, u}
  证明: rfl

@[simp]
-/
theorem liftInitialSeg_coe : (liftInitialSeg.{v, u} : Ordinal -> Ordinal) = lift.{v, u} :=
  rfl

@[simp]
/--
theorem `lift_lift` / 定理 `lift_lift`

English:
theorem lift_lift
  given: (a : Ordinal.{u})
  statement: lift.{w} (lift.{v} a) = lift.{max v w} a
  proof: (liftInitialSeg.trans liftInitialSeg).eq liftInitialSeg a

@[simp]

中文:
定理 lift_lift
  条件: (a : Ordinal.{u})
  结论: lift.{w} (lift.{v} a) = lift.{max v w} a
  证明: (liftInitialSeg.trans liftInitialSeg).eq liftInitialSeg a

@[simp]

Depends on / 依赖: liftInitialSeg, liftInitialSeg.trans
-/
theorem lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  (liftInitialSeg.trans liftInitialSeg).eq liftInitialSeg a

@[simp]
/--
theorem `lift_zero` / 定理 `lift_zero`

English:
theorem lift_zero
  statement: lift 0 = 0
  proof: type_eq_zero_of_empty _

@[simp]

中文:
定理 lift_zero
  结论: lift 0 = 0
  证明: type_eq_zero_of_empty _

@[simp]

Depends on / 依赖: type_eq_zero_of_empty
-/
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _

@[simp]
/--
theorem `lift_one` / 定理 `lift_one`

English:
theorem lift_one
  statement: lift 1 = 1
  proof: type_eq_one_of_unique _

@[simp]

中文:
定理 lift_one
  结论: lift 1 = 1
  证明: type_eq_one_of_unique _

@[simp]

Depends on / 依赖: type_eq_one_of_unique
-/
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _

@[simp]
/--
theorem `lift_card` / 定理 `lift_card`

English:
theorem lift_card
  given: (a)
  statement: Cardinal.lift.{u, v} (card a) = card (lift.{u} a)
  proof: inductionOn a fun _ _ _ => rfl

中文:
定理 lift_card
  条件: (a)
  结论: Cardinal.lift.{u, v} (card a) = card (lift.{u} a)
  证明: inductionOn a fun _ _ _ => rfl

Depends on / 依赖: MetricSpace, SeparationQuotient, gluePremetric, inductionOn, toTopologicalSpace, toUniformSpace, toUniformSpace.toTopologicalSpace
-/
theorem lift_card (a) : Cardinal.lift.{u, v} (card a) = card (lift.{u} a) :=
  inductionOn a fun _ _ _ => rfl

/--
theorem `mem_range_lift_of_le` / 定理 `mem_range_lift_of_le`

English:
theorem mem_range_lift_of_le
  given: {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b <= lift.{v} a)
  proof: liftInitialSeg.mem_range_of_le h

中文:
定理 mem_range_lift_of_le
  条件: {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b <= lift.{v} a)
  证明: liftInitialSeg.mem_range_of_le h

Depends on / 依赖: liftInitialSeg, liftInitialSeg.mem_range_of_le, mem_range_of_le
-/
theorem mem_range_lift_of_le {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b <= lift.{v} a) :
    b in Set.range lift.{v} :=
  liftInitialSeg.mem_range_of_le h

/--
theorem `le_lift_iff` / 定理 `le_lift_iff`

English:
theorem le_lift_iff
  given: {a : Ordinal.{u}} {b : Ordinal.{max u v}}
  proof: liftInitialSeg.le_apply_iff

中文:
定理 le_lift_iff
  条件: {a : Ordinal.{u}} {b : Ordinal.{max u v}}
  证明: liftInitialSeg.le_apply_iff

Depends on / 依赖: le_apply_iff, liftInitialSeg, liftInitialSeg.le_apply_iff
-/
theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b <= lift.{v} a ↔ exists a' <= a, lift.{v} a' = b :=
  liftInitialSeg.le_apply_iff

/--
theorem `lt_lift_iff` / 定理 `lt_lift_iff`

English:
theorem lt_lift_iff
  given: {a : Ordinal.{u}} {b : Ordinal.{max u v}}
  proof: liftInitialSeg.lt_apply_iff

@[simp]

中文:
定理 lt_lift_iff
  条件: {a : Ordinal.{u}} {b : Ordinal.{max u v}}
  证明: liftInitialSeg.lt_apply_iff

@[simp]

Depends on / 依赖: liftInitialSeg, liftInitialSeg.lt_apply_iff, lt_apply_iff
-/
theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b < lift.{v} a ↔ exists a' < a, lift.{v} a' = b :=
  liftInitialSeg.lt_apply_iff

@[simp]
/--
theorem `_root_.Cardinal.mk_Iio_ordinal` / 定理 `_root_.Cardinal.mk_Iio_ordinal`

English:
theorem _root_.Cardinal.mk_Iio_ordinal
  given: (o : Ordinal.{u})
  proof: by
  rw [lift_card]; rw [← typein_ordinal]
  rfl

@[deprecated (since := "2026-03-13")] alias mk_Iio_ordinal := Cardinal.mk_Iio_ordinal

中文:
定理 _root_.Cardinal.mk_Iio_ordinal
  条件: (o : Ordinal.{u})
  证明: by
  rw [lift_card]; rw [← typein_ordinal]
  rfl

@[deprecated (since := "2026-03-13")] alias mk_Iio_ordinal := Cardinal.mk_Iio_ordinal

Depends on / 依赖: lift_card, typein_ordinal
-/
theorem _root_.Cardinal.mk_Iio_ordinal (o : Ordinal.{u}) :
    #(Iio o) = Cardinal.lift.{u + 1} o.card := by
  rw [lift_card]; rw [← typein_ordinal]
  rfl

@[deprecated (since := "2026-03-13")] alias mk_Iio_ordinal := Cardinal.mk_Iio_ordinal

/-! ### The first infinite ordinal ω -/

/--
Definition of `omega0` / `omega0` 的定义

English:
definition omega0
  signature: : Ordinal.{u}
  body: lift (typeLT Nat)

@[inherit_doc] scoped notation "ω" => Ordinal.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

中文:
定义 omega0
  签名: : Ordinal.{u}
  定义体: lift (typeLT Nat)

@[inherit_doc] scoped notation "ω" => Ordinal.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

Depends on / 依赖: typeLT
-/
def omega0 : Ordinal.{u} :=
  lift (typeLT Nat)

@[inherit_doc] scoped notation "ω" => Ordinal.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

/-- Note that the presence of this lemma makes `simp [omega0]` form a loop. -/
@[simp]
/--
theorem `type_nat_lt` / 定理 `type_nat_lt`

English:
theorem type_nat_lt
  statement: typeLT Nat = ω
  proof: (lift_id _).symm

@[simp]

中文:
定理 type_nat_lt
  结论: typeLT 自然数 = ω
  证明: (lift_id _).symm

@[simp]

Depends on / 依赖: lift_id
-/
theorem type_nat_lt : typeLT Nat = ω :=
  (lift_id _).symm

@[simp]
/--
theorem `card_omega0` / 定理 `card_omega0`

English:
theorem card_omega0
  statement: card ω = ℵ₀
  proof: rfl

@[simp]

中文:
定理 card_omega0
  结论: card ω = ℵ₀
  证明: rfl

@[simp]
-/
theorem card_omega0 : card ω = ℵ₀ :=
  rfl

@[simp]
/--
theorem `lift_omega0` / 定理 `lift_omega0`

English:
theorem lift_omega0
  statement: lift ω = ω
  proof: lift_lift _

中文:
定理 lift_omega0
  结论: lift ω = ω
  证明: lift_lift _

Depends on / 依赖: lift_lift
-/
theorem lift_omega0 : lift ω = ω :=
  lift_lift _

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`Mathlib/SetTheory/Ordinal/Arithmetic.lean`.
-/


/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add Ordinal.{u}
  body: ⟨fun o₁ o₂ => Quotient.liftOn₂ o₁ o₂ (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => type (Sum.Lex r s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => (RelIso.sumLexCongr f g).ordinalType_congr⟩

中文:
实例 add
  签名: : Add Ordinal.{u}
  定义体: ⟨fun o₁ o₂ => Quotient.liftOn₂ o₁ o₂ (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => type (Sum.Lex r s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => (RelIso.sumLexCongr f g).ordinalType_congr⟩

Depends on / 依赖: Quotient, Quotient.liftOn, RelIso, RelIso.sumLexCongr, Sum.Lex, ordinalType_congr, sumLexCongr
-/
instance add : Add Ordinal.{u} :=
  ⟨fun o₁ o₂ => Quotient.liftOn₂ o₁ o₂ (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => type (Sum.Lex r s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => (RelIso.sumLexCongr f g).ordinalType_congr⟩

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: : AddMonoidWithOne Ordinal.{u} where
  body: inductionOn o fun α _ _ => (RelIso.emptySumLex _ _).ordinalType_congr
  add_zero o := inductionOn o fun α _ _ => (RelIso.sumLexEmpty _ _).ordinalType_congr
  add_assoc o₁ o₂ o₃ :=
    Quotient.inductionOn₃ o₁ o₂ o₃ fun _ _ _ => Quot.sound ⟨⟨sumAssoc .., by simp⟩⟩
  nsmul := nsmulRec

@[simp]

中文:
实例 addMonoidWithOne
  签名: : AddMonoidWithOne Ordinal.{u} where
  定义体: inductionOn o fun α _ _ => (RelIso.emptySumLex _ _).ordinalType_congr
  add_zero o := inductionOn o fun α _ _ => (RelIso.sumLexEmpty _ _).ordinalType_congr
  add_assoc o₁ o₂ o₃ :=
    Quotient.inductionOn₃ o₁ o₂ o₃ fun _ _ _ => Quot.sound ⟨⟨sumAssoc .., by simp⟩⟩
  nsmul := nsmulRec

@[simp]

Depends on / 依赖: RelIso, RelIso.emptySumLex, emptySumLex, inductionOn, ordinalType_congr
-/
instance addMonoidWithOne : AddMonoidWithOne Ordinal.{u} where
  zero_add o := inductionOn o fun α _ _ => (RelIso.emptySumLex _ _).ordinalType_congr
  add_zero o := inductionOn o fun α _ _ => (RelIso.sumLexEmpty _ _).ordinalType_congr
  add_assoc o₁ o₂ o₃ :=
    Quotient.inductionOn₃ o₁ o₂ o₃ fun _ _ _ => Quot.sound ⟨⟨sumAssoc .., by simp⟩⟩
  nsmul := nsmulRec

@[simp]
/--
theorem `card_add` / 定理 `card_add`

English:
theorem card_add
  given: (o₁ o₂ : Ordinal)
  statement: card (o₁ + o₂) = card o₁ + card o₂
  proof: inductionOn₂ o₁ o₂ fun _ _ _ _ _ _ => rfl

中文:
定理 card_add
  条件: (o₁ o₂ : Ordinal)
  结论: card (o₁ + o₂) = card o₁ + card o₂
  证明: inductionOn₂ o₁ o₂ fun _ _ _ _ _ _ => rfl
-/
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  inductionOn₂ o₁ o₂ fun _ _ _ _ _ _ => rfl

/--
theorem `card_add_one` / 定理 `card_add_one`

English:
theorem card_add_one
  given: (o : Ordinal)
  statement: card (o + 1) = card o + 1
  proof: by
  simp

@[simp]

中文:
定理 card_add_one
  条件: (o : Ordinal)
  结论: card (o + 1) = card o + 1
  证明: by
  simp

@[simp]
-/
theorem card_add_one (o : Ordinal) : card (o + 1) = card o + 1 := by
  simp

@[simp]
/--
theorem `type_sum_lex` / 定理 `type_sum_lex`

English:
theorem type_sum_lex
  statement: {α β : Type u} (r : α -> α -> Prop) (s : β -> β -> Prop) [IsWellOrder α r]
  proof: rfl

@[simp]

中文:
定理 type_sum_lex
  结论: {α β : 类型u} (r : α -> α -> 命题) (s : β -> β -> 命题) [IsWellOrder α r]
  证明: rfl

@[simp]
-/
theorem type_sum_lex {α β : Type u} (r : α -> α -> Prop) (s : β -> β -> Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s :=
  rfl

@[simp]
/--
theorem `card_nat` / 定理 `card_nat`

English:
theorem card_nat
  given: (n : Nat)
  statement: card.{u} n = n
  proof: by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]

@[simp]

中文:
定理 card_nat
  条件: (n : 自然数)
  结论: card.{u} n = n
  证明: by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]

@[simp]

Depends on / 依赖: Nat.cast_succ, card_add, card_one, cast_succ, toInductiveLimit
-/
theorem card_nat (n : Nat) : card.{u} n = n := by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]

@[simp]
/--
theorem `card_ofNat` / 定理 `card_ofNat`

English:
theorem card_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: card_nat n

中文:
定理 card_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: card_nat n

Depends on / 依赖: card_nat
-/
theorem card_ofNat (n : Nat) [n.AtLeastTwo] :
    card.{u} ofNat(n) = OfNat.ofNat n :=
  card_nat n

/--
Instance `instAddLeftMono` / 实例 `instAddLeftMono`

English:
instance instAddLeftMono
  signature: : AddLeftMono Ordinal.{u} where
  body: by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ =>
      (RelEmbedding.ofMonotone (Sum.recOn · Sum.inl (Sum.inr ∘ f)) ?_).ordinal_type_le
    simp [f.map_rel_iff]

中文:
实例 instAddLeftMono
  签名: : AddLeftMono Ordinal.{u} where
  定义体: by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ =>
      (RelEmbedding.ofMonotone (Sum.recOn · Sum.inl (Sum.inr ∘ f)) ?_).ordinal_type_le
    simp [f.map_rel_iff]

Depends on / 依赖: RelEmbedding, RelEmbedding.ofMonotone, Sum.inl, Sum.inr, Sum.recOn, f.map_rel_iff, map_rel_iff, ofMonotone, ordinal_type_le
-/
instance instAddLeftMono : AddLeftMono Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ =>
      (RelEmbedding.ofMonotone (Sum.recOn · Sum.inl (Sum.inr ∘ f)) ?_).ordinal_type_le
    simp [f.map_rel_iff]

/--
Instance `instAddRightMono` / 实例 `instAddRightMono`

English:
instance instAddRightMono
  signature: : AddRightMono Ordinal.{u} where
  body: by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ =>
      (RelEmbedding.ofMonotone (Sum.recOn · (Sum.inl ∘ f) Sum.inr) ?_).ordinal_type_le
    simp [f.map_rel_iff]

中文:
实例 instAddRightMono
  签名: : AddRightMono Ordinal.{u} where
  定义体: by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ =>
      (RelEmbedding.ofMonotone (Sum.recOn · (Sum.inl ∘ f) Sum.inr) ?_).ordinal_type_le
    simp [f.map_rel_iff]

Depends on / 依赖: RelEmbedding, RelEmbedding.ofMonotone, Sum.inl, Sum.inr, Sum.recOn, f.map_rel_iff, map_rel_iff, ofMonotone, ordinal_type_le
-/
instance instAddRightMono : AddRightMono Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ =>
      (RelEmbedding.ofMonotone (Sum.recOn · (Sum.inl ∘ f) Sum.inr) ?_).ordinal_type_le
    simp [f.map_rel_iff]

/--
Instance `existsAddOfLE` / 实例 `existsAddOfLE`

English:
instance existsAddOfLE
  signature: : ExistsAddOfLE Ordinal where
  body: by
    refine inductionOn₂ a b fun α r _ β s _ ⟨f⟩ => ?_
    obtain ⟨γ, t, _, ⟨g⟩⟩ := f.exists_sum_relIso
    exact ⟨type t, g.ordinalType_congr.symm⟩

中文:
实例 existsAddOfLE
  签名: : ExistsAddOfLE Ordinal where
  定义体: by
    refine inductionOn₂ a b fun α r _ β s _ ⟨f⟩ => ?_
    obtain ⟨γ, t, _, ⟨g⟩⟩ := f.exists_sum_relIso
    exact ⟨type t, g.ordinalType_congr.symm⟩

Depends on / 依赖: exists_sum_relIso, f.exists_sum_relIso, g.ordinalType_congr.symm, ordinalType_congr
-/
instance existsAddOfLE : ExistsAddOfLE Ordinal where
  exists_add_of_le {a b} := by
    refine inductionOn₂ a b fun α r _ β s _ ⟨f⟩ => ?_
    obtain ⟨γ, t, _, ⟨g⟩⟩ := f.exists_sum_relIso
    exact ⟨type t, g.ordinalType_congr.symm⟩

/--
Instance `canonicallyOrderedAdd` / 实例 `canonicallyOrderedAdd`

English:
instance canonicallyOrderedAdd
  signature: : CanonicallyOrderedAdd Ordinal where
  body: by simpa using add_le_add_left bot_le a
  le_self_add a b := by simpa using add_le_add_right bot_le a

@[deprecated zero_max (since := "2026-05-07")]

中文:
实例 canonicallyOrderedAdd
  签名: : CanonicallyOrderedAdd Ordinal where
  定义体: by simpa using add_le_add_left bot_le a
  le_self_add a b := by simpa using add_le_add_right bot_le a

@[deprecated zero_max (since := "2026-05-07")]

Depends on / 依赖: add_le_add_left, add_le_add_right, bot_le, le_self_add
-/
instance canonicallyOrderedAdd : CanonicallyOrderedAdd Ordinal where
  le_add_self a b := by simpa using add_le_add_left bot_le a
  le_self_add a b := by simpa using add_le_add_right bot_le a

@[deprecated zero_max (since := "2026-05-07")]
/--
theorem `max_zero_left` / 定理 `max_zero_left`

English:
theorem max_zero_left
  statement: forall a : Ordinal, max 0 a = a
  proof: zero_max

@[deprecated max_zero (since := "2026-05-07")]

中文:
定理 max_zero_left
  结论: 对任意 a : Ordinal, max 0 a = a
  证明: zero_max

@[deprecated max_zero (since := "2026-05-07")]

Depends on / 依赖: zero_max
-/
theorem max_zero_left : forall a : Ordinal, max 0 a = a :=
  zero_max

@[deprecated max_zero (since := "2026-05-07")]
/--
theorem `max_zero_right` / 定理 `max_zero_right`

English:
theorem max_zero_right
  statement: forall a : Ordinal, max a 0 = a
  proof: max_zero

@[deprecated _root_.max_eq_zero (since := "2026-05-07")]

中文:
定理 max_zero_right
  结论: 对任意 a : Ordinal, max a 0 = a
  证明: max_zero

@[deprecated _root_.max_eq_zero (since := "2026-05-07")]

Depends on / 依赖: max_zero
-/
theorem max_zero_right : forall a : Ordinal, max a 0 = a :=
  max_zero

@[deprecated _root_.max_eq_zero (since := "2026-05-07")]
/--
theorem `max_eq_zero` / 定理 `max_eq_zero`

English:
theorem max_eq_zero
  given: {a b : Ordinal}
  statement: max a b = 0 ↔ a = 0 ∧ b = 0
  proof: max_eq_zero

@[simp]

中文:
定理 max_eq_zero
  条件: {a b : Ordinal}
  结论: max a b = 0 ↔ a = 0 ∧ b = 0
  证明: max_eq_zero

@[simp]
-/
protected theorem max_eq_zero {a b : Ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  max_eq_zero

@[simp]
/--
theorem `sInf_empty` / 定理 `sInf_empty`

English:
theorem sInf_empty
  statement: sInf (∅ : Set Ordinal) = 0
  proof: dif_neg Set.not_nonempty_empty

中文:
定理 sInf_empty
  结论: sInf (∅ : Set Ordinal) = 0
  证明: dif_neg Set.not_nonempty_empty

Depends on / 依赖: Set.not_nonempty_empty, dif_neg, not_nonempty_empty
-/
theorem sInf_empty : sInf (∅ : Set Ordinal) = 0 :=
  dif_neg Set.not_nonempty_empty


/--
theorem `succ_le_iff'` / 定理 `succ_le_iff'`

English:
theorem succ_le_iff'
  given: {a b : Ordinal}
  statement: a + 1 <= b ↔ a < b
  proof: by
  refine inductionOn₂ a b fun α r _ β s _ => ⟨?_, ?_⟩ <;> rintro ⟨f⟩
  · refine ⟨((InitialSeg.leAdd _ _).trans f).toPrincipalSeg fun h => ?_⟩
    simpa using h (f (Sum.inr PUnit.unit))
  · apply (RelEmbedding.ofMonotone (Sum.recOn · f fun _ => f.top) ?_).ordinal_type_le
    simpa [f.map_rel_iff] 

中文:
定理 succ_le_iff'
  条件: {a b : Ordinal}
  结论: a + 1 <= b ↔ a < b
  证明: by
  refine inductionOn₂ a b fun α r _ β s _ => ⟨?_, ?_⟩ <;> rintro ⟨f⟩
  · refine ⟨((InitialSeg.leAdd _ _).trans f).toPrincipalSeg fun h => ?_⟩
    simpa using h (f (Sum.inr PUnit.unit))
  · apply (RelEmbedding.ofMonotone (Sum.recOn · f fun _ => f.top) ?_).ordinal_type_le
    simpa [f.map_rel_iff] 
-/
private theorem succ_le_iff' {a b : Ordinal} : a + 1 <= b ↔ a < b := by
  refine inductionOn₂ a b fun α r _ β s _ => ⟨?_, ?_⟩ <;> rintro ⟨f⟩
  · refine ⟨((InitialSeg.leAdd _ _).trans f).toPrincipalSeg fun h => ?_⟩
    simpa using h (f (Sum.inr PUnit.unit))
  · apply (RelEmbedding.ofMonotone (Sum.recOn · f fun _ => f.top) ?_).ordinal_type_le
    simpa [f.map_rel_iff] using f.lt_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoMaxOrder Ordinal
  body: ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

中文:
实例 :
  签名: NoMaxOrder Ordinal
  定义体: ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

Depends on / 依赖: le_rfl, succ_le_iff
-/
instance : NoMaxOrder Ordinal :=
  ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SuccOrder Ordinal.{u}
  body: SuccOrder.ofSuccLeIff (fun o => o + 1) (by exact succ_le_iff')

中文:
实例 :
  签名: SuccOrder Ordinal.{u}
  定义体: SuccOrder.ofSuccLeIff (fun o => o + 1) (by exact succ_le_iff')

Depends on / 依赖: SuccOrder, SuccOrder.ofSuccLeIff, ofSuccLeIff, succ_le_iff
-/
instance : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) (by exact succ_le_iff')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SuccAddOrder Ordinal
  body: ⟨fun _ => rfl⟩

@[deprecated succ_eq_add_one (since := "2026-02-26")]

中文:
实例 :
  签名: SuccAddOrder Ordinal
  定义体: ⟨fun _ => rfl⟩

@[deprecated succ_eq_add_one (since := "2026-02-26")]
-/
instance : SuccAddOrder Ordinal := ⟨fun _ => rfl⟩

@[deprecated succ_eq_add_one (since := "2026-02-26")]
/--
theorem `add_one_eq_succ` / 定理 `add_one_eq_succ`

English:
theorem add_one_eq_succ
  given: (o : Ordinal)
  statement: o + 1 = succ o
  proof: rfl

@[deprecated zero_add (since := "2026-02-26")]

中文:
定理 add_one_eq_succ
  条件: (o : Ordinal)
  结论: o + 1 = succ o
  证明: rfl

@[deprecated zero_add (since := "2026-02-26")]
-/
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl

@[deprecated zero_add (since := "2026-02-26")]
/--
theorem `succ_zero` / 定理 `succ_zero`

English:
theorem succ_zero
  statement: succ (0 : Ordinal) = 1
  proof: zero_add 1

@[deprecated one_add_one_eq_two (since := "2026-02-26")]

中文:
定理 succ_zero
  结论: succ (0 : Ordinal) = 1
  证明: zero_add 1

@[deprecated one_add_one_eq_two (since := "2026-02-26")]

Depends on / 依赖: zero_add
-/
theorem succ_zero : succ (0 : Ordinal) = 1 :=
  zero_add 1

@[deprecated one_add_one_eq_two (since := "2026-02-26")]
/--
theorem `succ_one` / 定理 `succ_one`

English:
theorem succ_one
  statement: succ (1 : Ordinal) = 2
  proof: one_add_one_eq_two

@[deprecated add_assoc (since := "2026-02-26")]

中文:
定理 succ_one
  结论: succ (1 : Ordinal) = 2
  证明: one_add_one_eq_two

@[deprecated add_assoc (since := "2026-02-26")]

Depends on / 依赖: one_add_one_eq_two
-/
theorem succ_one : succ (1 : Ordinal) = 2 := one_add_one_eq_two

@[deprecated add_assoc (since := "2026-02-26")]
/--
theorem `add_succ` / 定理 `add_succ`

English:
theorem add_succ
  given: (o₁ o₂ : Ordinal)
  statement: o₁ + succ o₂ = succ (o₁ + o₂)
  proof: (add_assoc _ _ _).symm

@[deprecated Order.one_le_iff_ne_zero (since := "2026-03-24")]

中文:
定理 add_succ
  条件: (o₁ o₂ : Ordinal)
  结论: o₁ + succ o₂ = succ (o₁ + o₂)
  证明: (add_assoc _ _ _).symm

@[deprecated Order.one_le_iff_ne_zero (since := "2026-03-24")]

Depends on / 依赖: add_assoc
-/
theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assoc _ _ _).symm

@[deprecated Order.one_le_iff_ne_zero (since := "2026-03-24")]
/--
theorem `one_le_iff_ne_zero` / 定理 `one_le_iff_ne_zero`

English:
theorem one_le_iff_ne_zero
  given: {o : Ordinal}
  statement: 1 <= o ↔ o != 0
  proof: Order.one_le_iff_ne_zero

@[deprecated add_pos_of_right (since := "2026-04-04")]

中文:
定理 one_le_iff_ne_zero
  条件: {o : Ordinal}
  结论: 1 <= o ↔ o != 0
  证明: Order.one_le_iff_ne_zero

@[deprecated add_pos_of_right (since := "2026-04-04")]
-/
protected theorem one_le_iff_ne_zero {o : Ordinal} : 1 <= o ↔ o != 0 :=
  Order.one_le_iff_ne_zero

@[deprecated add_pos_of_right (since := "2026-04-04")]
/--
theorem `succ_pos` / 定理 `succ_pos`

English:
theorem succ_pos
  given: (o : Ordinal)
  statement: 0 < succ o
  proof: add_pos_of_right zero_lt_one o

@[deprecated add_pos_of_right (since := "2026-04-04")]

中文:
定理 succ_pos
  条件: (o : Ordinal)
  结论: 0 < succ o
  证明: add_pos_of_right zero_lt_one o

@[deprecated add_pos_of_right (since := "2026-04-04")]

Depends on / 依赖: add_pos_of_right, zero_lt_one
-/
theorem succ_pos (o : Ordinal) : 0 < succ o :=
  add_pos_of_right zero_lt_one o

@[deprecated add_pos_of_right (since := "2026-04-04")]
/--
theorem `add_one_ne_zero` / 定理 `add_one_ne_zero`

English:
theorem add_one_ne_zero
  given: (o : Ordinal)
  statement: o + 1 != 0
  proof: (add_pos_of_right zero_lt_one o).ne'

@[deprecated add_pos_of_right (since := "2026-02-27")]

中文:
定理 add_one_ne_zero
  条件: (o : Ordinal)
  结论: o + 1 != 0
  证明: (add_pos_of_right zero_lt_one o).ne'

@[deprecated add_pos_of_right (since := "2026-02-27")]

Depends on / 依赖: add_pos_of_right, zero_lt_one
-/
theorem add_one_ne_zero (o : Ordinal) : o + 1 != 0 :=
  (add_pos_of_right zero_lt_one o).ne'

@[deprecated add_pos_of_right (since := "2026-02-27")]
/--
theorem `succ_ne_zero` / 定理 `succ_ne_zero`

English:
theorem succ_ne_zero
  given: (o : Ordinal)
  statement: succ o != 0
  proof: (add_pos_of_right zero_lt_one o).ne'

@[deprecated Order.lt_one_iff (since := "2026-03-24")]

中文:
定理 succ_ne_zero
  条件: (o : Ordinal)
  结论: succ o != 0
  证明: (add_pos_of_right zero_lt_one o).ne'

@[deprecated Order.lt_one_iff (since := "2026-03-24")]

Depends on / 依赖: add_pos_of_right, zero_lt_one
-/
theorem succ_ne_zero (o : Ordinal) : succ o != 0 :=
  (add_pos_of_right zero_lt_one o).ne'

@[deprecated Order.lt_one_iff (since := "2026-03-24")]
/--
theorem `lt_one_iff_zero` / 定理 `lt_one_iff_zero`

English:
theorem lt_one_iff_zero
  given: {a : Ordinal}
  statement: a < 1 ↔ a = 0
  proof: Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-03-24")]

中文:
定理 lt_one_iff_zero
  条件: {a : Ordinal}
  结论: a < 1 ↔ a = 0
  证明: Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-03-24")]

Depends on / 依赖: Order.lt_one_iff, lt_one_iff
-/
theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 :=
  Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-03-24")]
/--
theorem `le_one_iff` / 定理 `le_one_iff`

English:
theorem le_one_iff
  given: {a : Ordinal}
  statement: a <= 1 ↔ a = 0 ∨ a = 1
  proof: Order.le_one_iff

@[deprecated card_add_one (since := "2026-02-27")]

中文:
定理 le_one_iff
  条件: {a : Ordinal}
  结论: a <= 1 ↔ a = 0 ∨ a = 1
  证明: Order.le_one_iff

@[deprecated card_add_one (since := "2026-02-27")]
-/
protected theorem le_one_iff {a : Ordinal} : a <= 1 ↔ a = 0 ∨ a = 1 :=
  Order.le_one_iff

@[deprecated card_add_one (since := "2026-02-27")]
/--
theorem `card_succ` / 定理 `card_succ`

English:
theorem card_succ
  given: (o : Ordinal)
  statement: card (succ o) = card o + 1
  proof: by
  simp

@[deprecated Nat.cast_add_one (since := "2026-05-21")]

中文:
定理 card_succ
  条件: (o : Ordinal)
  结论: card (succ o) = card o + 1
  证明: by
  simp

@[deprecated Nat.cast_add_one (since := "2026-05-21")]
-/
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp

@[deprecated Nat.cast_add_one (since := "2026-05-21")]
/--
theorem `natCast_succ` / 定理 `natCast_succ`

English:
theorem natCast_succ
  given: (n : Nat)
  statement: ↑n.succ = succ (n : Ordinal)
  proof: n.cast_add_one

中文:
定理 natCast_succ
  条件: (n : 自然数)
  结论: ↑n.succ = succ (n : Ordinal)
  证明: n.cast_add_one

Depends on / 依赖: cast_add_one, n.cast_add_one
-/
theorem natCast_succ (n : Nat) : ↑n.succ = succ (n : Ordinal) :=
  n.cast_add_one

/--
Instance `uniqueIioOne` / 实例 `uniqueIioOne`

English:
instance uniqueIioOne
  signature: : Unique (Iio (1 : Ordinal)) where
  body: ⟨0, zero_lt_one' Ordinal⟩
uniq a := Subtype.ext lt_one_iff.1 a.2

@[simp]

中文:
实例 uniqueIioOne
  签名: : Unique (Iio (1 : Ordinal)) where
  定义体: ⟨0, zero_lt_one' Ordinal⟩
uniq a := Subtype.ext lt_one_iff.1 a.2

@[simp]

Depends on / 依赖: Ordinal, zero_lt_one
-/
instance uniqueIioOne : Unique (Iio (1 : Ordinal)) where
  default := ⟨0, zero_lt_one' Ordinal⟩
uniq a := Subtype.ext lt_one_iff.1 a.2

@[simp]
/--
theorem `Iio_one_default_eq` / 定理 `Iio_one_default_eq`

English:
theorem Iio_one_default_eq
  statement: (default : Iio (1 : Ordinal)) = ⟨0, zero_lt_one' Ordinal⟩
  proof: rfl

中文:
定理 Iio_one_default_eq
  结论: (default : Iio (1 : Ordinal)) = ⟨0, zero_lt_one' Ordinal⟩
  证明: rfl
-/
theorem Iio_one_default_eq : (default : Iio (1 : Ordinal)) = ⟨0, zero_lt_one' Ordinal⟩ :=
  rfl

/--
Instance `uniqueToTypeOne` / 实例 `uniqueToTypeOne`

English:
instance uniqueToTypeOne
  signature: : Unique (ToType 1) where
  body: enum (α := ToType 1) (· < ·) ⟨0, by simp⟩
  uniq a := by
    rw [← enum_typein (α := ToType 1) (· < ·) a]
    congr
    rw [← lt_one_iff]
    apply typein_lt_self

中文:
实例 uniqueToTypeOne
  签名: : Unique (ToType 1) where
  定义体: enum (α := ToType 1) (· < ·) ⟨0, by simp⟩
  uniq a := by
    rw [← enum_typein (α := ToType 1) (· < ·) a]
    congr
    rw [← lt_one_iff]
    apply typein_lt_self

Depends on / 依赖: ToType
-/
instance uniqueToTypeOne : Unique (ToType 1) where
  default := enum (α := ToType 1) (· < ·) ⟨0, by simp⟩
  uniq a := by
    rw [← enum_typein (α := ToType 1) (· < ·) a]
    congr
    rw [← lt_one_iff]
    apply typein_lt_self

/--
theorem `one_toType_eq` / 定理 `one_toType_eq`

English:
theorem one_toType_eq
  given: (x : ToType 1)
  statement: x = enum (· < ·) ⟨0, by simp⟩
  proof: Unique.eq_default x

中文:
定理 one_toType_eq
  条件: (x : ToType 1)
  结论: x = enum (· < ·) ⟨0, by simp⟩
  证明: Unique.eq_default x

Depends on / 依赖: Unique, Unique.eq_default, eq_default
-/
theorem one_toType_eq (x : ToType 1) : x = enum (· < ·) ⟨0, by simp⟩ :=
  Unique.eq_default x

set_option backward.isDefEq.respectTransparency false in
/--
theorem `type_lt_mem_range_succ_iff` / 定理 `type_lt_mem_range_succ_iff`

English:
theorem type_lt_mem_range_succ_iff
  given: [LinearOrder α] [WellFoundedLT α]
  proof: by
  simp_rw [← isTop_iff_isMax]
  constructor <;> intro ⟨a, ha⟩
  · refine ⟨enum (α := α) (· < ·) ⟨a, ?_⟩, fun b => ?_⟩
    · rw [mem_Iio, ← ha, lt_succ_iff]
    · rw [← enum_typein (α := α) (· < ·) b, ← not_lt, enum_le_enum (r := (· < ·)),
        Subtype.mk_le_mk, ← lt_succ_iff, ha]
      exact t

中文:
定理 type_lt_mem_range_succ_iff
  条件: [LinearOrder α] [WellFoundedLT α]
  证明: by
  simp_rw [← isTop_iff_isMax]
  constructor <;> intro ⟨a, ha⟩
  · refine ⟨enum (α := α) (· < ·) ⟨a, ?_⟩, fun b => ?_⟩
    · rw [mem_Iio, ← ha, lt_succ_iff]
    · rw [← enum_typein (α := α) (· < ·) b, ← not_lt, enum_le_enum (r := (· < ·)),
        Subtype.mk_le_mk, ← lt_succ_iff, ha]
      exact t

Depends on / 依赖: Subtype, Subtype.mk_le_mk, enum_le_enum, enum_typein, eq_of_forall_lt_iff, h.trans_lt, isTop_iff_isMax, lt_succ_iff, mem_Iio, mk_le_mk, not_lt, simp_rw, trans_lt, typein, typein_enum, typein_le_typein, typein_lt_type
-/
theorem type_lt_mem_range_succ_iff [LinearOrder α] [WellFoundedLT α] :
    typeLT α in range succ ↔ exists x : α, IsMax x := by
  simp_rw [← isTop_iff_isMax]
  constructor <;> intro ⟨a, ha⟩
  · refine ⟨enum (α := α) (· < ·) ⟨a, ?_⟩, fun b => ?_⟩
    · rw [mem_Iio, ← ha, lt_succ_iff]
    · rw [← enum_typein (α := α) (· < ·) b, ← not_lt, enum_le_enum (r := (· < ·)),
        Subtype.mk_le_mk, ← lt_succ_iff, ha]
      exact typein_lt_type ..
  · refine ⟨typein (α := α) (· < ·) a, eq_of_forall_lt_iff fun o => ?_⟩
    rw [lt_succ_iff]
    refine ⟨fun h => h.trans_lt (typein_lt_type _ _), fun h => ?_⟩
    rw [← typein_enum _ h]; rw [typein_le_typein]; rw [not_lt]
    apply ha

/--
theorem `type_lt_mem_range_succ` / 定理 `type_lt_mem_range_succ`

English:
theorem type_lt_mem_range_succ
  given: [LinearOrder α] [WellFoundedLT α] [OrderTop α]
  proof: type_lt_mem_range_succ_iff.2 ⟨⊤, isMax_top⟩

中文:
定理 type_lt_mem_range_succ
  条件: [LinearOrder α] [WellFoundedLT α] [OrderTop α]
  证明: type_lt_mem_range_succ_iff.2 ⟨⊤, isMax_top⟩

Depends on / 依赖: infer_instance, isMax_top, metric, type_lt_mem_range_succ_iff
-/
theorem type_lt_mem_range_succ [LinearOrder α] [WellFoundedLT α] [OrderTop α] :
    typeLT α in range succ :=
  type_lt_mem_range_succ_iff.2 ⟨⊤, isMax_top⟩

/--
theorem `isSuccPrelimit_type_lt_iff` / 定理 `isSuccPrelimit_type_lt_iff`

English:
theorem isSuccPrelimit_type_lt_iff
  given: [LinearOrder α] [WellFoundedLT α]
  proof: by
  rw [← not_iff_not]; rw [noMaxOrder_iff]; rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [type_lt_mem_range_succ_iff]
  simp [IsMax]

中文:
定理 isSuccPrelimit_type_lt_iff
  条件: [LinearOrder α] [WellFoundedLT α]
  证明: by
  rw [← not_iff_not]; rw [noMaxOrder_iff]; rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [type_lt_mem_range_succ_iff]
  simp [IsMax]

Depends on / 依赖: noMaxOrder_iff, not_iff_not, not_isSuccPrelimit_iff_mem_range_succ, type_lt_mem_range_succ_iff
-/
theorem isSuccPrelimit_type_lt_iff [LinearOrder α] [WellFoundedLT α] :
    IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α := by
  rw [← not_iff_not]; rw [noMaxOrder_iff]; rw [not_isSuccPrelimit_iff_mem_range_succ]; rw [type_lt_mem_range_succ_iff]
  simp [IsMax]

/--
theorem `isSuccPrelimit_type_lt` / 定理 `isSuccPrelimit_type_lt`

English:
theorem isSuccPrelimit_type_lt
  given: [LinearOrder α] [WellFoundedLT α] [h : NoMaxOrder α]
  proof: isSuccPrelimit_type_lt_iff.2 h

中文:
定理 isSuccPrelimit_type_lt
  条件: [LinearOrder α] [WellFoundedLT α] [h : NoMaxOrder α]
  证明: isSuccPrelimit_type_lt_iff.2 h

Depends on / 依赖: isSuccPrelimit_type_lt_iff
-/
theorem isSuccPrelimit_type_lt [LinearOrder α] [WellFoundedLT α] [h : NoMaxOrder α] :
    IsSuccPrelimit (typeLT α) :=
  isSuccPrelimit_type_lt_iff.2 h

/-! ### Extra properties of typein and enum -/

-- TODO: use `ToType.mk` for lemmas on `ToType` rather than `enum` and `typein`.

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `typein_one_toType` / 定理 `typein_one_toType`

English:
theorem typein_one_toType
  given: (x : ToType 1)
  statement: typein (α := ToType 1) (· < ·) x = 0
  proof: by
  rw [one_toType_eq x]; rw [typein_enum]

中文:
定理 typein_one_toType
  条件: (x : ToType 1)
  结论: typein (α := ToType 1) (· < ·) x = 0
  证明: by
  rw [one_toType_eq x]; rw [typein_enum]

Depends on / 依赖: ToType, one_toType_eq, typein_enum
-/
theorem typein_one_toType (x : ToType 1) : typein (α := ToType 1) (· < ·) x = 0 := by
  rw [one_toType_eq x]; rw [typein_enum]

/--
theorem `typein_le_typein'` / 定理 `typein_le_typein'`

English:
theorem typein_le_typein'
  given: (o : Ordinal) {x y : o.ToType}
  proof: by
  simp

中文:
定理 typein_le_typein'
  条件: (o : Ordinal) {x y : o.ToType}
  证明: by
  simp

Depends on / 依赖: ToType, o.ToType, typein
-/
theorem typein_le_typein' (o : Ordinal) {x y : o.ToType} :
    typein (α := o.ToType) (· < ·) x <= typein (α := o.ToType) (· < ·) y ↔ x <= y := by
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_enum_succ` / 定理 `le_enum_succ`

English:
theorem le_enum_succ
  given: {o : Ordinal} (a : (succ o).ToType)
  proof: by
  rw [← enum_typein (α := (succ o).ToType) (· < ·) a]; rw [enum_le_enum']; rw [Subtype.mk_le_mk]; rw [← lt_succ_iff]
  apply typein_lt_self

中文:
定理 le_enum_succ
  条件: {o : Ordinal} (a : (succ o).ToType)
  证明: by
  rw [← enum_typein (α := (succ o).ToType) (· < ·) a]; rw [enum_le_enum']; rw [Subtype.mk_le_mk]; rw [← lt_succ_iff]
  apply typein_lt_self

Depends on / 依赖: Subtype, Subtype.mk_le_mk, ToType, enum_le_enum, enum_typein, lt_succ, lt_succ_iff, mk_le_mk, type_toType, typein_lt_self
-/
theorem le_enum_succ {o : Ordinal} (a : (succ o).ToType) :
    a <= enum (α := (succ o).ToType) (· < ·) ⟨o, (type_toType _ ▸ lt_succ o)⟩ := by
  rw [← enum_typein (α := (succ o).ToType) (· < ·) a]; rw [enum_le_enum']; rw [Subtype.mk_le_mk]; rw [← lt_succ_iff]
  apply typein_lt_self

end Ordinal

/-! ### Representing a cardinal with an ordinal -/

namespace Cardinal

open Ordinal

/-- The ordinal corresponding to a cardinal `c` is the least ordinal whose cardinal is `c`. -/
@[no_expose]
/--
Definition of `ord` / `ord` 的定义

English:
definition ord
  signature: (c : Cardinal)
  body: Quot.liftOn c (fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2) by
  rintro α β ⟨f⟩
refine congr_arg sInf ext fun o => ⟨?_, ?_⟩ <;>
    rintro ⟨⟨r, hr⟩, rfl⟩ <;>
    refine ⟨⟨_, RelIso.IsWellOrder.preimage r ?_⟩, type_preimage _ _⟩
  exacts [f.symm, f]

中文:
定义 ord
  签名: (c : Cardinal)
  定义体: Quot.liftOn c (fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2) by
  rintro α β ⟨f⟩
refine congr_arg sInf ext fun o => ⟨?_, ?_⟩ <;>
    rintro ⟨⟨r, hr⟩, rfl⟩ <;>
    refine ⟨⟨_, RelIso.IsWellOrder.preimage r ?_⟩, type_preimage _ _⟩
  exacts [f.symm, f]

Depends on / 依赖: IsWellOrder, Quot.liftOn, RelIso, RelIso.IsWellOrder.preimage, congr_arg, exacts, f.symm, liftOn, preimage, type_preimage
-/
def ord (c : Cardinal) : Ordinal :=
Quot.liftOn c (fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2) by
  rintro α β ⟨f⟩
refine congr_arg sInf ext fun o => ⟨?_, ?_⟩ <;>
    rintro ⟨⟨r, hr⟩, rfl⟩ <;>
    refine ⟨⟨_, RelIso.IsWellOrder.preimage r ?_⟩, type_preimage _ _⟩
  exacts [f.symm, f]

/--
theorem `ord_eq_iInf` / 定理 `ord_eq_iInf`

English:
theorem ord_eq_iInf
  given: (α : Type u)
  statement: ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2
  proof: (rfl)

@[deprecated (since := "2026-03-15")] alias ord_eq_Inf := ord_eq_iInf

中文:
定理 ord_eq_iInf
  条件: (α : 类型u)
  结论: ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2
  证明: (rfl)

@[deprecated (since := "2026-03-15")] alias ord_eq_Inf := ord_eq_iInf
-/
theorem ord_eq_iInf (α : Type u) : ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2 :=
  (rfl)

@[deprecated (since := "2026-03-15")] alias ord_eq_Inf := ord_eq_iInf

/--
theorem `exists_ord_eq` / 定理 `exists_ord_eq`

English:
theorem exists_ord_eq
  given: (α)
  statement: exists (r : α -> α -> Prop) (_ : IsWellOrder α r), ord #α = type r
  proof: let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩

@[deprecated (since := "2026-03-29")] alias ord_eq := exists_ord_eq

中文:
定理 exists_ord_eq
  条件: (α)
  结论: 存在 (r : α -> α -> 命题) (_ : IsWellOrder α r), ord #α = type r
  证明: let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩

@[deprecated (since := "2026-03-29")] alias ord_eq := exists_ord_eq

Depends on / 依赖: IsWellOrder, ciInf_mem, wo.symm
-/
theorem exists_ord_eq (α) : exists (r : α -> α -> Prop) (_ : IsWellOrder α r), ord #α = type r :=
  let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩

@[deprecated (since := "2026-03-29")] alias ord_eq := exists_ord_eq

/--
theorem `exists_ord_eq_type_lt` / 定理 `exists_ord_eq_type_lt`

English:
theorem exists_ord_eq_type_lt
  given: (α)
  proof: by
  classical
  let ⟨r, _, hr⟩ := exists_ord_eq α
  let := linearOrderOfSTO r
  exact ⟨this, inferInstance, hr⟩

中文:
定理 exists_ord_eq_type_lt
  条件: (α)
  证明: by
  classical
  let ⟨r, _, hr⟩ := exists_ord_eq α
  let := linearOrderOfSTO r
  exact ⟨this, inferInstance, hr⟩

Depends on / 依赖: classical, exists_ord_eq, linearOrderOfSTO
-/
theorem exists_ord_eq_type_lt (α) :
    exists (_ : LinearOrder α) (_ : WellFoundedLT α), ord #α = typeLT α := by
  classical
  let ⟨r, _, hr⟩ := exists_ord_eq α
  let := linearOrderOfSTO r
  exact ⟨this, inferInstance, hr⟩

/--
theorem `ord_le_type` / 定理 `ord_le_type`

English:
theorem ord_le_type
  given: (r : α -> α -> Prop) [h : IsWellOrder α r]
  statement: ord #α <= type r
  proof: ciInf_le' _ (Subtype.mk r h)

@[simp]

中文:
定理 ord_le_type
  条件: (r : α -> α -> 命题) [h : IsWellOrder α r]
  结论: ord #α <= type r
  证明: ciInf_le' _ (Subtype.mk r h)

@[simp]

Depends on / 依赖: Subtype, Subtype.mk, ciInf_le
-/
theorem ord_le_type (r : α -> α -> Prop) [h : IsWellOrder α r] : ord #α <= type r :=
  ciInf_le' _ (Subtype.mk r h)

@[simp]
/--
theorem `card_ord` / 定理 `card_ord`

English:
theorem card_ord
  given: (c)
  statement: (ord c).card = c
  proof: c.inductionOn fun α => let ⟨r, _, e⟩ := exists_ord_eq α; e ▸ card_type r

中文:
定理 card_ord
  条件: (c)
  结论: (ord c).card = c
  证明: c.inductionOn fun α => let ⟨r, _, e⟩ := exists_ord_eq α; e ▸ card_type r

Depends on / 依赖: c.inductionOn, card_type, exists_ord_eq, inductionOn
-/
theorem card_ord (c) : (ord c).card = c :=
  c.inductionOn fun α => let ⟨r, _, e⟩ := exists_ord_eq α; e ▸ card_type r

/--
theorem `gc_ord_card` / 定理 `gc_ord_card`

English:
theorem gc_ord_card
  statement: GaloisConnection ord card
  proof: by
  refine fun c o => c.inductionOn fun α => o.inductionOn fun β s _ => ?_
  let ⟨r, _, e⟩ := exists_ord_eq α
  constructor <;> intro h
  · rw [e] at h
    exact card_le_card h
  · obtain ⟨f⟩ := h
    have g := RelEmbedding.preimage f s
    have := RelEmbedding.isWellOrder g
    exact (ord_le_type 

中文:
定理 gc_ord_card
  结论: GaloisConnection ord card
  证明: by
  refine fun c o => c.inductionOn fun α => o.inductionOn fun β s _ => ?_
  let ⟨r, _, e⟩ := exists_ord_eq α
  constructor <;> intro h
  · rw [e] at h
    exact card_le_card h
  · obtain ⟨f⟩ := h
    have g := RelEmbedding.preimage f s
    have := RelEmbedding.isWellOrder g
    exact (ord_le_type 

Depends on / 依赖: RelEmbedding, RelEmbedding.isWellOrder, RelEmbedding.preimage, c.inductionOn, card_le_card, exists_ord_eq, g.ordinal_type_le, inductionOn, isWellOrder, o.inductionOn, ord_le_type, ordinal_type_le, preimage
-/
theorem gc_ord_card : GaloisConnection ord card := by
  refine fun c o => c.inductionOn fun α => o.inductionOn fun β s _ => ?_
  let ⟨r, _, e⟩ := exists_ord_eq α
  constructor <;> intro h
  · rw [e] at h
    exact card_le_card h
  · obtain ⟨f⟩ := h
    have g := RelEmbedding.preimage f s
    have := RelEmbedding.isWellOrder g
    exact (ord_le_type _).trans g.ordinal_type_le

/--
Definition of `gciOrdCard` / `gciOrdCard` 的定义

English:
definition gciOrdCard
  signature: : GaloisCoinsertion ord card
  body: gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le

中文:
定义 gciOrdCard
  签名: : GaloisCoinsertion ord card
  定义体: gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le

Depends on / 依赖: c.card_ord.le, card_ord, gc_ord_card, gc_ord_card.toGaloisCoinsertion, toGaloisCoinsertion
-/
def gciOrdCard : GaloisCoinsertion ord card :=
  gc_ord_card.toGaloisCoinsertion fun c => c.card_ord.le

/--
theorem `ord_le` / 定理 `ord_le`

English:
theorem ord_le
  given: {c o}
  statement: ord c <= o ↔ c <= o.card
  proof: gc_ord_card.le_iff_le

中文:
定理 ord_le
  条件: {c o}
  结论: ord c <= o ↔ c <= o.card
  证明: gc_ord_card.le_iff_le

Depends on / 依赖: gc_ord_card, gc_ord_card.le_iff_le, le_iff_le
-/
theorem ord_le {c o} : ord c <= o ↔ c <= o.card :=
  gc_ord_card.le_iff_le

/--
theorem `lt_ord` / 定理 `lt_ord`

English:
theorem lt_ord
  given: {c o}
  statement: o < ord c ↔ o.card < c
  proof: gc_ord_card.lt_iff_lt

中文:
定理 lt_ord
  条件: {c o}
  结论: o < ord c ↔ o.card < c
  证明: gc_ord_card.lt_iff_lt

Depends on / 依赖: gc_ord_card, gc_ord_card.lt_iff_lt, lt_iff_lt
-/
theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt

/--
theorem `card_surjective` / 定理 `card_surjective`

English:
theorem card_surjective
  statement: Function.Surjective card
  proof: fun c => ⟨_, card_ord c⟩

中文:
定理 card_surjective
  结论: Function.Surjective card
  证明: fun c => ⟨_, card_ord c⟩

Depends on / 依赖: card_ord
-/
theorem card_surjective : Function.Surjective card :=
  fun c => ⟨_, card_ord c⟩

/--
theorem `bddAbove_ord_image_iff` / 定理 `bddAbove_ord_image_iff`

English:
theorem bddAbove_ord_image_iff
  given: {s : Set Cardinal}
  statement: BddAbove (ord '' s) ↔ BddAbove s
  proof: gc_ord_card.bddAbove_l_image

中文:
定理 bddAbove_ord_image_iff
  条件: {s : Set Cardinal}
  结论: BddAbove (ord '' s) ↔ BddAbove s
  证明: gc_ord_card.bddAbove_l_image

Depends on / 依赖: bddAbove_l_image, gc_ord_card, gc_ord_card.bddAbove_l_image
-/
theorem bddAbove_ord_image_iff {s : Set Cardinal} : BddAbove (ord '' s) ↔ BddAbove s :=
  gc_ord_card.bddAbove_l_image

/--
theorem `ord_card_le` / 定理 `ord_card_le`

English:
theorem ord_card_le
  given: (o : Ordinal)
  statement: o.card.ord <= o
  proof: gc_ord_card.l_u_le _

中文:
定理 ord_card_le
  条件: (o : Ordinal)
  结论: o.card.ord <= o
  证明: gc_ord_card.l_u_le _

Depends on / 依赖: gc_ord_card, gc_ord_card.l_u_le, l_u_le
-/
theorem ord_card_le (o : Ordinal) : o.card.ord <= o :=
  gc_ord_card.l_u_le _

/--
theorem `lt_ord_succ_card` / 定理 `lt_ord_succ_card`

English:
theorem lt_ord_succ_card
  given: (o : Ordinal)
  statement: o < (succ o.card).ord
  proof: lt_ord.2 lt_succ _

中文:
定理 lt_ord_succ_card
  条件: (o : Ordinal)
  结论: o < (succ o.card).ord
  证明: lt_ord.2 lt_succ _

Depends on / 依赖: lt_ord, lt_succ
-/
theorem lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord :=
lt_ord.2 lt_succ _

/--
theorem `card_le_iff` / 定理 `card_le_iff`

English:
theorem card_le_iff
  given: {o : Ordinal} {c : Cardinal}
  statement: o.card <= c ↔ o < (succ c).ord
  proof: by
  rw [lt_ord]; rw [lt_succ_iff]

中文:
定理 card_le_iff
  条件: {o : Ordinal} {c : Cardinal}
  结论: o.card <= c ↔ o < (succ c).ord
  证明: by
  rw [lt_ord]; rw [lt_succ_iff]

Depends on / 依赖: lt_ord, lt_succ_iff
-/
theorem card_le_iff {o : Ordinal} {c : Cardinal} : o.card <= c ↔ o < (succ c).ord := by
  rw [lt_ord]; rw [lt_succ_iff]

/--
lemma `card_le_of_le_ord` / 引理 `card_le_of_le_ord`

English:
lemma card_le_of_le_ord
  given: {o : Ordinal} {c : Cardinal} (ho : o <= c.ord)
  statement: o.card <= c
  proof: by
  rw [← card_ord c]; exact Ordinal.card_le_card ho

@[gcongr, mono]

中文:
引理 card_le_of_le_ord
  条件: {o : Ordinal} {c : Cardinal} (ho : o <= c.ord)
  结论: o.card <= c
  证明: by
  rw [← card_ord c]; exact Ordinal.card_le_card ho

@[gcongr, mono]

Depends on / 依赖: Ordinal, Ordinal.card_le_card, card_le_card, card_ord
-/
lemma card_le_of_le_ord {o : Ordinal} {c : Cardinal} (ho : o <= c.ord) : o.card <= c := by
  rw [← card_ord c]; exact Ordinal.card_le_card ho

@[gcongr, mono]
/--
theorem `ord_strictMono` / 定理 `ord_strictMono`

English:
theorem ord_strictMono
  statement: StrictMono ord
  proof: gciOrdCard.strictMono_l

@[gcongr, mono]

中文:
定理 ord_strictMono
  结论: StrictMono ord
  证明: gciOrdCard.strictMono_l

@[gcongr, mono]

Depends on / 依赖: gciOrdCard, gciOrdCard.strictMono_l, strictMono_l
-/
theorem ord_strictMono : StrictMono ord :=
  gciOrdCard.strictMono_l

@[gcongr, mono]
/--
theorem `ord_mono` / 定理 `ord_mono`

English:
theorem ord_mono
  statement: Monotone ord
  proof: gc_ord_card.monotone_l

中文:
定理 ord_mono
  结论: Monotone ord
  证明: gc_ord_card.monotone_l

Depends on / 依赖: gc_ord_card, gc_ord_card.monotone_l, monotone_l
-/
theorem ord_mono : Monotone ord :=
  gc_ord_card.monotone_l

/--
theorem `ord_injective` / 定理 `ord_injective`

English:
theorem ord_injective
  statement: Injective ord
  proof: ord_strictMono.injective

@[simp]

中文:
定理 ord_injective
  结论: Injective ord
  证明: ord_strictMono.injective

@[simp]

Depends on / 依赖: injective, ord_strictMono, ord_strictMono.injective
-/
theorem ord_injective : Injective ord :=
  ord_strictMono.injective

@[simp]
/--
theorem `ord_le_ord` / 定理 `ord_le_ord`

English:
theorem ord_le_ord
  given: {c₁ c₂}
  statement: ord c₁ <= ord c₂ ↔ c₁ <= c₂
  proof: gciOrdCard.l_le_l_iff

@[simp]

中文:
定理 ord_le_ord
  条件: {c₁ c₂}
  结论: ord c₁ <= ord c₂ ↔ c₁ <= c₂
  证明: gciOrdCard.l_le_l_iff

@[simp]

Depends on / 依赖: gciOrdCard, gciOrdCard.l_le_l_iff, l_le_l_iff
-/
theorem ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂ :=
  gciOrdCard.l_le_l_iff

@[simp]
/--
theorem `ord_lt_ord` / 定理 `ord_lt_ord`

English:
theorem ord_lt_ord
  given: {c₁ c₂}
  statement: ord c₁ < ord c₂ ↔ c₁ < c₂
  proof: ord_strictMono.lt_iff_lt

@[simp]

中文:
定理 ord_lt_ord
  条件: {c₁ c₂}
  结论: ord c₁ < ord c₂ ↔ c₁ < c₂
  证明: ord_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, ord_strictMono, ord_strictMono.lt_iff_lt
-/
theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
  ord_strictMono.lt_iff_lt

@[simp]
/--
theorem `ord_inj` / 定理 `ord_inj`

English:
theorem ord_inj
  given: {c₁ c₂}
  statement: ord c₁ = ord c₂ ↔ c₁ = c₂
  proof: ord_injective.eq_iff

@[simp]

中文:
定理 ord_inj
  条件: {c₁ c₂}
  结论: ord c₁ = ord c₂ ↔ c₁ = c₂
  证明: ord_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, ord_injective, ord_injective.eq_iff
-/
theorem ord_inj {c₁ c₂} : ord c₁ = ord c₂ ↔ c₁ = c₂ :=
  ord_injective.eq_iff

@[simp]
/--
theorem `ord_zero` / 定理 `ord_zero`

English:
theorem ord_zero
  statement: ord 0 = 0
  proof: gc_ord_card.l_bot

@[simp]

中文:
定理 ord_zero
  结论: ord 0 = 0
  证明: gc_ord_card.l_bot

@[simp]

Depends on / 依赖: gc_ord_card, gc_ord_card.l_bot, l_bot
-/
theorem ord_zero : ord 0 = 0 :=
  gc_ord_card.l_bot

@[simp]
/--
theorem `ord_natCast` / 定理 `ord_natCast`

English:
theorem ord_natCast
  given: (n : Nat)
  statement: ord n = n
  proof: by
  apply (ord_le.2 (card_nat n).ge).antisymm
  induction n with
  | zero => exact zero_le
  | succ n IH => exact (IH.trans_lt <| by simp).succ_le

@[deprecated (since := "2026-02-27")] alias ord_nat := ord_natCast

@[simp]

中文:
定理 ord_natCast
  条件: (n : 自然数)
  结论: ord n = n
  证明: by
  apply (ord_le.2 (card_nat n).ge).antisymm
  induction n with
  | zero => exact zero_le
  | succ n IH => exact (IH.trans_lt <| by simp).succ_le

@[deprecated (since := "2026-02-27")] alias ord_nat := ord_natCast

@[simp]

Depends on / 依赖: IH.trans_lt, antisymm, card_nat, ord_le, succ_le, trans_lt, zero_le
-/
theorem ord_natCast (n : Nat) : ord n = n := by
  apply (ord_le.2 (card_nat n).ge).antisymm
  induction n with
  | zero => exact zero_le
  | succ n IH => exact (IH.trans_lt <| by simp).succ_le

@[deprecated (since := "2026-02-27")] alias ord_nat := ord_natCast

@[simp]
/--
theorem `ord_ofNat` / 定理 `ord_ofNat`

English:
theorem ord_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ord ofNat(n) = OfNat.ofNat n
  proof: ord_natCast n

@[simp]

中文:
定理 ord_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ord of自然数(n) = Of自然数.of自然数 n
  证明: ord_natCast n

@[simp]

Depends on / 依赖: ord_natCast
-/
theorem ord_ofNat (n : Nat) [n.AtLeastTwo] : ord ofNat(n) = OfNat.ofNat n :=
  ord_natCast n

@[simp]
/--
theorem `ord_one` / 定理 `ord_one`

English:
theorem ord_one
  statement: ord 1 = 1
  proof: by simpa using ord_natCast 1

中文:
定理 ord_one
  结论: ord 1 = 1
  证明: by simpa using ord_natCast 1

Depends on / 依赖: ord_natCast
-/
theorem ord_one : ord 1 = 1 := by simpa using ord_natCast 1

/--
theorem `isNormal_ord` / 定理 `isNormal_ord`

English:
theorem isNormal_ord
  statement: Order.IsNormal ord where
  proof: ord_strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit := by
    intro a ha
    simp_rw [lowerBounds, upperBounds, mem_ofPred, forall_mem_image, ord_le]
    refine fun b H => le_of_forall_lt fun c hc => ?_
    simpa using H (ha.succ_lt hc)

@[simp]

中文:
定理 isNormal_ord
  结论: Order.IsNormal ord where
  证明: ord_strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit := by
    intro a ha
    simp_rw [lowerBounds, upperBounds, mem_ofPred, forall_mem_image, ord_le]
    refine fun b H => le_of_forall_lt fun c hc => ?_
    simpa using H (ha.succ_lt hc)

@[simp]

Depends on / 依赖: ord_strictMono
-/
theorem isNormal_ord : Order.IsNormal ord where
  strictMono := ord_strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit := by
    intro a ha
    simp_rw [lowerBounds, upperBounds, mem_ofPred, forall_mem_image, ord_le]
    refine fun b H => le_of_forall_lt fun c hc => ?_
    simpa using H (ha.succ_lt hc)

@[simp]
/--
theorem `ord_aleph0` / 定理 `ord_aleph0`

English:
theorem ord_aleph0
  statement: ord.{u} ℵ₀ = ω
  proof: by
refine le_antisymm (ord_le.2 le_rfl) le_of_forall_lt fun o h => ?_
  rcases Ordinal.lt_lift_iff.1 h with ⟨o, ho, rfl⟩
  rw [lt_ord]; rw [← lift_card]; rw [lift_lt_aleph0]; rw [← typein_enum _ ho]
  exact lt_aleph0_iff_fintype.2 ⟨Set.fintypeLTNat _⟩

@[simp]

中文:
定理 ord_aleph0
  结论: ord.{u} ℵ₀ = ω
  证明: by
refine le_antisymm (ord_le.2 le_rfl) le_of_forall_lt fun o h => ?_
  rcases Ordinal.lt_lift_iff.1 h with ⟨o, ho, rfl⟩
  rw [lt_ord]; rw [← lift_card]; rw [lift_lt_aleph0]; rw [← typein_enum _ ho]
  exact lt_aleph0_iff_fintype.2 ⟨Set.fintypeLTNat _⟩

@[simp]

Depends on / 依赖: Ordinal, Ordinal.lt_lift_iff, Set.fintypeLTNat, fintypeLTNat, le_antisymm, le_of_forall_lt, le_rfl, lift_card, lift_lt_aleph0, lt_aleph0_iff_fintype, lt_lift_iff, lt_ord, ord_le, typein_enum
-/
theorem ord_aleph0 : ord.{u} ℵ₀ = ω := by
refine le_antisymm (ord_le.2 le_rfl) le_of_forall_lt fun o h => ?_
  rcases Ordinal.lt_lift_iff.1 h with ⟨o, ho, rfl⟩
  rw [lt_ord]; rw [← lift_card]; rw [lift_lt_aleph0]; rw [← typein_enum _ ho]
  exact lt_aleph0_iff_fintype.2 ⟨Set.fintypeLTNat _⟩

@[simp]
/--
theorem `lift_ord` / 定理 `lift_ord`

English:
theorem lift_ord
  given: (c)
  statement: Ordinal.lift.{u, v} (ord c) = ord (lift.{u, v} c)
  proof: by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) ?_
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, _, rfl⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]

中文:
定理 lift_ord
  条件: (c)
  结论: Ordinal.lift.{u, v} (ord c) = ord (lift.{u, v} c)
  证明: by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) ?_
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, _, rfl⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]

Depends on / 依赖: Ordinal, Ordinal.lift_lt, Ordinal.lt_lift_iff, card_ord, le_antisymm, le_of_forall_lt, lift_card, lift_lt, lt_lift_iff, lt_ord, ord_le
-/
theorem lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lift.{u, v} c) := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) ?_
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, _, rfl⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]

/--
theorem `mk_ord_toType` / 定理 `mk_ord_toType`

English:
theorem mk_ord_toType
  given: (c : Cardinal)
  statement: #c.ord.ToType = c
  proof: by simp

中文:
定理 mk_ord_toType
  条件: (c : Cardinal)
  结论: #c.ord.ToType = c
  证明: by simp
-/
theorem mk_ord_toType (c : Cardinal) : #c.ord.ToType = c := by simp

/--
theorem `card_typein_lt` / 定理 `card_typein_lt`

English:
theorem card_typein_lt
  given: {r : α -> α -> Prop} [IsWellOrder α r] (x : α) (h : ord #α = type r)
  proof: by
  rw [← lt_ord]; rw [h]
  apply typein_lt_type

中文:
定理 card_typein_lt
  条件: {r : α -> α -> 命题} [IsWellOrder α r] (x : α) (h : ord #α = type r)
  证明: by
  rw [← lt_ord]; rw [h]
  apply typein_lt_type

Depends on / 依赖: lt_ord, typein_lt_type
-/
theorem card_typein_lt {r : α -> α -> Prop} [IsWellOrder α r] (x : α) (h : ord #α = type r) :
    card (typein r x) < #α := by
  rw [← lt_ord]; rw [h]
  apply typein_lt_type

/--
theorem `mk_Iio_lt` / 定理 `mk_Iio_lt`

English:
theorem mk_Iio_lt
  given: [LinearOrder α] [WellFoundedLT α] (i : α) (h : ord #α = typeLT α)
  proof: card_typein_lt (r := LT.lt) i h

中文:
定理 mk_Iio_lt
  条件: [LinearOrder α] [WellFoundedLT α] (i : α) (h : ord #α = typeLT α)
  证明: card_typein_lt (r := LT.lt) i h

Depends on / 依赖: LT.lt, card_typein_lt
-/
theorem mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) (h : ord #α = typeLT α) :
    #(Iio i) < #α :=
  card_typein_lt (r := LT.lt) i h

/--
theorem `mk_Ioi_lt` / 定理 `mk_Ioi_lt`

English:
theorem mk_Ioi_lt
  given: {α : Type*} [LinearOrder α] [WellFoundedGT α] (i : α) (h : ord #α = typeLT αᵒᵈ)
  proof: mk_Iio_lt (OrderDual.toDual i) h

@[deprecated mk_Iio_lt (since := "2026-04-12")]

中文:
定理 mk_Ioi_lt
  条件: {α : 类型} [LinearOrder α] [WellFoundedGT α] (i : α) (h : ord #α = typeLT αᵒᵈ)
  证明: mk_Iio_lt (OrderDual.toDual i) h

@[deprecated mk_Iio_lt (since := "2026-04-12")]

Depends on / 依赖: OrderDual, OrderDual.toDual, mk_Iio_lt, toDual
-/
theorem mk_Ioi_lt {α : Type*} [LinearOrder α] [WellFoundedGT α] (i : α) (h : ord #α = typeLT αᵒᵈ) :
    #(Ioi i) < #α :=
  mk_Iio_lt (OrderDual.toDual i) h

@[deprecated mk_Iio_lt (since := "2026-04-12")]
/--
theorem `mk_Iio_toType_ord_lt` / 定理 `mk_Iio_toType_ord_lt`

English:
theorem mk_Iio_toType_ord_lt
  given: {c : Cardinal} (i : c.ord.ToType)
  statement: #(Iio i) < c
  proof: by
  simpa using mk_Iio_lt i

@[deprecated (since := "2026-03-20")] alias mk_Iio_ord_toType := mk_Iio_toType_ord_lt

@[deprecated mk_Iio_lt (since := "2026-03-20")]

中文:
定理 mk_Iio_toType_ord_lt
  条件: {c : Cardinal} (i : c.ord.ToType)
  结论: #(Iio i) < c
  证明: by
  simpa using mk_Iio_lt i

@[deprecated (since := "2026-03-20")] alias mk_Iio_ord_toType := mk_Iio_toType_ord_lt

@[deprecated mk_Iio_lt (since := "2026-03-20")]

Depends on / 依赖: mk_Iio_lt
-/
theorem mk_Iio_toType_ord_lt {c : Cardinal} (i : c.ord.ToType) : #(Iio i) < c := by
  simpa using mk_Iio_lt i

@[deprecated (since := "2026-03-20")] alias mk_Iio_ord_toType := mk_Iio_toType_ord_lt

@[deprecated mk_Iio_lt (since := "2026-03-20")]
/--
theorem `card_typein_toType_lt` / 定理 `card_typein_toType_lt`

English:
theorem card_typein_toType_lt
  given: (c : Cardinal) (x : c.ord.ToType)
  proof: mk_Iio_toType_ord_lt x

@[simp]

中文:
定理 card_typein_toType_lt
  条件: (c : Cardinal) (x : c.ord.ToType)
  证明: mk_Iio_toType_ord_lt x

@[simp]

Depends on / 依赖: ToType, c.ord.ToType
-/
theorem card_typein_toType_lt (c : Cardinal) (x : c.ord.ToType) :
    card (typein (α := c.ord.ToType) (· < ·) x) < c :=
  mk_Iio_toType_ord_lt x

@[simp]
/--
theorem `ord_eq_zero` / 定理 `ord_eq_zero`

English:
theorem ord_eq_zero
  given: {a : Cardinal}
  statement: a.ord = 0 ↔ a = 0
  proof: ord_injective.eq_iff' ord_zero

@[simp]

中文:
定理 ord_eq_zero
  条件: {a : Cardinal}
  结论: a.ord = 0 ↔ a = 0
  证明: ord_injective.eq_iff' ord_zero

@[simp]

Depends on / 依赖: eq_iff, ord_injective, ord_injective.eq_iff, ord_zero
-/
theorem ord_eq_zero {a : Cardinal} : a.ord = 0 ↔ a = 0 :=
  ord_injective.eq_iff' ord_zero

@[simp]
/--
theorem `ord_eq_one` / 定理 `ord_eq_one`

English:
theorem ord_eq_one
  given: {a : Cardinal}
  statement: a.ord = 1 ↔ a = 1
  proof: ord_injective.eq_iff' ord_one

@[simp]

中文:
定理 ord_eq_one
  条件: {a : Cardinal}
  结论: a.ord = 1 ↔ a = 1
  证明: ord_injective.eq_iff' ord_one

@[simp]

Depends on / 依赖: eq_iff, ord_injective, ord_injective.eq_iff, ord_one
-/
theorem ord_eq_one {a : Cardinal} : a.ord = 1 ↔ a = 1 :=
  ord_injective.eq_iff' ord_one

@[simp]
/--
theorem `ord_pos` / 定理 `ord_pos`

English:
theorem ord_pos
  given: {a : Cardinal}
  statement: 0 < a.ord ↔ 0 < a
  proof: by
  rw [← ord_zero]; rw [ord_lt_ord]

@[simp]

中文:
定理 ord_pos
  条件: {a : Cardinal}
  结论: 0 < a.ord ↔ 0 < a
  证明: by
  rw [← ord_zero]; rw [ord_lt_ord]

@[simp]

Depends on / 依赖: ord_lt_ord, ord_zero
-/
theorem ord_pos {a : Cardinal} : 0 < a.ord ↔ 0 < a := by
  rw [← ord_zero]; rw [ord_lt_ord]

@[simp]
/--
theorem `omega0_le_ord` / 定理 `omega0_le_ord`

English:
theorem omega0_le_ord
  given: {a : Cardinal}
  statement: ω <= a.ord ↔ ℵ₀ <= a
  proof: by
  rw [← ord_aleph0]; rw [ord_le_ord]

@[simp]

中文:
定理 omega0_le_ord
  条件: {a : Cardinal}
  结论: ω <= a.ord ↔ ℵ₀ <= a
  证明: by
  rw [← ord_aleph0]; rw [ord_le_ord]

@[simp]

Depends on / 依赖: ord_aleph0, ord_le_ord
-/
theorem omega0_le_ord {a : Cardinal} : ω <= a.ord ↔ ℵ₀ <= a := by
  rw [← ord_aleph0]; rw [ord_le_ord]

@[simp]
/--
theorem `ord_le_omega0` / 定理 `ord_le_omega0`

English:
theorem ord_le_omega0
  given: {a : Cardinal}
  statement: a.ord <= ω ↔ a <= ℵ₀
  proof: by
  rw [← ord_aleph0]; rw [ord_le_ord]

@[simp]

中文:
定理 ord_le_omega0
  条件: {a : Cardinal}
  结论: a.ord <= ω ↔ a <= ℵ₀
  证明: by
  rw [← ord_aleph0]; rw [ord_le_ord]

@[simp]

Depends on / 依赖: ord_aleph0, ord_le_ord
-/
theorem ord_le_omega0 {a : Cardinal} : a.ord <= ω ↔ a <= ℵ₀ := by
  rw [← ord_aleph0]; rw [ord_le_ord]

@[simp]
/--
theorem `ord_lt_omega0` / 定理 `ord_lt_omega0`

English:
theorem ord_lt_omega0
  given: {a : Cardinal}
  statement: a.ord < ω ↔ a < ℵ₀
  proof: le_iff_le_iff_lt_iff_lt.1 omega0_le_ord

@[simp]

中文:
定理 ord_lt_omega0
  条件: {a : Cardinal}
  结论: a.ord < ω ↔ a < ℵ₀
  证明: le_iff_le_iff_lt_iff_lt.1 omega0_le_ord

@[simp]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, omega0_le_ord
-/
theorem ord_lt_omega0 {a : Cardinal} : a.ord < ω ↔ a < ℵ₀ :=
  le_iff_le_iff_lt_iff_lt.1 omega0_le_ord

@[simp]
/--
theorem `omega0_lt_ord` / 定理 `omega0_lt_ord`

English:
theorem omega0_lt_ord
  given: {a : Cardinal}
  statement: ω < a.ord ↔ ℵ₀ < a
  proof: le_iff_le_iff_lt_iff_lt.1 ord_le_omega0

@[simp]

中文:
定理 omega0_lt_ord
  条件: {a : Cardinal}
  结论: ω < a.ord ↔ ℵ₀ < a
  证明: le_iff_le_iff_lt_iff_lt.1 ord_le_omega0

@[simp]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, ord_le_omega0
-/
theorem omega0_lt_ord {a : Cardinal} : ω < a.ord ↔ ℵ₀ < a :=
  le_iff_le_iff_lt_iff_lt.1 ord_le_omega0

@[simp]
/--
theorem `ord_eq_omega0` / 定理 `ord_eq_omega0`

English:
theorem ord_eq_omega0
  given: {a : Cardinal}
  statement: a.ord = ω ↔ a = ℵ₀
  proof: ord_injective.eq_iff' ord_aleph0

中文:
定理 ord_eq_omega0
  条件: {a : Cardinal}
  结论: a.ord = ω ↔ a = ℵ₀
  证明: ord_injective.eq_iff' ord_aleph0

Depends on / 依赖: eq_iff, ord_aleph0, ord_injective, ord_injective.eq_iff
-/
theorem ord_eq_omega0 {a : Cardinal} : a.ord = ω ↔ a = ℵ₀ :=
  ord_injective.eq_iff' ord_aleph0

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
@[deprecated ord (since := "2026-02-27")]
/--
Definition of `ord.orderEmbedding` / `ord.orderEmbedding` 的定义

English:
definition ord.orderEmbedding
  signature: : Cardinal ↪o Ordinal
  body: OrderEmbedding.ofStrictMono _ fun _ _ => Cardinal.ord_lt_ord.2

@[deprecated ord (since := "2026-02-27")]

中文:
定义 ord.orderEmbedding
  签名: : Cardinal ↪o Ordinal
  定义体: OrderEmbedding.ofStrictMono _ fun _ _ => Cardinal.ord_lt_ord.2

@[deprecated ord (since := "2026-02-27")]

Depends on / 依赖: Cardinal, Cardinal.ord_lt_ord, OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, ord_lt_ord
-/
def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  OrderEmbedding.ofStrictMono _ fun _ _ => Cardinal.ord_lt_ord.2

@[deprecated ord (since := "2026-02-27")]
/--
theorem `ord.orderEmbedding_coe` / 定理 `ord.orderEmbedding_coe`

English:
theorem ord.orderEmbedding_coe
  statement: (ord.orderEmbedding : Cardinal -> Ordinal) = ord
  proof: rfl

中文:
定理 ord.orderEmbedding_coe
  结论: (ord.orderEmbedding : Cardinal -> Ordinal) = ord
  证明: rfl
-/
theorem ord.orderEmbedding_coe : (ord.orderEmbedding : Cardinal -> Ordinal) = ord :=
  rfl

/--
lemma `nonempty_ord_toType` / 引理 `nonempty_ord_toType`

English:
lemma nonempty_ord_toType
  given: {c : Cardinal} (h : c != 0)
  proof: by
  rwa [Ordinal.nonempty_toType_iff, ne_eq, ord_eq_zero]

中文:
引理 nonempty_ord_toType
  条件: {c : Cardinal} (h : c != 0)
  证明: by
  rwa [Ordinal.nonempty_toType_iff, ne_eq, ord_eq_zero]

Depends on / 依赖: Ordinal, Ordinal.nonempty_toType_iff, ne_eq, nonempty_toType_iff, ord_eq_zero
-/
lemma nonempty_ord_toType {c : Cardinal} (h : c != 0) :
    Nonempty c.ord.ToType := by
  rwa [Ordinal.nonempty_toType_iff, ne_eq, ord_eq_zero]

end Cardinal

namespace Ordinal

@[simp]
/--
theorem `nat_le_card` / 定理 `nat_le_card`

English:
theorem nat_le_card
  given: {o} {n : Nat}
  statement: (n : Cardinal) <= card o ↔ (n : Ordinal) <= o
  proof: by
  rw [← Cardinal.ord_le]; rw [Cardinal.ord_natCast]

@[simp]

中文:
定理 nat_le_card
  条件: {o} {n : 自然数}
  结论: (n : Cardinal) <= card o ↔ (n : Ordinal) <= o
  证明: by
  rw [← Cardinal.ord_le]; rw [Cardinal.ord_natCast]

@[simp]

Depends on / 依赖: Cardinal, Cardinal.ord_le, Cardinal.ord_natCast, ord_le, ord_natCast
-/
theorem nat_le_card {o} {n : Nat} : (n : Cardinal) <= card o ↔ (n : Ordinal) <= o := by
  rw [← Cardinal.ord_le]; rw [Cardinal.ord_natCast]

@[simp]
/--
theorem `one_le_card` / 定理 `one_le_card`

English:
theorem one_le_card
  given: {o}
  statement: 1 <= card o ↔ 1 <= o
  proof: by
  simpa using nat_le_card (n := 1)

@[simp]

中文:
定理 one_le_card
  条件: {o}
  结论: 1 <= card o ↔ 1 <= o
  证明: by
  simpa using nat_le_card (n := 1)

@[simp]

Depends on / 依赖: nat_le_card
-/
theorem one_le_card {o} : 1 <= card o ↔ 1 <= o := by
  simpa using nat_le_card (n := 1)

@[simp]
/--
theorem `ofNat_le_card` / 定理 `ofNat_le_card`

English:
theorem ofNat_le_card
  given: {o} {n : Nat} [n.AtLeastTwo]
  proof: nat_le_card

@[simp]

中文:
定理 ofNat_le_card
  条件: {o} {n : 自然数} [n.AtLeastTwo]
  证明: nat_le_card

@[simp]

Depends on / 依赖: nat_le_card
-/
theorem ofNat_le_card {o} {n : Nat} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) <= card o ↔ (OfNat.ofNat n : Ordinal) <= o :=
  nat_le_card

@[simp]
/--
theorem `aleph0_le_card` / 定理 `aleph0_le_card`

English:
theorem aleph0_le_card
  given: {o}
  statement: ℵ₀ <= card o ↔ ω <= o
  proof: by
  rw [← ord_le]; rw [ord_aleph0]

@[simp]

中文:
定理 aleph0_le_card
  条件: {o}
  结论: ℵ₀ <= card o ↔ ω <= o
  证明: by
  rw [← ord_le]; rw [ord_aleph0]

@[simp]

Depends on / 依赖: ord_aleph0, ord_le
-/
theorem aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o := by
  rw [← ord_le]; rw [ord_aleph0]

@[simp]
/--
theorem `card_lt_aleph0` / 定理 `card_lt_aleph0`

English:
theorem card_lt_aleph0
  given: {o}
  statement: card o < ℵ₀ ↔ o < ω
  proof: le_iff_le_iff_lt_iff_lt.1 aleph0_le_card

@[simp]

中文:
定理 card_lt_aleph0
  条件: {o}
  结论: card o < ℵ₀ ↔ o < ω
  证明: le_iff_le_iff_lt_iff_lt.1 aleph0_le_card

@[simp]

Depends on / 依赖: aleph0_le_card, le_iff_le_iff_lt_iff_lt
-/
theorem card_lt_aleph0 {o} : card o < ℵ₀ ↔ o < ω :=
  le_iff_le_iff_lt_iff_lt.1 aleph0_le_card

@[simp]
/--
theorem `nat_lt_card` / 定理 `nat_lt_card`

English:
theorem nat_lt_card
  given: {o} {n : Nat}
  statement: (n : Cardinal) < card o ↔ (n : Ordinal) < o
  proof: by
  rw [← natCast_add_one_le_iff]; rw [← succ_le_iff]; rw [← Nat.cast_add_one]; rw [nat_le_card]
  rfl

@[simp]

中文:
定理 nat_lt_card
  条件: {o} {n : 自然数}
  结论: (n : Cardinal) < card o ↔ (n : Ordinal) < o
  证明: by
  rw [← natCast_add_one_le_iff]; rw [← succ_le_iff]; rw [← Nat.cast_add_one]; rw [nat_le_card]
  rfl

@[simp]

Depends on / 依赖: Nat.cast_add_one, cast_add_one, natCast_add_one_le_iff, nat_le_card, succ_le_iff
-/
theorem nat_lt_card {o} {n : Nat} : (n : Cardinal) < card o ↔ (n : Ordinal) < o := by
  rw [← natCast_add_one_le_iff]; rw [← succ_le_iff]; rw [← Nat.cast_add_one]; rw [nat_le_card]
  rfl

@[simp]
/--
theorem `zero_lt_card` / 定理 `zero_lt_card`

English:
theorem zero_lt_card
  given: {o}
  statement: 0 < card o ↔ 0 < o
  proof: by
  simpa using nat_lt_card (n := 0)

@[simp]

中文:
定理 zero_lt_card
  条件: {o}
  结论: 0 < card o ↔ 0 < o
  证明: by
  simpa using nat_lt_card (n := 0)

@[simp]

Depends on / 依赖: nat_lt_card
-/
theorem zero_lt_card {o} : 0 < card o ↔ 0 < o := by
  simpa using nat_lt_card (n := 0)

@[simp]
/--
theorem `one_lt_card` / 定理 `one_lt_card`

English:
theorem one_lt_card
  given: {o}
  statement: 1 < card o ↔ 1 < o
  proof: by
  simpa using nat_lt_card (n := 1)

@[simp]

中文:
定理 one_lt_card
  条件: {o}
  结论: 1 < card o ↔ 1 < o
  证明: by
  simpa using nat_lt_card (n := 1)

@[simp]

Depends on / 依赖: nat_lt_card
-/
theorem one_lt_card {o} : 1 < card o ↔ 1 < o := by
  simpa using nat_lt_card (n := 1)

@[simp]
/--
theorem `ofNat_lt_card` / 定理 `ofNat_lt_card`

English:
theorem ofNat_lt_card
  given: {o} {n : Nat} [n.AtLeastTwo]
  proof: nat_lt_card

@[simp]

中文:
定理 ofNat_lt_card
  条件: {o} {n : 自然数} [n.AtLeastTwo]
  证明: nat_lt_card

@[simp]

Depends on / 依赖: nat_lt_card
-/
theorem ofNat_lt_card {o} {n : Nat} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < card o ↔ (OfNat.ofNat n : Ordinal) < o :=
  nat_lt_card

@[simp]
/--
theorem `card_lt_nat` / 定理 `card_lt_nat`

English:
theorem card_lt_nat
  given: {o} {n : Nat}
  statement: card o < n ↔ o < n
  proof: lt_iff_lt_of_le_iff_le nat_le_card

@[simp]

中文:
定理 card_lt_nat
  条件: {o} {n : 自然数}
  结论: card o < n ↔ o < n
  证明: lt_iff_lt_of_le_iff_le nat_le_card

@[simp]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, nat_le_card
-/
theorem card_lt_nat {o} {n : Nat} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp]
/--
theorem `card_lt_ofNat` / 定理 `card_lt_ofNat`

English:
theorem card_lt_ofNat
  given: {o} {n : Nat} [n.AtLeastTwo]
  proof: card_lt_nat

@[simp]

中文:
定理 card_lt_ofNat
  条件: {o} {n : 自然数} [n.AtLeastTwo]
  证明: card_lt_nat

@[simp]

Depends on / 依赖: card_lt_nat
-/
theorem card_lt_ofNat {o} {n : Nat} [n.AtLeastTwo] :
    card o < ofNat(n) ↔ o < OfNat.ofNat n :=
  card_lt_nat

@[simp]
/--
theorem `card_le_nat` / 定理 `card_le_nat`

English:
theorem card_le_nat
  given: {o} {n : Nat}
  statement: card o <= n ↔ o <= n
  proof: le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]

中文:
定理 card_le_nat
  条件: {o} {n : 自然数}
  结论: card o <= n ↔ o <= n
  证明: le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]

Depends on / 依赖: le_iff_le_iff_lt_iff_lt, nat_lt_card
-/
theorem card_le_nat {o} {n : Nat} : card o <= n ↔ o <= n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
/--
theorem `card_le_one` / 定理 `card_le_one`

English:
theorem card_le_one
  given: {o}
  statement: card o <= 1 ↔ o <= 1
  proof: by
  simpa using card_le_nat (n := 1)

@[simp]

中文:
定理 card_le_one
  条件: {o}
  结论: card o <= 1 ↔ o <= 1
  证明: by
  simpa using card_le_nat (n := 1)

@[simp]

Depends on / 依赖: card_le_nat
-/
theorem card_le_one {o} : card o <= 1 ↔ o <= 1 := by
  simpa using card_le_nat (n := 1)

@[simp]
/--
theorem `card_le_ofNat` / 定理 `card_le_ofNat`

English:
theorem card_le_ofNat
  given: {o} {n : Nat} [n.AtLeastTwo]
  proof: card_le_nat

@[simp]

中文:
定理 card_le_ofNat
  条件: {o} {n : 自然数} [n.AtLeastTwo]
  证明: card_le_nat

@[simp]

Depends on / 依赖: card_le_nat
-/
theorem card_le_ofNat {o} {n : Nat} [n.AtLeastTwo] :
    card o <= ofNat(n) ↔ o <= OfNat.ofNat n :=
  card_le_nat

@[simp]
/--
theorem `card_eq_nat` / 定理 `card_eq_nat`

English:
theorem card_eq_nat
  given: {o} {n : Nat}
  statement: card o = n ↔ o = n
  proof: by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp]

中文:
定理 card_eq_nat
  条件: {o} {n : 自然数}
  结论: card o = n ↔ o = n
  证明: by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp]

Depends on / 依赖: card_le_nat, le_antisymm_iff, nat_le_card
-/
theorem card_eq_nat {o} {n : Nat} : card o = n ↔ o = n := by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp]
/--
theorem `card_eq_zero` / 定理 `card_eq_zero`

English:
theorem card_eq_zero
  given: {o}
  statement: card o = 0 ↔ o = 0
  proof: by
  simpa using card_eq_nat (n := 0)

@[simp]

中文:
定理 card_eq_zero
  条件: {o}
  结论: card o = 0 ↔ o = 0
  证明: by
  simpa using card_eq_nat (n := 0)

@[simp]

Depends on / 依赖: card_eq_nat
-/
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 := by
  simpa using card_eq_nat (n := 0)

@[simp]
/--
theorem `card_eq_one` / 定理 `card_eq_one`

English:
theorem card_eq_one
  given: {o}
  statement: card o = 1 ↔ o = 1
  proof: by
  simpa using card_eq_nat (n := 1)

中文:
定理 card_eq_one
  条件: {o}
  结论: card o = 1 ↔ o = 1
  证明: by
  simpa using card_eq_nat (n := 1)

Depends on / 依赖: card_eq_nat
-/
theorem card_eq_one {o} : card o = 1 ↔ o = 1 := by
  simpa using card_eq_nat (n := 1)

/--
theorem `_root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0` / 定理 `_root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0`

English:
theorem _root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0
  given: (o : Ordinal) {c : Cardinal} (hc : c < ℵ₀)
  proof: by
  rcases lt_aleph0.mp hc with ⟨n, rfl⟩
  simp

中文:
定理 _root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0
  条件: (o : Ordinal) {c : Cardinal} (hc : c < ℵ₀)
  证明: by
  rcases lt_aleph0.mp hc with ⟨n, rfl⟩
  simp

Depends on / 依赖: lt_aleph0, lt_aleph0.mp
-/
theorem _root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0 (o : Ordinal) {c : Cardinal} (hc : c < ℵ₀) :
    o <= c.ord ↔ o.card <= c := by
  rcases lt_aleph0.mp hc with ⟨n, rfl⟩
  simp

/--
theorem `mem_range_lift_of_card_le` / 定理 `mem_range_lift_of_card_le`

English:
theorem mem_range_lift_of_card_le
  statement: {a : Cardinal.{u}} {b : Ordinal.{max u v}}
  proof: by
  rw [card_le_iff]; rw [← lift_succ]; rw [← lift_ord] at h
  exact mem_range_lift_of_le h.le

@[simp]

中文:
定理 mem_range_lift_of_card_le
  结论: {a : Cardinal.{u}} {b : Ordinal.{max u v}}
  证明: by
  rw [card_le_iff]; rw [← lift_succ]; rw [← lift_ord] at h
  exact mem_range_lift_of_le h.le

@[simp]

Depends on / 依赖: card_le_iff, h.le, lift_ord, lift_succ, mem_range_lift_of_le
-/
theorem mem_range_lift_of_card_le {a : Cardinal.{u}} {b : Ordinal.{max u v}}
    (h : card b <= Cardinal.lift.{v, u} a) : b in Set.range lift.{v, u} := by
  rw [card_le_iff]; rw [← lift_succ]; rw [← lift_ord] at h
  exact mem_range_lift_of_le h.le

@[simp]
/--
theorem `card_eq_ofNat` / 定理 `card_eq_ofNat`

English:
theorem card_eq_ofNat
  given: {o} {n : Nat} [n.AtLeastTwo]
  proof: card_eq_nat

中文:
定理 card_eq_ofNat
  条件: {o} {n : 自然数} [n.AtLeastTwo]
  证明: card_eq_nat

Depends on / 依赖: card_eq_nat
-/
theorem card_eq_ofNat {o} {n : Nat} [n.AtLeastTwo] :
    card o = ofNat(n) ↔ o = OfNat.ofNat n :=
  card_eq_nat

variable (r) in
@[simp]
/--
theorem `type_fintype` / 定理 `type_fintype`

English:
theorem type_fintype
  given: [IsWellOrder α r] [Fintype α]
  proof: by rw [← card_eq_nat, card_type, mk_fintype]

中文:
定理 type_fintype
  条件: [IsWellOrder α r] [Fintype α]
  证明: by rw [← card_eq_nat, card_type, mk_fintype]

Depends on / 依赖: card_eq_nat, card_type, mk_fintype
-/
theorem type_fintype [IsWellOrder α r] [Fintype α] :
    type r = Fintype.card α := by rw [← card_eq_nat, card_type, mk_fintype]

/--
theorem `type_fin` / 定理 `type_fin`

English:
theorem type_fin
  given: (n : Nat)
  statement: typeLT (Fin n) = n
  proof: by simp

中文:
定理 type_fin
  条件: (n : 自然数)
  结论: typeLT (Fin n) = n
  证明: by simp
-/
theorem type_fin (n : Nat) : typeLT (Fin n) = n := by simp

variable (r) in
/--
theorem `ord_mk_le_type` / 定理 `ord_mk_le_type`

English:
theorem ord_mk_le_type
  given: [IsWellOrder α r] (s : Set α)
  statement: (#s).ord <= type r
  proof: by
  grw [← ord_le_type, ord_le_ord, le_mk_iff_exists_set]
  use s

中文:
定理 ord_mk_le_type
  条件: [IsWellOrder α r] (s : Set α)
  结论: (#s).ord <= type r
  证明: by
  grw [← ord_le_type, ord_le_ord, le_mk_iff_exists_set]
  use s

Depends on / 依赖: le_mk_iff_exists_set, ord_le_ord, ord_le_type
-/
theorem ord_mk_le_type [IsWellOrder α r] (s : Set α) : (#s).ord <= type r := by
  grw [← ord_le_type, ord_le_ord, le_mk_iff_exists_set]
  use s

variable (r) in
/--
theorem `ord_mk_lt_type` / 定理 `ord_mk_lt_type`

English:
theorem ord_mk_lt_type
  given: [IsWellOrder α r] {s : Set α} (hfin : s.Finite) (h : sᶜ.Nonempty)
  proof: by
  grw [← ord_le_type, ord_lt_ord, ← mk_univ (α := α)]
  exact card_lt_card_of_left_finite hfin h.ssubset_univ

中文:
定理 ord_mk_lt_type
  条件: [IsWellOrder α r] {s : Set α} (hfin : s.Finite) (h : sᶜ.Nonempty)
  证明: by
  grw [← ord_le_type, ord_lt_ord, ← mk_univ (α := α)]
  exact card_lt_card_of_left_finite hfin h.ssubset_univ

Depends on / 依赖: card_lt_card_of_left_finite, h.ssubset_univ, mk_univ, ord_le_type, ord_lt_ord, ssubset_univ
-/
theorem ord_mk_lt_type [IsWellOrder α r] {s : Set α} (hfin : s.Finite) (h : sᶜ.Nonempty) :
    (#s).ord < type r := by
  grw [← ord_le_type, ord_lt_ord, ← mk_univ (α := α)]
  exact card_lt_card_of_left_finite hfin h.ssubset_univ

variable (r) in
/--
theorem `not_lt_enum_ord_mk_min_compl` / 定理 `not_lt_enum_ord_mk_min_compl`

English:
theorem not_lt_enum_ord_mk_min_compl
  statement: [IsWellOrder α r] {s : Set α} (hfin : s.Finite)
  proof: by
  grw [← typein_le_typein, typein_enum, Cardinal.le_ord_iff_card_le_of_lt_aleph0 _ hfin.lt_aleph0,
    card_typein_min_le_mk]

中文:
定理 not_lt_enum_ord_mk_min_compl
  结论: [IsWellOrder α r] {s : Set α} (hfin : s.Finite)
  证明: by
  grw [← typein_le_typein, typein_enum, Cardinal.le_ord_iff_card_le_of_lt_aleph0 _ hfin.lt_aleph0,
    card_typein_min_le_mk]

Depends on / 依赖: Cardinal, Cardinal.le_ord_iff_card_le_of_lt_aleph0, card_typein_min_le_mk, hfin.lt_aleph0, le_ord_iff_card_le_of_lt_aleph0, lt_aleph0, typein_enum, typein_le_typein
-/
theorem not_lt_enum_ord_mk_min_compl [IsWellOrder α r] {s : Set α} (hfin : s.Finite)
    (h : sᶜ.Nonempty) :
    ¬r (enum r ⟨#s |>.ord, ord_mk_lt_type r hfin h⟩) (IsWellFounded.wf.min (r := r) sᶜ h) := by
  grw [← typein_le_typein, typein_enum, Cardinal.le_ord_iff_card_le_of_lt_aleph0 _ hfin.lt_aleph0,
    card_typein_min_le_mk]

end Ordinal


/--
theorem `List.SortedGT.lt_ord_of_lt` / 定理 `List.SortedGT.lt_ord_of_lt`

English:
theorem List.SortedGT.lt_ord_of_lt
  statement: [LinearOrder α] [WellFoundedLT α] {l m : List α}
  proof: by
  replace hmltl : List.Lex (· < ·) m l := hmltl
  cases l with
  | nil => simp at hmltl
  | cons a as =>
    cases m with
    | nil => intro i hi; simp at hi
    | cons b bs =>
      intro i hi
      suffices h : i <= a by refine lt_of_le_of_lt ?_ (hlt a mem_cons_self); simpa
      cases hi with


中文:
定理 List.SortedGT.lt_ord_of_lt
  结论: [LinearOrder α] [WellFoundedLT α] {l m : List α}
  证明: by
  replace hmltl : List.Lex (· < ·) m l := hmltl
  cases l with
  | nil => simp at hmltl
  | cons a as =>
    cases m with
    | nil => intro i hi; simp at hi
    | cons b bs =>
      intro i hi
      suffices h : i <= a by refine lt_of_le_of_lt ?_ (hlt a mem_cons_self); simpa
      cases hi with

-/
theorem List.SortedGT.lt_ord_of_lt [LinearOrder α] [WellFoundedLT α] {l m : List α}
    {o : Ordinal} (hl : l.SortedGT) (hm : m.SortedGT) (hmltl : m < l)
    (hlt : forall i in l, Ordinal.typein (α := α) (· < ·) i < o) :
      forall i in m, Ordinal.typein (α := α) (· < ·) i < o := by
  replace hmltl : List.Lex (· < ·) m l := hmltl
  cases l with
  | nil => simp at hmltl
  | cons a as =>
    cases m with
    | nil => intro i hi; simp at hi
    | cons b bs =>
      intro i hi
      suffices h : i <= a by refine lt_of_le_of_lt ?_ (hlt a mem_cons_self); simpa
      cases hi with
      | head as => exact List.head_le_of_lt hmltl
      | tail b hi => exact le_of_lt (lt_of_lt_of_le (List.rel_of_pairwise_cons hm.pairwise hi)
          (List.head_le_of_lt hmltl))
