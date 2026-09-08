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
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Definition of ordinals -/


/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
/-
**WellOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled structure registering a well order on a type. Ordinals will be defined a
s a quotient
of this type.
-/
structure WellOrder : Type (u + 1) where
  /-- The underlying type of the order. -/
  α : Type u
  /-- The underlying relation of the order. -/
  r : α → α → Prop
  /-- The proposition that `r` is a well-ordering for `α`. -/
  wo : IsWellOrder α r

attribute [instance] WellOrder.wo

namespace WellOrder

/-
**WellOrder.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `WellOrder`。
形式化陈述：inhabited : Inhabited WellOrder
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited WellOrder :=
  ⟨⟨PEmpty, _, (inferInstance : IsWellOrder PEmpty emptyRelation)⟩⟩

end WellOrder

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
/-
**Ordinal.isEquivalent** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Ordinal.isEquivalent : Setoid WellOrder where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence relation on well orders on arbitrary types in universe `u`, given by
 order
isomorphism.
-/
instance Ordinal.isEquivalent : Setoid WellOrder where
  r := fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
@[pp_with_univ, wikidata Q191780]
/-
**Ordinal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ordinal : Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism.
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
/-
**Ordinal.ToType** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ordinal.ToType (o : Ordinal.{u}) : Type u
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A "canonical" type order-isomorphic to the ordinal `o`, living in the same unive
rse. This is
defined through the axiom of choice; in particular, it has no useful def-eqs, an
d it is not exposed.

Use this over `Iio o` only when it is paramount to have a `Type u` rather than a
 `Type (u + 1)`,
and convert using

```
Ordinal.ToType.mk : Iio o → o.ToType
Ordinal.ToType.toOrd : o.ToType → Iio o
```
-/
def Ordinal.ToType (o : Ordinal.{u}) : Type u :=
  o.out.α

@[no_expose]
/-
**linearOrder_toType** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：linearOrder_toType (o : Ordinal) : LinearOrder o.ToType
参数：o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrder_toType (o : Ordinal) : LinearOrder o.ToType :=
  @IsWellOrder.linearOrder _ o.out.r o.out.wo
/-
**wellFoundedLT_toType** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：wellFoundedLT_toType (o : Ordinal) : WellFoundedLT o.ToType
参数：o : Ordinal。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `WellOrder.wo`：∀ (self : WellOrder), IsWellOrder self.α self.r
-/
instance wellFoundedLT_toType (o : Ordinal) : WellFoundedLT o.ToType :=
  o.out.wo.toIsWellFounded
/-
**hasWellFounded_toType** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：hasWellFounded_toType (o : Ordinal) : WellFoundedRelation o.ToType
参数：o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasWellFounded_toType (o : Ordinal) : WellFoundedRelation o.ToType :=
  WellFoundedLT.toWellFoundedRelation

namespace Ordinal

@[no_expose]
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (o : Ordinal) : SuccOrder o.ToType :=
  .ofLinearWellFoundedLT _

/-! ### Basic properties of the order type -/

/-- The order type of a well order is an ordinal. -/
/-
**Ordinal.type** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：type (r : α -> α -> Prop) [wo : IsWellOrder α r] : Ordinal
参数：r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order type of a well order is an ordinal.
-/
def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧

/-- `typeLT α` is an abbreviation for the order type of the `<` relation of `α`. -/
scoped notation3 "typeLT " α:70 => @Ordinal.type α (· < ·) inferInstance

/-- info: typeLT ℕ : Ordinal.{0} -/
#guard_msgs in
#check typeLT ℕ

/-
**Ordinal.zero** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：zero : Zero Ordinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
-/
instance zero : Zero Ordinal :=
  ⟨type <| @emptyRelation PEmpty⟩
/-
**Ordinal.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：inhabited : Inhabited Ordinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited Ordinal :=
  ⟨0⟩
/-
**Ordinal.one** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：one : One Ordinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
instance one : One Ordinal :=
  ⟨type <| @emptyRelation PUnit⟩

@[simp]
/-
**Ordinal.type_toType** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_toType (o : Ordinal) : typeLT o.ToType = o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem type_toType (o : Ordinal) : typeLT o.ToType = o :=
  o.out_eq
/-
**Ordinal.type_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_eq {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r] 
[IsWellOrder β s] : type r = type s ↔ Nonempty (r ≃r s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
-/
theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotient.eq'
/-
**Ordinal._root_.RelIso.ordinalType_congr** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RelIso.ordinalType_congr {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩

@[deprecated (since := "2026-05-25")]
alias _root_.RelIso.ordinal_type_eq := RelIso.ordinalType_congr
/-
**Ordinal._root_.OrderIso.ordinalType_congr** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.ordinalType_congr {α β} [LinearOrder α] [LinearOrder β]
    [WellFoundedLT α] [WellFoundedLT β] (h : α ≃o β) : typeLT α = typeLT β :=
  h.toRelIsoLT.ordinalType_congr
/-
**Ordinal.type_eq_zero_of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0
参数：r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ordinalType_congr`：∀ {α β : Type u_1} {r : α → α → Prop} {s : β →
 β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ≃r s), O
rdinal.type r …
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
-/
theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinalType_congr

@[simp]
/-
**Ordinal.type_eq_zero_iff_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_eq_zero_iff_isEmpty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
· 使用定理 `Ordinal.type_eq`：type_eq {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
 [IsWellOrder α r] [IsWellOrder β s] : type r = type s ↔ Nonempty (r ≃r s)
· 使用定理 `Equiv.isEmpty`：∀ {α : Sort u_1} {β : Sort u_4} (e : α ≃ β) [IsEmpty β], 
IsEmpty α
· 使用定理 `Ordinal.type_eq_zero_of_empty`：type_eq_zero_of_empty (r) [IsWellOrder α 
r] [IsEmpty α] : type r = 0
-/
theorem type_eq_zero_iff_isEmpty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ type_eq_zero_of_empty r⟩
  let ⟨s⟩ := type_eq.1 h
  exact s.toEquiv.isEmpty
/-
**Ordinal.type_ne_zero_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_ne_zero_iff_nonempty [IsWellOrder α r] : type r != 0 ↔ Nonempty α
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
theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α := by simp
/-
**Ordinal.type_ne_zero_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r !
= 0
参数：r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.type_ne_zero_iff_nonempty`：type_ne_zero_iff_nonempty [IsWellOrde
r α r] : type r != 0 ↔ Nonempty α
-/
theorem type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h
/-
**Ordinal.type_pEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_pEmpty : type (@emptyRelation PEmpty) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
-/
theorem type_pEmpty : type (@emptyRelation PEmpty) = 0 :=
  rfl
/-
**Ordinal.type_empty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_empty : type (@emptyRelation Empty) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.type_eq_zero_of_empty`：type_eq_zero_of_empty (r) [IsWellOrder α 
r] [IsEmpty α] : type r = 0
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonEmpty`：Subsingleton Empty
-/
theorem type_empty : type (@emptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _
/-
**Ordinal.type_eq_one_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_eq_one_of_unique (r) [IsWellOrder α r] [Nonempty α] [Subsingleton α] 
: type r = 1
参数：r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `RelIso.ordinalType_congr`：∀ {α β : Type u_1} {r : α → α → Prop} {s : β →
 β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ≃r s), O
rdinal.type r …
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `instIrreflEmptyRelation_mathlib`：∀ {α : Sort u_1}, Std.Irrefl emptyRelat
ion
-/
theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Nonempty α] [Subsingleton α] : type r = 1 := by
  cases nonempty_unique α
  exact (RelIso.ofUniqueOfIrrefl r _).ordinalType_congr

@[simp]
/-
**Ordinal.type_eq_one_iff_unique** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Ordinal.type_eq`：type_eq {α β} {r : α -> α -> Prop} {s : β -> β -> Prop}
 [IsWellOrder α r] [IsWellOrder β s] : type r = type s ↔ Nonempty (r ≃r s)
· 使用定理 `Ordinal.type_eq_one_of_unique`：type_eq_one_of_unique (r) [IsWellOrder α 
r] [Nonempty α] [Subsingleton α] : type r = 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h ↦ let ⟨s⟩ := type_eq.1 h; ⟨s.toEquiv.unique⟩,
    fun ⟨_⟩ ↦ type_eq_one_of_unique r⟩
/-
**Ordinal.type_pUnit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_pUnit : type (@emptyRelation PUnit) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem type_pUnit : type (@emptyRelation PUnit) = 1 :=
  rfl
/-
**Ordinal.type_unit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_unit : type (@emptyRelation Unit) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem type_unit : type (@emptyRelation Unit) = 1 :=
  rfl

@[simp]
/-
**Ordinal.isEmpty_toType_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isEmpty_toType_iff {o : Ordinal} : IsEmpty o.ToType ↔ o = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_eq_zero_iff_isEmpty`：type_eq_zero_iff_isEmpty [IsWellOrder 
α r] : type r = 0 ↔ IsEmpty α
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isEmpty_toType_iff {o : Ordinal} : IsEmpty o.ToType ↔ o = 0 := by
  rw [← @type_eq_zero_iff_isEmpty o.ToType (· < ·), type_toType]

@[deprecated (since := "2026-02-18")] alias toType_empty_iff_eq_zero := isEmpty_toType_iff
/-
**Ordinal.isEmpty_toType_zero** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：isEmpty_toType_zero : IsEmpty (ToType 0)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.isEmpty_toType_iff`：isEmpty_toType_iff {o : Ordinal} : IsEmpty o
.ToType ↔ o = 0
-/
instance isEmpty_toType_zero : IsEmpty (ToType 0) :=
  isEmpty_toType_iff.2 rfl

@[simp]
/-
**Ordinal.nonempty_toType_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nonempty_toType_iff {o : Ordinal} : Nonempty o.ToType ↔ o != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_ne_zero_iff_nonempty`：type_ne_zero_iff_nonempty [IsWellOrde
r α r] : type r != 0 ↔ Nonempty α
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_toType_iff {o : Ordinal} : Nonempty o.ToType ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.ToType (· < ·), type_toType]

@[deprecated (since := "2026-02-18")] alias toType_nonempty_iff_ne_zero := nonempty_toType_iff
/-
**Ordinal.instNeZeroOne** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instNeZeroOne : NeZero (1 : Ordinal)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.type_ne_zero_of_nonempty`：type_ne_zero_of_nonempty (r) [IsWellOr
der α r] [h : Nonempty α] : type r != 0
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
instance instNeZeroOne : NeZero (1 : Ordinal) :=
  ⟨type_ne_zero_of_nonempty _⟩

@[deprecated _root_.one_ne_zero (since := "2026-05-12")]
/-
**Ordinal.one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：1 ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  _root_.one_ne_zero
/-
**Ordinal.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：nontrivial : Nontrivial Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
instance nontrivial : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, one_ne_zero⟩⟩

/-- `Quotient.inductionOn` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
/-
**Ordinal.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：inductionOn {motive : Ordinal -> Prop} (o : Ordinal) (type : forall (α r) 
[IsWellOrder α r], motive (type r)) : motive o
参数：o : Ordinal；type : forall (α r) [IsWellOrder α r], motive (type r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
`Quotient.inductionOn` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`.
-/
theorem inductionOn {motive : Ordinal → Prop} (o : Ordinal)
    (type : ∀ (α r) [IsWellOrder α r], motive (type r)) : motive o :=
  Quot.inductionOn o fun ⟨α, r, _⟩ ↦ type α r

/-- `Quotient.inductionOn₂` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
/-
**Ordinal.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：inductionOn {motive : Ordinal -> Prop} (o : Ordinal) (type : forall (α r) 
[IsWellOrder α r], motive (type r)) : motive o
参数：o : Ordinal；type : forall (α r) [IsWellOrder α r], motive (type r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
`Quotient.inductionOn₂` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`.
-/
theorem inductionOn₂ {motive : Ordinal → Ordinal → Prop} (o₁ o₂ : Ordinal)
    (type : ∀ (α r) [IsWellOrder α r] (β s) [IsWellOrder β s], motive (type r) (type s)) :
    motive o₁ o₂ :=
  Quotient.inductionOn₂ o₁ o₂ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ↦ type α r β s

/-- `Quotient.inductionOn₃` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`. -/
@[elab_as_elim]
/-
**Ordinal.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：inductionOn {motive : Ordinal -> Prop} (o : Ordinal) (type : forall (α r) 
[IsWellOrder α r], motive (type r)) : motive o
参数：o : Ordinal；type : forall (α r) [IsWellOrder α r], motive (type r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q

--- 原说明 ---
`Quotient.inductionOn₃` specialized to ordinals.

Not to be confused with well-founded induction `WellFoundedLT.induction`.
-/
theorem inductionOn₃ {motive : Ordinal → Ordinal → Ordinal → Prop} (o₁ o₂ o₃ : Ordinal)
    (type : ∀ (α r) [IsWellOrder α r] (β s) [IsWellOrder β s] (γ t) [IsWellOrder γ t],
      motive (type r) (type s) (type t)) : motive o₁ o₂ o₃ :=
  Quotient.inductionOn₃ o₁ o₂ o₃ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ↦ type α r β s γ t

open scoped Classical in
/-- To prove a result on ordinals, it suffices to prove it for order types of well-orders. -/
@[elab_as_elim]
/-
**Ordinal.inductionOnWellOrder** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：inductionOnWellOrder {motive : Ordinal -> Prop} (o : Ordinal) (type : fora
ll (α) [LinearOrder α] [WellFoundedLT α], motive (typeLT α)) : motive o
参数：o : Ordinal；type : forall (α) [LinearOrder α] [WellFoundedLT α], motive (type
LT α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r

--- 原说明 ---
To prove a result on ordinals, it suffices to prove it for order types of well-o
rders.
-/
theorem inductionOnWellOrder {motive : Ordinal → Prop} (o : Ordinal)
    (type : ∀ (α) [LinearOrder α] [WellFoundedLT α], motive (typeLT α)) : motive o :=
  inductionOn o fun α r wo ↦ @type α (linearOrderOfSTO r) wo.toIsWellFounded

open scoped Classical in
/-- To define a function on ordinals, it suffices to define them on order types of well-orders.

Since `LinearOrder` is data-carrying, `liftOnWellOrder_type` is not a definitional equality, unlike
`Quotient.liftOn_mk` which is always def-eq. -/
/-
**Ordinal.liftOnWellOrder** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：liftOnWellOrder {δ : Sort v} (o : Ordinal) (f : forall (α) [LinearOrder α]
 [WellFoundedLT α], δ) (c : forall (α) [LinearOrder α] [WellFoundedLT α] (β) [Li
nearOrder β] [WellFoundedLT β], typeLT α = typeLT β -> f α = f β) : δ
参数：o : Ordinal；f : forall (α) [LinearOrder α] [WellFoundedLT α], δ；c : forall (α
) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β], typeL
T α = typeLT β -> f α = f β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To define a function on ordinals, it suffices to define them on order types of w
ell-orders.

Since `LinearOrder` is data-carrying, `liftOnWellOrder_type` is not a definition
al equality, unlike
`Quotient.liftOn_mk` which is always def-eq.
-/
def liftOnWellOrder {δ : Sort v} (o : Ordinal) (f : ∀ (α) [LinearOrder α] [WellFoundedLT α], δ)
    (c : ∀ (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β],
      typeLT α = typeLT β → f α = f β) : δ :=
  Quotient.liftOn o (fun w ↦ @f w.α (linearOrderOfSTO w.r) w.wo.toIsWellFounded)
    fun w₁ w₂ h ↦ @c
      w₁.α (linearOrderOfSTO w₁.r) w₁.wo.toIsWellFounded
      w₂.α (linearOrderOfSTO w₂.r) w₂.wo.toIsWellFounded
      (Quotient.sound h)

@[simp]
/-
**Ordinal.liftOnWellOrder_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：liftOnWellOrder_type {δ : Sort v} (f : forall (α) [LinearOrder α] [WellFou
ndedLT α], δ) (c : forall (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder
 β] [WellFoundedLT β], typeLT α = typeLT β -> f α = f β) {γ} [LinearOrder γ] [We
llFoundedLT γ] : liftOnWellOrder (typeLT γ) f c = f γ
参数：f : forall (α) [LinearOrder α] [WellFoundedLT α], δ；c : forall (α) [LinearOrd
er α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β], typeLT α = typeLT
 β -> f α = f β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.liftOn'_mk`：∀ {α : Sort u_1} {β : Sort u_2} {s : Setoid α} (x :
 α) (f : α → β) (h : ∀ (a b : α), s a b → f a = f b),   ⟦x⟧.liftOn' f h = f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `LinearOrder.ext_lt`：LinearOrder.ext_lt {A B : LinearOrder α} (H : forall
 x y : α, (haveI
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftOnWellOrder_type {δ : Sort v} (f : ∀ (α) [LinearOrder α] [WellFoundedLT α], δ)
    (c : ∀ (α) [LinearOrder α] [WellFoundedLT α] (β) [LinearOrder β] [WellFoundedLT β],
      typeLT α = typeLT β → f α = f β) {γ} [LinearOrder γ] [WellFoundedLT γ] :
    liftOnWellOrder (typeLT γ) f c = f γ := by
  change Quotient.liftOn' ⟦_⟧ _ _ = _
  rw [Quotient.liftOn'_mk]
  congr
  exact LinearOrder.ext_lt fun _ _ ↦ Iff.rfl

/-! ### The order on ordinals -/

/--
For `Ordinal`:

* less-equal is defined such that well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an *initial* segment of `s`.
* less-than is defined such that well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a *principal* segment of `s`.

Note that most of the relevant results on initial and principal segments are proved in the
`Mathlib/Order/InitialSeg.lean` file.
-/
/-
**Ordinal.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：partialOrder : PartialOrder Ordinal where le a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `Ordinal`:

* less-equal is defined such that well orders `r` and `s` satisfy `type r ≤ type
 s` if there exists
  a function embedding `r` as an *initial* segment of `s`.
* less-than is defined such that well orders `r` and `s` satisfy `type r < type 
s` if there exists
  a function embedding `r` as a *principal* segment of `s`.

Note that most of the relevant results on initial and principal segments are pro
ved in the
`Mathlib/Order/InitialSeg.lean` file.
-/
instance partialOrder : PartialOrder Ordinal where
  le a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≼i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
        ⟨fun ⟨h⟩ => ⟨f.symm.toInitialSeg.trans <| h.trans g.toInitialSeg⟩, fun ⟨h⟩ =>
          ⟨f.toInitialSeg.trans <| h.trans g.symm.toInitialSeg⟩⟩
  lt a b :=
    Quotient.liftOn₂ a b (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => Nonempty (r ≺i s))
      fun _ _ _ _ ⟨f⟩ ⟨g⟩ => propext
        ⟨fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f.symm <| h.transRelIso g⟩,
          fun ⟨h⟩ => ⟨PrincipalSeg.relIsoTrans f <| h.transRelIso g.symm⟩⟩
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
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder Ordinal :=
  { (inferInstance : PartialOrder Ordinal) with
    le_total := fun a b => Quotient.inductionOn₂ a b fun ⟨_, r, _⟩ ⟨_, s, _⟩ =>
      (InitialSeg.total r s).recOn (fun f => Or.inl ⟨f⟩) fun f => Or.inr ⟨f⟩
    toDecidableLE := Classical.decRel _ }
/-
**Ordinal._root_.InitialSeg.ordinal_type_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.InitialSeg.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≼i s) : type r ≤ type s :=
  ⟨h⟩
/-
**Ordinal._root_.RelEmbedding.ordinal_type_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RelEmbedding.ordinal_type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ↪r s) : type r ≤ type s :=
  ⟨h.collapse⟩
/-
**Ordinal._root_.PrincipalSeg.ordinal_type_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.PrincipalSeg.ordinal_type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (h : r ≺i s) : type r < type s :=
  ⟨h⟩
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot Ordinal where
  bot := 0
  bot_le o := inductionOn o fun _ r _ ↦ (InitialSeg.ofIsEmpty _ r).ordinal_type_le

@[simp]
/-
**Ordinal.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：bot_eq_zero : (⊥ : Ordinal) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl
/-
**Ordinal.type_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_le_iff {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α
 r] [IsWellOrder β s] : type r <= type s ↔ Nonempty (r ≼i s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem type_le_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl
/-
**Ordinal.type_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_le_iff' {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder 
α r] [IsWellOrder β s] : type r <= type s ↔ Nonempty (r ↪r s)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem type_le_iff' {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r ≤ type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩
/-
**Ordinal.type_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lt_iff {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α
 r] [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] : type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl
/-
**Ordinal.type_set_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_set_le [LinearOrder α] [WellFoundedLT α] (s : Set α) : typeLT s <= ty
peLT α
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.type_le_iff'`：type_le_iff' {α β} {r : α -> α -> Prop} {s : β -> 
β -> Prop} [IsWellOrder α r] [IsWellOrder β s] : type r <= type s ↔ Nonempty (r 
↪r s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem type_set_le [LinearOrder α] [WellFoundedLT α] (s : Set α) : typeLT s ≤ typeLT α := by
  rw [type_le_iff']
  refine ⟨⟨Embedding.subtype _, ?_⟩⟩
  simp
/-
**Ordinal.type_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_mono [LinearOrder α] [WellFoundedLT α] {s t : Set α} (h : s subseteq 
t) : typeLT s <= typeLT t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.type_le_iff'`：type_le_iff' {α β} {r : α -> α -> Prop} {s : β -> 
β -> Prop} [IsWellOrder α r] [IsWellOrder β s] : type r <= type s ↔ Nonempty (r 
↪r s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem type_mono [LinearOrder α] [WellFoundedLT α] {s t : Set α} (h : s ⊆ t) :
    typeLT s ≤ typeLT t := by
  rw [type_le_iff']
  refine ⟨⟨embeddingOfSubset _ _ h, ?_⟩⟩
  aesop

/-- Given two ordinals `α ≤ β`, then `initialSegToType α β` is the initial segment embedding of
`α.ToType` into `β.ToType`. -/
@[deprecated type_le_iff (since := "2026-04-12")]
/-
**Ordinal.initialSegToType** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：initialSegToType {α β : Ordinal} (h : α <= β) : α.ToType <=i β.ToType
参数：h : α <= β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two ordinals `α ≤ β`, then `initialSegToType α β` is the initial segment e
mbedding of
`α.ToType` into `β.ToType`.
-/
def initialSegToType {α β : Ordinal} (h : α ≤ β) : α.ToType ≤i β.ToType := by
  apply Classical.choice (type_le_iff.mp _)
  rwa [type_toType, type_toType]

/-- Given two ordinals `α < β`, then `principalSegToType α β` is the principal segment embedding
of `α.ToType` into `β.ToType`. -/
@[deprecated type_lt_iff (since := "2026-04-12")]
/-
**Ordinal.principalSegToType** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：principalSegToType {α β : Ordinal} (h : α < β) : α.ToType <i β.ToType
参数：h : α < β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two ordinals `α < β`, then `principalSegToType α β` is the principal segme
nt embedding
of `α.ToType` into `β.ToType`.
-/
def principalSegToType {α β : Ordinal} (h : α < β) : α.ToType <i β.ToType := by
  apply Classical.choice (type_lt_iff.mp _)
  rwa [type_toType, type_toType]

/-! ### Enumerating elements in a well-order with ordinals -/

/-- The order type of an element inside a well order.

This is registered as a principal segment embedding into the ordinals, with top `type r`. -/
/-
**Ordinal.typein** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：typein (r : α -> α -> Prop) [IsWellOrder α r] : @PrincipalSeg α Ordinal.{u
} r (· < ·)
参数：r : α -> α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r

--- 原说明 ---
The order type of an element inside a well order.

This is registered as a principal segment embedding into the ordinals, with top 
`type r`.
-/
def typein (r : α → α → Prop) [IsWellOrder α r] : @PrincipalSeg α Ordinal.{u} r (· < ·) := by
  refine ⟨RelEmbedding.ofMonotone _ fun a b ha ↦
    ((PrincipalSeg.ofElement r a).codRestrict _ ?_ ?_).ordinal_type_lt, type r, fun a ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc⟩
    exact trans hc ha
  · exact ha
  · rintro ⟨b, rfl⟩
    exact (PrincipalSeg.ofElement _ _).ordinal_type_lt
  · refine inductionOn a ?_
    rintro β s wo ⟨g⟩
    exact ⟨_, g.subrelIso.ordinalType_congr⟩

@[simp]
/-
**Ordinal.type_subrel** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_subrel (r : α -> α -> Prop) [IsWellOrder α r] (a : α) : type (Subrel 
r (r · a)) = typein r a
参数：r : α -> α -> Prop；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrel.instIsWellOrderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsWe
llOrder α r] (p : α → Prop), IsWellOrder (Subtype p) (Subrel r p)
-/
theorem type_subrel (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    type (Subrel r (r · a)) = typein r a :=
  rfl

@[simp]
/-
**Ordinal.top_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：top_typein (r : α -> α -> Prop) [IsWellOrder α r] : (typein r).top = type 
r
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_typein (r : α → α → Prop) [IsWellOrder α r] : (typein r).top = type r :=
  rfl
/-
**Ordinal.typein_lt_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_lt_type (r : α -> α -> Prop) [IsWellOrder α r] (a : α) : typein r a
 < type r
参数：r : α -> α -> Prop；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.lt_top`：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
-/
theorem typein_lt_type (r : α → α → Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  (typein r).lt_top a
/-
**Ordinal.typein_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_lt_self {o : Ordinal} (i : o.ToType) : typein (α
参数：i : o.ToType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
-/
theorem typein_lt_self {o : Ordinal} (i : o.ToType) : typein (α := o.ToType) (· < ·) i < o := by
  simp_rw [← type_toType o]
  apply typein_lt_type

@[simp]
/-
**Ordinal.typein_top** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_top {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α 
r] [IsWellOrder β s] (f : r ≺i s) : typein s f.top = type r
参数：f : r ≺i s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ordinalType_congr`：∀ {α β : Type u_1} {r : α → α → Prop} {s : β →
 β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ≃r s), O
rdinal.type r …
· 使用定理 `Subrel.instIsWellOrderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsWe
llOrder α r] (p : α → Prop), IsWellOrder (Subtype p) (Subrel r p)
-/
theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : typein s f.top = type r :=
  f.subrelIso.ordinalType_congr

@[simp]
/-
**Ordinal.typein_lt_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_lt_typein (r : α -> α -> Prop) [IsWellOrder α r] {a b : α} : typein
 r a < typein r b ↔ r a b
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem typein_lt_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} :
    typein r a < typein r b ↔ r a b :=
  (typein r).map_rel_iff

@[simp]
/-
**Ordinal.typein_le_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_le_typein (r : α -> α -> Prop) [IsWellOrder α r] {a b : α} : typein
 r a <= typein r b ↔ ¬r b a
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Ordinal.typein_lt_typein`：typein_lt_typein (r : α -> α -> Prop) [IsWellO
rder α r] {a b : α} : typein r a < typein r b ↔ r a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem typein_le_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} :
    typein r a ≤ typein r b ↔ ¬r b a := by
  rw [← not_lt, typein_lt_typein]
/-
**Ordinal.typein_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_injective (r : α -> α -> Prop) [IsWellOrder α r] : Injective (typei
n r)
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem typein_injective (r : α → α → Prop) [IsWellOrder α r] : Injective (typein r) :=
  (typein r).injective
/-
**Ordinal.typein_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_inj (r : α -> α -> Prop) [IsWellOrder α r] {a b} : typein r a = typ
ein r b ↔ a = b
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ordinal.typein_injective`：typein_injective (r : α -> α -> Prop) [IsWellO
rder α r] : Injective (typein r)
-/
theorem typein_inj (r : α → α → Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff
/-
**Ordinal.mem_range_typein_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_typein_iff (r : α -> α -> Prop) [IsWellOrder α r] {o} : o in Set
.range (typein r) ↔ o < type r
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_iff_rel`：mem_range_iff_rel (f : r ≺i s) : forall 
{b : β}, b in Set.range f ↔ s b f.top
-/
theorem mem_range_typein_iff (r : α → α → Prop) [IsWellOrder α r] {o} :
    o ∈ Set.range (typein r) ↔ o < type r :=
  (typein r).mem_range_iff_rel
/-
**Ordinal.typein_surj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_surj (r : α -> α -> Prop) [IsWellOrder α r] {o} (h : o < type r) : 
o in Set.range (typein r)
参数：r : α -> α -> Prop；h : o < type r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_of_rel_top`：mem_range_of_rel_top (f : r ≺i s) {b 
: β} (h : s b f.top) : b in Set.range f
-/
theorem typein_surj (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    o ∈ Set.range (typein r) :=
  (typein r).mem_range_of_rel_top h
/-
**Ordinal.typein_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_surjOn (r : α -> α -> Prop) [IsWellOrder α r] : Set.SurjOn (typein 
r) Set.univ (Set.Iio (type r))
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.surjOn`：surjOn (f : r ≺i s) : Set.SurjOn f Set.univ { b | s
 b f.top }
-/
theorem typein_surjOn (r : α → α → Prop) [IsWellOrder α r] :
    Set.SurjOn (typein r) Set.univ (Set.Iio (type r)) :=
  (typein r).surjOn

@[simp]
/-
**Ordinal.type_Iio_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : α) : type (α
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
theorem type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : α) :
    type (α := Iio x) LT.lt = typein LT.lt x :=
  rfl

/-- A well order `r` is order-isomorphic to the set of ordinals smaller than `type r`.
`enum r ⟨o, h⟩` is the `o`-th element of `α` ordered by `r`.

That is, `enum` maps an initial segment of the ordinals, those less than the order type of `r`, to
the elements of `α`. -/
@[simps! symm_apply_coe]
/-
**Ordinal.enum** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：enum (r : α -> α -> Prop) [IsWellOrder α r] : (· < · : Iio (type r) -> Iio
 (type r) -> Prop) ≃r r
参数：r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A well order `r` is order-isomorphic to the set of ordinals smaller than `type r
`.
`enum r ⟨o, h⟩` is the `o`-th element of `α` ordered by `r`.

That is, `enum` maps an initial segment of the ordinals, those less than the ord
er type of `r`, to
the elements of `α`.
-/
def enum (r : α → α → Prop) [IsWellOrder α r] : (· < · : Iio (type r) → Iio (type r) → Prop) ≃r r :=
  (typein r).subrelIso

@[simp]
/-
**Ordinal.typein_enum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] {o} (h : o < type r) : 
typein r (enum r ⟨o, h⟩) = o
参数：r : α -> α -> Prop；h : o < type r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.apply_subrelIso`：apply_subrelIso (f : r ≺i s) (b : {b // s 
b f.top}) : f (f.subrelIso b) = b
-/
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) :
    typein r (enum r ⟨o, h⟩) = o :=
  (typein r).apply_subrelIso _
/-
**Ordinal.enum_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_type {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r
] [IsWellOrder β s] (f : s ≺i r) {h : type s < type r} : enum r ⟨type s, h⟩ = f.
top
参数：f : s ≺i r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.typein_top`：typein_top {α β} {r : α -> α -> Prop} {s : β -> β ->
 Prop} [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : typein s f.top = type 
r
-/
theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : s ≺i r) {h : type s < type r} : enum r ⟨type s, h⟩ = f.top :=
  (typein r).injective <| (typein_enum _ _).trans (typein_top _).symm

@[simp]
/-
**Ordinal.enum_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] (a : α) : enum r ⟨typei
n r a, typein_lt_type r a⟩ = a
参数：r : α -> α -> Prop；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enum_type`：enum_type {α β} {r : α -> α -> Prop} {s : β -> β -> P
rop} [IsWellOrder α r] [IsWellOrder β s] (f : s ≺i r) {h : type s < type r} : en
um r ⟨t…
· 使用定理 `Subrel.instIsWellOrderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsWe
llOrder α r] (p : α → Prop), IsWellOrder (Subtype p) (Subrel r p)
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
-/
theorem enum_typein (r : α → α → Prop) [IsWellOrder α r] (a : α) :
    enum r ⟨typein r a, typein_lt_type r a⟩ = a :=
  enum_type (PrincipalSeg.ofElement r a)
/-
**Ordinal.enum_lt_enum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_lt_enum {r : α -> α -> Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
 : r (enum r o₁) (enum r o₂) ↔ o₁ < o₂
参数：type r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
theorem enum_lt_enum {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    r (enum r o₁) (enum r o₂) ↔ o₁ < o₂ :=
  (enum _).map_rel_iff
/-
**Ordinal.enum_le_enum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_le_enum (r : α -> α -> Prop) [IsWellOrder α r] {o₁ o₂ : Iio (type r)}
 : ¬r (enum r o₁) (enum r o₂) ↔ o₂ <= o₁
参数：r : α -> α -> Prop；type r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.enum_lt_enum`：enum_lt_enum {r : α -> α -> Prop} [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : r (enum r o₁) (enum r o₂) ↔ o₁ < o₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem enum_le_enum (r : α → α → Prop) [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    ¬r (enum r o₁) (enum r o₂) ↔ o₂ ≤ o₁ := by
  rw [enum_lt_enum (r := r), not_lt]

-- TODO: generalize to other well-orders
@[simp]
/-
**Ordinal.enum_le_enum'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_le_enum' (a : Ordinal) {o₁ o₂ : Iio (type (· < ·))} : enum (· < ·) o₁
 <= enum (α
参数：a : Ordinal；type (· < ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.enum_le_enum`：enum_le_enum (r : α -> α -> Prop) [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : ¬r (enum r o₁) (enum r o₂) ↔ o₂ <= o₁
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem enum_le_enum' (a : Ordinal) {o₁ o₂ : Iio (type (· < ·))} :
    enum (· < ·) o₁ ≤ enum (α := a.ToType) (· < ·) o₂ ↔ o₁ ≤ o₂ := by
  rw [← enum_le_enum, not_lt]
/-
**Ordinal.enum_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_inj {r : α -> α -> Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} : e
num r o₁ = enum r o₂ ↔ o₁ = o₂
参数：type r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
theorem enum_inj {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Iio (type r)} :
    enum r o₁ = enum r o₂ ↔ o₁ = o₂ :=
  EmbeddingLike.apply_eq_iff_eq _
/-
**Ordinal.enum_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_zero_le {r : α -> α -> Prop} [IsWellOrder α r] (h0 : 0 < type r) (a :
 α) : ¬r a (enum r ⟨0, h0⟩)
参数：h0 : 0 < type r；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `Ordinal.enum_le_enum`：enum_le_enum (r : α -> α -> Prop) [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : ¬r (enum r o₁) (enum r o₂) ↔ o₂ <= o₁
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem enum_zero_le {r : α → α → Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) :
    ¬r a (enum r ⟨0, h0⟩) := by
  rw [← enum_typein r a, enum_le_enum r]
  exact bot_le (α := Ordinal)
/-
**Ordinal.enum_zero_le'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.ToType) : enum (α
参数：h0 : 0 < o；a : o.ToType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Ordinal.enum_zero_le`：enum_zero_le {r : α -> α -> Prop} [IsWellOrder α r
] (h0 : 0 < type r) (a : α) : ¬r a (enum r ⟨0, h0⟩)
-/
theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.ToType) :
    enum (α := o.ToType) (· < ·) ⟨0, type_toType _ ▸ h0⟩ ≤ a := by
  rw [← not_lt]
  apply enum_zero_le

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.relIso_enum'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：relIso_enum' {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsW
ellOrder α r] [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) : forall (hr : o < ty
pe r) (hs : o < type s), f (enum r ⟨o, hr⟩) = enum s ⟨o, hs⟩
参数：f : r ≃r s；o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.enum_type`：enum_type {α β} {r : α -> α -> Prop} {s : β -> β -> P
rop} [IsWellOrder α r] [IsWellOrder β s] (f : s ≺i r) {h : type s < type r} : en
um r ⟨t…
-/
theorem relIso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) :
    ∀ (hr : o < type r) (hs : o < type s), f (enum r ⟨o, hr⟩) = enum s ⟨o, hs⟩ := by
  refine inductionOn o ?_; rintro γ t wo ⟨g⟩ ⟨h⟩
  rw [enum_type g, enum_type (g.transRelIso f)]; rfl
/-
**Ordinal.relIso_enum** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：relIso_enum {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWe
llOrder α r] [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) : f 
(enum r ⟨o, hr⟩) = enum s ⟨o, hr.trans_eq (Quotient.sound ⟨f⟩)⟩
参数：f : r ≃r s；o : Ordinal；hr : o < type r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.relIso_enum'`：relIso_enum' {α β : Type u} {r : α -> α -> Prop} {
s : β -> β -> Prop} [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) (o : Ordina
l) : foral…
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem relIso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r]
    [IsWellOrder β s] (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r ⟨o, hr⟩) = enum s ⟨o, hr.trans_eq (Quotient.sound ⟨f⟩)⟩ :=
  relIso_enum' _ _ _ _

/-- The order isomorphism between ordinals less than `o` and `o.ToType`. -/
@[simps! -isSimp]
/-
**Ordinal.ToType.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal.ToType`。
形式化陈述：{o : Ordinal.{u_1}} → ↑(Set.Iio o) ≃o o.ToType
参数：Set.Iio o。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.typein_lt_self`：typein_lt_self {o : Ordinal} (i : o.ToType) : ty
pein (α

--- 原说明 ---
The order isomorphism between ordinals less than `o` and `o.ToType`.
-/
def ToType.mk {o : Ordinal} : Set.Iio o ≃o o.ToType where
  toFun x := enum (α := o.ToType) (· < ·) ⟨x.1, type_toType _ ▸ x.2⟩
  invFun x := ⟨typein (α := o.ToType) (· < ·) x, typein_lt_self x⟩
  left_inv _ := Subtype.ext (typein_enum _ _)
  right_inv _ := enum_typein _ _
  map_rel_iff' := enum_le_enum' _

/-- Convert an element of `α.toType` to the corresponding `Ordinal` -/
/-
**Ordinal.ToType.toOrd** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal.ToType`。
形式化陈述：{o : Ordinal.{u_1}} → o.ToType → ↑(Set.Iio o)
参数：Set.Iio o。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert an element of `α.toType` to the corresponding `Ordinal`
-/
abbrev ToType.toOrd {o : Ordinal} (α : o.ToType) : Set.Iio o := ToType.mk.symm α
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (o : Ordinal) : Coe o.ToType (Set.Iio o) where
  coe := ToType.toOrd
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (o : Ordinal) : CoeOut o.ToType Ordinal where
  coe x := x.toOrd
/-
**Ordinal.small_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：small_Iio (o : Ordinal.{u}) : Small.{u} (Iio o)
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_Iio (o : Ordinal.{u}) : Small.{u} (Iio o) :=
  ⟨_, ⟨ToType.mk.toEquiv⟩⟩
/-
**Ordinal.small_Iic** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：small_Iic (o : Ordinal.{u}) : Small.{u} (Iic o)
参数：o : Ordinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_right`：Iio_union_right : Iio a union {a} = Iic a
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance small_Iic (o : Ordinal.{u}) : Small.{u} (Iic o) := by
  rw [← Iio_union_right]
  infer_instance
/-
**Ordinal.small_Ico** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：small_Ico (a b : Ordinal.{u}) : Small.{u} (Ico a b)
参数：a b : Ordinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
-/
instance small_Ico (a b : Ordinal.{u}) : Small.{u} (Ico a b) := small_subset Ico_subset_Iio_self
/-
**Ordinal.small_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：small_Icc (a b : Ordinal.{u}) : Small.{u} (Icc a b)
参数：a b : Ordinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
-/
instance small_Icc (a b : Ordinal.{u}) : Small.{u} (Icc a b) := small_subset Icc_subset_Iic_self
/-
**Ordinal.small_Ioo** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：small_Ioo (a b : Ordinal.{u}) : Small.{u} (Ioo a b)
参数：a b : Ordinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
-/
instance small_Ioo (a b : Ordinal.{u}) : Small.{u} (Ioo a b) := small_subset Ioo_subset_Iio_self
/-
**Ordinal.small_Ioc** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：small_Ioc (a b : Ordinal.{u}) : Small.{u} (Ioc a b)
参数：a b : Ordinal.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_subset`：small_subset {s t : Set α} (hts : t subseteq s) [Small.{u}
 s] : Small.{u} t
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
-/
instance small_Ioc (a b : Ordinal.{u}) : Small.{u} (Ioc a b) := small_subset Ioc_subset_Iic_self

/-- `o.ToType` is an `OrderBot` whenever `o ≠ 0`. -/
@[instance_reducible, deprecated WellFoundedLT.toOrderBot (since := "2026-04-12")]
/-
**Ordinal.toTypeOrderBot** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：toTypeOrderBot {o : Ordinal} (ho : o != 0) : OrderBot o.ToType where bot
参数：ho : o != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`o.ToType` is an `OrderBot` whenever `o ≠ 0`.
-/
def toTypeOrderBot {o : Ordinal} (ho : o ≠ 0) : OrderBot o.ToType where
  bot := (enum (· < ·)) ⟨0, _⟩
  bot_le := enum_zero_le' (bot_lt_iff_ne_bot.2 ho)

@[deprecated "use `WellFoundedLT.toOrderBot` if you need an `OrderBot` instance"
(since := "2026-04-12")]
/-
**Ordinal.enum_zero_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) : enum (α
参数：ho : 0 < o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (α := o.ToType) (· < ·) ⟨0, by rwa [type_toType]⟩ =
      have H := toTypeOrderBot (o := o) (by rintro rfl; simp at ho)
      (⊥ : o.ToType) :=
  rfl
/-
**Ordinal.lt_wf** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_wf : @WellFounded Ordinal (· < ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `wellFounded_iff_wellFounded_subrel`：wellFounded_iff_wellFounded_subrel {
r : α -> α -> Prop} [IsTrans α r] : WellFounded r ↔ forall b, WellFounded (Subre
l r (r · b)) where mp h …
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `RelHomClass.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r 
s] (f : F), W…
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
-/
theorem lt_wf : @WellFounded Ordinal (· < ·) :=
  wellFounded_iff_wellFounded_subrel.mpr (·.induction_on fun ⟨_, _, wo⟩ ↦
    RelHomClass.wellFounded (enum _) wo.wf)
/-
**Ordinal.wellFoundedRelation** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：wellFoundedRelation : WellFoundedRelation Ordinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lt_wf`：lt_wf : @WellFounded Ordinal (· < ·)
-/
instance wellFoundedRelation : WellFoundedRelation Ordinal :=
  ⟨(· < ·), lt_wf⟩
/-
**Ordinal.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：wellFoundedLT : WellFoundedLT Ordinal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lt_wf`：lt_wf : @WellFounded Ordinal (· < ·)
-/
instance wellFoundedLT : WellFoundedLT Ordinal :=
  ⟨lt_wf⟩
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[deprecated WellFoundedLT.induction (since := "2026-02-27")]
/-
**Ordinal.induction** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：induction {p : Ordinal.{u} -> Prop} (i : Ordinal.{u}) (h : forall j, (fora
ll k, k < j -> p k) -> p j) : p i
参数：i : Ordinal.{u}；h : forall j, (forall k, k < j -> p k) -> p j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
-/
theorem induction {p : Ordinal.{u} → Prop} (i : Ordinal.{u}) (h : ∀ j, (∀ k, k < j → p k) → p j) :
    p i :=
  WellFoundedLT.induction i h
/-
**Ordinal.typein_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_apply {α β} {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder 
α r] [IsWellOrder β s] (f : r ≼i s) (a : α) : typein s (f a) = typein r a
参数：f : r ≼i s；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InitialSeg.transPrincipal_apply`：transPrincipal_apply [IsWellOrder β s] 
[IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) : f.transPrincipal g a = g (f a)
· 使用定理 `PrincipalSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s :
 β → β → Prop} [IsWellOrder β s] (f g : PrincipalSeg r s)   (a : α), f.toRelEmbe
dding…
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≼i s) (a : α) : typein s (f a) = typein r a := by
  rw [← f.transPrincipal_apply _ a, (f.transPrincipal _).eq]

/-! ### Cardinality of ordinals -/

/-- The cardinal of an ordinal is the cardinality of any type on which a relation with that order
type is defined. -/
/-
**Ordinal.card** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：card : Ordinal -> Cardinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinal of an ordinal is the cardinality of any type on which a relation wi
th that order
type is defined.
-/
def card : Ordinal → Cardinal :=
  Quotient.map WellOrder.α fun _ _ ⟨e⟩ => ⟨e.toEquiv⟩

@[simp]
/-
**Ordinal.card_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_type (r : α -> α -> Prop) [IsWellOrder α r] : card (type r) = #α
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_type (r : α → α → Prop) [IsWellOrder α r] : card (type r) = #α :=
  rfl

@[simp]
/-
**Ordinal.card_typein** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_typein {r : α -> α -> Prop} [IsWellOrder α r] (x : α) : (typein r x).
card = #{ y // r y x }
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_typein {r : α → α → Prop} [IsWellOrder α r] (x : α) :
    (typein r x).card = #{ y // r y x } :=
  rfl

@[gcongr]
/-
**Ordinal.card_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card o₁ <= card o₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
-/
theorem card_le_card {o₁ o₂ : Ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  inductionOn o₁ fun _ _ _ => inductionOn o₂ fun _ _ _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

@[simp]
/-
**Ordinal.card_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_zero : card 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
-/
theorem card_zero : card 0 = 0 := mk_eq_zero _

@[simp]
/-
**Ordinal.card_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_one : card 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem card_one : card 1 = 1 := mk_eq_one _

@[simp]
/-
**Ordinal._root_.Cardinal.mk_toType** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.mk_toType (o : Ordinal) : #o.ToType = o.card :=
  (Ordinal.card_type _).symm.trans <| by rw [Ordinal.type_toType]

variable (r) in
/-- The cardinality of a set is an upper-bound for the cardinality of the order type of the set's
mex (minimum excluded value). See `not_lt_enum_ord_mk_min_compl` for the `α` version. -/
/-
**Ordinal.card_typein_min_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_typein_min_le_mk [IsWellOrder α r] {s : Set α} (hs : sᶜ.Nonempty) : (
typein r <| IsWellFounded.wf.min (r
参数：hs : sᶜ.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.cardinalMk_subtype_lt_min_compl_le`：∀ {α : Type u} {r : α → 
α → Prop} (wf : WellFounded r) {s : Set α} (hs : sᶜ.Nonempty),   Cardinal.mk { x
 // r x (wf.min sᶜ hs) } ≤ Cardinal.…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r

--- 原说明 ---
The cardinality of a set is an upper-bound for the cardinality of the order type
 of the set's
mex (minimum excluded value). See `not_lt_enum_ord_mk_min_compl` for the `α` ver
sion.
-/
theorem card_typein_min_le_mk [IsWellOrder α r] {s : Set α} (hs : sᶜ.Nonempty) :
    (typein r <| IsWellFounded.wf.min (r := r) sᶜ hs).card ≤ #s :=
  IsWellFounded.wf.cardinalMk_subtype_lt_min_compl_le hs

/-! ### Lifting ordinals to a higher universe -/

/-- The universe lift operation for ordinals, which embeds `Ordinal.{u}` as
  a proper initial segment of `Ordinal.{v}` for `v > u`. For the initial segment version,
  see `liftInitialSeg`. -/
@[pp_with_univ]
/-
**Ordinal.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：lift (o : Ordinal.{v}) : Ordinal.{max v u}
参数：o : Ordinal.{v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universe lift operation for ordinals, which embeds `Ordinal.{u}` as
  a proper initial segment of `Ordinal.{v}` for `v > u`. For the initial segment
 version,
  see `liftInitialSeg`.
-/
def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  Quotient.liftOn o (fun w => type <| ULift.down ⁻¹'o w.r) fun ⟨_, r, _⟩ ⟨_, s, _⟩ ⟨f⟩ =>
    Quot.sound
      ⟨(RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm⟩

@[simp]
/-
**Ordinal.type_ulift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_ulift (r : α -> α -> Prop) [IsWellOrder α r] : type (ULift.down ⁻¹'o 
r) = lift.{v} (type r)
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.IsWellOrder.ulift`：∀ {α : Type u} (r : α → α → Prop) [IsWellOrder
 α r], IsWellOrder (ULift.{u_5, u} α) (ULift.down ⁻¹'o r)
-/
theorem type_ulift (r : α → α → Prop) [IsWellOrder α r] :
    type (ULift.down ⁻¹'o r) = lift.{v} (type r) :=
  rfl

@[deprecated (since := "2026-02-20")] alias type_uLift := type_ulift

@[simp]
/-
**Ordinal.type_lt_ulift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lt_ulift [LinearOrder α] [WellFoundedLT α] : typeLT (ULift α) = lift.
{v} (typeLT α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTULift`：∀ {α : Type u_1} [inst : LT α] [h : WellFoundedL
T α], WellFoundedLT (ULift.{u_4, u_1} α)
-/
theorem type_lt_ulift [LinearOrder α] [WellFoundedLT α] :
    typeLT (ULift α) = lift.{v} (typeLT α) :=
  rfl
/-
**Ordinal._root_.RelIso.ordinal_lift_type_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RelIso.ordinal_lift_type_eq {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) : lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equiv.ulift r).trans <|
      f.trans (RelIso.preimage Equiv.ulift s).symm).ordinalType_congr

@[simp]
/-
**Ordinal.type_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_preimage {α β : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β
 ≃ α) : type (f ⁻¹'o r) = type r
参数：r : α -> α -> Prop；f : β ≃ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ordinalType_congr`：∀ {α β : Type u_1} {r : α → α → Prop} {s : β →
 β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ≃r s), O
rdinal.type r …
· 使用定理 `RelIso.IsWellOrder.preimage`：∀ {β : Type u_2} {α : Type u} (r : α → α → 
Prop) [IsWellOrder α r] (f : β ≃ α), IsWellOrder β (⇑f ⁻¹'o r)
-/
theorem type_preimage {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinalType_congr

@[simp]
/-
**Ordinal.type_lift_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lift_preimage (r : α -> α -> Prop) [IsWellOrder α r] (f : β ≃ α) : li
ft.{u} (type (f ⁻¹'o r)) = lift.{v} (type r)
参数：r : α -> α -> Prop；f : β ≃ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ordinal_lift_type_eq`：∀ {α : Type u} {β : Type v} {r : α → α → Pr
op} {s : β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (f 
: r ≃r s), Ordina…
· 使用定理 `RelIso.IsWellOrder.preimage`：∀ {β : Type u_2} {α : Type u} (r : α → α → 
Prop) [IsWellOrder α r] (f : β ≃ α), IsWellOrder β (⇑f ⁻¹'o r)
-/
theorem type_lift_preimage (r : α → α → Prop) [IsWellOrder α r]
    (f : β ≃ α) : lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

/-- `lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't seem to work. -/
/-
**Ordinal.lift_umax** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_umax : lift.{max u v, u} = lift.{v, u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧

--- 原说明 ---
`lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't seem to work.
-/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    inductionOn a fun _ r _ =>
      Quotient.sound ⟨(RelIso.preimage Equiv.ulift r).trans (RelIso.preimage Equiv.ulift r).symm⟩

/-- An ordinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work. -/
/-
**Ordinal.lift_id'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_id' (a : Ordinal) : lift a = a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧

--- 原说明 ---
An ordinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work.
-/
theorem lift_id' (a : Ordinal) : lift a = a :=
  inductionOn a fun _ r _ => Quotient.sound ⟨RelIso.preimage Equiv.ulift r⟩

/-- An ordinal lifted to the same universe equals itself. -/
@[simp]
/-
**Ordinal.lift_id** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_id : forall a, lift.{u, u} a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a

--- 原说明 ---
An ordinal lifted to the same universe equals itself.
-/
theorem lift_id : ∀ a, lift.{u, u} a = a :=
  lift_id'.{u, u}

/-- An ordinal lifted to the zero universe equals itself. -/
@[simp]
/-
**Ordinal.lift_uzero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_uzero (a : Ordinal.{u}) : lift.{0} a = a
参数：a : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a

--- 原说明 ---
An ordinal lifted to the zero universe equals itself.
-/
theorem lift_uzero (a : Ordinal.{u}) : lift.{0} a = a :=
  lift_id' a
/-
**Ordinal.lift_type_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrde
r β s] : lift.{max v w} (type r) <= lift.{max u w} (type s) ↔ Nonempty (r ≼i s)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ Nonempty (r ≼i s) := by
  constructor <;> refine fun ⟨f⟩ ↦ ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).toInitialSeg)
  · exact (RelIso.preimage Equiv.ulift r).toInitialSeg.trans
      (f.trans (RelIso.preimage Equiv.ulift s).symm.toInitialSeg)
/-
**Ordinal.lift_type_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrde
r β s] : lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
-/
theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) := by
  refine Quotient.eq'.trans ⟨?_, ?_⟩ <;> refine fun ⟨f⟩ ↦ ⟨?_⟩
  · exact (RelIso.preimage Equiv.ulift r).symm.trans <| f.trans (RelIso.preimage Equiv.ulift s)
  · exact (RelIso.preimage Equiv.ulift r).trans <| f.trans (RelIso.preimage Equiv.ulift s).symm
/-
**Ordinal.lift_type_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrde
r β s] : lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s) := by
  constructor <;> refine fun ⟨f⟩ ↦ ⟨?_⟩
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r).symm).transInitial
      (RelIso.preimage Equiv.ulift s).toInitialSeg
  · exact (f.relIsoTrans (RelIso.preimage Equiv.ulift r)).transInitial
      (RelIso.preimage Equiv.ulift s).symm.toInitialSeg

@[simp]
/-
**Ordinal.lift_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_le {a b : Ordinal} : lift.{u, v} a <= lift.{u, v} b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₂`：inductionOn₂ {motive : Ordinal -> Ordinal -> Prop}
 (o₁ o₂ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s
], motive …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Ordinal.lift_type_le`：lift_type_le {α : Type u} {β : Type v} {r s} [IsWe
llOrder α r] [IsWellOrder β s] : lift.{max v w} (type r) <= lift.{max u w} (type
 s) ↔ None…
-/
theorem lift_le {a b : Ordinal} : lift.{u, v} a ≤ lift.{u, v} b ↔ a ≤ b :=
  inductionOn₂ a b fun α r _ β s _ => by
    rw [← lift_umax]
    exact lift_type_le.{_, _, u}

@[simp]
/-
**Ordinal.lift_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v} b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_inj {a b : Ordinal} : lift.{u, v} a = lift.{u, v} b ↔ a = b := by
  simp_rw [le_antisymm_iff, lift_le]

@[simp]
/-
**Ordinal.lift_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b ↔ a < b := by
  simp_rw [lt_iff_le_not_ge, lift_le]

@[simp]
/-
**Ordinal.lift_typein_top** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_typein_top {r : α -> α -> Prop} {s : β -> β -> Prop} [IsWellOrder α r
] [IsWellOrder β s] (f : r ≺i s) : lift.{u} (typein s f.top) = lift (type r)
参数：f : r ≺i s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ordinal_lift_type_eq`：∀ {α : Type u} {β : Type v} {r : α → α → Pr
op} {s : β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (f 
: r ≃r s), Ordina…
· 使用定理 `Subrel.instIsWellOrderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsWe
llOrder α r] (p : α → Prop), IsWellOrder (Subtype p) (Subrel r p)
-/
theorem lift_typein_top {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) : lift.{u} (typein s f.top) = lift (type r) :=
  f.subrelIso.ordinal_lift_type_eq

@[simp]
/-
**Ordinal.typein_ordinal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_ordinal (o : Ordinal.{u}) : typein LT.lt o = lift.{u + 1} o
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `RelIso.ordinal_lift_type_eq`：∀ {α : Type u} {β : Type v} {r : α → α → Pr
op} {s : β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (f 
: r ≃r s), Ordina…
· 使用定理 `Ordinal.lift_id'`：lift_id' (a : Ordinal) : lift a = a
· 使用定理 `Ordinal.type_Iio_lt`：type_Iio_lt [LinearOrder α] [WellFoundedLT α] (x : 
α) : type (α
-/
theorem typein_ordinal (o : Ordinal.{u}) : typein LT.lt o = lift.{u + 1} o := by
  nth_rw 2 [← o.type_toType]
  rw [← ToType.mk.toRelIsoLT.ordinal_lift_type_eq, lift_id'.{u, u + 1}, type_Iio_lt]
/-
**Ordinal.type_lt_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lt_Iio (o : Ordinal.{u}) : typeLT (Iio o) = lift.{u + 1} o
参数：o : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.typein_ordinal`：typein_ordinal (o : Ordinal.{u}) : typein LT.lt 
o = lift.{u + 1} o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem type_lt_Iio (o : Ordinal.{u}) : typeLT (Iio o) = lift.{u + 1} o := by simp

/-- Initial segment version of the lift operation on ordinals, embedding `Ordinal.{u}` in
`Ordinal.{v}` as an initial segment when `u ≤ v`. -/
/-
**Ordinal.liftInitialSeg** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：liftInitialSeg : Ordinal.{v} <=i Ordinal.{max u v}
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Initial segment version of the lift operation on ordinals, embedding `Ordinal.{u
}` in
`Ordinal.{v}` as an initial segment when `u ≤ v`.
-/
def liftInitialSeg : Ordinal.{v} ≤i Ordinal.{max u v} := by
  refine ⟨RelEmbedding.ofMonotone lift.{u} (by simp),
    fun a b ↦ Ordinal.inductionOn₂ a b fun α r _ β s _ h ↦ ?_⟩
  rw [RelEmbedding.ofMonotone_coe, ← lift_id'.{max u v} (type s),
    ← lift_umax.{v, u}, lift_type_lt] at h
  obtain ⟨f⟩ := h
  use typein r f.top
  rw [RelEmbedding.ofMonotone_coe, ← lift_umax, lift_typein_top, lift_id']

@[simp]
/-
**Ordinal.liftInitialSeg_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：liftInitialSeg_coe : (liftInitialSeg.{v, u} : Ordinal -> Ordinal) = lift.{
v, u}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftInitialSeg_coe : (liftInitialSeg.{v, u} : Ordinal → Ordinal) = lift.{v, u} :=
  rfl

@[simp]
/-
**Ordinal.lift_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) = lift.{max v w} a
参数：a : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β
 → β → Prop} [IsWellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
theorem lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  (liftInitialSeg.trans liftInitialSeg).eq liftInitialSeg a

@[simp]
/-
**Ordinal.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_zero : lift 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.type_eq_zero_of_empty`：type_eq_zero_of_empty (r) [IsWellOrder α 
r] [IsEmpty α] : type r = 0
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPEmpty`：Subsingleton PEmpty.{u_1}
· 使用定理 `ULift.instIsEmpty`：∀ {α : Type u} [IsEmpty α], IsEmpty (ULift.{u_1, u} α
)
-/
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _

@[simp]
/-
**Ordinal.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_one : lift 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.type_eq_one_of_unique`：type_eq_one_of_unique (r) [IsWellOrder α 
r] [Nonempty α] [Subsingleton α] : type r = 1
· 使用定理 `instIsWellOrderEmptyRelationOfSubsingleton`：∀ {α : Type u} [Subsingleton
 α], IsWellOrder α emptyRelation
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `ULift.instNonempty_mathlib`：∀ {α : Type u} [Nonempty α], Nonempty (ULift
.{u_1, u} α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instSubsingletonULift`：∀ {α : Type u_1} [Subsingleton α], Subsingleton (
ULift.{u_2, u_1} α)
-/
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _

@[simp]
/-
**Ordinal.lift_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_card (a) : Cardinal.lift.{u, v} (card a) = card (lift.{u} a)
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
-/
theorem lift_card (a) : Cardinal.lift.{u, v} (card a) = card (lift.{u} a) :=
  inductionOn a fun _ _ _ => rfl
/-
**Ordinal.mem_range_lift_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_lift_of_le {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b <= l
ift.{v} a) : b in Set.range lift.{v}
参数：h : b <= lift.{v} a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_le`：mem_range_of_le [LT α] (f : α <=i β) (h : b 
<= f a) : b in Set.range f
-/
theorem mem_range_lift_of_le {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b ≤ lift.{v} a) :
    b ∈ Set.range lift.{v} :=
  liftInitialSeg.mem_range_of_le h
/-
**Ordinal.le_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} : b <= lift.{v} a ↔ 
exists a' <= a, lift.{v} a' = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.le_apply_iff`：le_apply_iff [PartialOrder α] (f : α <=i β) : b
 <= f a ↔ exists c <= a, f c = b
-/
theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b ≤ lift.{v} a ↔ ∃ a' ≤ a, lift.{v} a' = b :=
  liftInitialSeg.le_apply_iff
/-
**Ordinal.lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} : b < lift.{v} a ↔ e
xists a' < a, lift.{v} a' = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.lt_apply_iff`：lt_apply_iff [PartialOrder α] (f : α <=i β) : b
 < f a ↔ exists a' < a, f a' = b
-/
theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} :
    b < lift.{v} a ↔ ∃ a' < a, lift.{v} a' = b :=
  liftInitialSeg.lt_apply_iff

@[simp]
/-
**Ordinal._root_.Cardinal.mk_Iio_ordinal** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.mk_Iio_ordinal (o : Ordinal.{u}) :
    #(Iio o) = Cardinal.lift.{u + 1} o.card := by
  rw [lift_card, ← typein_ordinal]
  rfl

@[deprecated (since := "2026-03-13")] alias mk_Iio_ordinal := Cardinal.mk_Iio_ordinal

/-! ### The first infinite ordinal ω -/

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
/-
**Ordinal.omega0** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：omega0 : Ordinal.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ω` is the first infinite ordinal, defined as the order type of `ℕ`.
-/
def omega0 : Ordinal.{u} :=
  lift (typeLT ℕ)

@[inherit_doc] scoped notation "ω" => Ordinal.omega0
recommended_spelling "omega0" for "ω" in [omega0, «termω»]

/-- Note that the presence of this lemma makes `simp [omega0]` form a loop. -/
@[simp]
/-
**Ordinal.type_nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_nat_lt : typeLT Nat = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Ordinal.lift_id`：lift_id : forall a, lift.{u, u} a = a

--- 原说明 ---
Note that the presence of this lemma makes `simp [omega0]` form a loop.
-/
theorem type_nat_lt : typeLT ℕ = ω :=
  (lift_id _).symm

@[simp]
/-
**Ordinal.card_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_omega0 : card ω = ℵ₀
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_omega0 : card ω = ℵ₀ :=
  rfl

@[simp]
/-
**Ordinal.lift_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lift_omega0 : lift ω = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lift_lift`：lift_lift (a : Ordinal.{u}) : lift.{w} (lift.{v} a) =
 lift.{max v w} a
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


/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
every element of `o₁` is smaller than every element of `o₂`. -/
/-
**Ordinal.add** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：add : Add Ordinal.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …

--- 原说明 ---
`o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declar
ing that
every element of `o₁` is smaller than every element of `o₂`.
-/
instance add : Add Ordinal.{u} :=
  ⟨fun o₁ o₂ => Quotient.liftOn₂ o₁ o₂ (fun ⟨_, r, _⟩ ⟨_, s, _⟩ => type (Sum.Lex r s))
    fun _ _ _ _ ⟨f⟩ ⟨g⟩ => (RelIso.sumLexCongr f g).ordinalType_congr⟩
/-
**Ordinal.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：addMonoidWithOne : AddMonoidWithOne Ordinal.{u} where zero_add o
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne : AddMonoidWithOne Ordinal.{u} where
  zero_add o := inductionOn o fun α _ _ => (RelIso.emptySumLex _ _).ordinalType_congr
  add_zero o := inductionOn o fun α _ _ => (RelIso.sumLexEmpty _ _).ordinalType_congr
  add_assoc o₁ o₂ o₃ :=
    Quotient.inductionOn₃ o₁ o₂ o₃ fun _ _ _ ↦ Quot.sound ⟨⟨sumAssoc .., by simp⟩⟩
  nsmul := nsmulRec

@[simp]
/-
**Ordinal.card_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₂`：inductionOn₂ {motive : Ordinal -> Ordinal -> Prop}
 (o₁ o₂ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s
], motive …
-/
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  inductionOn₂ o₁ o₂ fun _ _ _ _ _ _ ↦ rfl
/-
**Ordinal.card_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_add_one (o : Ordinal) : card (o + 1) = card o + 1
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.card_add`：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ 
+ card o₂
· 使用定理 `Ordinal.card_one`：card_one : card 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_add_one (o : Ordinal) : card (o + 1) = card o + 1 := by
  simp

@[simp]
/-
**Ordinal.type_sum_lex** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_sum_lex {α β : Type u} (r : α -> α -> Prop) (s : β -> β -> Prop) [IsW
ellOrder α r] [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
-/
theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r]
    [IsWellOrder β s] : type (Sum.Lex r s) = type r + type s :=
  rfl

@[simp]
/-
**Ordinal.card_nat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_nat (n : Nat) : card.{u} n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.card_zero`：card_zero : card 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Ordinal.card_add`：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ 
+ card o₂
· 使用定理 `Ordinal.card_one`：card_one : card 1 = 1
-/
theorem card_nat (n : ℕ) : card.{u} n = n := by
  induction n <;> [simp; simp only [card_add, card_one, Nat.cast_succ, *]]

@[simp]
/-
**Ordinal.card_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_ofNat (n : Nat) [n.AtLeastTwo] : card.{u} ofNat(n) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_nat`：card_nat (n : Nat) : card.{u} n = n
-/
theorem card_ofNat (n : ℕ) [n.AtLeastTwo] :
    card.{u} ofNat(n) = OfNat.ofNat n :=
  card_nat n
/-
**Ordinal.instAddLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instAddLeftMono : AddLeftMono Ordinal.{u} where elim c a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₃`：inductionOn₃ {motive : Ordinal -> Ordinal -> Ordin
al -> Prop} (o₁ o₂ o₃ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [I
sWellOrder…
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
· 使用定理 `Sum.instTrichotomousLex_mathlib`：∀ {α : Type u_1} {β : Type u_2} (r : α 
→ α → Prop) (s : β → β → Prop) [Std.Trichotomous r] [Std.Trichotomous s],   Std.
Trichotomous (Sum.Lex…
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `InitialSeg.map_rel_iff`：map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f 
b) ↔ r a b
-/
instance instAddLeftMono : AddLeftMono Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦
      (RelEmbedding.ofMonotone (Sum.recOn · Sum.inl (Sum.inr ∘ f)) ?_).ordinal_type_le
    simp [f.map_rel_iff]
/-
**Ordinal.instAddRightMono** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instAddRightMono : AddRightMono Ordinal.{u} where elim c a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₃`：inductionOn₃ {motive : Ordinal -> Ordinal -> Ordin
al -> Prop} (o₁ o₂ o₃ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [I
sWellOrder…
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
· 使用定理 `Sum.instTrichotomousLex_mathlib`：∀ {α : Type u_1} {β : Type u_2} (r : α 
→ α → Prop) (s : β → β → Prop) [Std.Trichotomous r] [Std.Trichotomous s],   Std.
Trichotomous (Sum.Lex…
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `InitialSeg.map_rel_iff`：map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f 
b) ↔ r a b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance instAddRightMono : AddRightMono Ordinal.{u} where
  elim c a b := by
    refine inductionOn₃ a b c fun α r _ β s _ γ t _ ⟨f⟩ ↦
      (RelEmbedding.ofMonotone (Sum.recOn · (Sum.inl ∘ f) Sum.inr) ?_).ordinal_type_le
    simp [f.map_rel_iff]
/-
**Ordinal.existsAddOfLE** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：existsAddOfLE : ExistsAddOfLE Ordinal where exists_add_of_le {a b}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.inductionOn₂`：inductionOn₂ {motive : Ordinal -> Ordinal -> Prop}
 (o₁ o₂ : Ordinal) (type : forall (α r) [IsWellOrder α r] (β s) [IsWellOrder β s
], motive …
· 使用定理 `InitialSeg.exists_sum_relIso`：exists_sum_relIso {β : Type u} {s : β -> β
 -> Prop} [IsWellOrder β s] (f : r ≼i s) : exists (γ : Type u) (t : γ -> γ -> Pr
op), IsWellOrder γ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …
· 使用定理 `RelIso.ordinalType_congr`：∀ {α β : Type u_1} {r : α → α → Prop} {s : β →
 β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ≃r s), O
rdinal.type r …
-/
instance existsAddOfLE : ExistsAddOfLE Ordinal where
  exists_add_of_le {a b} := by
    refine inductionOn₂ a b fun α r _ β s _ ⟨f⟩ ↦ ?_
    obtain ⟨γ, t, _, ⟨g⟩⟩ := f.exists_sum_relIso
    exact ⟨type t, g.ordinalType_congr.symm⟩
/-
**Ordinal.canonicallyOrderedAdd** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：canonicallyOrderedAdd : CanonicallyOrderedAdd Ordinal where le_add_self a 
b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
instance canonicallyOrderedAdd : CanonicallyOrderedAdd Ordinal where
  le_add_self a b := by simpa using add_le_add_left bot_le a
  le_self_add a b := by simpa using add_le_add_right bot_le a

@[deprecated zero_max (since := "2026-05-07")]
/-
**Ordinal.max_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：max_zero_left : forall a : Ordinal, max 0 a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_max`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Zero α] [IsB
otZeroClass α] (a : α), max 0 a = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem max_zero_left : ∀ a : Ordinal, max 0 a = a :=
  zero_max

@[deprecated max_zero (since := "2026-05-07")]
/-
**Ordinal.max_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：max_zero_right : forall a : Ordinal, max a 0 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_zero`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Zero α] [IsB
otZeroClass α] (a : α), max a 0 = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem max_zero_right : ∀ a : Ordinal, max a 0 = a :=
  max_zero

@[deprecated _root_.max_eq_zero (since := "2026-05-07")]
/-
**Ordinal.max_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a b : Ordinal.{u_1}}, max a b = 0 ↔ a = 0 ∧ b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_zero`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Zero α] [
IsBotZeroClass α] {a b : α}, max a b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
protected theorem max_eq_zero {a b : Ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  max_eq_zero

@[simp]
/-
**Ordinal.sInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sInf_empty : sInf (∅ : Set Ordinal) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.not_nonempty_empty`：not_nonempty_empty : ¬(∅ : Set α).Nonempty
-/
theorem sInf_empty : sInf (∅ : Set Ordinal) = 0 :=
  dif_neg Set.not_nonempty_empty

/-! ### Successor order properties -/

/-
**Ordinal.succ_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Successor order properties
-/
private theorem succ_le_iff' {a b : Ordinal} : a + 1 ≤ b ↔ a < b := by
  refine inductionOn₂ a b fun α r _ β s _ ↦ ⟨?_, ?_⟩ <;> rintro ⟨f⟩
  · refine ⟨((InitialSeg.leAdd _ _).trans f).toPrincipalSeg fun h ↦ ?_⟩
    simpa using h (f (Sum.inr PUnit.unit))
  · apply (RelEmbedding.ofMonotone (Sum.recOn · f fun _ ↦ f.top) ?_).ordinal_type_le
    simpa [f.map_rel_iff] using f.lt_top
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMaxOrder Ordinal :=
  ⟨fun _ => ⟨_, succ_le_iff'.1 le_rfl⟩⟩
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) (by exact succ_le_iff')
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SuccAddOrder Ordinal := ⟨fun _ => rfl⟩

@[deprecated succ_eq_add_one (since := "2026-02-26")]
/-
**Ordinal.add_one_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_one_eq_succ (o : Ordinal) : o + 1 = succ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl

@[deprecated zero_add (since := "2026-02-26")]
/-
**Ordinal.succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_zero : succ (0 : Ordinal) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem succ_zero : succ (0 : Ordinal) = 1 :=
  zero_add 1

@[deprecated one_add_one_eq_two (since := "2026-02-26")]
/-
**Ordinal.succ_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_one : succ (1 : Ordinal) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
-/
theorem succ_one : succ (1 : Ordinal) = 2 := one_add_one_eq_two

@[deprecated add_assoc (since := "2026-02-26")]
/-
**Ordinal.add_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assoc _ _ _).symm

@[deprecated Order.one_le_iff_ne_zero (since := "2026-03-24")]
/-
**Ordinal.one_le_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {o : Ordinal.{u_1}}, 1 ≤ o ↔ o ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
protected theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 :=
  Order.one_le_iff_ne_zero

@[deprecated add_pos_of_right (since := "2026-04-04")]
/-
**Ordinal.succ_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_pos (o : Ordinal) : 0 < succ o
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
-/
theorem succ_pos (o : Ordinal) : 0 < succ o :=
  add_pos_of_right zero_lt_one o

@[deprecated add_pos_of_right (since := "2026-04-04")]
/-
**Ordinal.add_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_one_ne_zero (o : Ordinal) : o + 1 != 0
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
-/
theorem add_one_ne_zero (o : Ordinal) : o + 1 ≠ 0 :=
  (add_pos_of_right zero_lt_one o).ne'

@[deprecated add_pos_of_right (since := "2026-02-27")]
/-
**Ordinal.succ_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：succ_ne_zero (o : Ordinal) : succ o != 0
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
-/
theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  (add_pos_of_right zero_lt_one o).ne'

@[deprecated Order.lt_one_iff (since := "2026-03-24")]
/-
**Ordinal.lt_one_iff_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 :=
  Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-03-24")]
/-
**Ordinal.le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ {a : Ordinal.{u_1}}, a ≤ 1 ↔ a = 0 ∨ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
protected theorem le_one_iff {a : Ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 :=
  Order.le_one_iff

@[deprecated card_add_one (since := "2026-02-27")]
/-
**Ordinal.card_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_succ (o : Ordinal) : card (succ o) = card o + 1
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.card_add`：card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ 
+ card o₂
· 使用定理 `Ordinal.card_one`：card_one : card 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp

@[deprecated Nat.cast_add_one (since := "2026-05-21")]
/-
**Ordinal.natCast_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_succ (n : Nat) : ↑n.succ = succ (n : Ordinal)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
-/
theorem natCast_succ (n : ℕ) : ↑n.succ = succ (n : Ordinal) :=
  n.cast_add_one
/-
**Ordinal.uniqueIioOne** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：uniqueIioOne : Unique (Iio (1 : Ordinal)) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueIioOne : Unique (Iio (1 : Ordinal)) where
  default := ⟨0, zero_lt_one' Ordinal⟩
  uniq a := Subtype.ext <| lt_one_iff.1 a.2

@[simp]
/-
**Ordinal.Iio_one_default_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：Iio_one_default_eq : (default : Iio (1 : Ordinal)) = ⟨0, zero_lt_one' Ordi
nal⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_one_default_eq : (default : Iio (1 : Ordinal)) = ⟨0, zero_lt_one' Ordinal⟩ :=
  rfl
/-
**Ordinal.uniqueToTypeOne** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：uniqueToTypeOne : Unique (ToType 1) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueToTypeOne : Unique (ToType 1) where
  default := enum (α := ToType 1) (· < ·) ⟨0, by simp⟩
  uniq a := by
    rw [← enum_typein (α := ToType 1) (· < ·) a]
    congr
    rw [← lt_one_iff]
    apply typein_lt_self
/-
**Ordinal.one_toType_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_toType_eq (x : ToType 1) : x = enum (· < ·) ⟨0, by simp⟩
参数：x : ToType 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
theorem one_toType_eq (x : ToType 1) : x = enum (· < ·) ⟨0, by simp⟩ :=
  Unique.eq_default x

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.type_lt_mem_range_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lt_mem_range_succ_iff [LinearOrder α] [WellFoundedLT α] : typeLT α in
 range succ ↔ exists x : α, IsMax x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Set.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iio
 b ↔ x < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Ordinal.enum_le_enum`：enum_le_enum (r : α -> α -> Prop) [IsWellOrder α r
] {o₁ o₂ : Iio (type r)} : ¬r (enum r o₁) (enum r o₂) ↔ o₂ <= o₁
· 使用定理 `Subtype.mk_le_mk`：mk_le_mk [LE α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) <= ⟨y, hy⟩ ↔ x <= y
· 使用定理 `eq_of_forall_lt_iff`：eq_of_forall_lt_iff (h : forall c, c < a ↔ c < b) :
 a = b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Ordinal.typein_le_typein`：typein_le_typein (r : α -> α -> Prop) [IsWellO
rder α r] {a b : α} : typein r a <= typein r b ↔ ¬r b a
-/
theorem type_lt_mem_range_succ_iff [LinearOrder α] [WellFoundedLT α] :
    typeLT α ∈ range succ ↔ ∃ x : α, IsMax x := by
  simp_rw [← isTop_iff_isMax]
  constructor <;> intro ⟨a, ha⟩
  · refine ⟨enum (α := α) (· < ·) ⟨a, ?_⟩, fun b ↦ ?_⟩
    · rw [mem_Iio, ← ha, lt_succ_iff]
    · rw [← enum_typein (α := α) (· < ·) b, ← not_lt, enum_le_enum (r := (· < ·)),
        Subtype.mk_le_mk, ← lt_succ_iff, ha]
      exact typein_lt_type ..
  · refine ⟨typein (α := α) (· < ·) a, eq_of_forall_lt_iff fun o ↦ ?_⟩
    rw [lt_succ_iff]
    refine ⟨fun h ↦ h.trans_lt (typein_lt_type _ _), fun h ↦ ?_⟩
    rw [← typein_enum _ h, typein_le_typein, not_lt]
    apply ha
/-
**Ordinal.type_lt_mem_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_lt_mem_range_succ [LinearOrder α] [WellFoundedLT α] [OrderTop α] : ty
peLT α in range succ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.type_lt_mem_range_succ_iff`：type_lt_mem_range_succ_iff [LinearOr
der α] [WellFoundedLT α] : typeLT α in range succ ↔ exists x : α, IsMax x
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem type_lt_mem_range_succ [LinearOrder α] [WellFoundedLT α] [OrderTop α] :
    typeLT α ∈ range succ :=
  type_lt_mem_range_succ_iff.2 ⟨⊤, isMax_top⟩
/-
**Ordinal.isSuccPrelimit_type_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_type_lt_iff [LinearOrder α] [WellFoundedLT α] : IsSuccPreli
mit (typeLT α) ↔ NoMaxOrder α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `noMaxOrder_iff`：∀ {α : Type u_1} [inst : Preorder α], NoMaxOrder α ↔ ∀ (
x : α), ¬IsMax x
· 使用定理 `Order.not_isSuccPrelimit_iff_mem_range_succ`：not_isSuccPrelimit_iff_mem_
range_succ : ¬ IsSuccPrelimit a ↔ a in range (succ : α -> α)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.type_lt_mem_range_succ_iff`：type_lt_mem_range_succ_iff [LinearOr
der α] [WellFoundedLT α] : typeLT α in range succ ↔ exists x : α, IsMax x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSuccPrelimit_type_lt_iff [LinearOrder α] [WellFoundedLT α] :
    IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α := by
  rw [← not_iff_not, noMaxOrder_iff, not_isSuccPrelimit_iff_mem_range_succ,
    type_lt_mem_range_succ_iff]
  simp [IsMax]
/-
**Ordinal.isSuccPrelimit_type_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccPrelimit_type_lt [LinearOrder α] [WellFoundedLT α] [h : NoMaxOrder α
] : IsSuccPrelimit (typeLT α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Ordinal.isSuccPrelimit_type_lt_iff`：isSuccPrelimit_type_lt_iff [LinearOr
der α] [WellFoundedLT α] : IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α
-/
theorem isSuccPrelimit_type_lt [LinearOrder α] [WellFoundedLT α] [h : NoMaxOrder α] :
    IsSuccPrelimit (typeLT α) :=
  isSuccPrelimit_type_lt_iff.2 h

/-! ### Extra properties of typein and enum -/

-- TODO: use `ToType.mk` for lemmas on `ToType` rather than `enum` and `typein`.

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Ordinal.typein_one_toType** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_one_toType (x : ToType 1) : typein (α
参数：x : ToType 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.one_toType_eq`：one_toType_eq (x : ToType 1) : x = enum (· < ·) ⟨
0, by simp⟩
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
-/
theorem typein_one_toType (x : ToType 1) : typein (α := ToType 1) (· < ·) x = 0 := by
  rw [one_toType_eq x, typein_enum]
/-
**Ordinal.typein_le_typein'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：typein_le_typein' (o : Ordinal) {x y : o.ToType} : typein (α
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem typein_le_typein' (o : Ordinal) {x y : o.ToType} :
    typein (α := o.ToType) (· < ·) x ≤ typein (α := o.ToType) (· < ·) y ↔ x ≤ y := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Ordinal.le_enum_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_enum_succ {o : Ordinal} (a : (succ o).ToType) : a <= enum (α
参数：a : (succ o).ToType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.enum_typein`：enum_typein (r : α -> α -> Prop) [IsWellOrder α r] 
(a : α) : enum r ⟨typein r a, typein_lt_type r a⟩ = a
· 使用定理 `Ordinal.enum_le_enum'`：enum_le_enum' (a : Ordinal) {o₁ o₂ : Iio (type (·
 < ·))} : enum (· < ·) o₁ <= enum (α
· 使用定理 `Subtype.mk_le_mk`：mk_le_mk [LE α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) <= ⟨y, hy⟩ ↔ x <= y
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.typein_lt_self`：typein_lt_self {o : Ordinal} (i : o.ToType) : ty
pein (α
-/
theorem le_enum_succ {o : Ordinal} (a : (succ o).ToType) :
    a ≤ enum (α := (succ o).ToType) (· < ·) ⟨o, (type_toType _ ▸ lt_succ o)⟩ := by
  rw [← enum_typein (α := (succ o).ToType) (· < ·) a, enum_le_enum', Subtype.mk_le_mk,
    ← lt_succ_iff]
  apply typein_lt_self

end Ordinal

/-! ### Representing a cardinal with an ordinal -/

namespace Cardinal

open Ordinal

/-- The ordinal corresponding to a cardinal `c` is the least ordinal whose cardinal is `c`. -/
@[no_expose]
/-
**Cardinal.ord** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：ord (c : Cardinal) : Ordinal
参数：c : Cardinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal corresponding to a cardinal `c` is the least ordinal whose cardinal 
is `c`.
-/
def ord (c : Cardinal) : Ordinal :=
  Quot.liftOn c (fun α : Type u => ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2) <| by
  rintro α β ⟨f⟩
  refine congr_arg sInf <| ext fun o ↦ ⟨?_, ?_⟩ <;>
    rintro ⟨⟨r, hr⟩, rfl⟩ <;>
    refine ⟨⟨_, RelIso.IsWellOrder.preimage r ?_⟩, type_preimage _ _⟩
  exacts [f.symm, f]
/-
**Cardinal.ord_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_eq_iInf (α : Type u) : ord #α = ⨅ r : { r // IsWellOrder α r }, @type 
α r.1 r.2
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ord_eq_iInf (α : Type u) : ord #α = ⨅ r : { r // IsWellOrder α r }, @type α r.1 r.2 :=
  (rfl)

@[deprecated (since := "2026-03-15")] alias ord_eq_Inf := ord_eq_iInf

/-- There exists a well-order on `α` whose order type is exactly `ord #α`. -/
/-
**Cardinal.exists_ord_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_ord_eq (α) : exists (r : α -> α -> Prop) (_ : IsWellOrder α r), ord
 #α = type r
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ciInf_mem`：ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
There exists a well-order on `α` whose order type is exactly `ord #α`.
-/
theorem exists_ord_eq (α) : ∃ (r : α → α → Prop) (_ : IsWellOrder α r), ord #α = type r :=
  let ⟨r, wo⟩ := ciInf_mem fun r : { r // IsWellOrder α r } => @type α r.1 r.2
  ⟨r.1, r.2, wo.symm⟩

@[deprecated (since := "2026-03-29")] alias ord_eq := exists_ord_eq

/-- There exists a well-order on `α` whose order type is exactly `ord #α`. -/
/-
**Cardinal.exists_ord_eq_type_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_ord_eq_type_lt (α) : exists (_ : LinearOrder α) (_ : WellFoundedLT 
α), ord #α = typeLT α
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r

--- 原说明 ---
There exists a well-order on `α` whose order type is exactly `ord #α`.
-/
theorem exists_ord_eq_type_lt (α) :
    ∃ (_ : LinearOrder α) (_ : WellFoundedLT α), ord #α = typeLT α := by
  classical
  let ⟨r, _, hr⟩ := exists_ord_eq α
  let := linearOrderOfSTO r
  exact ⟨this, inferInstance, hr⟩
/-
**Cardinal.ord_le_type** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_le_type (r : α -> α -> Prop) [h : IsWellOrder α r] : ord #α <= type r
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le'`：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i
-/
theorem ord_le_type (r : α → α → Prop) [h : IsWellOrder α r] : ord #α ≤ type r :=
  ciInf_le' _ (Subtype.mk r h)

@[simp]
/-
**Cardinal.card_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_ord (c) : (ord c).card = c
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `Ordinal.card_type`：card_type (r : α -> α -> Prop) [IsWellOrder α r] : ca
rd (type r) = #α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem card_ord (c) : (ord c).card = c :=
  c.inductionOn fun α ↦ let ⟨r, _, e⟩ := exists_ord_eq α; e ▸ card_type r

/-- Galois connection between `Cardinal.ord` and `Ordinal.card`. -/
/-
**Cardinal.gc_ord_card** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：gc_ord_card : GaloisConnection ord card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Ordinal.inductionOn`：inductionOn {motive : Ordinal -> Prop} (o : Ordinal
) (type : forall (α r) [IsWellOrder α r], motive (type r)) : motive o
· 使用定理 `Cardinal.exists_ord_eq`：exists_ord_eq (α) : exists (r : α -> α -> Prop) 
(_ : IsWellOrder α r), ord #α = type r
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.ord_le_type`：ord_le_type (r : α -> α -> Prop) [h : IsWellOrder 
α r] : ord #α <= type r
· 使用定理 `RelEmbedding.ordinal_type_le`：∀ {α β : Type u_1} {r : α → α → Prop} {s :
 β → β → Prop} [inst : IsWellOrder α r] [inst_1 : IsWellOrder β s]   (h : r ↪r s
), Ordinal.type r …

--- 原说明 ---
Galois connection between `Cardinal.ord` and `Ordinal.card`.
-/
theorem gc_ord_card : GaloisConnection ord card := by
  refine fun c o ↦ c.inductionOn fun α ↦ o.inductionOn fun β s _ ↦ ?_
  let ⟨r, _, e⟩ := exists_ord_eq α
  constructor <;> intro h
  · rw [e] at h
    exact card_le_card h
  · obtain ⟨f⟩ := h
    have g := RelEmbedding.preimage f s
    have := RelEmbedding.isWellOrder g
    exact (ord_le_type _).trans g.ordinal_type_le

/-- Galois coinsertion between `Cardinal.ord` and `Ordinal.card`. -/
/-
**Cardinal.gciOrdCard** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：gciOrdCard : GaloisCoinsertion ord card
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card

--- 原说明 ---
Galois coinsertion between `Cardinal.ord` and `Ordinal.card`.
-/
def gciOrdCard : GaloisCoinsertion ord card :=
  gc_ord_card.toGaloisCoinsertion fun c ↦ c.card_ord.le
/-
**Cardinal.ord_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_le {c o} : ord c <= o ↔ c <= o.card
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card
-/
theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
  gc_ord_card.le_iff_le
/-
**Cardinal.lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_ord {c o} : o < ord c ↔ o.card < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.lt_iff_lt`：lt_iff_lt (gc : GaloisConnection l u) {a : α
} {b : β} : b < l a ↔ u b < a
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card
-/
theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt
/-
**Cardinal.card_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_surjective : Function.Surjective card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
-/
theorem card_surjective : Function.Surjective card :=
  fun c ↦ ⟨_, card_ord c⟩
/-
**Cardinal.bddAbove_ord_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：bddAbove_ord_image_iff {s : Set Cardinal} : BddAbove (ord '' s) ↔ BddAbove
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.bddAbove_l_image`：bddAbove_l_image {s : Set α} : BddAbo
ve (l '' s) ↔ BddAbove s
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card
-/
theorem bddAbove_ord_image_iff {s : Set Cardinal} : BddAbove (ord '' s) ↔ BddAbove s :=
  gc_ord_card.bddAbove_l_image
/-
**Cardinal.ord_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_card_le (o : Ordinal) : o.card.ord <= o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card
-/
theorem ord_card_le (o : Ordinal) : o.card.ord ≤ o :=
  gc_ord_card.l_u_le _
/-
**Cardinal.lt_ord_succ_card** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
-/
theorem lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord :=
  lt_ord.2 <| lt_succ _
/-
**Cardinal.card_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_le_iff {o : Ordinal} {c : Cardinal} : o.card <= c ↔ o < (succ c).ord
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem card_le_iff {o : Ordinal} {c : Cardinal} : o.card ≤ c ↔ o < (succ c).ord := by
  rw [lt_ord, lt_succ_iff]

/--
A variation on `Cardinal.lt_ord` using `≤`: If `o` is no greater than the
initial ordinal of cardinality `c`, then its cardinal is no greater than `c`.

The converse, however, is false (for instance, `o = ω+1` and `c = ℵ₀`).
-/
/-
**Cardinal.card_le_of_le_ord** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：card_le_of_le_ord {o : Ordinal} {c : Cardinal} (ho : o <= c.ord) : o.card 
<= c
参数：ho : o <= c.ord。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂

--- 原说明 ---
A variation on `Cardinal.lt_ord` using `≤`: If `o` is no greater than the
initial ordinal of cardinality `c`, then its cardinal is no greater than `c`.

The converse, however, is false (for instance, `o = ω+1` and `c = ℵ₀`).
-/
lemma card_le_of_le_ord {o : Ordinal} {c : Cardinal} (ho : o ≤ c.ord) : o.card ≤ c := by
  rw [← card_ord c]; exact Ordinal.card_le_card ho

@[gcongr, mono]
/-
**Cardinal.ord_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_strictMono : StrictMono ord
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.strictMono_l`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion 
l u), StrictMono l
-/
theorem ord_strictMono : StrictMono ord :=
  gciOrdCard.strictMono_l

@[gcongr, mono]
/-
**Cardinal.ord_mono** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_mono : Monotone ord
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card
-/
theorem ord_mono : Monotone ord :=
  gc_ord_card.monotone_l
/-
**Cardinal.ord_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_injective : Injective ord
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Cardinal.ord_strictMono`：ord_strictMono : StrictMono ord
-/
theorem ord_injective : Injective ord :=
  ord_strictMono.injective

@[simp]
/-
**Cardinal.ord_le_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
-/
theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
  gciOrdCard.l_le_l_iff

@[simp]
/-
**Cardinal.ord_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Cardinal.ord_strictMono`：ord_strictMono : StrictMono ord
-/
theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
  ord_strictMono.lt_iff_lt

@[simp]
/-
**Cardinal.ord_inj** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_inj {c₁ c₂} : ord c₁ = ord c₂ ↔ c₁ = c₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Cardinal.ord_injective`：ord_injective : Injective ord
-/
theorem ord_inj {c₁ c₂} : ord c₁ = ord c₂ ↔ c₁ = c₂ :=
  ord_injective.eq_iff

@[simp]
/-
**Cardinal.ord_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_zero : ord 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Cardinal.gc_ord_card`：gc_ord_card : GaloisConnection ord card
-/
theorem ord_zero : ord 0 = 0 :=
  gc_ord_card.l_bot

@[simp]
/-
**Cardinal.ord_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_natCast (n : Nat) : ord n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ordinal.card_nat`：card_nat (n : Nat) : card.{u} n = n
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LT.lt.succ_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder 
α] {a b : α}, a < b → Order.succ a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem ord_natCast (n : ℕ) : ord n = n := by
  apply (ord_le.2 (card_nat n).ge).antisymm
  induction n with
  | zero => exact zero_le
  | succ n IH => exact (IH.trans_lt <| by simp).succ_le

@[deprecated (since := "2026-02-27")] alias ord_nat := ord_natCast

@[simp]
/-
**Cardinal.ord_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_ofNat (n : Nat) [n.AtLeastTwo] : ord ofNat(n) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ord_natCast`：ord_natCast (n : Nat) : ord n = n
-/
theorem ord_ofNat (n : ℕ) [n.AtLeastTwo] : ord ofNat(n) = OfNat.ofNat n :=
  ord_natCast n

@[simp]
/-
**Cardinal.ord_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_one : ord 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.ord_natCast`：ord_natCast (n : Nat) : ord n = n
-/
theorem ord_one : ord 1 = 1 := by simpa using ord_natCast 1
/-
**Cardinal.isNormal_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：isNormal_ord : Order.IsNormal ord where strictMono
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ord_strictMono`：ord_strictMono : StrictMono ord
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Order.IsSuccLimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : PartialOrd
er α] [inst_1 : SuccOrder α],   Order.IsSuccLimit b → a < b → Order.succ a < b
-/
theorem isNormal_ord : Order.IsNormal ord where
  strictMono := ord_strictMono
  mem_lowerBounds_upperBounds_of_isSuccLimit := by
    intro a ha
    simp_rw [lowerBounds, upperBounds, mem_ofPred, forall_mem_image, ord_le]
    refine fun b H ↦ le_of_forall_lt fun c hc ↦ ?_
    simpa using H (ha.succ_lt hc)

@[simp]
/-
**Cardinal.ord_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_aleph0 : ord.{u} ℵ₀ = ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_lift_iff`：lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v
}} : b < lift.{v} a ↔ exists a' < a, lift.{v} a' = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_card`：lift_card (a) : Cardinal.lift.{u, v} (card a) = card 
(lift.{u} a)
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Cardinal.lt_aleph0_iff_fintype`：lt_aleph0_iff_fintype {α : Type u} : #α 
< ℵ₀ ↔ Nonempty (Fintype α)
-/
theorem ord_aleph0 : ord.{u} ℵ₀ = ω := by
  refine le_antisymm (ord_le.2 le_rfl) <| le_of_forall_lt fun o h ↦ ?_
  rcases Ordinal.lt_lift_iff.1 h with ⟨o, ho, rfl⟩
  rw [lt_ord, ← lift_card, lift_lt_aleph0, ← typein_enum _ ho]
  exact lt_aleph0_iff_fintype.2 ⟨Set.fintypeLTNat _⟩

@[simp]
/-
**Cardinal.lift_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lift.{u, v} c)
参数：c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_lift_iff`：lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v
}} : b < lift.{v} a ↔ exists a' < a, lift.{v} a' = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lift_card`：lift_card (a) : Cardinal.lift.{u, v} (card a) = card 
(lift.{u} a)
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Ordinal.lift_lt`：lift_lt {a b : Ordinal} : lift.{u, v} a < lift.{u, v} b
 ↔ a < b
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lift.{u, v} c) := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) ?_
  · rcases Ordinal.lt_lift_iff.1 ha with ⟨a, _, rfl⟩
    rwa [lt_ord, ← lift_card, lift_lt, ← lt_ord, ← Ordinal.lift_lt]
  · rw [ord_le, ← lift_card, card_ord]
/-
**Cardinal.mk_ord_toType** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_ord_toType (c : Cardinal) : #c.ord.ToType = c
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_ord_toType (c : Cardinal) : #c.ord.ToType = c := by simp
/-
**Cardinal.card_typein_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_typein_lt {r : α -> α -> Prop} [IsWellOrder α r] (x : α) (h : ord #α 
= type r) : card (typein r x) < #α
参数：x : α；h : ord #α = type r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
-/
theorem card_typein_lt {r : α → α → Prop} [IsWellOrder α r] (x : α) (h : ord #α = type r) :
    card (typein r x) < #α := by
  rw [← lt_ord, h]
  apply typein_lt_type
/-
**Cardinal.mk_Iio_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) (h : ord #α = typeLT α
) : #(Iio i) < #α
参数：i : α；h : ord #α = typeLT α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.card_typein_lt`：card_typein_lt {r : α -> α -> Prop} [IsWellOrde
r α r] (x : α) (h : ord #α = type r) : card (typein r x) < #α
-/
theorem mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) (h : ord #α = typeLT α) :
    #(Iio i) < #α :=
  card_typein_lt (r := LT.lt) i h
/-
**Cardinal.mk_Ioi_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ioi_lt {α : Type*} [LinearOrder α] [WellFoundedGT α] (i : α) (h : ord #
α = typeLT αᵒᵈ) : #(Ioi i) < #α
参数：i : α；h : ord #α = typeLT αᵒᵈ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `Cardinal.mk_Iio_lt`：mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) 
(h : ord #α = typeLT α) : #(Iio i) < #α
-/
theorem mk_Ioi_lt {α : Type*} [LinearOrder α] [WellFoundedGT α] (i : α) (h : ord #α = typeLT αᵒᵈ) :
    #(Ioi i) < #α :=
  mk_Iio_lt (OrderDual.toDual i) h

@[deprecated mk_Iio_lt (since := "2026-04-12")]
/-
**Cardinal.mk_Iio_toType_ord_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Iio_toType_ord_lt {c : Cardinal} (i : c.ord.ToType) : #(Iio i) < c
参数：i : c.ord.ToType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_toType`：∀ (o : Ordinal.{u_1}), Cardinal.mk o.ToType = o.card
· 使用定理 `Cardinal.card_ord`：card_ord (c) : (ord c).card = c
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Cardinal.mk_Iio_lt`：mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) 
(h : ord #α = typeLT α) : #(Iio i) < #α
-/
theorem mk_Iio_toType_ord_lt {c : Cardinal} (i : c.ord.ToType) : #(Iio i) < c := by
  simpa using mk_Iio_lt i

@[deprecated (since := "2026-03-20")] alias mk_Iio_ord_toType := mk_Iio_toType_ord_lt

@[deprecated mk_Iio_lt (since := "2026-03-20")]
/-
**Cardinal.card_typein_toType_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：card_typein_toType_lt (c : Cardinal) (x : c.ord.ToType) : card (typein (α
参数：c : Cardinal；x : c.ord.ToType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_Iio_toType_ord_lt`：mk_Iio_toType_ord_lt {c : Cardinal} (i : 
c.ord.ToType) : #(Iio i) < c
-/
theorem card_typein_toType_lt (c : Cardinal) (x : c.ord.ToType) :
    card (typein (α := c.ord.ToType) (· < ·) x) < c :=
  mk_Iio_toType_ord_lt x

@[simp]
/-
**Cardinal.ord_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_eq_zero {a : Cardinal} : a.ord = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Cardinal.ord_injective`：ord_injective : Injective ord
· 使用定理 `Cardinal.ord_zero`：ord_zero : ord 0 = 0
-/
theorem ord_eq_zero {a : Cardinal} : a.ord = 0 ↔ a = 0 :=
  ord_injective.eq_iff' ord_zero

@[simp]
/-
**Cardinal.ord_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_eq_one {a : Cardinal} : a.ord = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Cardinal.ord_injective`：ord_injective : Injective ord
· 使用定理 `Cardinal.ord_one`：ord_one : ord 1 = 1
-/
theorem ord_eq_one {a : Cardinal} : a.ord = 1 ↔ a = 1 :=
  ord_injective.eq_iff' ord_one

@[simp]
/-
**Cardinal.ord_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_pos {a : Cardinal} : 0 < a.ord ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_zero`：ord_zero : ord 0 = 0
· 使用定理 `Cardinal.ord_lt_ord`：ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ord_pos {a : Cardinal} : 0 < a.ord ↔ 0 < a := by
  rw [← ord_zero, ord_lt_ord]

@[simp]
/-
**Cardinal.omega0_le_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：omega0_le_ord {a : Cardinal} : ω <= a.ord ↔ ℵ₀ <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem omega0_le_ord {a : Cardinal} : ω ≤ a.ord ↔ ℵ₀ ≤ a := by
  rw [← ord_aleph0, ord_le_ord]

@[simp]
/-
**Cardinal.ord_le_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_le_omega0 {a : Cardinal} : a.ord <= ω ↔ a <= ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ord_le_omega0 {a : Cardinal} : a.ord ≤ ω ↔ a ≤ ℵ₀ := by
  rw [← ord_aleph0, ord_le_ord]

@[simp]
/-
**Cardinal.ord_lt_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_lt_omega0 {a : Cardinal} : a.ord < ω ↔ a < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Cardinal.omega0_le_ord`：omega0_le_ord {a : Cardinal} : ω <= a.ord ↔ ℵ₀ <
= a
-/
theorem ord_lt_omega0 {a : Cardinal} : a.ord < ω ↔ a < ℵ₀ :=
  le_iff_le_iff_lt_iff_lt.1 omega0_le_ord

@[simp]
/-
**Cardinal.omega0_lt_ord** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：omega0_lt_ord {a : Cardinal} : ω < a.ord ↔ ℵ₀ < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Cardinal.ord_le_omega0`：ord_le_omega0 {a : Cardinal} : a.ord <= ω ↔ a <=
 ℵ₀
-/
theorem omega0_lt_ord {a : Cardinal} : ω < a.ord ↔ ℵ₀ < a :=
  le_iff_le_iff_lt_iff_lt.1 ord_le_omega0

@[simp]
/-
**Cardinal.ord_eq_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：ord_eq_omega0 {a : Cardinal} : a.ord = ω ↔ a = ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Cardinal.ord_injective`：ord_injective : Injective ord
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
-/
theorem ord_eq_omega0 {a : Cardinal} : a.ord = ω ↔ a = ℵ₀ :=
  ord_injective.eq_iff' ord_aleph0

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
@[deprecated ord (since := "2026-02-27")]
/-
**Cardinal.ord.orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal.ord`。
形式化陈述：Cardinal.{u_1} ↪o Ordinal.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular fu
nction, see `ord`.
-/
def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  OrderEmbedding.ofStrictMono _ fun _ _ ↦ Cardinal.ord_lt_ord.2

@[deprecated ord (since := "2026-02-27")]
/-
**Cardinal.ord.orderEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.ord`。
形式化陈述：⇑Cardinal.ord.orderEmbedding = Cardinal.ord
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ord.orderEmbedding_coe : (ord.orderEmbedding : Cardinal → Ordinal) = ord :=
  rfl
/-
**Cardinal.nonempty_ord_toType** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：nonempty_ord_toType {c : Cardinal} (h : c != 0) : Nonempty c.ord.ToType
参数：h : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.nonempty_toType_iff`：nonempty_toType_iff {o : Ordinal} : Nonempt
y o.ToType ↔ o != 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Cardinal.ord_eq_zero`：ord_eq_zero {a : Cardinal} : a.ord = 0 ↔ a = 0
-/
lemma nonempty_ord_toType {c : Cardinal} (h : c ≠ 0) :
    Nonempty c.ord.ToType := by
  rwa [Ordinal.nonempty_toType_iff, ne_eq, ord_eq_zero]

end Cardinal

namespace Ordinal

@[simp]
/-
**Ordinal.nat_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nat_le_card {o} {n : Nat} : (n : Cardinal) <= card o ↔ (n : Ordinal) <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Cardinal.ord_natCast`：ord_natCast (n : Nat) : ord n = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o := by
  rw [← Cardinal.ord_le, Cardinal.ord_natCast]

@[simp]
/-
**Ordinal.one_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_le_card {o} : 1 <= card o ↔ 1 <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.nat_le_card`：nat_le_card {o} {n : Nat} : (n : Cardinal) <= card 
o ↔ (n : Ordinal) <= o
-/
theorem one_le_card {o} : 1 ≤ card o ↔ 1 ≤ o := by
  simpa using nat_le_card (n := 1)

@[simp]
/-
**Ordinal.ofNat_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：ofNat_le_card {o} {n : Nat} [n.AtLeastTwo] : (ofNat(n) : Cardinal) <= card
 o ↔ (OfNat.ofNat n : Ordinal) <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nat_le_card`：nat_le_card {o} {n : Nat} : (n : Cardinal) <= card 
o ↔ (n : Ordinal) <= o
-/
theorem ofNat_le_card {o} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) ≤ card o ↔ (OfNat.ofNat n : Ordinal) ≤ o :=
  nat_le_card

@[simp]
/-
**Ordinal.aleph0_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.ord_le`：ord_le {c o} : ord c <= o ↔ c <= o.card
· 使用定理 `Cardinal.ord_aleph0`：ord_aleph0 : ord.{u} ℵ₀ = ω
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem aleph0_le_card {o} : ℵ₀ ≤ card o ↔ ω ≤ o := by
  rw [← ord_le, ord_aleph0]

@[simp]
/-
**Ordinal.card_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_lt_aleph0 {o} : card o < ℵ₀ ↔ o < ω
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Ordinal.aleph0_le_card`：aleph0_le_card {o} : ℵ₀ <= card o ↔ ω <= o
-/
theorem card_lt_aleph0 {o} : card o < ℵ₀ ↔ o < ω :=
  le_iff_le_iff_lt_iff_lt.1 aleph0_le_card

@[simp]
/-
**Ordinal.nat_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nat_lt_card {o} {n : Nat} : (n : Cardinal) < card o ↔ (n : Ordinal) < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.natCast_add_one_le_iff`：natCast_add_one_le_iff {n : Nat} {c : C
ardinal} : n + 1 <= c ↔ n < c
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Ordinal.nat_le_card`：nat_le_card {o} {n : Nat} : (n : Cardinal) <= card 
o ↔ (n : Ordinal) <= o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o := by
  rw [← natCast_add_one_le_iff, ← succ_le_iff, ← Nat.cast_add_one, nat_le_card]
  rfl

@[simp]
/-
**Ordinal.zero_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_lt_card {o} : 0 < card o ↔ 0 < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.nat_lt_card`：nat_lt_card {o} {n : Nat} : (n : Cardinal) < card o
 ↔ (n : Ordinal) < o
-/
theorem zero_lt_card {o} : 0 < card o ↔ 0 < o := by
  simpa using nat_lt_card (n := 0)

@[simp]
/-
**Ordinal.one_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_lt_card {o} : 1 < card o ↔ 1 < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.nat_lt_card`：nat_lt_card {o} {n : Nat} : (n : Cardinal) < card o
 ↔ (n : Ordinal) < o
-/
theorem one_lt_card {o} : 1 < card o ↔ 1 < o := by
  simpa using nat_lt_card (n := 1)

@[simp]
/-
**Ordinal.ofNat_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：ofNat_lt_card {o} {n : Nat} [n.AtLeastTwo] : (ofNat(n) : Cardinal) < card 
o ↔ (OfNat.ofNat n : Ordinal) < o
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nat_lt_card`：nat_lt_card {o} {n : Nat} : (n : Cardinal) < card o
 ↔ (n : Ordinal) < o
-/
theorem ofNat_lt_card {o} {n : ℕ} [n.AtLeastTwo] :
    (ofNat(n) : Cardinal) < card o ↔ (OfNat.ofNat n : Ordinal) < o :=
  nat_lt_card

@[simp]
/-
**Ordinal.card_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_lt_nat {o} {n : Nat} : card o < n ↔ o < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Ordinal.nat_le_card`：nat_le_card {o} {n : Nat} : (n : Cardinal) <= card 
o ↔ (n : Ordinal) <= o
-/
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp]
/-
**Ordinal.card_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_lt_ofNat {o} {n : Nat} [n.AtLeastTwo] : card o < ofNat(n) ↔ o < OfNat
.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_lt_nat`：card_lt_nat {o} {n : Nat} : card o < n ↔ o < n
-/
theorem card_lt_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o < ofNat(n) ↔ o < OfNat.ofNat n :=
  card_lt_nat

@[simp]
/-
**Ordinal.card_le_nat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_le_nat {o} {n : Nat} : card o <= n ↔ o <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Ordinal.nat_lt_card`：nat_lt_card {o} {n : Nat} : (n : Cardinal) < card o
 ↔ (n : Ordinal) < o
-/
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
/-
**Ordinal.card_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_le_one {o} : card o <= 1 ↔ o <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.card_le_nat`：card_le_nat {o} {n : Nat} : card o <= n ↔ o <= n
-/
theorem card_le_one {o} : card o ≤ 1 ↔ o ≤ 1 := by
  simpa using card_le_nat (n := 1)

@[simp]
/-
**Ordinal.card_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_le_ofNat {o} {n : Nat} [n.AtLeastTwo] : card o <= ofNat(n) ↔ o <= OfN
at.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_le_nat`：card_le_nat {o} {n : Nat} : card o <= n ↔ o <= n
-/
theorem card_le_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o ≤ ofNat(n) ↔ o ≤ OfNat.ofNat n :=
  card_le_nat

@[simp]
/-
**Ordinal.card_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_eq_nat {o} {n : Nat} : card o = n ↔ o = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n := by
  simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp]
/-
**Ordinal.card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_eq_zero {o} : card o = 0 ↔ o = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.card_eq_nat`：card_eq_nat {o} {n : Nat} : card o = n ↔ o = n
-/
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 := by
  simpa using card_eq_nat (n := 0)

@[simp]
/-
**Ordinal.card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_eq_one {o} : card o = 1 ↔ o = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.card_eq_nat`：card_eq_nat {o} {n : Nat} : card o = n ↔ o = n
-/
theorem card_eq_one {o} : card o = 1 ↔ o = 1 := by
  simpa using card_eq_nat (n := 1)
/-
**Ordinal._root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命
名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cardinal.le_ord_iff_card_le_of_lt_aleph0 (o : Ordinal) {c : Cardinal} (hc : c < ℵ₀) :
    o ≤ c.ord ↔ o.card ≤ c := by
  rcases lt_aleph0.mp hc with ⟨n, rfl⟩
  simp
/-
**Ordinal.mem_range_lift_of_card_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_lift_of_card_le {a : Cardinal.{u}} {b : Ordinal.{max u v}} (h : 
card b <= Cardinal.lift.{v, u} a) : b in Set.range lift.{v, u}
参数：h : card b <= Cardinal.lift.{v, u} a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.mem_range_lift_of_le`：mem_range_lift_of_le {a : Ordinal.{u}} {b 
: Ordinal.{max u v}} (h : b <= lift.{v} a) : b in Set.range lift.{v}
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ord`：lift_ord (c) : Ordinal.lift.{u, v} (ord c) = ord (lif
t.{u, v} c)
· 使用定理 `Cardinal.lift_succ`：lift_succ (a) : lift.{v, u} (succ a) = succ (lift.{v
, u} a)
· 使用定理 `Cardinal.card_le_iff`：card_le_iff {o : Ordinal} {c : Cardinal} : o.card 
<= c ↔ o < (succ c).ord
-/
theorem mem_range_lift_of_card_le {a : Cardinal.{u}} {b : Ordinal.{max u v}}
    (h : card b ≤ Cardinal.lift.{v, u} a) : b ∈ Set.range lift.{v, u} := by
  rw [card_le_iff, ← lift_succ, ← lift_ord] at h
  exact mem_range_lift_of_le h.le

@[simp]
/-
**Ordinal.card_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_eq_ofNat {o} {n : Nat} [n.AtLeastTwo] : card o = ofNat(n) ↔ o = OfNat
.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.card_eq_nat`：card_eq_nat {o} {n : Nat} : card o = n ↔ o = n
-/
theorem card_eq_ofNat {o} {n : ℕ} [n.AtLeastTwo] :
    card o = ofNat(n) ↔ o = OfNat.ofNat n :=
  card_eq_nat

variable (r) in
@[simp]
/-
**Ordinal.type_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_fintype [IsWellOrder α r] [Fintype α] : type r = Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.card_eq_nat`：card_eq_nat {o} {n : Nat} : card o = n ↔ o = n
· 使用定理 `Ordinal.card_type`：card_type (r : α -> α -> Prop) [IsWellOrder α r] : ca
rd (type r) = #α
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
-/
theorem type_fintype [IsWellOrder α r] [Fintype α] :
    type r = Fintype.card α := by rw [← card_eq_nat, card_type, mk_fintype]
/-
**Ordinal.type_fin** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_fin (n : Nat) : typeLT (Fin n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.type_fintype`：type_fintype [IsWellOrder α r] [Fintype α] : type 
r = Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem type_fin (n : ℕ) : typeLT (Fin n) = n := by simp

variable (r) in
/-
**Ordinal.ord_mk_le_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：ord_mk_le_type [IsWellOrder α r] (s : Set α) : (#s).ord <= type r
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.ord_le_type`：ord_le_type (r : α -> α -> Prop) [h : IsWellOrder 
α r] : ord #α <= type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_le_ord`：ord_le_ord {c₁ c₂} : ord c₁ <= ord c₂ ↔ c₁ <= c₂
· 使用定理 `Cardinal.le_mk_iff_exists_set`：le_mk_iff_exists_set {c : Cardinal} {α : 
Type u} : c <= #α ↔ exists p : Set α, #p = c
-/
theorem ord_mk_le_type [IsWellOrder α r] (s : Set α) : (#s).ord ≤ type r := by
  grw [← ord_le_type, ord_le_ord, le_mk_iff_exists_set]
  use s

variable (r) in
/-
**Ordinal.ord_mk_lt_type** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：ord_mk_lt_type [IsWellOrder α r] {s : Set α} (hfin : s.Finite) (h : sᶜ.Non
empty) : (#s).ord < type r
参数：hfin : s.Finite；h : sᶜ.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.ord_le_type`：ord_le_type (r : α -> α -> Prop) [h : IsWellOrder 
α r] : ord #α <= type r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ord_lt_ord`：ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用引理 `Cardinal.card_lt_card_of_left_finite`：card_lt_card_of_left_finite {A B :
 Set α} (hfin : A.Finite) (hlt : A ⊂ B) : #A < #B
· 使用定理 `Set.Nonempty.ssubset_univ`：∀ {α : Type u} {s : Set α}, sᶜ.Nonempty → s ⊂
 Set.univ
-/
theorem ord_mk_lt_type [IsWellOrder α r] {s : Set α} (hfin : s.Finite) (h : sᶜ.Nonempty) :
    (#s).ord < type r := by
  grw [← ord_le_type, ord_lt_ord, ← mk_univ (α := α)]
  exact card_lt_card_of_left_finite hfin h.ssubset_univ

variable (r) in
/-- The `#s`-th element of `α` is an upper-bound for the set's mex (minimum excluded value),
ordered by `r`, when `s` is finite. See `card_typein_min_le_mk` for the `Ordinal` version. -/
/-
**Ordinal.not_lt_enum_ord_mk_min_compl** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_lt_enum_ord_mk_min_compl [IsWellOrder α r] {s : Set α} (hfin : s.Finit
e) (h : sᶜ.Nonempty) : ¬r (enum r ⟨#s |>.ord, ord_mk_lt_type r hfin h⟩) (IsWellF
ounded.wf.min (r
参数：hfin : s.Finite；h : sᶜ.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.ord_mk_lt_type`：ord_mk_lt_type [IsWellOrder α r] {s : Set α} (hf
in : s.Finite) (h : sᶜ.Nonempty) : (#s).ord < type r
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.typein_le_typein`：typein_le_typein (r : α -> α -> Prop) [IsWellO
rder α r] {a b : α} : typein r a <= typein r b ↔ ¬r b a
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Cardinal.le_ord_iff_card_le_of_lt_aleph0`：∀ (o : Ordinal.{u_1}) {c : Car
dinal.{u_1}}, c < Cardinal.aleph0 → (o ≤ c.ord ↔ o.card ≤ c)
· 使用定理 `Set.Finite.lt_aleph0`：∀ {α : Type u} {S : Set α}, S.Finite → Cardinal.mk
 ↑S < Cardinal.aleph0
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Ordinal.card_typein_min_le_mk`：card_typein_min_le_mk [IsWellOrder α r] {
s : Set α} (hs : sᶜ.Nonempty) : (typein r <| IsWellFounded.wf.min (r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The `#s`-th element of `α` is an upper-bound for the set's mex (minimum excluded
 value),
ordered by `r`, when `s` is finite. See `card_typein_min_le_mk` for the `Ordinal
` version.
-/
theorem not_lt_enum_ord_mk_min_compl [IsWellOrder α r] {s : Set α} (hfin : s.Finite)
    (h : sᶜ.Nonempty) :
    ¬r (enum r ⟨#s |>.ord, ord_mk_lt_type r hfin h⟩) (IsWellFounded.wf.min (r := r) sᶜ h) := by
  grw [← typein_le_typein, typein_enum, Cardinal.le_ord_iff_card_le_of_lt_aleph0 _ hfin.lt_aleph0,
    card_typein_min_le_mk]

end Ordinal

/-! ### Sorted lists -/

/-
**List.SortedGT.lt_ord_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.SortedGT.lt_ord_of_lt [LinearOrder α] [WellFoundedLT α] {l m : List α
} {o : Ordinal} (hl : l.SortedGT) (hm : m.SortedGT) (hmltl : m < l) (hlt : foral
l i in l, Ordinal.typein (α
参数：hl : l.SortedGT；hm : m.SortedGT；hmltl : m < l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head_le_of_lt`：head_le_of_lt [Preorder α] {a a' : α} {l l' : List α
} (h : (a' :: l') < (a :: l)) : a' <= a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `List.rel_of_pairwise_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α 
→ α → Prop}, List.Pairwise R (a :: l) → ∀ {a' : α}, a' ∈ l → R a a'
· 使用定理 `List.SortedGT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGT → List.Pairwise (fun x1 x2 => x1 > x2) l
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l

--- 原说明 ---
### Sorted lists
-/
theorem List.SortedGT.lt_ord_of_lt [LinearOrder α] [WellFoundedLT α] {l m : List α}
    {o : Ordinal} (hl : l.SortedGT) (hm : m.SortedGT) (hmltl : m < l)
    (hlt : ∀ i ∈ l, Ordinal.typein (α := α) (· < ·) i < o) :
      ∀ i ∈ m, Ordinal.typein (α := α) (· < ·) i < o := by
  replace hmltl : List.Lex (· < ·) m l := hmltl
  cases l with
  | nil => simp at hmltl
  | cons a as =>
    cases m with
    | nil => intro i hi; simp at hi
    | cons b bs =>
      intro i hi
      suffices h : i ≤ a by refine lt_of_le_of_lt ?_ (hlt a mem_cons_self); simpa
      cases hi with
      | head as => exact List.head_le_of_lt hmltl
      | tail b hi => exact le_of_lt (lt_of_lt_of_le (List.rel_of_pairwise_cons hm.pairwise hi)
          (List.head_le_of_lt hmltl))
