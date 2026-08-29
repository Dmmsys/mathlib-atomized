/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Tactic.ApplyFun

/-!
# Symmetric powers

This file defines symmetric powers of a type. The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `Data.Sym.Sym2`.

TODO: This was created as supporting material for `Sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

@[expose] public section

assert_not_exists MonoidWithZero
open List (Vector)
open Function

/--
Definition of `Sym` / `Sym` 的定义

English:
definition Sym
  signature: (α : Type*) (n : Nat)
  body: { s : Multiset α // Multiset.card s = n }
deriving [DecidableEq α] -> DecidableEq _

中文:
定义 Sym
  签名: (α : 类型) (n : 自然数)
  定义体: { s : Multiset α // Multiset.card s = n }
deriving [DecidableEq α] -> DecidableEq _

Depends on / 依赖: Multiset, Multiset.card
-/
def Sym (α : Type*) (n : Nat) :=
  { s : Multiset α // Multiset.card s = n }
deriving [DecidableEq α] -> DecidableEq _

/--
Definition of `Sym.toMultiset` / `Sym.toMultiset` 的定义

English:
definition Sym.toMultiset
  signature: {α : Type*} {n : Nat} (s : Sym α n)
  body: s.1

中文:
定义 Sym.toMultiset
  签名: {α : 类型} {n : 自然数} (s : Sym α n)
  定义体: s.1
-/
@[coe] def Sym.toMultiset {α : Type*} {n : Nat} (s : Sym α n) : Multiset α :=
  s.1

/--
Instance `Sym.hasCoe` / 实例 `Sym.hasCoe`

English:
instance Sym.hasCoe
  signature: (α : Type*) (n : Nat)
  body: ⟨Sym.toMultiset⟩

中文:
实例 Sym.hasCoe
  签名: (α : 类型) (n : 自然数)
  定义体: ⟨Sym.toMultiset⟩

Depends on / 依赖: Sym.toMultiset, toMultiset
-/
instance Sym.hasCoe (α : Type*) (n : Nat) : CoeOut (Sym α n) (Multiset α) :=
  ⟨Sym.toMultiset⟩

/--
Definition of `List.Vector.Perm.isSetoid` / `List.Vector.Perm.isSetoid` 的定义

English:
abbreviation List.Vector.Perm.isSetoid
  signature: (α : Type*) (n : Nat)
  body: (List.isSetoid α).comap Subtype.val

中文:
缩写 列表.Vector.置换.isSetoid
  签名: (α : 类型) (n : 自然数)
  定义体: (List.isSetoid α).comap Subtype.val

Depends on / 依赖: List.isSetoid, Subtype, Subtype.val, isSetoid
-/
abbrev List.Vector.Perm.isSetoid (α : Type*) (n : Nat) : Setoid (Vector α n) :=
  (List.isSetoid α).comap Subtype.val

attribute [local instance] Vector.Perm.isSetoid

-- Copy over the `DecidableRel` instance across the definition.
-- (Although `List.Vector.Perm.isSetoid` is an `abbrev`, `List.isSetoid` is not.)
instance {α : Type*} {n : Nat} [DecidableEq α] :
    DecidableRel (· ≈ · : List.Vector α n -> List.Vector α n -> Prop) :=
  fun _ _ => List.decidablePerm _ _

namespace Sym

variable {α β : Type*} {n n' m : Nat} {s : Sym α n} {a b : α}

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Sym α n -> Multiset α)
  proof: Subtype.coe_injective

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: 单射 ((↑) : Sym α n -> Multiset α)
  证明: Subtype.coe_injective

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : Sym α n -> Multiset α) :=
  Subtype.coe_injective

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {s₁ s₂ : Sym α n}
  statement: (s₁ : Multiset α) = s₂ ↔ s₁ = s₂
  proof: coe_injective.eq_iff

中文:
定理 coe_inj
  条件: {s₁ s₂ : Sym α n}
  结论: (s₁ : Multiset α) = s₂ ↔ s₁ = s₂
  证明: coe_injective.eq_iff

Depends on / 依赖: coe_injective, coe_injective.eq_iff, eq_iff
-/
theorem coe_inj {s₁ s₂ : Sym α n} : (s₁ : Multiset α) = s₂ ↔ s₁ = s₂ :=
  coe_injective.eq_iff

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s₁ s₂ : Sym α n} (h : (s₁ : Multiset α) = ↑s₂)
  statement: s₁ = s₂
  proof: coe_injective h

@[simp]

中文:
定理 ext
  条件: {s₁ s₂ : Sym α n} (h : (s₁ : Multiset α) = ↑s₂)
  结论: s₁ = s₂
  证明: coe_injective h

@[simp]
-/
@[ext] theorem ext {s₁ s₂ : Sym α n} (h : (s₁ : Multiset α) = ↑s₂) : s₁ = s₂ :=
  coe_injective h

@[simp]
/--
theorem `val_eq_coe` / 定理 `val_eq_coe`

English:
theorem val_eq_coe
  given: (s : Sym α n)
  statement: s.1 = ↑s
  proof: rfl

中文:
定理 val_eq_coe
  条件: (s : Sym α n)
  结论: s.1 = ↑s
  证明: rfl
-/
theorem val_eq_coe (s : Sym α n) : s.1 = ↑s :=
  rfl

/-- Construct an element of the `n`th symmetric power from a multiset of cardinality `n`.
-/
@[match_pattern]
/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (m : Multiset α) (h : Multiset.card m = n)
  body: ⟨m, h⟩

中文:
缩写 mk
  签名: (m : Multiset α) (h : Multiset.card m = n)
  定义体: ⟨m, h⟩
-/
abbrev mk (m : Multiset α) (h : Multiset.card m = n) : Sym α n :=
  ⟨m, h⟩

/-- The unique element in `Sym α 0`. -/
@[match_pattern]
/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : Sym α 0
  body: ⟨0, Multiset.card_zero⟩

@[simp]

中文:
定义 nil
  签名: : Sym α 0
  定义体: ⟨0, Multiset.card_zero⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.card_zero, card_zero
-/
def nil : Sym α 0 :=
  ⟨0, Multiset.card_zero⟩

@[simp]
/--
theorem `coe_nil` / 定理 `coe_nil`

English:
theorem coe_nil
  statement: ↑(@Sym.nil α) = (0 : Multiset α)
  proof: rfl

中文:
定理 coe_nil
  结论: ↑(@Sym.nil α) = (0 : Multiset α)
  证明: rfl
-/
theorem coe_nil : ↑(@Sym.nil α) = (0 : Multiset α) :=
  rfl

/-- Inserts an element into the term of `Sym α n`, increasing the length by one.
-/
@[match_pattern]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α) (s : Sym α n)
  body: ⟨a ::ₘ s.1, by rw [Multiset.card_cons, s.2]⟩

@[inherit_doc]
infixr:67 " ::ₛ " => cons

@[simp]

中文:
定义 cons
  签名: (a : α) (s : Sym α n)
  定义体: ⟨a ::ₘ s.1, by rw [Multiset.card_cons, s.2]⟩

@[inherit_doc]
infixr:67 " ::ₛ " => cons

@[simp]

Depends on / 依赖: Multiset, Multiset.card_cons, card_cons
-/
def cons (a : α) (s : Sym α n) : Sym α n.succ :=
  ⟨a ::ₘ s.1, by rw [Multiset.card_cons, s.2]⟩

@[inherit_doc]
infixr:67 " ::ₛ " => cons

@[simp]
/--
theorem `cons_inj_right` / 定理 `cons_inj_right`

English:
theorem cons_inj_right
  given: (a : α) (s s' : Sym α n)
  statement: a ::ₛ s = a ::ₛ s' ↔ s = s'
  proof: Subtype.ext_iff.trans (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm

@[simp]

中文:
定理 cons_inj_right
  条件: (a : α) (s s' : Sym α n)
  结论: a ::ₛ s = a ::ₛ s' ↔ s = s'
  证明: Subtype.ext_iff.trans (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm

@[simp]

Depends on / 依赖: Multiset, Multiset.cons_inj_right, Subtype, Subtype.ext_iff.symm, Subtype.ext_iff.trans, cons_inj_right, ext_iff
-/
theorem cons_inj_right (a : α) (s s' : Sym α n) : a ::ₛ s = a ::ₛ s' ↔ s = s' :=
Subtype.ext_iff.trans (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm

@[simp]
/--
theorem `cons_inj_left` / 定理 `cons_inj_left`

English:
theorem cons_inj_left
  given: (a a' : α) (s : Sym α n)
  statement: a ::ₛ s = a' ::ₛ s ↔ a = a'
  proof: Subtype.ext_iff.trans Multiset.cons_inj_left _

中文:
定理 cons_inj_left
  条件: (a a' : α) (s : Sym α n)
  结论: a ::ₛ s = a' ::ₛ s ↔ a = a'
  证明: Subtype.ext_iff.trans Multiset.cons_inj_left _

Depends on / 依赖: Multiset, Multiset.cons_inj_left, Subtype, Subtype.ext_iff.trans, cons_inj_left, ext_iff
-/
theorem cons_inj_left (a a' : α) (s : Sym α n) : a ::ₛ s = a' ::ₛ s ↔ a = a' :=
Subtype.ext_iff.trans Multiset.cons_inj_left _

/--
theorem `cons_swap` / 定理 `cons_swap`

English:
theorem cons_swap
  given: (a b : α) (s : Sym α n)
  statement: a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s
  proof: Subtype.ext Multiset.cons_swap a b s.1

中文:
定理 cons_swap
  条件: (a b : α) (s : Sym α n)
  结论: a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s
  证明: Subtype.ext Multiset.cons_swap a b s.1

Depends on / 依赖: Multiset, Multiset.cons_swap, Subtype, Subtype.ext, cons_swap
-/
theorem cons_swap (a b : α) (s : Sym α n) : a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s :=
Subtype.ext Multiset.cons_swap a b s.1

/--
theorem `coe_cons` / 定理 `coe_cons`

English:
theorem coe_cons
  given: (s : Sym α n) (a : α)
  statement: (a ::ₛ s : Multiset α) = a ::ₘ s
  proof: rfl

中文:
定理 coe_cons
  条件: (s : Sym α n) (a : α)
  结论: (a ::ₛ s : Multiset α) = a ::ₘ s
  证明: rfl
-/
theorem coe_cons (s : Sym α n) (a : α) : (a ::ₛ s : Multiset α) = a ::ₘ s :=
  rfl

/--
Definition of `ofVector` / `ofVector` 的定义

English:
definition ofVector
  signature: : List.Vector α n -> Sym α n
  body: fun x => ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

中文:
定义 ofVector
  签名: : 列表.Vector α n -> Sym α n
  定义体: fun x => ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

Depends on / 依赖: Multiset, Multiset.coe_card, coe_card, x.val
-/
def ofVector : List.Vector α n -> Sym α n :=
  fun x => ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (List.Vector α n) (Sym α n)
  body: ofVector x

@[simp]

中文:
实例 :
  签名: Coe (列表.Vector α n) (Sym α n)
  定义体: ofVector x

@[simp]

Depends on / 依赖: ofVector
-/
instance : Coe (List.Vector α n) (Sym α n) where coe x := ofVector x

@[simp]
/--
theorem `ofVector_nil` / 定理 `ofVector_nil`

English:
theorem ofVector_nil
  statement: ↑(Vector.nil : List.Vector α 0) = (Sym.nil : Sym α 0)
  proof: rfl

@[simp]

中文:
定理 ofVector_nil
  结论: ↑(Vector.nil : 列表.Vector α 0) = (Sym.nil : Sym α 0)
  证明: rfl

@[simp]
-/
theorem ofVector_nil : ↑(Vector.nil : List.Vector α 0) = (Sym.nil : Sym α 0) :=
  rfl

@[simp]
/--
theorem `ofVector_cons` / 定理 `ofVector_cons`

English:
theorem ofVector_cons
  given: (a : α) (v : List.Vector α n)
  proof: by
  cases v
  rfl

@[simp]

中文:
定理 ofVector_cons
  条件: (a : α) (v : 列表.Vector α n)
  证明: by
  cases v
  rfl

@[simp]
-/
theorem ofVector_cons (a : α) (v : List.Vector α n) :
    ↑(Vector.cons a v) = a ::ₛ (↑v : Sym α n) := by
  cases v
  rfl

@[simp]
/--
theorem `card_coe` / 定理 `card_coe`

English:
theorem card_coe
  statement: Multiset.card (s : Multiset α) = n
  proof: s.prop

中文:
定理 card_coe
  结论: Multiset.card (s : Multiset α) = n
  证明: s.prop

Depends on / 依赖: s.prop
-/
theorem card_coe : Multiset.card (s : Multiset α) = n := s.prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Sym α n)
  body: ⟨fun s a => a in s.1⟩

中文:
实例 :
  签名: Membership α (Sym α n)
  定义体: ⟨fun s a => a in s.1⟩
-/
instance : Membership α (Sym α n) :=
  ⟨fun s a => a in s.1⟩

/--
Instance `decidableMem` / 实例 `decidableMem`

English:
instance decidableMem
  signature: [DecidableEq α] (a : α) (s : Sym α n)
  body: s.1.decidableMem _

中文:
实例 decidableMem
  签名: [DecidableEq α] (a : α) (s : Sym α n)
  定义体: s.1.decidableMem _

Depends on / 依赖: decidableMem
-/
instance decidableMem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a in s) :=
  s.1.decidableMem _

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (s : Multiset α) (h : Multiset.card s = n)
  statement: mk s h = s
  proof: rfl

@[simp]

中文:
引理 coe_mk
  条件: (s : Multiset α) (h : Multiset.card s = n)
  结论: mk s h = s
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_mk (s : Multiset α) (h : Multiset.card s = n) : mk s h = s := rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: (a : α) (s : Multiset α) (h : Multiset.card s = n)
  statement: a in mk s h ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: (a : α) (s : Multiset α) (h : Multiset.card s = n)
  结论: a in mk s h ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk (a : α) (s : Multiset α) (h : Multiset.card s = n) : a in mk s h ↔ a in s :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : Sym α n -> Prop}
  proof: by
  simp [Sym]

中文:
引理 «对任意»
  条件: {p : Sym α n -> 命题}
  证明: by
  simp [Sym]
-/
lemma «forall» {p : Sym α n -> Prop} :
    (forall s : Sym α n, p s) ↔ forall (s : Multiset α) (hs : Multiset.card s = n), p (Sym.mk s hs) := by
  simp [Sym]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : Sym α n -> Prop}
  proof: by
  simp [Sym]

@[simp]

中文:
引理 «存在»
  条件: {p : Sym α n -> 命题}
  证明: by
  simp [Sym]

@[simp]
-/
lemma «exists» {p : Sym α n -> Prop} :
    (exists s : Sym α n, p s) ↔ exists (s : Multiset α) (hs : Multiset.card s = n), p (Sym.mk s hs) := by
  simp [Sym]

@[simp]
/--
theorem `notMem_nil` / 定理 `notMem_nil`

English:
theorem notMem_nil
  given: (a : α)
  statement: a ∉ (nil : Sym α 0)
  proof: Multiset.notMem_zero a

@[simp]

中文:
定理 notMem_nil
  条件: (a : α)
  结论: a ∉ (nil : Sym α 0)
  证明: Multiset.notMem_zero a

@[simp]

Depends on / 依赖: Multiset, Multiset.notMem_zero, notMem_zero
-/
theorem notMem_nil (a : α) : a ∉ (nil : Sym α 0) :=
  Multiset.notMem_zero a

@[simp]
/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  statement: a in b ::ₛ s ↔ a = b ∨ a in s
  proof: Multiset.mem_cons

@[simp]

中文:
定理 mem_cons
  结论: a in b ::ₛ s ↔ a = b ∨ a in s
  证明: Multiset.mem_cons

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_cons, mem_cons
-/
theorem mem_cons : a in b ::ₛ s ↔ a = b ∨ a in s :=
  Multiset.mem_cons

@[simp]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  statement: a in (s : Multiset α) ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_coe
  结论: a in (s : Multiset α) ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe : a in (s : Multiset α) ↔ a in s :=
  Iff.rfl

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: (h : a in s)
  statement: a in b ::ₛ s
  proof: Multiset.mem_cons_of_mem h

中文:
定理 mem_cons_of_mem
  条件: (h : a in s)
  结论: a in b ::ₛ s
  证明: Multiset.mem_cons_of_mem h

Depends on / 依赖: Multiset, Multiset.mem_cons_of_mem, mem_cons_of_mem
-/
theorem mem_cons_of_mem (h : a in s) : a in b ::ₛ s :=
  Multiset.mem_cons_of_mem h

/--
theorem `mem_cons_self` / 定理 `mem_cons_self`

English:
theorem mem_cons_self
  given: (a : α) (s : Sym α n)
  statement: a in a ::ₛ s
  proof: Multiset.mem_cons_self a s.1

中文:
定理 mem_cons_self
  条件: (a : α) (s : Sym α n)
  结论: a in a ::ₛ s
  证明: Multiset.mem_cons_self a s.1

Depends on / 依赖: Multiset, Multiset.mem_cons_self, mem_cons_self
-/
theorem mem_cons_self (a : α) (s : Sym α n) : a in a ::ₛ s :=
  Multiset.mem_cons_self a s.1

/--
theorem `cons_of_coe_eq` / 定理 `cons_of_coe_eq`

English:
theorem cons_of_coe_eq
  given: (a : α) (v : List.Vector α n)
  statement: a ::ₛ (↑v : Sym α n) = ↑(a ::ᵥ v)
  proof: Subtype.ext by
    cases v
    rfl

中文:
定理 cons_of_coe_eq
  条件: (a : α) (v : 列表.Vector α n)
  结论: a ::ₛ (↑v : Sym α n) = ↑(a ::ᵥ v)
  证明: Subtype.ext by
    cases v
    rfl

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem cons_of_coe_eq (a : α) (v : List.Vector α n) : a ::ₛ (↑v : Sym α n) = ↑(a ::ᵥ v) :=
Subtype.ext by
    cases v
    rfl

open scoped List in
/--
theorem `sound` / 定理 `sound`

English:
theorem sound
  given: {a b : List.Vector α n} (h : a.val ~ b.val)
  statement: (↑a : Sym α n) = ↑b
  proof: Subtype.ext Quotient.sound h

中文:
定理 sound
  条件: {a b : 列表.Vector α n} (h : a.val ~ b.val)
  结论: (↑a : Sym α n) = ↑b
  证明: Subtype.ext Quotient.sound h

Depends on / 依赖: Quotient, Quotient.sound, Subtype, Subtype.ext
-/
theorem sound {a b : List.Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b :=
Subtype.ext Quotient.sound h

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a in s)
  body: ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans s.property.symm ▸ n.pred_succ⟩

@[simp]

中文:
定义 erase
  签名: [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a in s)
  定义体: ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans s.property.symm ▸ n.pred_succ⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.card_erase_of_mem, card_erase_of_mem, n.pred_succ, pred_succ, property, s.property.symm, s.val.erase
-/
def erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a in s) : Sym α n :=
⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans s.property.symm ▸ n.pred_succ⟩

@[simp]
/--
theorem `erase_mk` / 定理 `erase_mk`

English:
theorem erase_mk
  statement: [DecidableEq α] (m : Multiset α)
  proof: rfl

@[simp]

中文:
定理 erase_mk
  结论: [DecidableEq α] (m : Multiset α)
  证明: rfl

@[simp]
-/
theorem erase_mk [DecidableEq α] (m : Multiset α)
    (hc : Multiset.card m = n + 1) (a : α) (h : a in m) :
    (mk m hc).erase a h = mk (m.erase a)
        (by rw [Multiset.card_erase_of_mem h, hc, Nat.add_one, Nat.pred_succ]) :=
  rfl

@[simp]
/--
theorem `coe_erase` / 定理 `coe_erase`

English:
theorem coe_erase
  given: [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s)
  proof: rfl

@[simp]

中文:
定理 coe_erase
  条件: [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s)
  证明: rfl

@[simp]
-/
theorem coe_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s) :
    (s.erase a h : Multiset α) = Multiset.erase s a :=
  rfl

@[simp]
/--
theorem `cons_erase` / 定理 `cons_erase`

English:
theorem cons_erase
  given: [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s)
  statement: a ::ₛ s.erase a h = s
  proof: coe_injective Multiset.cons_erase h

@[simp]

中文:
定理 cons_erase
  条件: [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s)
  结论: a ::ₛ s.erase a h = s
  证明: coe_injective Multiset.cons_erase h

@[simp]

Depends on / 依赖: Multiset, Multiset.cons_erase, coe_injective, cons_erase
-/
theorem cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s) : a ::ₛ s.erase a h = s :=
coe_injective Multiset.cons_erase h

@[simp]
/--
theorem `erase_cons_head` / 定理 `erase_cons_head`

English:
theorem erase_cons_head
  statement: [DecidableEq α] (s : Sym α n) (a : α)
  proof: coe_injective Multiset.erase_cons_head a s.1

中文:
定理 erase_cons_head
  结论: [DecidableEq α] (s : Sym α n) (a : α)
  证明: coe_injective Multiset.erase_cons_head a s.1

Depends on / 依赖: mem_cons_self
-/
theorem erase_cons_head [DecidableEq α] (s : Sym α n) (a : α)
    (h : a in a ::ₛ s := mem_cons_self a s) : (a ::ₛ s).erase a h = s :=
coe_injective Multiset.erase_cons_head a s.1

/--
Definition of `Sym'` / `Sym'` 的定义

English:
definition Sym'
  signature: (α : Type*) (n : Nat)
  body: Quotient (Vector.Perm.isSetoid α n)

中文:
定义 Sym'
  签名: (α : 类型) (n : 自然数)
  定义体: Quotient (Vector.Perm.isSetoid α n)

Depends on / 依赖: Quotient, Vector, Vector.Perm.isSetoid, isSetoid
-/
def Sym' (α : Type*) (n : Nat) :=
  Quotient (Vector.Perm.isSetoid α n)

/--
Definition of `cons'` / `cons'` 的定义

English:
definition cons'
  signature: {α : Type*} {n : Nat}
  body: fun a =>
  Quotient.map (Vector.cons a) fun ⟨_, _⟩ ⟨_, _⟩ h => List.Perm.cons _ h

@[inherit_doc]
scoped notation a " :: " b => cons' a b

中文:
定义 cons'
  签名: {α : 类型} {n : 自然数}
  定义体: fun a =>
  Quotient.map (Vector.cons a) fun ⟨_, _⟩ ⟨_, _⟩ h => List.Perm.cons _ h

@[inherit_doc]
scoped notation a " :: " b => cons' a b
-/
def cons' {α : Type*} {n : Nat} : α -> Sym' α n -> Sym' α (Nat.succ n) := fun a =>
  Quotient.map (Vector.cons a) fun ⟨_, _⟩ ⟨_, _⟩ h => List.Perm.cons _ h

@[inherit_doc]
scoped notation a " :: " b => cons' a b

/--
Definition of `symEquivSym'` / `symEquivSym'` 的定义

English:
definition symEquivSym'
  signature: {α : Type*} {n : Nat}
  body: Equiv.subtypeQuotientEquivQuotientSubtype _ _ (fun _ => by rfl) fun _ _ => by rfl

中文:
定义 symEquivSym'
  签名: {α : 类型} {n : 自然数}
  定义体: Equiv.subtypeQuotientEquivQuotientSubtype _ _ (fun _ => by rfl) fun _ _ => by rfl

Depends on / 依赖: Equiv.subtypeQuotientEquivQuotientSubtype, subtypeQuotientEquivQuotientSubtype
-/
def symEquivSym' {α : Type*} {n : Nat} : Sym α n ≃ Sym' α n :=
  Equiv.subtypeQuotientEquivQuotientSubtype _ _ (fun _ => by rfl) fun _ _ => by rfl

/--
theorem `cons_equiv_eq_equiv_cons` / 定理 `cons_equiv_eq_equiv_cons`

English:
theorem cons_equiv_eq_equiv_cons
  given: (α : Type*) (n : Nat) (a : α) (s : Sym α n)
  proof: by
  rcases s with ⟨⟨l⟩, _⟩
  rfl

中文:
定理 cons_equiv_eq_equiv_cons
  条件: (α : 类型) (n : 自然数) (a : α) (s : Sym α n)
  证明: by
  rcases s with ⟨⟨l⟩, _⟩
  rfl
-/
theorem cons_equiv_eq_equiv_cons (α : Type*) (n : Nat) (a : α) (s : Sym α n) :
    (a :: symEquivSym' s) = symEquivSym' (a ::ₛ s) := by
  rcases s with ⟨⟨l⟩, _⟩
  rfl

/--
Instance `instZeroSym` / 实例 `instZeroSym`

English:
instance instZeroSym
  signature: : Zero (Sym α 0)
  body: ⟨⟨0, rfl⟩⟩

中文:
实例 instZeroSym
  签名: : 零 (Sym α 0)
  定义体: ⟨⟨0, rfl⟩⟩

Depends on / 依赖: CommGroup, IsSolvable
-/
instance instZeroSym : Zero (Sym α 0) :=
  ⟨⟨0, rfl⟩⟩

/--
theorem `toMultiset_zero` / 定理 `toMultiset_zero`

English:
theorem toMultiset_zero
  statement: toMultiset (0 : Sym α 0) = 0
  proof: rfl

中文:
定理 toMultiset_zero
  结论: toMultiset (0 : Sym α 0) = 0
  证明: rfl
-/
@[simp] theorem toMultiset_zero : toMultiset (0 : Sym α 0) = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Sym α 0)
  body: ⟨0⟩

中文:
实例 :
  签名: EmptyCollection (Sym α 0)
  定义体: ⟨0⟩
-/
instance : EmptyCollection (Sym α 0) :=
  ⟨0⟩

/--
theorem `eq_nil_of_card_zero` / 定理 `eq_nil_of_card_zero`

English:
theorem eq_nil_of_card_zero
  given: (s : Sym α 0)
  statement: s = nil
  proof: Subtype.ext Multiset.card_eq_zero.1 s.2

中文:
定理 eq_nil_of_card_zero
  条件: (s : Sym α 0)
  结论: s = nil
  证明: Subtype.ext Multiset.card_eq_zero.1 s.2

Depends on / 依赖: IsSolvable, Multiset, Multiset.card_eq_zero, Subsingleton, Subtype, Subtype.ext, card_eq_zero
-/
theorem eq_nil_of_card_zero (s : Sym α 0) : s = nil :=
Subtype.ext Multiset.card_eq_zero.1 s.2

/--
Instance `uniqueZero` / 实例 `uniqueZero`

English:
instance uniqueZero
  signature: : Unique (Sym α 0)
  body: ⟨⟨nil⟩, eq_nil_of_card_zero⟩

中文:
实例 uniqueZero
  签名: : 唯一 (Sym α 0)
  定义体: ⟨⟨nil⟩, eq_nil_of_card_zero⟩

Depends on / 依赖: eq_nil_of_card_zero
-/
instance uniqueZero : Unique (Sym α 0) :=
  ⟨⟨nil⟩, eq_nil_of_card_zero⟩

/--
Definition of `replicate` / `replicate` 的定义

English:
definition replicate
  signature: (n : Nat) (a : α)
  body: ⟨Multiset.replicate n a, Multiset.card_replicate _ _⟩

中文:
定义 replicate
  签名: (n : 自然数) (a : α)
  定义体: ⟨Multiset.replicate n a, Multiset.card_replicate _ _⟩

Depends on / 依赖: Multiset, Multiset.card_replicate, Multiset.replicate, card_replicate, replicate
-/
def replicate (n : Nat) (a : α) : Sym α n :=
  ⟨Multiset.replicate n a, Multiset.card_replicate _ _⟩

/--
theorem `replicate_succ` / 定理 `replicate_succ`

English:
theorem replicate_succ
  given: {a : α} {n : Nat}
  statement: replicate n.succ a = a ::ₛ replicate n a
  proof: rfl

中文:
定理 replicate_succ
  条件: {a : α} {n : 自然数}
  结论: replicate n.succ a = a ::ₛ replicate n a
  证明: rfl

Depends on / 依赖: H.subtype_injective, isSolvable_of_isSolvable_injective, subtype_injective
-/
theorem replicate_succ {a : α} {n : Nat} : replicate n.succ a = a ::ₛ replicate n a :=
  rfl

/--
theorem `coe_replicate` / 定理 `coe_replicate`

English:
theorem coe_replicate
  statement: (replicate n a : Multiset α) = Multiset.replicate n a
  proof: rfl

中文:
定理 coe_replicate
  结论: (replicate n a : Multiset α) = Multiset.replicate n a
  证明: rfl
-/
theorem coe_replicate : (replicate n a : Multiset α) = Multiset.replicate n a :=
  rfl

/--
theorem `val_replicate` / 定理 `val_replicate`

English:
theorem val_replicate
  statement: (replicate n a).val = Multiset.replicate n a
  proof: by
  rw [val_eq_coe]; rw [coe_replicate]

@[simp]

中文:
定理 val_replicate
  结论: (replicate n a).val = Multiset.replicate n a
  证明: by
  rw [val_eq_coe]; rw [coe_replicate]

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, _surjective, coe_replicate, isSolvable_of_surjective, val_eq_coe
-/
theorem val_replicate : (replicate n a).val = Multiset.replicate n a := by
  rw [val_eq_coe]; rw [coe_replicate]

@[simp]
/--
theorem `mem_replicate` / 定理 `mem_replicate`

English:
theorem mem_replicate
  statement: b in replicate n a ↔ n != 0 ∧ b = a
  proof: Multiset.mem_replicate

中文:
定理 mem_replicate
  结论: b in replicate n a ↔ n != 0 ∧ b = a
  证明: Multiset.mem_replicate

Depends on / 依赖: Multiset, Multiset.mem_replicate, mem_replicate
-/
theorem mem_replicate : b in replicate n a ↔ n != 0 ∧ b = a :=
  Multiset.mem_replicate

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_replicate_iff` / 定理 `eq_replicate_iff`

English:
theorem eq_replicate_iff
  statement: s = replicate n a ↔ forall b in s, b = a
  proof: by
  rw [Subtype.ext_iff]; rw [val_replicate]; rw [Multiset.eq_replicate]
  exact and_iff_right s.2

中文:
定理 eq_replicate_iff
  结论: s = replicate n a ↔ 对任意 b in s, b = a
  证明: by
  rw [Subtype.ext_iff]; rw [val_replicate]; rw [Multiset.eq_replicate]
  exact and_iff_right s.2

Depends on / 依赖: MonoidHom, MonoidHom.inl, MonoidHom.snd, Multiset, Multiset.eq_replicate, Prod.ext, Subtype, Subtype.ext_iff, and_iff_right, eq_replicate, ext_iff, hx.symm, isSolvable_of_ker_le_range, val_replicate
-/
theorem eq_replicate_iff : s = replicate n a ↔ forall b in s, b = a := by
  rw [Subtype.ext_iff]; rw [val_replicate]; rw [Multiset.eq_replicate]
  exact and_iff_right s.2

/--
theorem `exists_mem` / 定理 `exists_mem`

English:
theorem exists_mem
  given: (s : Sym α n.succ)
  statement: exists a, a in s
  proof: Multiset.card_pos_iff_exists_mem.1 s.2.symm ▸ n.succ_pos

中文:
定理 存在_mem
  条件: (s : Sym α n.succ)
  结论: 存在 a, a in s
  证明: Multiset.card_pos_iff_exists_mem.1 s.2.symm ▸ n.succ_pos

Depends on / 依赖: Multiset, Multiset.card_pos_iff_exists_mem, card_pos_iff_exists_mem, n.succ_pos, succ_pos
-/
theorem exists_mem (s : Sym α n.succ) : exists a, a in s :=
Multiset.card_pos_iff_exists_mem.1 s.2.symm ▸ n.succ_pos

/--
theorem `exists_cons_of_mem` / 定理 `exists_cons_of_mem`

English:
theorem exists_cons_of_mem
  given: {s : Sym α (n + 1)} {a : α} (h : a in s)
  statement: exists t, s = a ::ₛ t
  proof: by
  obtain ⟨m, h⟩ := Multiset.exists_cons_of_mem h
  have : Multiset.card m = n := by
    apply_fun Multiset.card at h
    rw [s.2]; rw [Multiset.card_cons]; rw [add_left_inj] at h
    exact h.symm
  use ⟨m, this⟩
  apply Subtype.ext
  exact h

中文:
定理 存在_cons_of_mem
  条件: {s : Sym α (n + 1)} {a : α} (h : a in s)
  结论: 存在 t, s = a ::ₛ t
  证明: by
  obtain ⟨m, h⟩ := Multiset.exists_cons_of_mem h
  have : Multiset.card m = n := by
    apply_fun Multiset.card at h
    rw [s.2]; rw [Multiset.card_cons]; rw [add_left_inj] at h
    exact h.symm
  use ⟨m, this⟩
  apply Subtype.ext
  exact h

Depends on / 依赖: Multiset, Multiset.card, Multiset.card_cons, Multiset.exists_cons_of_mem, Subtype, Subtype.ext, add_left_inj, apply_fun, card_cons, exists_cons_of_mem, h.symm
-/
theorem exists_cons_of_mem {s : Sym α (n + 1)} {a : α} (h : a in s) : exists t, s = a ::ₛ t := by
  obtain ⟨m, h⟩ := Multiset.exists_cons_of_mem h
  have : Multiset.card m = n := by
    apply_fun Multiset.card at h
    rw [s.2]; rw [Multiset.card_cons]; rw [add_left_inj] at h
    exact h.symm
  use ⟨m, this⟩
  apply Subtype.ext
  exact h

/--
theorem `exists_eq_cons_of_succ` / 定理 `exists_eq_cons_of_succ`

English:
theorem exists_eq_cons_of_succ
  given: (s : Sym α n.succ)
  statement: exists (a : α) (s' : Sym α n), s = a ::ₛ s'
  proof: by
  obtain ⟨a, ha⟩ := exists_mem s
  classical exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩

中文:
定理 存在_eq_cons_of_succ
  条件: (s : Sym α n.succ)
  结论: 存在 (a : α) (s' : Sym α n), s = a ::ₛ s'
  证明: by
  obtain ⟨a, ha⟩ := exists_mem s
  classical exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩

Depends on / 依赖: classical, cons_erase, exists_mem, s.erase
-/
theorem exists_eq_cons_of_succ (s : Sym α n.succ) : exists (a : α) (s' : Sym α n), s = a ::ₛ s' := by
  obtain ⟨a, ha⟩ := exists_mem s
  classical exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩

/--
theorem `eq_replicate` / 定理 `eq_replicate`

English:
theorem eq_replicate
  given: {a : α} {n : Nat} {s : Sym α n}
  statement: s = replicate n a ↔ forall b in s, b = a
  proof: Subtype.ext_iff.trans Multiset.eq_replicate.trans and_iff_right s.prop

中文:
定理 eq_replicate
  条件: {a : α} {n : 自然数} {s : Sym α n}
  结论: s = replicate n a ↔ 对任意 b in s, b = a
  证明: Subtype.ext_iff.trans Multiset.eq_replicate.trans and_iff_right s.prop

Depends on / 依赖: Multiset, Multiset.eq_replicate.trans, Subtype, Subtype.ext_iff.trans, and_iff_right, eq_replicate, ext_iff, s.prop
-/
theorem eq_replicate {a : α} {n : Nat} {s : Sym α n} : s = replicate n a ↔ forall b in s, b = a :=
Subtype.ext_iff.trans Multiset.eq_replicate.trans and_iff_right s.prop

/--
theorem `eq_replicate_of_subsingleton` / 定理 `eq_replicate_of_subsingleton`

English:
theorem eq_replicate_of_subsingleton
  given: [Subsingleton α] (a : α) {n : Nat} (s : Sym α n)
  proof: eq_replicate.2 fun _ _ => Subsingleton.elim _ _

中文:
定理 eq_replicate_of_subsingleton
  条件: [子单例 α] (a : α) {n : 自然数} (s : Sym α n)
  证明: eq_replicate.2 fun _ _ => Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, eq_replicate
-/
theorem eq_replicate_of_subsingleton [Subsingleton α] (a : α) {n : Nat} (s : Sym α n) :
    s = replicate n a :=
  eq_replicate.2 fun _ _ => Subsingleton.elim _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] (n
  body: ⟨by
    cases n
    · simp [eq_iff_true_of_subsingleton]
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_replicate_of_subsingleton b s']; rw [eq_replicate_of_subsingleton b s]⟩

中文:
实例 [子单例
  签名: α] (n
  定义体: ⟨by
    cases n
    · simp [eq_iff_true_of_subsingleton]
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_replicate_of_subsingleton b s']; rw [eq_replicate_of_subsingleton b s]⟩

Depends on / 依赖: eq_iff_true_of_subsingleton, eq_replicate_of_subsingleton, exists_mem
-/
instance [Subsingleton α] (n : Nat) : Subsingleton (Sym α n) :=
  ⟨by
    cases n
    · simp [eq_iff_true_of_subsingleton]
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_replicate_of_subsingleton b s']; rw [eq_replicate_of_subsingleton b s]⟩

/--
Instance `inhabitedSym` / 实例 `inhabitedSym`

English:
instance inhabitedSym
  signature: [Inhabited α] (n : Nat)
  body: ⟨replicate n default⟩

中文:
实例 inhabitedSym
  签名: [可居 α] (n : 自然数)
  定义体: ⟨replicate n default⟩

Depends on / 依赖: replicate
-/
instance inhabitedSym [Inhabited α] (n : Nat) : Inhabited (Sym α n) :=
  ⟨replicate n default⟩

/--
Instance `inhabitedSym'` / 实例 `inhabitedSym'`

English:
instance inhabitedSym'
  signature: [Inhabited α] (n : Nat)
  body: ⟨Quotient.mk' (List.Vector.replicate n default)⟩

中文:
实例 inhabitedSym'
  签名: [可居 α] (n : 自然数)
  定义体: ⟨Quotient.mk' (List.Vector.replicate n default)⟩

Depends on / 依赖: List.Vector.replicate, Quotient, Quotient.mk, Vector, replicate
-/
instance inhabitedSym' [Inhabited α] (n : Nat) : Inhabited (Sym' α n) :=
  ⟨Quotient.mk' (List.Vector.replicate n default)⟩

instance (n : Nat) [IsEmpty α] : IsEmpty (Sym α n.succ) :=
  ⟨fun s => by
    obtain ⟨a, -⟩ := exists_mem s
    exact isEmptyElim a⟩

instance (n : Nat) [Unique α] : Unique (Sym α n) :=
  Unique.mk' _

/--
theorem `replicate_right_inj` / 定理 `replicate_right_inj`

English:
theorem replicate_right_inj
  given: {a b : α} {n : Nat} (h : n != 0)
  statement: replicate n a = replicate n b ↔ a = b
  proof: Subtype.ext_iff.trans (Multiset.replicate_right_inj h)

中文:
定理 replicate_right_inj
  条件: {a b : α} {n : 自然数} (h : n != 0)
  结论: replicate n a = replicate n b ↔ a = b
  证明: Subtype.ext_iff.trans (Multiset.replicate_right_inj h)

Depends on / 依赖: Multiset, Multiset.replicate_right_inj, Subtype, Subtype.ext_iff.trans, ext_iff, replicate_right_inj
-/
theorem replicate_right_inj {a b : α} {n : Nat} (h : n != 0) : replicate n a = replicate n b ↔ a = b :=
  Subtype.ext_iff.trans (Multiset.replicate_right_inj h)

/--
theorem `replicate_right_injective` / 定理 `replicate_right_injective`

English:
theorem replicate_right_injective
  given: {n : Nat} (h : n != 0)
  proof: fun _ _ => (replicate_right_inj h).1

中文:
定理 replicate_right_injective
  条件: {n : 自然数} (h : n != 0)
  证明: fun _ _ => (replicate_right_inj h).1

Depends on / 依赖: replicate_right_inj
-/
theorem replicate_right_injective {n : Nat} (h : n != 0) :
    Function.Injective (replicate n : α -> Sym α n) := fun _ _ => (replicate_right_inj h).1

instance (n : Nat) [Nontrivial α] : Nontrivial (Sym α (n + 1)) :=
  (replicate_right_injective n.succ_ne_zero).nontrivial

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {n : Nat} (f : α -> β) (x : Sym α n)
  body: ⟨x.val.map f, by simp⟩

@[simp]

中文:
定义 map
  签名: {n : 自然数} (f : α -> β) (x : Sym α n)
  定义体: ⟨x.val.map f, by simp⟩

@[simp]

Depends on / 依赖: x.val.map
-/
def map {n : Nat} (f : α -> β) (x : Sym α n) : Sym β n :=
  ⟨x.val.map f, by simp⟩

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {n : Nat} {f : α -> β} {b : β} {l : Sym α n}
  proof: Multiset.mem_map

中文:
定理 mem_map
  条件: {n : 自然数} {f : α -> β} {b : β} {l : Sym α n}
  证明: Multiset.mem_map

Depends on / 依赖: Multiset, Multiset.mem_map, mem_map
-/
theorem mem_map {n : Nat} {f : α -> β} {b : β} {l : Sym α n} :
    b in Sym.map f l ↔ exists a, a in l ∧ f a = b :=
  Multiset.mem_map

set_option backward.isDefEq.respectTransparency false in
/-- Note: `Sym.map_id` is not simp-normal, as simp ends up unfolding `id` with `Sym.map_congr` -/
@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: {α : Type*} {n : Nat} (s : Sym α n)
  statement: Sym.map (fun x : α => x) s = s
  proof: by
  ext; simp only [map, Multiset.map_id', ← val_eq_coe]

中文:
定理 map_id'
  条件: {α : 类型} {n : 自然数} (s : Sym α n)
  结论: Sym.map (fun x : α => x) s = s
  证明: by
  ext; simp only [map, Multiset.map_id', ← val_eq_coe]

Depends on / 依赖: Multiset, Multiset.map_id, map_id, val_eq_coe
-/
theorem map_id' {α : Type*} {n : Nat} (s : Sym α n) : Sym.map (fun x : α => x) s = s := by
  ext; simp only [map, Multiset.map_id', ← val_eq_coe]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {α : Type*} {n : Nat} (s : Sym α n)
  statement: Sym.map id s = s
  proof: by
  ext; simp only [map, id_eq, Multiset.map_id', ← val_eq_coe]

@[simp]

中文:
定理 map_id
  条件: {α : 类型} {n : 自然数} (s : Sym α n)
  结论: Sym.map id s = s
  证明: by
  ext; simp only [map, id_eq, Multiset.map_id', ← val_eq_coe]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_id, id_eq, map_id, val_eq_coe
-/
theorem map_id {α : Type*} {n : Nat} (s : Sym α n) : Sym.map id s = s := by
  ext; simp only [map, id_eq, Multiset.map_id', ← val_eq_coe]

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {α β γ : Type*} {n : Nat} (g : β -> γ) (f : α -> β) (s : Sym α n)
  proof: Subtype.ext by dsimp only [Sym.map]; simp

@[simp]

中文:
定理 map_map
  条件: {α β γ : 类型} {n : 自然数} (g : β -> γ) (f : α -> β) (s : Sym α n)
  证明: Subtype.ext by dsimp only [Sym.map]; simp

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, Sym.map
-/
theorem map_map {α β γ : Type*} {n : Nat} (g : β -> γ) (f : α -> β) (s : Sym α n) :
    Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s :=
Subtype.ext by dsimp only [Sym.map]; simp

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : α -> β)
  statement: Sym.map f (0 : Sym α 0) = (0 : Sym β 0)
  proof: rfl

@[simp]

中文:
定理 map_zero
  条件: (f : α -> β)
  结论: Sym.map f (0 : Sym α 0) = (0 : Sym β 0)
  证明: rfl

@[simp]
-/
theorem map_zero (f : α -> β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0) :=
  rfl

@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: {n : Nat} (f : α -> β) (a : α) (s : Sym α n)
  statement: (a ::ₛ s).map f = f a ::ₛ s.map f
  proof: ext Multiset.map_cons _ _ _

@[congr]

中文:
定理 map_cons
  条件: {n : 自然数} (f : α -> β) (a : α) (s : Sym α n)
  结论: (a ::ₛ s).map f = f a ::ₛ s.map f
  证明: ext Multiset.map_cons _ _ _

@[congr]

Depends on / 依赖: Multiset, Multiset.map_cons, map_cons
-/
theorem map_cons {n : Nat} (f : α -> β) (a : α) (s : Sym α n) : (a ::ₛ s).map f = f a ::ₛ s.map f :=
ext Multiset.map_cons _ _ _

@[congr]
/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  given: {f g : α -> β} {s : Sym α n} (h : forall x in s, f x = g x)
  statement: map f s = map g s
  proof: Subtype.ext Multiset.map_congr rfl h

@[simp]

中文:
定理 map_congr
  条件: {f g : α -> β} {s : Sym α n} (h : 对任意 x in s, f x = g x)
  结论: map f s = map g s
  证明: Subtype.ext Multiset.map_congr rfl h

@[simp]

Depends on / 依赖: Multiset, Multiset.map_congr, Subtype, Subtype.ext, map_congr
-/
theorem map_congr {f g : α -> β} {s : Sym α n} (h : forall x in s, f x = g x) : map f s = map g s :=
Subtype.ext Multiset.map_congr rfl h

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: {f : α -> β} {m : Multiset α} {hc : Multiset.card m = n}
  proof: rfl

@[simp]

中文:
定理 map_mk
  条件: {f : α -> β} {m : Multiset α} {hc : Multiset.card m = n}
  证明: rfl

@[simp]
-/
theorem map_mk {f : α -> β} {m : Multiset α} {hc : Multiset.card m = n} :
    map f (mk m hc) = mk (m.map f) (by simp [hc]) :=
  rfl

@[simp]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (s : Sym α n) (f : α -> β)
  statement: ↑(s.map f) = Multiset.map f s
  proof: rfl

中文:
定理 coe_map
  条件: (s : Sym α n) (f : α -> β)
  结论: ↑(s.map f) = Multiset.map f s
  证明: rfl
-/
theorem coe_map (s : Sym α n) (f : α -> β) : ↑(s.map f) = Multiset.map f s :=
  rfl

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> β} (hf : Injective f) (n : Nat)
  proof: fun _ _ h =>
coe_injective Multiset.map_injective hf coe_inj.2 h

中文:
定理 map_injective
  条件: {f : α -> β} (hf : 单射 f) (n : 自然数)
  证明: fun _ _ h =>
coe_injective Multiset.map_injective hf coe_inj.2 h
-/
theorem map_injective {f : α -> β} (hf : Injective f) (n : Nat) :
    Injective (map f : Sym α n -> Sym β n) := fun _ _ h =>
coe_injective Multiset.map_injective hf coe_inj.2 h

/-- Mapping an equivalence `α ≃ β` using `Sym.map` gives an equivalence between `Sym α n` and
`Sym β n`. -/
@[simps]
/--
Definition of `equivCongr` / `equivCongr` 的定义

English:
definition equivCongr
  signature: (e : α ≃ β)
  body: map e
  invFun := map e.symm
  left_inv x := by rw [map_map, Equiv.symm_comp_self, map_id]
  right_inv x := by rw [map_map, Equiv.self_comp_symm, map_id]

中文:
定义 equivCongr
  签名: (e : α ≃ β)
  定义体: map e
  invFun := map e.symm
  left_inv x := by rw [map_map, Equiv.symm_comp_self, map_id]
  right_inv x := by rw [map_map, Equiv.self_comp_symm, map_id]
-/
def equivCongr (e : α ≃ β) : Sym α n ≃ Sym β n where
  toFun := map e
  invFun := map e.symm
  left_inv x := by rw [map_map, Equiv.symm_comp_self, map_id]
  right_inv x := by rw [map_map, Equiv.self_comp_symm, map_id]

/--
Definition of `attach` / `attach` 的定义

English:
definition attach
  signature: (s : Sym α n)
  body: ⟨s.val.attach, by (conv_rhs => rw [← s.2, ← Multiset.card_attach])⟩

@[simp]

中文:
定义 attach
  签名: (s : Sym α n)
  定义体: ⟨s.val.attach, by (conv_rhs => rw [← s.2, ← Multiset.card_attach])⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.card_attach, attach, card_attach, conv_rhs, s.val.attach
-/
def attach (s : Sym α n) : Sym { x // x in s } n :=
  ⟨s.val.attach, by (conv_rhs => rw [← s.2, ← Multiset.card_attach])⟩

@[simp]
/--
theorem `attach_mk` / 定理 `attach_mk`

English:
theorem attach_mk
  given: {m : Multiset α} {hc : Multiset.card m = n}
  proof: rfl

@[simp]

中文:
定理 attach_mk
  条件: {m : Multiset α} {hc : Multiset.card m = n}
  证明: rfl

@[simp]
-/
theorem attach_mk {m : Multiset α} {hc : Multiset.card m = n} :
    attach (mk m hc) = mk m.attach (Multiset.card_attach.trans hc) :=
  rfl

@[simp]
/--
theorem `coe_attach` / 定理 `coe_attach`

English:
theorem coe_attach
  given: (s : Sym α n)
  statement: (s.attach : Multiset { a // a in s }) =
  proof: rfl

中文:
定理 coe_attach
  条件: (s : Sym α n)
  结论: (s.attach : Multiset { a // a in s }) =
  证明: rfl
-/
theorem coe_attach (s : Sym α n) : (s.attach : Multiset { a // a in s }) =
    Multiset.attach (s : Multiset α) :=
  rfl

/--
theorem `attach_map_coe` / 定理 `attach_map_coe`

English:
theorem attach_map_coe
  given: (s : Sym α n)
  statement: s.attach.map (↑) = s
  proof: coe_injective Multiset.attach_map_val _

@[simp]

中文:
定理 attach_map_coe
  条件: (s : Sym α n)
  结论: s.attach.map (↑) = s
  证明: coe_injective Multiset.attach_map_val _

@[simp]

Depends on / 依赖: Multiset, Multiset.attach_map_val, attach_map_val, coe_injective
-/
theorem attach_map_coe (s : Sym α n) : s.attach.map (↑) = s :=
coe_injective Multiset.attach_map_val _

@[simp]
/--
theorem `mem_attach` / 定理 `mem_attach`

English:
theorem mem_attach
  given: (s : Sym α n) (x : { x // x in s })
  statement: x in s.attach
  proof: Multiset.mem_attach _ _

@[simp]

中文:
定理 mem_attach
  条件: (s : Sym α n) (x : { x // x in s })
  结论: x in s.attach
  证明: Multiset.mem_attach _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_attach, mem_attach
-/
theorem mem_attach (s : Sym α n) (x : { x // x in s }) : x in s.attach :=
  Multiset.mem_attach _ _

@[simp]
/--
theorem `attach_nil` / 定理 `attach_nil`

English:
theorem attach_nil
  statement: (nil : Sym α 0).attach = nil
  proof: rfl

@[simp]

中文:
定理 attach_nil
  结论: (nil : Sym α 0).attach = nil
  证明: rfl

@[simp]
-/
theorem attach_nil : (nil : Sym α 0).attach = nil :=
  rfl

@[simp]
/--
theorem `attach_cons` / 定理 `attach_cons`

English:
theorem attach_cons
  given: (x : α) (s : Sym α n)
  proof: coe_injective Multiset.attach_cons _ _

中文:
定理 attach_cons
  条件: (x : α) (s : Sym α n)
  证明: coe_injective Multiset.attach_cons _ _

Depends on / 依赖: Multiset, Multiset.attach_cons, attach_cons, coe_injective
-/
theorem attach_cons (x : α) (s : Sym α n) :
    (cons x s).attach =
      cons ⟨x, mem_cons_self _ _⟩ (s.attach.map fun x => ⟨x, mem_cons_of_mem x.prop⟩) :=
coe_injective Multiset.attach_cons _ _

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {n m : Nat} (h : n = m)
  body: ⟨s.val, s.2.trans h⟩
  invFun s := ⟨s.val, s.2.trans h.symm⟩

@[simp]

中文:
定义 cast
  签名: {n m : 自然数} (h : n = m)
  定义体: ⟨s.val, s.2.trans h⟩
  invFun s := ⟨s.val, s.2.trans h.symm⟩

@[simp]
-/
protected def cast {n m : Nat} (h : n = m) : Sym α n ≃ Sym α m where
  toFun s := ⟨s.val, s.2.trans h⟩
  invFun s := ⟨s.val, s.2.trans h.symm⟩

@[simp]
/--
theorem `cast_rfl` / 定理 `cast_rfl`

English:
theorem cast_rfl
  statement: Sym.cast rfl s = s
  proof: Subtype.ext rfl

@[simp]

中文:
定理 cast_rfl
  结论: Sym.cast rfl s = s
  证明: Subtype.ext rfl

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem cast_rfl : Sym.cast rfl s = s :=
  Subtype.ext rfl

@[simp]
/--
theorem `cast_cast` / 定理 `cast_cast`

English:
theorem cast_cast
  given: {n'' : Nat} (h : n = n') (h' : n' = n'')
  proof: rfl

@[simp]

中文:
定理 cast_cast
  条件: {n'' : 自然数} (h : n = n') (h' : n' = n'')
  证明: rfl

@[simp]
-/
theorem cast_cast {n'' : Nat} (h : n = n') (h' : n' = n'') :
    Sym.cast h' (Sym.cast h s) = Sym.cast (h.trans h') s :=
  rfl

@[simp]
/--
theorem `coe_cast` / 定理 `coe_cast`

English:
theorem coe_cast
  given: (h : n = m)
  statement: (Sym.cast h s : Multiset α) = s
  proof: rfl

@[simp]

中文:
定理 coe_cast
  条件: (h : n = m)
  结论: (Sym.cast h s : Multiset α) = s
  证明: rfl

@[simp]
-/
theorem coe_cast (h : n = m) : (Sym.cast h s : Multiset α) = s :=
  rfl

@[simp]
/--
theorem `mem_cast` / 定理 `mem_cast`

English:
theorem mem_cast
  given: (h : n = m)
  statement: a in Sym.cast h s ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_cast
  条件: (h : n = m)
  结论: a in Sym.cast h s ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cast (h : n = m) : a in Sym.cast h s ↔ a in s :=
  Iff.rfl

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (s : Sym α n) (s' : Sym α n')
  body: ⟨s.1 + s'.1, by rw [Multiset.card_add, s.2, s'.2]⟩

@[simp]

中文:
定义 append
  签名: (s : Sym α n) (s' : Sym α n')
  定义体: ⟨s.1 + s'.1, by rw [Multiset.card_add, s.2, s'.2]⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.card_add, card_add
-/
def append (s : Sym α n) (s' : Sym α n') : Sym α (n + n') :=
  ⟨s.1 + s'.1, by rw [Multiset.card_add, s.2, s'.2]⟩

@[simp]
/--
theorem `append_inj_right` / 定理 `append_inj_right`

English:
theorem append_inj_right
  given: (s : Sym α n) {t t' : Sym α n'}
  statement: s.append t = s.append t' ↔ t = t'
  proof: Subtype.ext_iff.trans (add_right_inj _).trans Subtype.ext_iff.symm

@[simp]

中文:
定理 append_inj_right
  条件: (s : Sym α n) {t t' : Sym α n'}
  结论: s.append t = s.append t' ↔ t = t'
  证明: Subtype.ext_iff.trans (add_right_inj _).trans Subtype.ext_iff.symm

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff.symm, Subtype.ext_iff.trans, add_right_inj, ext_iff
-/
theorem append_inj_right (s : Sym α n) {t t' : Sym α n'} : s.append t = s.append t' ↔ t = t' :=
Subtype.ext_iff.trans (add_right_inj _).trans Subtype.ext_iff.symm

@[simp]
/--
theorem `append_inj_left` / 定理 `append_inj_left`

English:
theorem append_inj_left
  given: {s s' : Sym α n} (t : Sym α n')
  statement: s.append t = s'.append t ↔ s = s'
  proof: Subtype.ext_iff.trans (add_left_inj _).trans Subtype.ext_iff.symm

中文:
定理 append_inj_left
  条件: {s s' : Sym α n} (t : Sym α n')
  结论: s.append t = s'.append t ↔ s = s'
  证明: Subtype.ext_iff.trans (add_left_inj _).trans Subtype.ext_iff.symm

Depends on / 依赖: Subtype, Subtype.ext_iff.symm, Subtype.ext_iff.trans, add_left_inj, ext_iff
-/
theorem append_inj_left {s s' : Sym α n} (t : Sym α n') : s.append t = s'.append t ↔ s = s' :=
Subtype.ext_iff.trans (add_left_inj _).trans Subtype.ext_iff.symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `append_comm` / 定理 `append_comm`

English:
theorem append_comm
  given: (s : Sym α n') (s' : Sym α n')
  proof: by
  simp [append, add_comm]

@[simp, norm_cast]

中文:
定理 append_comm
  条件: (s : Sym α n') (s' : Sym α n')
  证明: by
  simp [append, add_comm]

@[simp, norm_cast]

Depends on / 依赖: add_comm, append
-/
theorem append_comm (s : Sym α n') (s' : Sym α n') :
    s.append s' = Sym.cast (add_comm _ _) (s'.append s) := by
  simp [append, add_comm]

@[simp, norm_cast]
/--
theorem `coe_append` / 定理 `coe_append`

English:
theorem coe_append
  given: (s : Sym α n) (s' : Sym α n')
  statement: (s.append s' : Multiset α) = s + s'
  proof: rfl

中文:
定理 coe_append
  条件: (s : Sym α n) (s' : Sym α n')
  结论: (s.append s' : Multiset α) = s + s'
  证明: rfl
-/
theorem coe_append (s : Sym α n) (s' : Sym α n') : (s.append s' : Multiset α) = s + s' :=
  rfl

/--
theorem `mem_append_iff` / 定理 `mem_append_iff`

English:
theorem mem_append_iff
  given: {s' : Sym α m}
  statement: a in s.append s' ↔ a in s ∨ a in s'
  proof: Multiset.mem_add

中文:
定理 mem_append_iff
  条件: {s' : Sym α m}
  结论: a in s.append s' ↔ a in s ∨ a in s'
  证明: Multiset.mem_add

Depends on / 依赖: H.subtype_injective, Multiset, Multiset.mem_add, finite_of_injective, mem_add, subtype_injective
-/
theorem mem_append_iff {s' : Sym α m} : a in s.append s' ↔ a in s ∨ a in s' :=
  Multiset.mem_add

set_option backward.isDefEq.respectTransparency false in
/-- `a ↦ {a}` as an equivalence between `α` and `Sym α 1`. -/
@[simps apply]
/--
Definition of `oneEquiv` / `oneEquiv` 的定义

English:
definition oneEquiv
  signature: : α ≃ Sym α 1 where
  body: ⟨{a}, by simp⟩
  invFun s := (Equiv.subtypeQuotientEquivQuotientSubtype
      (·.length = 1) _ (fun _ => Iff.rfl) (fun l l' => by rfl) s).liftOn
    (fun l => l.1.head <| List.length_pos_iff.mp <| by simp)
    fun ⟨_, _⟩ ⟨_, h⟩ => fun perm => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
      exact List.eq_of_mem_singleton (List.Perm.mem_iff perm |>.mp <| List.head_mem _)
  right_inv := by rintro ⟨⟨l⟩, h⟩; obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h; rfl

中文:
定义 oneEquiv
  签名: : α ≃ Sym α 1 where
  定义体: ⟨{a}, by simp⟩
  invFun s := (Equiv.subtypeQuotientEquivQuotientSubtype
      (·.length = 1) _ (fun _ => Iff.rfl) (fun l l' => by rfl) s).liftOn
    (fun l => l.1.head <| List.length_pos_iff.mp <| by simp)
    fun ⟨_, _⟩ ⟨_, h⟩ => fun perm => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
      exact List.eq_of_mem_singleton (List.Perm.mem_iff perm |>.mp <| List.head_mem _)
  right_inv := by rintro ⟨⟨l⟩, h⟩; obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h; rfl
-/
def oneEquiv : α ≃ Sym α 1 where
  toFun a := ⟨{a}, by simp⟩
  invFun s := (Equiv.subtypeQuotientEquivQuotientSubtype
      (·.length = 1) _ (fun _ => Iff.rfl) (fun l l' => by rfl) s).liftOn
    (fun l => l.1.head <| List.length_pos_iff.mp <| by simp)
    fun ⟨_, _⟩ ⟨_, h⟩ => fun perm => by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
      exact List.eq_of_mem_singleton (List.Perm.mem_iff perm |>.mp <| List.head_mem _)
  right_inv := by rintro ⟨⟨l⟩, h⟩; obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h; rfl

/--
Definition of `fill` / `fill` 的定义

English:
definition fill
  signature: (a : α) (i : Fin (n + 1)) (m : Sym α (n - i))
  body: Sym.cast (Nat.sub_add_cancel i.is_le) (m.append (replicate i a))

中文:
定义 fill
  签名: (a : α) (i : 有限集 (n + 1)) (m : Sym α (n - i))
  定义体: Sym.cast (Nat.sub_add_cancel i.is_le) (m.append (replicate i a))

Depends on / 依赖: Nat.sub_add_cancel, Sym.cast, append, i.is_le, is_le, m.append, replicate, sub_add_cancel
-/
def fill (a : α) (i : Fin (n + 1)) (m : Sym α (n - i)) : Sym α n :=
  Sym.cast (Nat.sub_add_cancel i.is_le) (m.append (replicate i a))

/--
theorem `coe_fill` / 定理 `coe_fill`

English:
theorem coe_fill
  given: {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)}
  proof: rfl

中文:
定理 coe_fill
  条件: {a : α} {i : 有限集 (n + 1)} {m : Sym α (n - i)}
  证明: rfl
-/
theorem coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} :
    (fill a i m : Multiset α) = m + replicate i a :=
  rfl

/--
theorem `mem_fill_iff` / 定理 `mem_fill_iff`

English:
theorem mem_fill_iff
  given: {a b : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
  proof: by
  rw [fill]; rw [mem_cast]; rw [mem_append_iff]; rw [or_comm]; rw [mem_replicate]

中文:
定理 mem_fill_iff
  条件: {a b : α} {i : 有限集 (n + 1)} {s : Sym α (n - i)}
  证明: by
  rw [fill]; rw [mem_cast]; rw [mem_append_iff]; rw [or_comm]; rw [mem_replicate]

Depends on / 依赖: mem_append_iff, mem_cast, mem_replicate, or_comm
-/
theorem mem_fill_iff {a b : α} {i : Fin (n + 1)} {s : Sym α (n - i)} :
    a in Sym.fill b i s ↔ (i : Nat) != 0 ∧ a = b ∨ a in s := by
  rw [fill]; rw [mem_cast]; rw [mem_append_iff]; rw [or_comm]; rw [mem_replicate]

open Multiset

/--
Definition of `filterNe` / `filterNe` 的定义

English:
definition filterNe
  signature: [DecidableEq α] (a : α) (m : Sym α n)
  body: ⟨⟨m.1.count a, (count_le_card _ _).trans_lt by rw [m.2, Nat.lt_succ_iff]⟩,
    m.1.filter (a != ·),
Nat.eq_sub_of_add_eq
      Eq.trans
        (by
          rw [← countP_eq_card_filter]; rw [add_comm]
          simp only [eq_comm, Ne, count]
          rw [← card_eq_countP_add_countP _ _])
        m.2⟩

中文:
定义 filterNe
  签名: [DecidableEq α] (a : α) (m : Sym α n)
  定义体: ⟨⟨m.1.count a, (count_le_card _ _).trans_lt by rw [m.2, Nat.lt_succ_iff]⟩,
    m.1.filter (a != ·),
Nat.eq_sub_of_add_eq
      Eq.trans
        (by
          rw [← countP_eq_card_filter]; rw [add_comm]
          simp only [eq_comm, Ne, count]
          rw [← card_eq_countP_add_countP _ _])
        m.2⟩

Depends on / 依赖: Eq.trans, Nat.eq_sub_of_add_eq, Nat.lt_succ_iff, add_comm, card_eq_countP_add_countP, countP_eq_card_filter, count_le_card, eq_comm, eq_sub_of_add_eq, filter, lt_succ_iff, trans_lt
-/
def filterNe [DecidableEq α] (a : α) (m : Sym α n) : Σ i : Fin (n + 1), Sym α (n - i) :=
⟨⟨m.1.count a, (count_le_card _ _).trans_lt by rw [m.2, Nat.lt_succ_iff]⟩,
    m.1.filter (a != ·),
Nat.eq_sub_of_add_eq
      Eq.trans
        (by
          rw [← countP_eq_card_filter]; rw [add_comm]
          simp only [eq_comm, Ne, count]
          rw [← card_eq_countP_add_countP _ _])
        m.2⟩

/--
theorem `sigma_sub_ext` / 定理 `sigma_sub_ext`

English:
theorem sigma_sub_ext
  given: {m₁ m₂ : Σ i : Fin (n + 1), Sym α (n - i)} (h : (m₁.2 : Multiset α) = m₂.2)
  proof: Sigma.subtype_ext
    (Fin.ext <| by
      rw [← Nat.sub_sub_self (Nat.le_of_lt_succ m₁.1.is_lt)]; rw [← m₁.2.2]; rw [val_eq_coe]; rw [h]; rw [← val_eq_coe]; rw [m₂.2.2]; rw [Nat.sub_sub_self (Nat.le_of_lt_succ m₂.1.is_lt)])
    h

中文:
定理 sigma_sub_ext
  条件: {m₁ m₂ : Σ i : 有限集 (n + 1), Sym α (n - i)} (h : (m₁.2 : Multiset α) = m₂.2)
  证明: Sigma.subtype_ext
    (Fin.ext <| by
      rw [← Nat.sub_sub_self (Nat.le_of_lt_succ m₁.1.is_lt)]; rw [← m₁.2.2]; rw [val_eq_coe]; rw [h]; rw [← val_eq_coe]; rw [m₂.2.2]; rw [Nat.sub_sub_self (Nat.le_of_lt_succ m₂.1.is_lt)])
    h

Depends on / 依赖: Fin.ext, Nat.le_of_lt_succ, Nat.sub_sub_self, Sigma.subtype_ext, is_lt, le_of_lt_succ, sub_sub_self, subtype_ext, val_eq_coe
-/
theorem sigma_sub_ext {m₁ m₂ : Σ i : Fin (n + 1), Sym α (n - i)} (h : (m₁.2 : Multiset α) = m₂.2) :
    m₁ = m₂ :=
  Sigma.subtype_ext
    (Fin.ext <| by
      rw [← Nat.sub_sub_self (Nat.le_of_lt_succ m₁.1.is_lt)]; rw [← m₁.2.2]; rw [val_eq_coe]; rw [h]; rw [← val_eq_coe]; rw [m₂.2.2]; rw [Nat.sub_sub_self (Nat.le_of_lt_succ m₂.1.is_lt)])
    h

/--
theorem `fill_filterNe` / 定理 `fill_filterNe`

English:
theorem fill_filterNe
  given: [DecidableEq α] (a : α) (m : Sym α n)
  proof: Sym.ext
    (by
      rw [coe_fill]; rw [filterNe]; rw [← val_eq_coe]; rw [Subtype.coe_mk]; rw [Fin.val_mk]
      ext b; dsimp
      rw [count_add]; rw [count_filter]; rw [Sym.coe_replicate]; rw [count_replicate]
      obtain rfl | h := eq_or_ne a b
      · rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add]
      · rw [if_pos h, if_neg h, add_zero])

中文:
定理 fill_filterNe
  条件: [DecidableEq α] (a : α) (m : Sym α n)
  证明: Sym.ext
    (by
      rw [coe_fill]; rw [filterNe]; rw [← val_eq_coe]; rw [Subtype.coe_mk]; rw [Fin.val_mk]
      ext b; dsimp
      rw [count_add]; rw [count_filter]; rw [Sym.coe_replicate]; rw [count_replicate]
      obtain rfl | h := eq_or_ne a b
      · rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add]
      · rw [if_pos h, if_neg h, add_zero])

Depends on / 依赖: Fin.val_mk, Subtype, Subtype.coe_mk, Sym.coe_replicate, Sym.ext, add_zero, coe_fill, coe_mk, coe_replicate, count_add, count_filter, count_replicate, eq_or_ne, filterNe, if_neg, if_pos, not_not, val_eq_coe, val_mk, zero_add
-/
theorem fill_filterNe [DecidableEq α] (a : α) (m : Sym α n) :
    (m.filterNe a).2.fill a (m.filterNe a).1 = m :=
  Sym.ext
    (by
      rw [coe_fill]; rw [filterNe]; rw [← val_eq_coe]; rw [Subtype.coe_mk]; rw [Fin.val_mk]
      ext b; dsimp
      rw [count_add]; rw [count_filter]; rw [Sym.coe_replicate]; rw [count_replicate]
      obtain rfl | h := eq_or_ne a b
      · rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add]
      · rw [if_pos h, if_neg h, add_zero])

/--
theorem `filter_ne_fill` / 定理 `filter_ne_fill`

English:
theorem filter_ne_fill
  proof: sigma_sub_ext
    (by
      rw [filterNe]; rw [← val_eq_coe]; rw [Subtype.coe_mk]; rw [val_eq_coe]; rw [coe_fill]
      rw [filter_add]; rw [filter_eq_self.2]; rw [add_eq_left]; rw [eq_zero_iff_forall_notMem]
      · intro b hb
        rw [mem_filter]; rw [Sym.mem_coe]; rw [mem_replicate] at hb
        exact hb.2 hb.1.2.symm
· exact fun a ha ha' => h ha'.symm ▸ ha)

中文:
定理 filter_ne_fill
  证明: sigma_sub_ext
    (by
      rw [filterNe]; rw [← val_eq_coe]; rw [Subtype.coe_mk]; rw [val_eq_coe]; rw [coe_fill]
      rw [filter_add]; rw [filter_eq_self.2]; rw [add_eq_left]; rw [eq_zero_iff_forall_notMem]
      · intro b hb
        rw [mem_filter]; rw [Sym.mem_coe]; rw [mem_replicate] at hb
        exact hb.2 hb.1.2.symm
· exact fun a ha ha' => h ha'.symm ▸ ha)

Depends on / 依赖: Subtype, Subtype.coe_mk, Sym.mem_coe, add_eq_left, coe_fill, coe_mk, eq_zero_iff_forall_notMem, filterNe, filter_add, filter_eq_self, mem_coe, mem_filter, mem_replicate, sigma_sub_ext, val_eq_coe
-/
theorem filter_ne_fill
    [DecidableEq α] (a : α) (m : Σ i : Fin (n + 1), Sym α (n - i)) (h : a ∉ m.2) :
    (m.2.fill a m.1).filterNe a = m :=
  sigma_sub_ext
    (by
      rw [filterNe]; rw [← val_eq_coe]; rw [Subtype.coe_mk]; rw [val_eq_coe]; rw [coe_fill]
      rw [filter_add]; rw [filter_eq_self.2]; rw [add_eq_left]; rw [eq_zero_iff_forall_notMem]
      · intro b hb
        rw [mem_filter]; rw [Sym.mem_coe]; rw [mem_replicate] at hb
        exact hb.2 hb.1.2.symm
· exact fun a ha ha' => h ha'.symm ▸ ha)

/--
theorem `count_coe_fill_self_of_notMem` / 定理 `count_coe_fill_self_of_notMem`

English:
theorem count_coe_fill_self_of_notMem
  statement: [DecidableEq α] {a : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
  proof: by
  simp [coe_fill, coe_replicate, hx]

中文:
定理 count_coe_fill_self_of_notMem
  结论: [DecidableEq α] {a : α} {i : 有限集 (n + 1)} {s : Sym α (n - i)}
  证明: by
  simp [coe_fill, coe_replicate, hx]

Depends on / 依赖: coe_fill, coe_replicate
-/
theorem count_coe_fill_self_of_notMem [DecidableEq α] {a : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : a ∉ s) :
    count a (fill a i s : Multiset α) = i := by
  simp [coe_fill, coe_replicate, hx]

/--
theorem `count_coe_fill_of_ne` / 定理 `count_coe_fill_of_ne`

English:
theorem count_coe_fill_of_ne
  statement: [DecidableEq α] {a x : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
  proof: by
  suffices x ∉ Multiset.replicate i a by simp [coe_fill, coe_replicate, this]
  simp [Multiset.mem_replicate, hx]

中文:
定理 count_coe_fill_of_ne
  结论: [DecidableEq α] {a x : α} {i : 有限集 (n + 1)} {s : Sym α (n - i)}
  证明: by
  suffices x ∉ Multiset.replicate i a by simp [coe_fill, coe_replicate, this]
  simp [Multiset.mem_replicate, hx]

Depends on / 依赖: Multiset, Multiset.mem_replicate, Multiset.replicate, coe_fill, coe_replicate, mem_replicate, replicate
-/
theorem count_coe_fill_of_ne [DecidableEq α] {a x : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : x != a) :
    count x (fill a i s : Multiset α) = count x s := by
  suffices x ∉ Multiset.replicate i a by simp [coe_fill, coe_replicate, this]
  simp [Multiset.mem_replicate, hx]

end Sym

section Equiv

/-! ### Combinatorial equivalences -/


variable {α : Type*} {n : Nat}

open Sym

namespace SymOptionSuccEquiv

/--
Definition of `encode` / `encode` 的定义

English:
definition encode
  signature: [DecidableEq α] (s : Sym (Option α) n.succ)
  body: if h : none in s then Sum.inl (s.erase none h)
  else
    Sum.inr
      (s.attach.map fun o =>
o.1.get Option.ne_none_iff_isSome.1 ne_of_mem_of_not_mem o.2 h)

@[simp]

中文:
定义 encode
  签名: [DecidableEq α] (s : Sym (选项类型 α) n.succ)
  定义体: if h : none in s then Sum.inl (s.erase none h)
  else
    Sum.inr
      (s.attach.map fun o =>
o.1.get Option.ne_none_iff_isSome.1 ne_of_mem_of_not_mem o.2 h)

@[simp]

Depends on / 依赖: Option.ne_none_iff_isSome, Sum.inl, Sum.inr, attach, ne_none_iff_isSome, ne_of_mem_of_not_mem, s.attach.map, s.erase
-/
def encode [DecidableEq α] (s : Sym (Option α) n.succ) : Sym (Option α) n oplus Sym α n.succ :=
  if h : none in s then Sum.inl (s.erase none h)
  else
    Sum.inr
      (s.attach.map fun o =>
o.1.get Option.ne_none_iff_isSome.1 ne_of_mem_of_not_mem o.2 h)

@[simp]
/--
theorem `encode_of_none_mem` / 定理 `encode_of_none_mem`

English:
theorem encode_of_none_mem
  given: [DecidableEq α] (s : Sym (Option α) n.succ) (h : none in s)
  proof: dif_pos h

@[simp]

中文:
定理 encode_of_none_mem
  条件: [DecidableEq α] (s : Sym (选项类型 α) n.succ) (h : none in s)
  证明: dif_pos h

@[simp]

Depends on / 依赖: dif_pos
-/
theorem encode_of_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none in s) :
    encode s = Sum.inl (s.erase none h) :=
  dif_pos h

@[simp]
/--
theorem `encode_of_none_notMem` / 定理 `encode_of_none_notMem`

English:
theorem encode_of_none_notMem
  given: [DecidableEq α] (s : Sym (Option α) n.succ) (h : none ∉ s)
  proof: dif_neg h

中文:
定理 encode_of_none_notMem
  条件: [DecidableEq α] (s : Sym (选项类型 α) n.succ) (h : none ∉ s)
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem encode_of_none_notMem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none ∉ s) :
    encode s =
      Sum.inr
        (s.attach.map fun o =>
o.1.get Option.ne_none_iff_isSome.1 ne_of_mem_of_not_mem o.2 h) :=
  dif_neg h

/--
Definition of `decode` / `decode` 的定义

English:
definition decode
  signature: : Sym (Option α) n oplus Sym α n.succ -> Sym (Option α) n.succ

中文:
定义 decode
  签名: : Sym (选项类型 α) n oplus Sym α n.succ -> Sym (选项类型 α) n.succ
-/
def decode : Sym (Option α) n oplus Sym α n.succ -> Sym (Option α) n.succ
  | Sum.inl s => none ::ₛ s
  | Sum.inr s => s.map Embedding.some

@[simp]
/--
theorem `decode_inl` / 定理 `decode_inl`

English:
theorem decode_inl
  given: (s : Sym (Option α) n)
  statement: decode (Sum.inl s) = none ::ₛ s
  proof: rfl

@[simp]

中文:
定理 decode_inl
  条件: (s : Sym (选项类型 α) n)
  结论: decode (和.inl s) = none ::ₛ s
  证明: rfl

@[simp]
-/
theorem decode_inl (s : Sym (Option α) n) : decode (Sum.inl s) = none ::ₛ s :=
  rfl

@[simp]
/--
theorem `decode_inr` / 定理 `decode_inr`

English:
theorem decode_inr
  given: (s : Sym α n.succ)
  statement: decode (Sum.inr s) = s.map Embedding.some
  proof: rfl

@[simp]

中文:
定理 decode_inr
  条件: (s : Sym α n.succ)
  结论: decode (和.inr s) = s.map 嵌入.some
  证明: rfl

@[simp]
-/
theorem decode_inr (s : Sym α n.succ) : decode (Sum.inr s) = s.map Embedding.some :=
  rfl

@[simp]
/--
theorem `decode_encode` / 定理 `decode_encode`

English:
theorem decode_encode
  given: [DecidableEq α] (s : Sym (Option α) n.succ)
  statement: decode (encode s) = s
  proof: by
  by_cases h : none in s
  · simp [h]
  · simp only [decode, h, not_false_iff, encode_of_none_notMem, Embedding.some_apply, map_map,
      comp_apply, Option.some_get]
    convert! s.attach_map_coe

@[simp]

中文:
定理 decode_encode
  条件: [DecidableEq α] (s : Sym (选项类型 α) n.succ)
  结论: decode (encode s) = s
  证明: by
  by_cases h : none in s
  · simp [h]
  · simp only [decode, h, not_false_iff, encode_of_none_notMem, Embedding.some_apply, map_map,
      comp_apply, Option.some_get]
    convert! s.attach_map_coe

@[simp]

Depends on / 依赖: Embedding, Embedding.some_apply, Option.some_get, attach_map_coe, comp_apply, convert, decode, encode_of_none_notMem, map_map, not_false_iff, s.attach_map_coe, some_apply, some_get
-/
theorem decode_encode [DecidableEq α] (s : Sym (Option α) n.succ) : decode (encode s) = s := by
  by_cases h : none in s
  · simp [h]
  · simp only [decode, h, not_false_iff, encode_of_none_notMem, Embedding.some_apply, map_map,
      comp_apply, Option.some_get]
    convert! s.attach_map_coe

@[simp]
/--
theorem `encode_decode` / 定理 `encode_decode`

English:
theorem encode_decode
  given: [DecidableEq α] (s : Sym (Option α) n oplus Sym α n.succ)
  proof: by
  obtain s | s := s
  · simp
  · unfold SymOptionSuccEquiv.encode
    split_ifs with h
    · obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
      exact Option.some_ne_none _ ha
    · refine congr_arg Sum.inr ?_
      refine map_injective (Option.some_injective _) _ ?_
      refine Eq.trans ?_ (.trans (SymOptionSuccEquiv.decode (Sum.inr s)).attach_map_coe ?_) <;> simp

中文:
定理 encode_decode
  条件: [DecidableEq α] (s : Sym (选项类型 α) n oplus Sym α n.succ)
  证明: by
  obtain s | s := s
  · simp
  · unfold SymOptionSuccEquiv.encode
    split_ifs with h
    · obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
      exact Option.some_ne_none _ ha
    · refine congr_arg Sum.inr ?_
      refine map_injective (Option.some_injective _) _ ?_
      refine Eq.trans ?_ (.trans (SymOptionSuccEquiv.decode (Sum.inr s)).attach_map_coe ?_) <;> simp

Depends on / 依赖: Eq.trans, Multiset, Multiset.mem_map.mp, Option.some_injective, Option.some_ne_none, Sum.inr, SymOptionSuccEquiv, SymOptionSuccEquiv.decode, SymOptionSuccEquiv.encode, attach_map_coe, congr_arg, decode, encode, map_injective, mem_map, some_injective, some_ne_none, split_ifs
-/
theorem encode_decode [DecidableEq α] (s : Sym (Option α) n oplus Sym α n.succ) :
    encode (decode s) = s := by
  obtain s | s := s
  · simp
  · unfold SymOptionSuccEquiv.encode
    split_ifs with h
    · obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
      exact Option.some_ne_none _ ha
    · refine congr_arg Sum.inr ?_
      refine map_injective (Option.some_injective _) _ ?_
      refine Eq.trans ?_ (.trans (SymOptionSuccEquiv.decode (Sum.inr s)).attach_map_coe ?_) <;> simp

end SymOptionSuccEquiv

--@[simps]
/--
Definition of `symOptionSuccEquiv` / `symOptionSuccEquiv` 的定义

English:
definition symOptionSuccEquiv
  signature: [DecidableEq α]
  body: SymOptionSuccEquiv.encode
  invFun := SymOptionSuccEquiv.decode
  left_inv := SymOptionSuccEquiv.decode_encode
  right_inv := SymOptionSuccEquiv.encode_decode

中文:
定义 symOptionSuccEquiv
  签名: [DecidableEq α]
  定义体: SymOptionSuccEquiv.encode
  invFun := SymOptionSuccEquiv.decode
  left_inv := SymOptionSuccEquiv.decode_encode
  right_inv := SymOptionSuccEquiv.encode_decode

Depends on / 依赖: SymOptionSuccEquiv, SymOptionSuccEquiv.encode, encode
-/
def symOptionSuccEquiv [DecidableEq α] :
    Sym (Option α) n.succ ≃ Sym (Option α) n oplus Sym α n.succ where
  toFun := SymOptionSuccEquiv.encode
  invFun := SymOptionSuccEquiv.decode
  left_inv := SymOptionSuccEquiv.decode_encode
  right_inv := SymOptionSuccEquiv.encode_decode

end Equiv
