/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Defs
public import Mathlib.Order.BoundedOrder.Basic

/-!
# Definition of `0` and `::ₘ`

This file defines constructors for multisets:

* `Zero (Multiset α)` instance: the empty multiset
* `Multiset.cons`: add one element to a multiset
* `Singleton α (Multiset α)` instance: multiset with one element

It also defines the following predicates on multisets:

* `Multiset.Rel`: `Rel r s t` lifts the relation `r` between two elements to a relation between `s`
  and `t`, s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`.

## Notation

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.

## Main results

* `Multiset.rec`: recursion on adding one element to a multiset at a time.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Empty multiset -/


/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : Multiset α
  body: @nil α

中文:
定义 zero
  签名: : Multiset α
  定义体: @nil α
-/
protected def zero : Multiset α :=
  @nil α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Multiset α)
  body: ⟨Multiset.zero⟩

中文:
实例 :
  签名: Zero (Multiset α)
  定义体: ⟨Multiset.zero⟩

Depends on / 依赖: Multiset, Multiset.zero
-/
instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Multiset α)
  body: ⟨0⟩

中文:
实例 :
  签名: EmptyCollection (Multiset α)
  定义体: ⟨0⟩
-/
instance : EmptyCollection (Multiset α) :=
  ⟨0⟩

/--
Instance `inhabitedMultiset` / 实例 `inhabitedMultiset`

English:
instance inhabitedMultiset
  signature: : Inhabited (Multiset α)
  body: ⟨0⟩

中文:
实例 inhabitedMultiset
  签名: : Inhabited (Multiset α)
  定义体: ⟨0⟩
-/
instance inhabitedMultiset : Inhabited (Multiset α) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (Multiset α) where
  body: 0
  uniq := by rintro ⟨_ | ⟨a, l⟩⟩; exacts [rfl, isEmptyElim a]

@[simp]

中文:
实例 [IsEmpty
  签名: α] : Unique (Multiset α) where
  定义体: 0
  uniq := by rintro ⟨_ | ⟨a, l⟩⟩; exacts [rfl, isEmptyElim a]

@[simp]
-/
instance [IsEmpty α] : Unique (Multiset α) where
  default := 0
  uniq := by rintro ⟨_ | ⟨a, l⟩⟩; exacts [rfl, isEmptyElim a]

@[simp]
/--
theorem `coe_nil` / 定理 `coe_nil`

English:
theorem coe_nil
  statement: (@nil α : Multiset α) = 0
  proof: rfl

@[simp]

中文:
定理 coe_nil
  结论: (@nil α : Multiset α) = 0
  证明: rfl

@[simp]
-/
theorem coe_nil : (@nil α : Multiset α) = 0 :=
  rfl

@[simp]
/--
theorem `empty_eq_zero` / 定理 `empty_eq_zero`

English:
theorem empty_eq_zero
  statement: (∅ : Multiset α) = 0
  proof: rfl

@[simp]

中文:
定理 empty_eq_zero
  结论: (∅ : Multiset α) = 0
  证明: rfl

@[simp]
-/
theorem empty_eq_zero : (∅ : Multiset α) = 0 :=
  rfl

@[simp]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: (l : List α)
  statement: (l : Multiset α) = 0 ↔ l = []
  proof: Iff.trans coe_eq_coe perm_nil

中文:
定理 coe_eq_zero
  条件: (l : List α)
  结论: (l : Multiset α) = 0 ↔ l = []
  证明: Iff.trans coe_eq_coe perm_nil

Depends on / 依赖: Iff.trans, coe_eq_coe, perm_nil
-/
theorem coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = [] :=
  Iff.trans coe_eq_coe perm_nil

/--
theorem `coe_eq_zero_iff_isEmpty` / 定理 `coe_eq_zero_iff_isEmpty`

English:
theorem coe_eq_zero_iff_isEmpty
  given: (l : List α)
  statement: (l : Multiset α) = 0 ↔ l.isEmpty
  proof: Iff.trans (coe_eq_zero l) isEmpty_iff.symm

中文:
定理 coe_eq_zero_iff_isEmpty
  条件: (l : List α)
  结论: (l : Multiset α) = 0 ↔ l.isEmpty
  证明: Iff.trans (coe_eq_zero l) isEmpty_iff.symm

Depends on / 依赖: Iff.trans, coe_eq_zero, isEmpty_iff, isEmpty_iff.symm
-/
theorem coe_eq_zero_iff_isEmpty (l : List α) : (l : Multiset α) = 0 ↔ l.isEmpty :=
  Iff.trans (coe_eq_zero l) isEmpty_iff.symm

/-! ### `Multiset.cons` -/

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α) (s : Multiset α)
  body: Quot.liftOn s (fun l => (a :: l : Multiset α)) fun _ _ p => Quot.sound (p.cons a)

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

中文:
定义 cons
  签名: (a : α) (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (a :: l : Multiset α)) fun _ _ p => Quot.sound (p.cons a)

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, liftOn, p.cons
-/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (a :: l : Multiset α)) fun _ _ p => Quot.sound (p.cons a)

@[inherit_doc Multiset.cons]
infixr:67 " ::ₘ " => Multiset.cons

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert α (Multiset α)
  body: ⟨cons⟩

@[simp]

中文:
实例 :
  签名: Insert α (Multiset α)
  定义体: ⟨cons⟩

@[simp]
-/
instance : Insert α (Multiset α) :=
  ⟨cons⟩

@[simp]
/--
theorem `insert_eq_cons` / 定理 `insert_eq_cons`

English:
theorem insert_eq_cons
  given: (a : α) (s : Multiset α)
  statement: insert a s = a ::ₘ s
  proof: rfl

@[simp]

中文:
定理 insert_eq_cons
  条件: (a : α) (s : Multiset α)
  结论: insert a s = a ::ₘ s
  证明: rfl

@[simp]
-/
theorem insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s :=
  rfl

@[simp]
/--
theorem `cons_coe` / 定理 `cons_coe`

English:
theorem cons_coe
  given: (a : α) (l : List α)
  statement: (a ::ₘ l : Multiset α) = (a :: l : List α)
  proof: rfl

@[simp]

中文:
定理 cons_coe
  条件: (a : α) (l : List α)
  结论: (a ::ₘ l : Multiset α) = (a :: l : List α)
  证明: rfl

@[simp]
-/
theorem cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α) :=
  rfl

@[simp]
/--
theorem `cons_inj_left` / 定理 `cons_inj_left`

English:
theorem cons_inj_left
  given: {a b : α} (s : Multiset α)
  statement: a ::ₘ s = b ::ₘ s ↔ a = b
  proof: ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
singleton_perm_singleton.1 (perm_append_right_iff _).1 this,
    congr_arg (· ::ₘ _)⟩

@[simp]

中文:
定理 cons_inj_left
  条件: {a b : α} (s : Multiset α)
  结论: a ::ₘ s = b ::ₘ s ↔ a = b
  证明: ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
singleton_perm_singleton.1 (perm_append_right_iff _).1 this,
    congr_arg (· ::ₘ _)⟩

@[simp]

Depends on / 依赖: Quot.inductionOn, Quotient, Quotient.exact, congr_arg, inductionOn, perm_append_right_iff, singleton_perm_singleton
-/
theorem cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b :=
  ⟨Quot.inductionOn s fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotient.exact e
singleton_perm_singleton.1 (perm_append_right_iff _).1 this,
    congr_arg (· ::ₘ _)⟩

@[simp]
/--
theorem `cons_inj_right` / 定理 `cons_inj_right`

English:
theorem cons_inj_right
  given: (a : α)
  statement: forall {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t
  proof: by
  rintro ⟨l₁⟩ ⟨l₂⟩; simp

@[elab_as_elim]

中文:
定理 cons_inj_right
  条件: (a : α)
  结论: 对任意 {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t
  证明: by
  rintro ⟨l₁⟩ ⟨l₂⟩; simp

@[elab_as_elim]
-/
theorem cons_inj_right (a : α) : forall {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t := by
  rintro ⟨l₁⟩ ⟨l₂⟩; simp

@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {p : Multiset α -> Prop} (empty : p 0)
  proof: by
  rintro ⟨l⟩; induction l with | nil => exact empty | cons _ _ ih => exact cons _ _ ih

@[elab_as_elim]

中文:
定理 induction
  结论: {p : Multiset α -> 命题} (empty : p 0)
  证明: by
  rintro ⟨l⟩; induction l with | nil => exact empty | cons _ _ ih => exact cons _ _ ih

@[elab_as_elim]
-/
protected theorem induction {p : Multiset α -> Prop} (empty : p 0)
    (cons : forall (a : α) (s : Multiset α), p s -> p (a ::ₘ s)) : forall s, p s := by
  rintro ⟨l⟩; induction l with | nil => exact empty | cons _ _ ih => exact cons _ _ ih

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {p : Multiset α -> Prop} (s : Multiset α) (empty : p 0)
  proof: Multiset.induction empty cons s

中文:
定理 induction_on
  结论: {p : Multiset α -> 命题} (s : Multiset α) (empty : p 0)
  证明: Multiset.induction empty cons s
-/
protected theorem induction_on {p : Multiset α -> Prop} (s : Multiset α) (empty : p 0)
    (cons : forall (a : α) (s : Multiset α), p s -> p (a ::ₘ s)) : p s :=
  Multiset.induction empty cons s

/--
theorem `cons_swap` / 定理 `cons_swap`

English:
theorem cons_swap
  given: (a b : α) (s : Multiset α)
  statement: a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s
  proof: Quot.inductionOn s fun _ => Quotient.sound Perm.swap _ _ _

中文:
定理 cons_swap
  条件: (a b : α) (s : Multiset α)
  结论: a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s
  证明: Quot.inductionOn s fun _ => Quotient.sound Perm.swap _ _ _

Depends on / 依赖: Perm.swap, Quot.inductionOn, Quotient, Quotient.sound, inductionOn
-/
theorem cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
Quot.inductionOn s fun _ => Quotient.sound Perm.swap _ _ _

section Rec

variable {C : Multiset α -> Sort*}

/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `Multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: (C_0 : C 0) (C_cons : forall a m, C m -> C (a ::ₘ m))
  body: Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun _ _ h =>
    h.rec_heq
      (fun hl _ => by congr 1; exact Quot.sound hl)
      (C_cons_heq _ _ ⟦_⟧ _)

中文:
定义 rec
  签名: (C_0 : C 0) (C_cons : 对任意 a m, C m -> C (a ::ₘ m))
  定义体: Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun _ _ h =>
    h.rec_heq
      (fun hl _ => by congr 1; exact Quot.sound hl)
      (C_cons_heq _ _ ⟦_⟧ _)

Depends on / 依赖: C_cons, C_cons_heq, List.rec, Quot.sound, Quotient, Quotient.hrecOn, h.rec_heq, hrecOn, rec_heq
-/
def rec (C_0 : C 0) (C_cons : forall a m, C m -> C (a ::ₘ m))
    (C_cons_heq :
      forall a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b))
    (m : Multiset α) : C m :=
  Quotient.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b) fun _ _ h =>
    h.rec_heq
      (fun hl _ => by congr 1; exact Quot.sound hl)
      (C_cons_heq _ _ ⟦_⟧ _)

/-- Companion to `Multiset.rec` with more convenient argument order. -/
@[elab_as_elim]
protected
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: (m : Multiset α) (C_0 : C 0) (C_cons : forall a m, C m -> C (a ::ₘ m))
  body: Multiset.rec C_0 C_cons C_cons_heq m

中文:
定义 recOn
  签名: (m : Multiset α) (C_0 : C 0) (C_cons : 对任意 a m, C m -> C (a ::ₘ m))
  定义体: Multiset.rec C_0 C_cons C_cons_heq m

Depends on / 依赖: C_cons, C_cons_heq, Multiset, Multiset.rec
-/
def recOn (m : Multiset α) (C_0 : C 0) (C_cons : forall a m, C m -> C (a ::ₘ m))
    (C_cons_heq :
      forall a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)) :
    C m :=
  Multiset.rec C_0 C_cons C_cons_heq m

variable {C_0 : C 0} {C_cons : forall a m, C m -> C (a ::ₘ m)}
  {C_cons_heq :
    forall a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)}

@[simp]
/--
theorem `recOn_0` / 定理 `recOn_0`

English:
theorem recOn_0
  statement: @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0
  proof: rfl

@[simp]

中文:
定理 recOn_0
  结论: @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0
  证明: rfl

@[simp]
-/
theorem recOn_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0 :=
  rfl

@[simp]
/--
theorem `recOn_cons` / 定理 `recOn_cons`

English:
theorem recOn_cons
  given: (a : α) (m : Multiset α)
  proof: Quotient.inductionOn m fun _ => rfl

中文:
定理 recOn_cons
  条件: (a : α) (m : Multiset α)
  证明: Quotient.inductionOn m fun _ => rfl

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem recOn_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq) :=
  Quotient.inductionOn m fun _ => rfl

end Rec

section Mem

@[simp, grind =]
/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  given: {a b : α} {s : Multiset α}
  statement: a in b ::ₘ s ↔ a = b ∨ a in s
  proof: Quot.inductionOn s fun _ => List.mem_cons

中文:
定理 mem_cons
  条件: {a b : α} {s : Multiset α}
  结论: a in b ::ₘ s ↔ a = b ∨ a in s
  证明: Quot.inductionOn s fun _ => List.mem_cons

Depends on / 依赖: List.mem_cons, Quot.inductionOn, inductionOn, mem_cons
-/
theorem mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ a = b ∨ a in s :=
  Quot.inductionOn s fun _ => List.mem_cons

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: {a b : α} {s : Multiset α} (h : a in s)
  statement: a in b ::ₘ s
  proof: mem_cons.2 Or.inr h

中文:
定理 mem_cons_of_mem
  条件: {a b : α} {s : Multiset α} (h : a in s)
  结论: a in b ::ₘ s
  证明: mem_cons.2 Or.inr h

Depends on / 依赖: Or.inr, mem_cons
-/
theorem mem_cons_of_mem {a b : α} {s : Multiset α} (h : a in s) : a in b ::ₘ s :=
mem_cons.2 Or.inr h

/--
theorem `mem_cons_self` / 定理 `mem_cons_self`

English:
theorem mem_cons_self
  given: (a : α) (s : Multiset α)
  statement: a in a ::ₘ s
  proof: mem_cons.2 (Or.inl rfl)

中文:
定理 mem_cons_self
  条件: (a : α) (s : Multiset α)
  结论: a in a ::ₘ s
  证明: mem_cons.2 (Or.inl rfl)

Depends on / 依赖: Or.inl, mem_cons
-/
theorem mem_cons_self (a : α) (s : Multiset α) : a in a ::ₘ s :=
  mem_cons.2 (Or.inl rfl)

/--
theorem `forall_mem_cons` / 定理 `forall_mem_cons`

English:
theorem forall_mem_cons
  given: {p : α -> Prop} {a : α} {s : Multiset α}
  proof: Quotient.inductionOn' s fun _ => List.forall_mem_cons

中文:
定理 forall_mem_cons
  条件: {p : α -> 命题} {a : α} {s : Multiset α}
  证明: Quotient.inductionOn' s fun _ => List.forall_mem_cons

Depends on / 依赖: List.forall_mem_cons, Quotient, Quotient.inductionOn, forall_mem_cons, inductionOn
-/
theorem forall_mem_cons {p : α -> Prop} {a : α} {s : Multiset α} :
    (forall x in a ::ₘ s, p x) ↔ p a ∧ forall x in s, p x :=
  Quotient.inductionOn' s fun _ => List.forall_mem_cons

/--
theorem `exists_cons_of_mem` / 定理 `exists_cons_of_mem`

English:
theorem exists_cons_of_mem
  given: {s : Multiset α} {a : α}
  statement: a in s -> exists t, s = a ::ₘ t
  proof: Quot.inductionOn s fun l (h : a in l) =>
    let ⟨l₁, l₂, e⟩ := append_of_mem h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp, grind ←]

中文:
定理 exists_cons_of_mem
  条件: {s : Multiset α} {a : α}
  结论: a in s -> 存在 t, s = a ::ₘ t
  证明: Quot.inductionOn s fun l (h : a in l) =>
    let ⟨l₁, l₂, e⟩ := append_of_mem h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp, grind ←]

Depends on / 依赖: Quot.inductionOn, Quot.sound, append_of_mem, e.symm, inductionOn, perm_middle
-/
theorem exists_cons_of_mem {s : Multiset α} {a : α} : a in s -> exists t, s = a ::ₘ t :=
  Quot.inductionOn s fun l (h : a in l) =>
    let ⟨l₁, l₂, e⟩ := append_of_mem h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp, grind ←]
/--
theorem `notMem_zero` / 定理 `notMem_zero`

English:
theorem notMem_zero
  given: (a : α)
  statement: a ∉ (0 : Multiset α)
  proof: List.not_mem_nil

中文:
定理 notMem_zero
  条件: (a : α)
  结论: a ∉ (0 : Multiset α)
  证明: List.not_mem_nil

Depends on / 依赖: List.not_mem_nil, not_mem_nil
-/
theorem notMem_zero (a : α) : a ∉ (0 : Multiset α) :=
  List.not_mem_nil

/--
theorem `eq_zero_of_forall_notMem` / 定理 `eq_zero_of_forall_notMem`

English:
theorem eq_zero_of_forall_notMem
  given: {s : Multiset α}
  statement: (forall x, x ∉ s) -> s = 0
  proof: Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl

中文:
定理 eq_zero_of_forall_notMem
  条件: {s : Multiset α}
  结论: (对任意 x, x ∉ s) -> s = 0
  证明: Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl

Depends on / 依赖: Quot.inductionOn, eq_nil_iff_forall_not_mem, eq_nil_iff_forall_not_mem.mpr, inductionOn
-/
theorem eq_zero_of_forall_notMem {s : Multiset α} : (forall x, x ∉ s) -> s = 0 :=
  Quot.inductionOn s fun l H => by rw [eq_nil_iff_forall_not_mem.mpr H]; rfl

/--
theorem `eq_zero_iff_forall_notMem` / 定理 `eq_zero_iff_forall_notMem`

English:
theorem eq_zero_iff_forall_notMem
  given: {s : Multiset α}
  statement: s = 0 ↔ forall a, a ∉ s
  proof: ⟨fun h => h.symm ▸ fun _ => notMem_zero _, eq_zero_of_forall_notMem⟩

中文:
定理 eq_zero_iff_forall_notMem
  条件: {s : Multiset α}
  结论: s = 0 ↔ 对任意 a, a ∉ s
  证明: ⟨fun h => h.symm ▸ fun _ => notMem_zero _, eq_zero_of_forall_notMem⟩

Depends on / 依赖: eq_zero_of_forall_notMem, h.symm, notMem_zero
-/
theorem eq_zero_iff_forall_notMem {s : Multiset α} : s = 0 ↔ forall a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => notMem_zero _, eq_zero_of_forall_notMem⟩

/--
theorem `exists_mem_of_ne_zero` / 定理 `exists_mem_of_ne_zero`

English:
theorem exists_mem_of_ne_zero
  given: {s : Multiset α}
  statement: s != 0 -> exists a : α, a in s
  proof: Quot.inductionOn s fun l hl =>
    match l, hl with
| [], h => False.elim h rfl
    | a :: l, _ => ⟨a, by simp⟩

中文:
定理 exists_mem_of_ne_zero
  条件: {s : Multiset α}
  结论: s != 0 -> 存在 a : α, a in s
  证明: Quot.inductionOn s fun l hl =>
    match l, hl with
| [], h => False.elim h rfl
    | a :: l, _ => ⟨a, by simp⟩

Depends on / 依赖: False.elim, Quot.inductionOn, inductionOn
-/
theorem exists_mem_of_ne_zero {s : Multiset α} : s != 0 -> exists a : α, a in s :=
  Quot.inductionOn s fun l hl =>
    match l, hl with
| [], h => False.elim h rfl
    | a :: l, _ => ⟨a, by simp⟩

/--
theorem `empty_or_exists_mem` / 定理 `empty_or_exists_mem`

English:
theorem empty_or_exists_mem
  given: (s : Multiset α)
  statement: s = 0 ∨ exists a, a in s
  proof: or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]

中文:
定理 empty_or_exists_mem
  条件: (s : Multiset α)
  结论: s = 0 ∨ 存在 a, a in s
  证明: or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]

Depends on / 依赖: Multiset, Multiset.exists_mem_of_ne_zero, exists_mem_of_ne_zero, or_iff_not_imp_left, or_iff_not_imp_left.mpr
-/
theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ exists a, a in s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]
/--
theorem `zero_ne_cons` / 定理 `zero_ne_cons`

English:
theorem zero_ne_cons
  given: {a : α} {m : Multiset α}
  statement: 0 != a ::ₘ m
  proof: fun h =>
  have : a in (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  notMem_zero _ this

@[simp]

中文:
定理 zero_ne_cons
  条件: {a : α} {m : Multiset α}
  结论: 0 != a ::ₘ m
  证明: fun h =>
  have : a in (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  notMem_zero _ this

@[simp]
-/
theorem zero_ne_cons {a : α} {m : Multiset α} : 0 != a ::ₘ m := fun h =>
  have : a in (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  notMem_zero _ this

@[simp]
/--
theorem `cons_ne_zero` / 定理 `cons_ne_zero`

English:
theorem cons_ne_zero
  given: {a : α} {m : Multiset α}
  statement: a ::ₘ m != 0
  proof: zero_ne_cons.symm

中文:
定理 cons_ne_zero
  条件: {a : α} {m : Multiset α}
  结论: a ::ₘ m != 0
  证明: zero_ne_cons.symm

Depends on / 依赖: zero_ne_cons, zero_ne_cons.symm
-/
theorem cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m != 0 :=
  zero_ne_cons.symm

/--
theorem `cons_eq_cons` / 定理 `cons_eq_cons`

English:
theorem cons_eq_cons
  given: {a b : α} {as bs : Multiset α}
  proof: by
  have : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases h : a = b
    · subst h
      simp_all
    · have : a in b ::ₘ bs := eq ▸ mem_cons_self _ _
      have : a in bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp only [h, hcs, false_a

中文:
定理 cons_eq_cons
  条件: {a b : α} {as bs : Multiset α}
  证明: by
  have : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases h : a = b
    · subst h
      simp_all
    · have : a in b ::ₘ bs := eq ▸ mem_cons_self _ _
      have : a in bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp only [h, hcs, false_a

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, cons_inj_right, cons_swap, exists_cons_of_mem, exists_eq_right, false_and, false_or, mem_cons_self, ne_eq, not_false_eq_true, true_and
-/
theorem cons_eq_cons {a b : α} {as bs : Multiset α} :
    a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a != b ∧ exists cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs := by
  have : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases h : a = b
    · subst h
      simp_all
    · have : a in b ::ₘ bs := eq ▸ mem_cons_self _ _
      have : a in bs := by simpa [h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp only [h, hcs, false_and, ne_eq, not_false_eq_true, cons_inj_right, exists_eq_right',
        true_and, false_or]
      have : a ::ₘ as = b ::ₘ a ::ₘ cs := by simp [eq, hcs]
      have : a ::ₘ as = a ::ₘ b ::ₘ cs := by rwa [cons_swap]
      simpa using this
  · intro h
    rcases h with (⟨eq₁, eq₂⟩ | ⟨_, cs, eq₁, eq₂⟩)
    · simp [*]
    · simp [*, cons_swap a b]

end Mem



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton α (Multiset α)
  body: ⟨fun a => a ::ₘ 0⟩

中文:
实例 :
  签名: Singleton α (Multiset α)
  定义体: ⟨fun a => a ::ₘ 0⟩
-/
instance : Singleton α (Multiset α) :=
  ⟨fun a => a ::ₘ 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulSingleton α (Multiset α)
  body: ⟨fun _ => rfl⟩

@[simp]

中文:
实例 :
  签名: LawfulSingleton α (Multiset α)
  定义体: ⟨fun _ => rfl⟩

@[simp]
-/
instance : LawfulSingleton α (Multiset α) :=
  ⟨fun _ => rfl⟩

@[simp]
/--
theorem `cons_zero` / 定理 `cons_zero`

English:
theorem cons_zero
  given: (a : α)
  statement: a ::ₘ 0 = {a}
  proof: rfl

@[simp, norm_cast]

中文:
定理 cons_zero
  条件: (a : α)
  结论: a ::ₘ 0 = {a}
  证明: rfl

@[simp, norm_cast]
-/
theorem cons_zero (a : α) : a ::ₘ 0 = {a} :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_singleton` / 定理 `coe_singleton`

English:
theorem coe_singleton
  given: (a : α)
  statement: ([a] : Multiset α) = {a}
  proof: rfl

@[simp]

中文:
定理 coe_singleton
  条件: (a : α)
  结论: ([a] : Multiset α) = {a}
  证明: rfl

@[simp]
-/
theorem coe_singleton (a : α) : ([a] : Multiset α) = {a} :=
  rfl

@[simp]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: {a b : α}
  statement: b in ({a} : Multiset α) ↔ b = a
  proof: by
  simp only [← cons_zero, mem_cons, iff_self, or_false, notMem_zero]

中文:
定理 mem_singleton
  条件: {a b : α}
  结论: b in ({a} : Multiset α) ↔ b = a
  证明: by
  simp only [← cons_zero, mem_cons, iff_self, or_false, notMem_zero]

Depends on / 依赖: cons_zero, iff_self, mem_cons, notMem_zero, or_false
-/
theorem mem_singleton {a b : α} : b in ({a} : Multiset α) ↔ b = a := by
  simp only [← cons_zero, mem_cons, iff_self, or_false, notMem_zero]

/--
theorem `mem_singleton_self` / 定理 `mem_singleton_self`

English:
theorem mem_singleton_self
  given: (a : α)
  statement: a in ({a} : Multiset α)
  proof: by
  rw [← cons_zero]
  exact mem_cons_self _ _

@[simp]

中文:
定理 mem_singleton_self
  条件: (a : α)
  结论: a in ({a} : Multiset α)
  证明: by
  rw [← cons_zero]
  exact mem_cons_self _ _

@[simp]

Depends on / 依赖: cons_zero, mem_cons_self
-/
theorem mem_singleton_self (a : α) : a in ({a} : Multiset α) := by
  rw [← cons_zero]
  exact mem_cons_self _ _

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  given: {a b : α}
  statement: ({a} : Multiset α) = {b} ↔ a = b
  proof: by
  simp_rw [← cons_zero]
  exact cons_inj_left _

@[simp, norm_cast]

中文:
定理 singleton_inj
  条件: {a b : α}
  结论: ({a} : Multiset α) = {b} ↔ a = b
  证明: by
  simp_rw [← cons_zero]
  exact cons_inj_left _

@[simp, norm_cast]

Depends on / 依赖: cons_inj_left, cons_zero, simp_rw
-/
theorem singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b := by
  simp_rw [← cons_zero]
  exact cons_inj_left _

@[simp, norm_cast]
/--
theorem `coe_eq_singleton` / 定理 `coe_eq_singleton`

English:
theorem coe_eq_singleton
  given: {l : List α} {a : α}
  statement: (l : Multiset α) = {a} ↔ l = [a]
  proof: by
  rw [← coe_singleton]; rw [coe_eq_coe]; rw [List.perm_singleton]

@[simp]

中文:
定理 coe_eq_singleton
  条件: {l : List α} {a : α}
  结论: (l : Multiset α) = {a} ↔ l = [a]
  证明: by
  rw [← coe_singleton]; rw [coe_eq_coe]; rw [List.perm_singleton]

@[simp]

Depends on / 依赖: List.perm_singleton, coe_eq_coe, coe_singleton, perm_singleton
-/
theorem coe_eq_singleton {l : List α} {a : α} : (l : Multiset α) = {a} ↔ l = [a] := by
  rw [← coe_singleton]; rw [coe_eq_coe]; rw [List.perm_singleton]

@[simp]
/--
theorem `singleton_eq_cons_iff` / 定理 `singleton_eq_cons_iff`

English:
theorem singleton_eq_cons_iff
  given: {a b : α} (m : Multiset α)
  statement: {a} = b ::ₘ m ↔ a = b ∧ m = 0
  proof: by
  rw [← cons_zero]; rw [cons_eq_cons]
  simp [eq_comm]

中文:
定理 singleton_eq_cons_iff
  条件: {a b : α} (m : Multiset α)
  结论: {a} = b ::ₘ m ↔ a = b ∧ m = 0
  证明: by
  rw [← cons_zero]; rw [cons_eq_cons]
  simp [eq_comm]

Depends on / 依赖: cons_eq_cons, cons_zero, eq_comm
-/
theorem singleton_eq_cons_iff {a b : α} (m : Multiset α) : {a} = b ::ₘ m ↔ a = b ∧ m = 0 := by
  rw [← cons_zero]; rw [cons_eq_cons]
  simp [eq_comm]

/--
theorem `pair_comm` / 定理 `pair_comm`

English:
theorem pair_comm
  given: (x y : α)
  statement: ({x, y} : Multiset α) = {y, x}
  proof: cons_swap x y 0

中文:
定理 pair_comm
  条件: (x y : α)
  结论: ({x, y} : Multiset α) = {y, x}
  证明: cons_swap x y 0

Depends on / 依赖: cons_swap
-/
theorem pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x} :=
  cons_swap x y 0

/-! ### `Multiset.Subset` -/


section Subset
variable {s : Multiset α} {a : α}

@[simp]
/--
theorem `zero_subset` / 定理 `zero_subset`

English:
theorem zero_subset
  given: (s : Multiset α)
  statement: 0 subseteq s
  proof: fun _ => not_mem_nil.elim

中文:
定理 zero_subset
  条件: (s : Multiset α)
  结论: 0 subseteq s
  证明: fun _ => not_mem_nil.elim

Depends on / 依赖: not_mem_nil, not_mem_nil.elim
-/
theorem zero_subset (s : Multiset α) : 0 subseteq s := fun _ => not_mem_nil.elim

/--
theorem `subset_cons` / 定理 `subset_cons`

English:
theorem subset_cons
  given: (s : Multiset α) (a : α)
  statement: s subseteq a ::ₘ s
  proof: fun _ => mem_cons_of_mem

中文:
定理 subset_cons
  条件: (s : Multiset α) (a : α)
  结论: s subseteq a ::ₘ s
  证明: fun _ => mem_cons_of_mem

Depends on / 依赖: mem_cons_of_mem
-/
theorem subset_cons (s : Multiset α) (a : α) : s subseteq a ::ₘ s := fun _ => mem_cons_of_mem

/--
theorem `ssubset_cons` / 定理 `ssubset_cons`

English:
theorem ssubset_cons
  given: {s : Multiset α} {a : α} (ha : a ∉ s)
  statement: s ⊂ a ::ₘ s
  proof: ⟨subset_cons _ _, fun h => ha h mem_cons_self _ _⟩

@[simp]

中文:
定理 ssubset_cons
  条件: {s : Multiset α} {a : α} (ha : a ∉ s)
  结论: s ⊂ a ::ₘ s
  证明: ⟨subset_cons _ _, fun h => ha h mem_cons_self _ _⟩

@[simp]

Depends on / 依赖: mem_cons_self, subset_cons
-/
theorem ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s :=
⟨subset_cons _ _, fun h => ha h mem_cons_self _ _⟩

@[simp]
/--
theorem `cons_subset` / 定理 `cons_subset`

English:
theorem cons_subset
  given: {a : α} {s t : Multiset α}
  statement: a ::ₘ s subseteq t ↔ a in t ∧ s subseteq t
  proof: by
  simp [subset_iff, or_imp, forall_and]

中文:
定理 cons_subset
  条件: {a : α} {s t : Multiset α}
  结论: a ::ₘ s subseteq t ↔ a in t ∧ s subseteq t
  证明: by
  simp [subset_iff, or_imp, forall_and]

Depends on / 依赖: forall_and, or_imp, subset_iff
-/
theorem cons_subset {a : α} {s t : Multiset α} : a ::ₘ s subseteq t ↔ a in t ∧ s subseteq t := by
  simp [subset_iff, or_imp, forall_and]

/--
theorem `cons_subset_cons` / 定理 `cons_subset_cons`

English:
theorem cons_subset_cons
  given: {a : α} {s t : Multiset α}
  statement: s subseteq t -> a ::ₘ s subseteq a ::ₘ t
  proof: Quotient.inductionOn₂ s t fun _ _ => List.cons_subset_cons _

中文:
定理 cons_subset_cons
  条件: {a : α} {s t : Multiset α}
  结论: s subseteq t -> a ::ₘ s subseteq a ::ₘ t
  证明: Quotient.inductionOn₂ s t fun _ _ => List.cons_subset_cons _

Depends on / 依赖: List.cons_subset_cons, Quotient, Quotient.inductionOn, cons_subset_cons
-/
theorem cons_subset_cons {a : α} {s t : Multiset α} : s subseteq t -> a ::ₘ s subseteq a ::ₘ t :=
  Quotient.inductionOn₂ s t fun _ _ => List.cons_subset_cons _

/--
theorem `eq_zero_of_subset_zero` / 定理 `eq_zero_of_subset_zero`

English:
theorem eq_zero_of_subset_zero
  given: {s : Multiset α} (h : s subseteq 0)
  statement: s = 0
  proof: eq_zero_of_forall_notMem fun _ hx => notMem_zero _ (h hx)

中文:
定理 eq_zero_of_subset_zero
  条件: {s : Multiset α} (h : s subseteq 0)
  结论: s = 0
  证明: eq_zero_of_forall_notMem fun _ hx => notMem_zero _ (h hx)

Depends on / 依赖: eq_zero_of_forall_notMem, notMem_zero
-/
theorem eq_zero_of_subset_zero {s : Multiset α} (h : s subseteq 0) : s = 0 :=
  eq_zero_of_forall_notMem fun _ hx => notMem_zero _ (h hx)

/--
lemma `subset_zero` / 引理 `subset_zero`

English:
lemma subset_zero
  statement: s subseteq 0 ↔ s = 0
  proof: ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩

中文:
引理 subset_zero
  结论: s subseteq 0 ↔ s = 0
  证明: ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩
-/
@[simp] lemma subset_zero : s subseteq 0 ↔ s = 0 :=
  ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩

/--
lemma `zero_ssubset` / 引理 `zero_ssubset`

English:
lemma zero_ssubset
  statement: 0 ⊂ s ↔ s != 0
  proof: by
  simp [(right_iff_left_not_left : 0 ⊂ s ↔ 0 subseteq s ∧ ¬s subseteq 0)]

中文:
引理 zero_ssubset
  结论: 0 ⊂ s ↔ s != 0
  证明: by
  simp [(right_iff_left_not_left : 0 ⊂ s ↔ 0 subseteq s ∧ ¬s subseteq 0)]
-/
@[simp] lemma zero_ssubset : 0 ⊂ s ↔ s != 0 := by
  simp [(right_iff_left_not_left : 0 ⊂ s ↔ 0 subseteq s ∧ ¬s subseteq 0)]

/--
lemma `singleton_subset` / 引理 `singleton_subset`

English:
lemma singleton_subset
  statement: {a} subseteq s ↔ a in s
  proof: by simp [subset_iff]

中文:
引理 singleton_subset
  结论: {a} subseteq s ↔ a in s
  证明: by simp [subset_iff]
-/
@[simp] lemma singleton_subset : {a} subseteq s ↔ a in s := by simp [subset_iff]

/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {p : Multiset α -> Prop} (S : Multiset α) (h₁ : p 0)
  proof: @Multiset.induction_on α (fun T => T subseteq S -> p T) S (fun _ => h₁)
    (fun _ _ hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

中文:
定理 induction_on'
  结论: {p : Multiset α -> 命题} (S : Multiset α) (h₁ : p 0)
  证明: @Multiset.induction_on α (fun T => T subseteq S -> p T) S (fun _ => h₁)
    (fun _ _ hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

Depends on / 依赖: Multiset, Multiset.induction_on, Subset, Subset.refl, cons_subset, induction_on, subseteq
-/
theorem induction_on' {p : Multiset α -> Prop} (S : Multiset α) (h₁ : p 0)
    (h₂ : forall {a s}, a in S -> s subseteq S -> p s -> p (insert a s)) : p S :=
  @Multiset.induction_on α (fun T => T subseteq S -> p T) S (fun _ => h₁)
    (fun _ _ hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

end Subset

/-! ### Partial order on `Multiset`s -/

section

variable {s t : Multiset α} {a : α}

/--
theorem `zero_le` / 定理 `zero_le`

English:
theorem zero_le
  given: (s : Multiset α)
  statement: 0 <= s
  proof: Quot.inductionOn s fun l => (nil_sublist l).subperm

中文:
定理 zero_le
  条件: (s : Multiset α)
  结论: 0 <= s
  证明: Quot.inductionOn s fun l => (nil_sublist l).subperm

Depends on / 依赖: Quot.inductionOn, inductionOn, nil_sublist, subperm
-/
theorem zero_le (s : Multiset α) : 0 <= s :=
  Quot.inductionOn s fun l => (nil_sublist l).subperm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Multiset α)
  body: 0
  bot_le := zero_le

中文:
实例 :
  签名: OrderBot (Multiset α)
  定义体: 0
  bot_le := zero_le
-/
instance : OrderBot (Multiset α) where
  bot := 0
  bot_le := zero_le

/-- This is a `rfl` and `simp` version of `bot_eq_zero`. -/
@[simp]
/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : Multiset α) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  结论: (⊥ : Multiset α) = 0
  证明: rfl
-/
theorem bot_eq_zero : (⊥ : Multiset α) = 0 :=
  rfl

/--
theorem `le_zero` / 定理 `le_zero`

English:
theorem le_zero
  statement: s <= 0 ↔ s = 0
  proof: le_bot_iff

中文:
定理 le_zero
  结论: s <= 0 ↔ s = 0
  证明: le_bot_iff

Depends on / 依赖: le_bot_iff
-/
theorem le_zero : s <= 0 ↔ s = 0 :=
  le_bot_iff

/--
theorem `lt_cons_self` / 定理 `lt_cons_self`

English:
theorem lt_cons_self
  given: (s : Multiset α) (a : α)
  statement: s < a ::ₘ s
  proof: Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons_self _ _).subperm,
      fun p => _root_.ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

中文:
定理 lt_cons_self
  条件: (s : Multiset α) (a : α)
  结论: s < a ::ₘ s
  证明: Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons_self _ _).subperm,
      fun p => _root_.ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

Depends on / 依赖: Quot.inductionOn, _root_, _root_.ne_of_lt, inductionOn, length, length_eq, lt_iff_le_and_ne, lt_succ_self, ne_of_lt, p.length_eq, sublist_cons_self, subperm
-/
theorem lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s :=
  Quot.inductionOn s fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by simpa [lt_iff_le_and_ne]
    ⟨(sublist_cons_self _ _).subperm,
      fun p => _root_.ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

/--
theorem `le_cons_self` / 定理 `le_cons_self`

English:
theorem le_cons_self
  given: (s : Multiset α) (a : α)
  statement: s <= a ::ₘ s
  proof: le_of_lt lt_cons_self _ _

中文:
定理 le_cons_self
  条件: (s : Multiset α) (a : α)
  结论: s <= a ::ₘ s
  证明: le_of_lt lt_cons_self _ _

Depends on / 依赖: le_of_lt, lt_cons_self
-/
theorem le_cons_self (s : Multiset α) (a : α) : s <= a ::ₘ s :=
le_of_lt lt_cons_self _ _

/--
theorem `cons_le_cons_iff` / 定理 `cons_le_cons_iff`

English:
theorem cons_le_cons_iff
  given: (a : α)
  statement: a ::ₘ s <= a ::ₘ t ↔ s <= t
  proof: Quotient.inductionOn₂ s t fun _ _ => subperm_cons a

中文:
定理 cons_le_cons_iff
  条件: (a : α)
  结论: a ::ₘ s <= a ::ₘ t ↔ s <= t
  证明: Quotient.inductionOn₂ s t fun _ _ => subperm_cons a
-/
@[simp] theorem cons_le_cons_iff (a : α) : a ::ₘ s <= a ::ₘ t ↔ s <= t :=
  Quotient.inductionOn₂ s t fun _ _ => subperm_cons a

/--
theorem `cons_le_cons` / 定理 `cons_le_cons`

English:
theorem cons_le_cons
  given: (a : α)
  statement: s <= t -> a ::ₘ s <= a ::ₘ t
  proof: (cons_le_cons_iff a).2

中文:
定理 cons_le_cons
  条件: (a : α)
  结论: s <= t -> a ::ₘ s <= a ::ₘ t
  证明: (cons_le_cons_iff a).2

Depends on / 依赖: cons_le_cons_iff
-/
theorem cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ t :=
  (cons_le_cons_iff a).2

/--
lemma `cons_lt_cons_iff` / 引理 `cons_lt_cons_iff`

English:
lemma cons_lt_cons_iff
  statement: a ::ₘ s < a ::ₘ t ↔ s < t
  proof: lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

中文:
引理 cons_lt_cons_iff
  结论: a ::ₘ s < a ::ₘ t ↔ s < t
  证明: lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)
-/
@[simp] lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

/--
lemma `cons_lt_cons` / 引理 `cons_lt_cons`

English:
lemma cons_lt_cons
  given: (a : α) (h : s < t)
  statement: a ::ₘ s < a ::ₘ t
  proof: cons_lt_cons_iff.2 h

中文:
引理 cons_lt_cons
  条件: (a : α) (h : s < t)
  结论: a ::ₘ s < a ::ₘ t
  证明: cons_lt_cons_iff.2 h

Depends on / 依赖: cons_lt_cons_iff
-/
lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

/--
theorem `le_cons_of_notMem` / 定理 `le_cons_of_notMem`

English:
theorem le_cons_of_notMem
  given: (m : a ∉ s)
  statement: s <= a ::ₘ t ↔ s <= t
  proof: by
refine ⟨?_, fun h => le_trans h le_cons_self _ _⟩
  suffices forall {t'}, s <= t' -> a in t' -> a ::ₘ s <= t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine leInductionOn h ?_
  introv s m₁ m₂
  rcases append_of_mem m₂ with ⟨r₁, r₂, rfl⟩
 

中文:
定理 le_cons_of_notMem
  条件: (m : a ∉ s)
  结论: s <= a ::ₘ t ↔ s <= t
  证明: by
refine ⟨?_, fun h => le_trans h le_cons_self _ _⟩
  suffices forall {t'}, s <= t' -> a in t' -> a ::ₘ s <= t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine leInductionOn h ?_
  introv s m₁ m₂
  rcases append_of_mem m₂ with ⟨r₁, r₂, rfl⟩
 

Depends on / 依赖: append_of_mem, cons_le_cons_iff, introv, leInductionOn, le_cons_self, le_trans, mem_cons_self, perm_middle, perm_middle.subperm_left, resolve_right, revert, sublist_or_mem_of_sublist, subperm, subperm_cons, subperm_left
-/
theorem le_cons_of_notMem (m : a ∉ s) : s <= a ::ₘ t ↔ s <= t := by
refine ⟨?_, fun h => le_trans h le_cons_self _ _⟩
  suffices forall {t'}, s <= t' -> a in t' -> a ::ₘ s <= t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine leInductionOn h ?_
  introv s m₁ m₂
  rcases append_of_mem m₂ with ⟨r₁, r₂, rfl⟩
  exact
    perm_middle.subperm_left.2
      ((subperm_cons _).2 <| ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)

/--
theorem `cons_le_of_notMem` / 定理 `cons_le_of_notMem`

English:
theorem cons_le_of_notMem
  given: (hs : a ∉ s)
  statement: a ::ₘ s <= t ↔ a in t ∧ s <= t
  proof: by
  apply Iff.intro (fun h => ⟨subset_of_le h (mem_cons_self a s), le_trans (le_cons_self s a) h⟩)
  rintro ⟨h₁, h₂⟩; rcases exists_cons_of_mem h₁ with ⟨_, rfl⟩
  exact cons_le_cons _ ((le_cons_of_notMem hs).mp h₂)

@[simp]

中文:
定理 cons_le_of_notMem
  条件: (hs : a ∉ s)
  结论: a ::ₘ s <= t ↔ a in t ∧ s <= t
  证明: by
  apply Iff.intro (fun h => ⟨subset_of_le h (mem_cons_self a s), le_trans (le_cons_self s a) h⟩)
  rintro ⟨h₁, h₂⟩; rcases exists_cons_of_mem h₁ with ⟨_, rfl⟩
  exact cons_le_cons _ ((le_cons_of_notMem hs).mp h₂)

@[simp]

Depends on / 依赖: Iff.intro, cons_le_cons, exists_cons_of_mem, le_cons_of_notMem, le_cons_self, le_trans, mem_cons_self, subset_of_le
-/
theorem cons_le_of_notMem (hs : a ∉ s) : a ::ₘ s <= t ↔ a in t ∧ s <= t := by
  apply Iff.intro (fun h => ⟨subset_of_le h (mem_cons_self a s), le_trans (le_cons_self s a) h⟩)
  rintro ⟨h₁, h₂⟩; rcases exists_cons_of_mem h₁ with ⟨_, rfl⟩
  exact cons_le_cons _ ((le_cons_of_notMem hs).mp h₂)

@[simp]
/--
theorem `singleton_ne_zero` / 定理 `singleton_ne_zero`

English:
theorem singleton_ne_zero
  given: (a : α)
  statement: ({a} : Multiset α) != 0
  proof: ne_of_gt (lt_cons_self _ _)

@[simp]
.symm theorem zero_ne_singleton (a : α) : 0 != ({a} : Multiset α) := singleton_ne_zero _

@[simp]

中文:
定理 singleton_ne_zero
  条件: (a : α)
  结论: ({a} : Multiset α) != 0
  证明: ne_of_gt (lt_cons_self _ _)

@[simp]
.symm theorem zero_ne_singleton (a : α) : 0 != ({a} : Multiset α) := singleton_ne_zero _

@[simp]

Depends on / 依赖: lt_cons_self, ne_of_gt
-/
theorem singleton_ne_zero (a : α) : ({a} : Multiset α) != 0 :=
  ne_of_gt (lt_cons_self _ _)

@[simp]
.symm theorem zero_ne_singleton (a : α) : 0 != ({a} : Multiset α) := singleton_ne_zero _

@[simp]
/--
theorem `singleton_le` / 定理 `singleton_le`

English:
theorem singleton_le
  given: {a : α} {s : Multiset α}
  statement: {a} <= s ↔ a in s
  proof: ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨_t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩

中文:
定理 singleton_le
  条件: {a : α} {s : Multiset α}
  结论: {a} <= s ↔ a in s
  证明: ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨_t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩

Depends on / 依赖: cons_le_cons, e.symm, exists_cons_of_mem, mem_of_le, mem_singleton_self, zero_le
-/
theorem singleton_le {a : α} {s : Multiset α} : {a} <= s ↔ a in s :=
  ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨_t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩

/--
lemma `le_singleton` / 引理 `le_singleton`

English:
lemma le_singleton
  statement: s <= {a} ↔ s = 0 ∨ s = {a}
  proof: Quot.induction_on s fun l => by simp only [← coe_singleton, quot_mk_to_coe'', coe_le,
    coe_eq_zero, coe_eq_coe, perm_singleton, subperm_singleton_iff]

中文:
引理 le_singleton
  结论: s <= {a} ↔ s = 0 ∨ s = {a}
  证明: Quot.induction_on s fun l => by simp only [← coe_singleton, quot_mk_to_coe'', coe_le,
    coe_eq_zero, coe_eq_coe, perm_singleton, subperm_singleton_iff]
-/
@[simp] lemma le_singleton : s <= {a} ↔ s = 0 ∨ s = {a} :=
  Quot.induction_on s fun l => by simp only [← coe_singleton, quot_mk_to_coe'', coe_le,
    coe_eq_zero, coe_eq_coe, perm_singleton, subperm_singleton_iff]

/--
lemma `lt_singleton` / 引理 `lt_singleton`

English:
lemma lt_singleton
  statement: s < {a} ↔ s = 0
  proof: by
  simp only [lt_iff_le_and_ne, le_singleton, or_and_right, Ne, and_not_self, or_false,
    and_iff_left_iff_imp]
  rintro rfl
  exact (singleton_ne_zero _).symm

中文:
引理 lt_singleton
  结论: s < {a} ↔ s = 0
  证明: by
  simp only [lt_iff_le_and_ne, le_singleton, or_and_right, Ne, and_not_self, or_false,
    and_iff_left_iff_imp]
  rintro rfl
  exact (singleton_ne_zero _).symm
-/
@[simp] lemma lt_singleton : s < {a} ↔ s = 0 := by
  simp only [lt_iff_le_and_ne, le_singleton, or_and_right, Ne, and_not_self, or_false,
    and_iff_left_iff_imp]
  rintro rfl
  exact (singleton_ne_zero _).symm

/--
lemma `ssubset_singleton_iff` / 引理 `ssubset_singleton_iff`

English:
lemma ssubset_singleton_iff
  statement: s ⊂ {a} ↔ s = 0
  proof: by
  refine ⟨fun hs => eq_zero_of_subset_zero fun b hb => (hs.2 ?_).elim, ?_⟩
  · obtain rfl := mem_singleton.1 (hs.1 hb)
    rwa [singleton_subset]
  · rintro rfl
    simp

中文:
引理 ssubset_singleton_iff
  结论: s ⊂ {a} ↔ s = 0
  证明: by
  refine ⟨fun hs => eq_zero_of_subset_zero fun b hb => (hs.2 ?_).elim, ?_⟩
  · obtain rfl := mem_singleton.1 (hs.1 hb)
    rwa [singleton_subset]
  · rintro rfl
    simp
-/
@[simp] lemma ssubset_singleton_iff : s ⊂ {a} ↔ s = 0 := by
  refine ⟨fun hs => eq_zero_of_subset_zero fun b hb => (hs.2 ?_).elim, ?_⟩
  · obtain rfl := mem_singleton.1 (hs.1 hb)
    rwa [singleton_subset]
  · rintro rfl
    simp

end

/-! ### Cardinality -/

@[simp]
/--
theorem `card_zero` / 定理 `card_zero`

English:
theorem card_zero
  statement: @card α 0 = 0
  proof: rfl

@[simp]

中文:
定理 card_zero
  结论: @card α 0 = 0
  证明: rfl

@[simp]
-/
theorem card_zero : @card α 0 = 0 :=
  rfl

@[simp]
/--
theorem `card_cons` / 定理 `card_cons`

English:
theorem card_cons
  given: (a : α) (s : Multiset α)
  statement: card (a ::ₘ s) = card s + 1
  proof: Quot.inductionOn s fun _l => rfl

@[simp]

中文:
定理 card_cons
  条件: (a : α) (s : Multiset α)
  结论: card (a ::ₘ s) = card s + 1
  证明: Quot.inductionOn s fun _l => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1 :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/--
theorem `card_singleton` / 定理 `card_singleton`

English:
theorem card_singleton
  given: (a : α)
  statement: card ({a} : Multiset α) = 1
  proof: by
  simp only [← cons_zero, card_zero, card_cons]

中文:
定理 card_singleton
  条件: (a : α)
  结论: card ({a} : Multiset α) = 1
  证明: by
  simp only [← cons_zero, card_zero, card_cons]

Depends on / 依赖: card_cons, card_zero, cons_zero
-/
theorem card_singleton (a : α) : card ({a} : Multiset α) = 1 := by
  simp only [← cons_zero, card_zero, card_cons]

/--
theorem `card_pair` / 定理 `card_pair`

English:
theorem card_pair
  given: (a b : α)
  statement: card {a, b} = 2
  proof: by
  rw [insert_eq_cons]; rw [card_cons]; rw [card_singleton]

中文:
定理 card_pair
  条件: (a b : α)
  结论: card {a, b} = 2
  证明: by
  rw [insert_eq_cons]; rw [card_cons]; rw [card_singleton]

Depends on / 依赖: card_cons, card_singleton, insert_eq_cons
-/
theorem card_pair (a b : α) : card {a, b} = 2 := by
  rw [insert_eq_cons]; rw [card_cons]; rw [card_singleton]

/--
theorem `card_eq_one` / 定理 `card_eq_one`

English:
theorem card_eq_one
  given: {s : Multiset α}
  statement: card s = 1 ↔ exists a, s = {a}
  proof: ⟨Quot.inductionOn s fun _l h => (List.length_eq_one_iff.1 h).imp fun _a => congr_arg _,
    fun ⟨_a, e⟩ => e.symm ▸ rfl⟩

中文:
定理 card_eq_one
  条件: {s : Multiset α}
  结论: card s = 1 ↔ 存在 a, s = {a}
  证明: ⟨Quot.inductionOn s fun _l h => (List.length_eq_one_iff.1 h).imp fun _a => congr_arg _,
    fun ⟨_a, e⟩ => e.symm ▸ rfl⟩

Depends on / 依赖: List.length_eq_one_iff, Quot.inductionOn, congr_arg, e.symm, inductionOn, length_eq_one_iff
-/
theorem card_eq_one {s : Multiset α} : card s = 1 ↔ exists a, s = {a} :=
  ⟨Quot.inductionOn s fun _l h => (List.length_eq_one_iff.1 h).imp fun _a => congr_arg _,
    fun ⟨_a, e⟩ => e.symm ▸ rfl⟩

/--
theorem `lt_iff_cons_le` / 定理 `lt_iff_cons_le`

English:
theorem lt_iff_cons_le
  given: {s t : Multiset α}
  statement: s < t ↔ exists a, a ::ₘ s <= t
  proof: ⟨Quotient.inductionOn₂ s t fun _l₁ _l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_card h),
    fun ⟨_a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp]

中文:
定理 lt_iff_cons_le
  条件: {s t : Multiset α}
  结论: s < t ↔ 存在 a, a ::ₘ s <= t
  证明: ⟨Quotient.inductionOn₂ s t fun _l₁ _l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_card h),
    fun ⟨_a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, Subperm, Subperm.exists_of_length_lt, card_lt_card, exists_of_length_lt, le_of_lt, lt_cons_self, lt_of_lt_of_le
-/
theorem lt_iff_cons_le {s t : Multiset α} : s < t ↔ exists a, a ::ₘ s <= t :=
  ⟨Quotient.inductionOn₂ s t fun _l₁ _l₂ h =>
      Subperm.exists_of_length_lt (le_of_lt h) (card_lt_card h),
    fun ⟨_a, h⟩ => lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp]
/--
theorem `card_eq_zero` / 定理 `card_eq_zero`

English:
theorem card_eq_zero
  given: {s : Multiset α}
  statement: card s = 0 ↔ s = 0
  proof: ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩

中文:
定理 card_eq_zero
  条件: {s : Multiset α}
  结论: card s = 0 ↔ s = 0
  证明: ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩

Depends on / 依赖: eq_of_le_of_card_le, le_of_eq, zero_le
-/
theorem card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0 :=
  ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, fun e => by simp [e]⟩

/--
theorem `card_pos` / 定理 `card_pos`

English:
theorem card_pos
  given: {s : Multiset α}
  statement: 0 < card s ↔ s != 0
  proof: Nat.pos_iff_ne_zero.trans not_congr card_eq_zero

中文:
定理 card_pos
  条件: {s : Multiset α}
  结论: 0 < card s ↔ s != 0
  证明: Nat.pos_iff_ne_zero.trans not_congr card_eq_zero

Depends on / 依赖: Nat.pos_iff_ne_zero.trans, card_eq_zero, not_congr, pos_iff_ne_zero
-/
theorem card_pos {s : Multiset α} : 0 < card s ↔ s != 0 :=
Nat.pos_iff_ne_zero.trans not_congr card_eq_zero

/--
theorem `card_pos_iff_exists_mem` / 定理 `card_pos_iff_exists_mem`

English:
theorem card_pos_iff_exists_mem
  given: {s : Multiset α}
  statement: 0 < card s ↔ exists a, a in s
  proof: Quot.inductionOn s fun _l => length_pos_iff_exists_mem

中文:
定理 card_pos_iff_exists_mem
  条件: {s : Multiset α}
  结论: 0 < card s ↔ 存在 a, a in s
  证明: Quot.inductionOn s fun _l => length_pos_iff_exists_mem

Depends on / 依赖: Quot.inductionOn, inductionOn, length_pos_iff_exists_mem
-/
theorem card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ exists a, a in s :=
  Quot.inductionOn s fun _l => length_pos_iff_exists_mem

/--
theorem `card_eq_two` / 定理 `card_eq_two`

English:
theorem card_eq_two
  given: {s : Multiset α}
  statement: card s = 2 ↔ exists x y, s = {x, y}
  proof: ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_two.mp h).imp fun _a => Exists.imp fun _b => congr_arg _,
    fun ⟨_a, _b, e⟩ => e.symm ▸ rfl⟩

中文:
定理 card_eq_two
  条件: {s : Multiset α}
  结论: card s = 2 ↔ 存在 x y, s = {x, y}
  证明: ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_two.mp h).imp fun _a => Exists.imp fun _b => congr_arg _,
    fun ⟨_a, _b, e⟩ => e.symm ▸ rfl⟩

Depends on / 依赖: Exists, Exists.imp, List.length_eq_two.mp, Quot.inductionOn, congr_arg, e.symm, inductionOn, length_eq_two
-/
theorem card_eq_two {s : Multiset α} : card s = 2 ↔ exists x y, s = {x, y} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_two.mp h).imp fun _a => Exists.imp fun _b => congr_arg _,
    fun ⟨_a, _b, e⟩ => e.symm ▸ rfl⟩

/--
theorem `card_eq_three` / 定理 `card_eq_three`

English:
theorem card_eq_three
  given: {s : Multiset α}
  statement: card s = 3 ↔ exists x y z, s = {x, y, z}
  proof: ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_three.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => congr_arg _,
    fun ⟨_a, _b, _c, e⟩ => e.symm ▸ rfl⟩

中文:
定理 card_eq_three
  条件: {s : Multiset α}
  结论: card s = 3 ↔ 存在 x y z, s = {x, y, z}
  证明: ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_three.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => congr_arg _,
    fun ⟨_a, _b, _c, e⟩ => e.symm ▸ rfl⟩

Depends on / 依赖: Exists, Exists.imp, List.length_eq_three.mp, Quot.inductionOn, congr_arg, e.symm, inductionOn, length_eq_three
-/
theorem card_eq_three {s : Multiset α} : card s = 3 ↔ exists x y z, s = {x, y, z} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_three.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => congr_arg _,
    fun ⟨_a, _b, _c, e⟩ => e.symm ▸ rfl⟩

/--
theorem `card_eq_four` / 定理 `card_eq_four`

English:
theorem card_eq_four
  given: {s : Multiset α}
  statement: card s = 4 ↔ exists x y z w, s = {x, y, z, w}
  proof: ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_four.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => Exists.imp fun _d => congr_arg _,
    fun ⟨_a, _b, _c, _d, e⟩ => e.symm ▸ rfl⟩

中文:
定理 card_eq_four
  条件: {s : Multiset α}
  结论: card s = 4 ↔ 存在 x y z w, s = {x, y, z, w}
  证明: ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_four.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => Exists.imp fun _d => congr_arg _,
    fun ⟨_a, _b, _c, _d, e⟩ => e.symm ▸ rfl⟩

Depends on / 依赖: Exists, Exists.imp, List.length_eq_four.mp, Quot.inductionOn, congr_arg, e.symm, inductionOn, length_eq_four
-/
theorem card_eq_four {s : Multiset α} : card s = 4 ↔ exists x y z w, s = {x, y, z, w} :=
  ⟨Quot.inductionOn s fun _l h =>
      (List.length_eq_four.mp h).imp fun _a =>
        Exists.imp fun _b => Exists.imp fun _c => Exists.imp fun _d => congr_arg _,
    fun ⟨_a, _b, _c, _d, e⟩ => e.symm ▸ rfl⟩

/--
theorem `card_eq_succ_iff` / 定理 `card_eq_succ_iff`

English:
theorem card_eq_succ_iff
  given: {s : Multiset α} {n : Nat}
  proof: by
  refine ⟨?_, by aesop⟩
  induction s using Multiset.induction generalizing n with aesop

中文:
定理 card_eq_succ_iff
  条件: {s : Multiset α} {n : 自然数}
  证明: by
  refine ⟨?_, by aesop⟩
  induction s using Multiset.induction generalizing n with aesop

Depends on / 依赖: Multiset, Multiset.induction, generalizing
-/
theorem card_eq_succ_iff {s : Multiset α} {n : Nat} :
    card s = n + 1 ↔ exists a t, a ::ₘ t = s ∧ card t = n := by
  refine ⟨?_, by aesop⟩
  induction s using Multiset.induction generalizing n with aesop

/-! ### Map for partial functions -/

@[simp]
/--
theorem `pmap_zero` / 定理 `pmap_zero`

English:
theorem pmap_zero
  given: {p : α -> Prop} (f : forall a, p a -> β) (h : forall a in (0 : Multiset α), p a)
  proof: rfl

@[simp]

中文:
定理 pmap_zero
  条件: {p : α -> 命题} (f : 对任意 a, p a -> β) (h : 对任意 a in (0 : Multiset α), p a)
  证明: rfl

@[simp]
-/
theorem pmap_zero {p : α -> Prop} (f : forall a, p a -> β) (h : forall a in (0 : Multiset α), p a) :
    pmap f 0 h = 0 :=
  rfl

@[simp]
/--
theorem `pmap_cons` / 定理 `pmap_cons`

English:
theorem pmap_cons
  given: {p : α -> Prop} (f : forall a, p a -> β) (a : α) (m : Multiset α)
  proof: Quotient.inductionOn m fun _l _h => rfl

@[simp]

中文:
定理 pmap_cons
  条件: {p : α -> 命题} (f : 对任意 a, p a -> β) (a : α) (m : Multiset α)
  证明: Quotient.inductionOn m fun _l _h => rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem pmap_cons {p : α -> Prop} (f : forall a, p a -> β) (a : α) (m : Multiset α) :
    forall h : forall b in a ::ₘ m, p b,
      pmap f (a ::ₘ m) h =
f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun a ha => h a mem_cons_of_mem ha :=
  Quotient.inductionOn m fun _l _h => rfl

@[simp]
/--
theorem `attach_zero` / 定理 `attach_zero`

English:
theorem attach_zero
  statement: (0 : Multiset α).attach = 0
  proof: rfl

中文:
定理 attach_zero
  结论: (0 : Multiset α).attach = 0
  证明: rfl
-/
theorem attach_zero : (0 : Multiset α).attach = 0 :=
  rfl

/-! ### Lift a relation to `Multiset`s -/

section Rel

/-- `Rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`. -/
@[mk_iff]
/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: (r : α -> β -> Prop)
  constructors (2):
    - zero: Rel r 0 0
    - cons: {a b as bs} : r a b -> Rel r as bs -> Rel r (a ::ₘ as) (b ::ₘ bs)

中文:
归纳类型 Rel
  参数: (r : α -> β -> 命题)
  构造子 (2 个):
    - zero: Rel r 0 0
    - cons: {a b as bs} : r a b -> Rel r as bs -> Rel r (a ::ₘ as) (b ::ₘ bs)

Depends on / 依赖: Rel.cons, Rel.recOn, Rel.zero
-/
inductive Rel (r : α -> β -> Prop) : Multiset α -> Multiset β -> Prop
  | zero : Rel r 0 0
  | cons {a b as bs} : r a b -> Rel r as bs -> Rel r (a ::ₘ as) (b ::ₘ bs)

variable {δ : Type*} {r : α -> β -> Prop} {p : γ -> δ -> Prop}

/--
theorem `rel_flip_aux` / 定理 `rel_flip_aux`

English:
theorem rel_flip_aux
  given: {s t} (h : Rel r s t)
  statement: Rel (flip r) t s
  proof: Rel.recOn h Rel.zero fun h₀ _h₁ ih => Rel.cons h₀ ih

中文:
定理 rel_flip_aux
  条件: {s t} (h : Rel r s t)
  结论: Rel (flip r) t s
  证明: Rel.recOn h Rel.zero fun h₀ _h₁ ih => Rel.cons h₀ ih
-/
private theorem rel_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s :=
  Rel.recOn h Rel.zero fun h₀ _h₁ ih => Rel.cons h₀ ih

/--
theorem `rel_flip` / 定理 `rel_flip`

English:
theorem rel_flip
  given: {s t}
  statement: Rel (flip r) s t ↔ Rel r t s
  proof: ⟨rel_flip_aux, rel_flip_aux⟩

中文:
定理 rel_flip
  条件: {s t}
  结论: Rel (flip r) s t ↔ Rel r t s
  证明: ⟨rel_flip_aux, rel_flip_aux⟩

Depends on / 依赖: rel_flip_aux
-/
theorem rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s :=
  ⟨rel_flip_aux, rel_flip_aux⟩

/--
theorem `rel_refl_of_refl_on` / 定理 `rel_refl_of_refl_on`

English:
theorem rel_refl_of_refl_on
  given: {m : Multiset α} {r : α -> α -> Prop}
  statement: (forall x in m, r x x) -> Rel r m m
  proof: by
  refine m.induction_on ?_ ?_
  · intros
    apply Rel.zero
  · intro a m ih h
    exact Rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))

中文:
定理 rel_refl_of_refl_on
  条件: {m : Multiset α} {r : α -> α -> 命题}
  结论: (对任意 x in m, r x x) -> Rel r m m
  证明: by
  refine m.induction_on ?_ ?_
  · intros
    apply Rel.zero
  · intro a m ih h
    exact Rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))

Depends on / 依赖: Rel.cons, Rel.zero, induction_on, intros, m.induction_on, mem_cons_of_mem, mem_cons_self
-/
theorem rel_refl_of_refl_on {m : Multiset α} {r : α -> α -> Prop} : (forall x in m, r x x) -> Rel r m m := by
  refine m.induction_on ?_ ?_
  · intros
    apply Rel.zero
  · intro a m ih h
    exact Rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))

/--
theorem `rel_eq_refl` / 定理 `rel_eq_refl`

English:
theorem rel_eq_refl
  given: {s : Multiset α}
  statement: Rel (· = ·) s s
  proof: rel_refl_of_refl_on fun _x _hx => rfl

中文:
定理 rel_eq_refl
  条件: {s : Multiset α}
  结论: Rel (· = ·) s s
  证明: rel_refl_of_refl_on fun _x _hx => rfl

Depends on / 依赖: rel_refl_of_refl_on
-/
theorem rel_eq_refl {s : Multiset α} : Rel (· = ·) s s :=
  rel_refl_of_refl_on fun _x _hx => rfl

/--
theorem `rel_eq` / 定理 `rel_eq`

English:
theorem rel_eq
  given: {s t : Multiset α}
  statement: Rel (· = ·) s t ↔ s = t
  proof: by
  constructor
  · intro h
    induction h <;> simp [*]
  · rintro rfl
    exact rel_eq_refl

中文:
定理 rel_eq
  条件: {s t : Multiset α}
  结论: Rel (· = ·) s t ↔ s = t
  证明: by
  constructor
  · intro h
    induction h <;> simp [*]
  · rintro rfl
    exact rel_eq_refl

Depends on / 依赖: rel_eq_refl
-/
theorem rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t := by
  constructor
  · intro h
    induction h <;> simp [*]
  · rintro rfl
    exact rel_eq_refl

/--
theorem `Rel.mono` / 定理 `Rel.mono`

English:
theorem Rel.mono
  statement: {r p : α -> β -> Prop} {s t} (hst : Rel r s t)
  proof: by
  induction hst with
  | zero => exact Rel.zero
  | @cons a b s t hab _hst ih =>
    apply Rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'

中文:
定理 Rel.mono
  结论: {r p : α -> β -> 命题} {s t} (hst : Rel r s t)
  证明: by
  induction hst with
  | zero => exact Rel.zero
  | @cons a b s t hab _hst ih =>
    apply Rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'

Depends on / 依赖: Rel.cons, Rel.zero, _hst, mem_cons_of_mem, mem_cons_self
-/
theorem Rel.mono {r p : α -> β -> Prop} {s t} (hst : Rel r s t)
    (h : forall a in s, forall b in t, r a b -> p a b) : Rel p s t := by
  induction hst with
  | zero => exact Rel.zero
  | @cons a b s t hab _hst ih =>
    apply Rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'

/--
theorem `rel_flip_eq` / 定理 `rel_flip_eq`

English:
theorem rel_flip_eq
  given: {s t : Multiset α}
  statement: Rel (fun a b => b = a) s t ↔ s = t
  proof: show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]

@[simp]

中文:
定理 rel_flip_eq
  条件: {s t : Multiset α}
  结论: Rel (fun a b => b = a) s t ↔ s = t
  证明: show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]

@[simp]

Depends on / 依赖: eq_comm, rel_eq, rel_flip
-/
theorem rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t :=
  show Rel (flip (· = ·)) s t ↔ s = t by rw [rel_flip, rel_eq, eq_comm]

@[simp]
/--
theorem `rel_zero_left` / 定理 `rel_zero_left`

English:
theorem rel_zero_left
  given: {b : Multiset β}
  statement: Rel r 0 b ↔ b = 0
  proof: by rw [rel_iff]; simp

@[simp]

中文:
定理 rel_zero_left
  条件: {b : Multiset β}
  结论: Rel r 0 b ↔ b = 0
  证明: by rw [rel_iff]; simp

@[simp]

Depends on / 依赖: rel_iff
-/
theorem rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0 := by rw [rel_iff]; simp

@[simp]
/--
theorem `rel_zero_right` / 定理 `rel_zero_right`

English:
theorem rel_zero_right
  given: {a : Multiset α}
  statement: Rel r a 0 ↔ a = 0
  proof: by rw [rel_iff]; simp

中文:
定理 rel_zero_right
  条件: {a : Multiset α}
  结论: Rel r a 0 ↔ a = 0
  证明: by rw [rel_iff]; simp

Depends on / 依赖: rel_iff
-/
theorem rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0 := by rw [rel_iff]; simp

/--
theorem `rel_cons_left` / 定理 `rel_cons_left`

English:
theorem rel_cons_left
  given: {a as bs}
  proof: by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as with
    | zero => simp at hm
    | @cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨rfl, rfl⟩ | ⟨_h, cs, eq₁, eq₂⟩)
      · exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨

中文:
定理 rel_cons_left
  条件: {a as bs}
  证明: by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as with
    | zero => simp at hm
    | @cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨rfl, rfl⟩ | ⟨_h, cs, eq₁, eq₂⟩)
      · exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨

Depends on / 依赖: Eq.symm, Rel.cons, cons_eq_cons, cons_swap, eq.symm, generalize, generalizing
-/
theorem rel_cons_left {a as bs} :
    Rel r (a ::ₘ as) bs ↔ exists b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs' := by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as with
    | zero => simp at hm
    | @cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨rfl, rfl⟩ | ⟨_h, cs, eq₁, eq₂⟩)
      · exact ⟨b, bs, ha'b, h, rfl⟩
      · rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ Rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩
  · exact fun ⟨b, bs', hab, h, Eq⟩ => Eq.symm ▸ Rel.cons hab h

/--
theorem `rel_cons_right` / 定理 `rel_cons_right`

English:
theorem rel_cons_right
  given: {as b bs}
  proof: by
  rw [← rel_flip]; rw [rel_cons_left]
  refine exists₂_congr fun a as' => ?_
  rw [rel_flip]; rw [flip]

中文:
定理 rel_cons_right
  条件: {as b bs}
  证明: by
  rw [← rel_flip]; rw [rel_cons_left]
  refine exists₂_congr fun a as' => ?_
  rw [rel_flip]; rw [flip]

Depends on / 依赖: rel_cons_left, rel_flip
-/
theorem rel_cons_right {as b bs} :
    Rel r as (b ::ₘ bs) ↔ exists a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as' := by
  rw [← rel_flip]; rw [rel_cons_left]
  refine exists₂_congr fun a as' => ?_
  rw [rel_flip]; rw [flip]

/--
theorem `card_eq_card_of_rel` / 定理 `card_eq_card_of_rel`

English:
theorem card_eq_card_of_rel
  given: {r : α -> β -> Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t)
  proof: by induction h <;> simp [*]

中文:
定理 card_eq_card_of_rel
  条件: {r : α -> β -> 命题} {s : Multiset α} {t : Multiset β} (h : Rel r s t)
  证明: by induction h <;> simp [*]
-/
theorem card_eq_card_of_rel {r : α -> β -> Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) :
    card s = card t := by induction h <;> simp [*]

/--
theorem `exists_mem_of_rel_of_mem` / 定理 `exists_mem_of_rel_of_mem`

English:
theorem exists_mem_of_rel_of_mem
  statement: {r : α -> β -> Prop} {s : Multiset α} {t : Multiset β}
  proof: by
  induction h with
  | zero => simp
  | @cons x y s t hxy _ ih =>
    intro a ha
    rcases mem_cons.1 ha with ha | ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩

中文:
定理 exists_mem_of_rel_of_mem
  结论: {r : α -> β -> 命题} {s : Multiset α} {t : Multiset β}
  证明: by
  induction h with
  | zero => simp
  | @cons x y s t hxy _ ih =>
    intro a ha
    rcases mem_cons.1 ha with ha | ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩

Depends on / 依赖: Or.inr, ha.symm, mem_cons, mem_cons_self
-/
theorem exists_mem_of_rel_of_mem {r : α -> β -> Prop} {s : Multiset α} {t : Multiset β}
    (h : Rel r s t) : forall {a : α}, a in s -> exists b in t, r a b := by
  induction h with
  | zero => simp
  | @cons x y s t hxy _ ih =>
    intro a ha
    rcases mem_cons.1 ha with ha | ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩

/--
theorem `rel_of_forall` / 定理 `rel_of_forall`

English:
theorem rel_of_forall
  statement: {m1 m2 : Multiset α} {r : α -> α -> Prop} (h : forall a b, a in m1 -> b in m2 -> r a b)
  proof: by
  revert m1
  refine @(m2.induction_on ?_ ?_)
  · intro m _h hc
    rw [rel_zero_right]; rw [← card_eq_zero]; rw [hc]; rw [card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rf

中文:
定理 rel_of_forall
  结论: {m1 m2 : Multiset α} {r : α -> α -> 命题} (h : 对任意 a b, a in m1 -> b in m2 -> r a b)
  证明: by
  revert m1
  refine @(m2.induction_on ?_ ?_)
  · intro m _h hc
    rw [rel_zero_right]; rw [← card_eq_zero]; rw [hc]; rw [card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rf

Depends on / 依赖: Nat.succ_pos, card_cons, card_eq_zero, card_pos_iff_exists_mem, card_zero, exists_cons_of_mem, hc.symm, induction_on, m2.induction_on, mem_cons_of_mem, mem_cons_self, rel_cons_right, rel_cons_right.mpr, rel_zero_right, revert, succ_pos
-/
theorem rel_of_forall {m1 m2 : Multiset α} {r : α -> α -> Prop} (h : forall a b, a in m1 -> b in m2 -> r a b)
    (hc : card m1 = card m2) : m1.Rel r m2 := by
  revert m1
  refine @(m2.induction_on ?_ ?_)
  · intro m _h hc
    rw [rel_zero_right]; rw [← card_eq_zero]; rw [hc]; rw [card_zero]
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_pos _)
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb
    refine rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih ?_ ?_, rfl⟩
    · exact fun _ _ ha hb => h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb)
    · simpa using hc

protected nonrec
/--
theorem `Rel.trans` / 定理 `Rel.trans`

English:
theorem Rel.trans
  statement: (r : α -> α -> Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
  proof: by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  | cons x t ih =>
    obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.c

中文:
定理 Rel.trans
  结论: (r : α -> α -> 命题) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
  证明: by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  | cons x t ih =>
    obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.c

Depends on / 依赖: Multiset, Multiset.Rel.cons, Multiset.induction_on, _root_, _root_.trans, generalizing, induction_on, rel_cons_left, rel_cons_left.mp, rel_cons_right, rel_cons_right.mp, rel_zero_left, rel_zero_left.mp, rel_zero_right, rel_zero_right.mp
-/
theorem Rel.trans (r : α -> α -> Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t)
    (r2 : Rel r t u) : Rel r s u := by
  induction t using Multiset.induction_on generalizing s u with
  | empty => rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
  | cons x t ih =>
    obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.cons (_root_.trans ha1 hb1) (ih ha2 hb2)

end Rel

@[simp]
/--
theorem `pairwise_zero` / 定理 `pairwise_zero`

English:
theorem pairwise_zero
  given: (r : α -> α -> Prop)
  statement: Multiset.Pairwise r 0
  proof: ⟨[], rfl, List.Pairwise.nil⟩

中文:
定理 pairwise_zero
  条件: (r : α -> α -> 命题)
  结论: Multiset.Pairwise r 0
  证明: ⟨[], rfl, List.Pairwise.nil⟩

Depends on / 依赖: List.Pairwise.nil, Pairwise
-/
theorem pairwise_zero (r : α -> α -> Prop) : Multiset.Pairwise r 0 :=
  ⟨[], rfl, List.Pairwise.nil⟩

section Nodup

variable {s : Multiset α} {a : α}

@[simp]
/--
theorem `nodup_zero` / 定理 `nodup_zero`

English:
theorem nodup_zero
  statement: @Nodup α 0
  proof: Pairwise.nil

@[simp]

中文:
定理 nodup_zero
  结论: @Nodup α 0
  证明: Pairwise.nil

@[simp]

Depends on / 依赖: Pairwise, Pairwise.nil
-/
theorem nodup_zero : @Nodup α 0 :=
  Pairwise.nil

@[simp]
/--
theorem `nodup_cons` / 定理 `nodup_cons`

English:
theorem nodup_cons
  given: {a : α} {s : Multiset α}
  statement: Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s
  proof: Quot.induction_on s fun _ => List.nodup_cons

中文:
定理 nodup_cons
  条件: {a : α} {s : Multiset α}
  结论: Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s
  证明: Quot.induction_on s fun _ => List.nodup_cons

Depends on / 依赖: List.nodup_cons, Quot.induction_on, induction_on, nodup_cons
-/
theorem nodup_cons {a : α} {s : Multiset α} : Nodup (a ::ₘ s) ↔ a ∉ s ∧ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_cons

/--
theorem `Nodup.cons` / 定理 `Nodup.cons`

English:
theorem Nodup.cons
  given: (m : a ∉ s) (n : Nodup s)
  statement: Nodup (a ::ₘ s)
  proof: nodup_cons.2 ⟨m, n⟩

中文:
定理 Nodup.cons
  条件: (m : a ∉ s) (n : Nodup s)
  结论: Nodup (a ::ₘ s)
  证明: nodup_cons.2 ⟨m, n⟩

Depends on / 依赖: nodup_cons
-/
theorem Nodup.cons (m : a ∉ s) (n : Nodup s) : Nodup (a ::ₘ s) :=
  nodup_cons.2 ⟨m, n⟩

/--
theorem `Nodup.of_cons` / 定理 `Nodup.of_cons`

English:
theorem Nodup.of_cons
  given: (h : Nodup (a ::ₘ s))
  statement: Nodup s
  proof: (nodup_cons.1 h).2

中文:
定理 Nodup.of_cons
  条件: (h : Nodup (a ::ₘ s))
  结论: Nodup s
  证明: (nodup_cons.1 h).2
-/
theorem Nodup.of_cons (h : Nodup (a ::ₘ s)) : Nodup s :=
  (nodup_cons.1 h).2

/--
theorem `Nodup.notMem` / 定理 `Nodup.notMem`

English:
theorem Nodup.notMem
  given: (h : Nodup (a ::ₘ s))
  statement: a ∉ s
  proof: (nodup_cons.1 h).1

中文:
定理 Nodup.notMem
  条件: (h : Nodup (a ::ₘ s))
  结论: a ∉ s
  证明: (nodup_cons.1 h).1
-/
theorem Nodup.notMem (h : Nodup (a ::ₘ s)) : a ∉ s :=
  (nodup_cons.1 h).1

end Nodup

end Multiset
