/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Disjointness and complements

This file defines `Disjoint`, `Codisjoint`, and the `IsCompl` predicate.

## Main declarations

* `Disjoint x y`: two elements of a lattice are disjoint if their `inf` is the bottom element.
* `Codisjoint x y`: two elements of a lattice are codisjoint if their `join` is the top element.
* `IsCompl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non-distributive lattice, an element can have several complements.
* `ComplementedLattice α`: Typeclass stating that any element of a lattice has a complement.

-/

@[expose] public section

open Function

variable {α : Type*}

section Disjoint

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `Inf` would require additional `Decidable`
arguments. -/
@[to_dual /-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implementing `Sup` would require additional `Decidable`
arguments. -/]
/--
Definition of `Disjoint` / `Disjoint` 的定义

English:
definition Disjoint
  signature: (a b : α)
  body: forall ⦃x⦄, x <= a -> x <= b -> x <= ⊥

@[to_dual (attr := simp)]

中文:
定义 Disjoint
  签名: (a b : α)
  定义体: forall ⦃x⦄, x <= a -> x <= b -> x <= ⊥

@[to_dual (attr := simp)]
-/
def Disjoint (a b : α) : Prop :=
  forall ⦃x⦄, x <= a -> x <= b -> x <= ⊥

@[to_dual (attr := simp)]
/--
theorem `disjoint_of_subsingleton` / 定理 `disjoint_of_subsingleton`

English:
theorem disjoint_of_subsingleton
  given: [Subsingleton α]
  statement: Disjoint a b
  proof: fun x _ _ => le_of_eq (Subsingleton.elim x ⊥)

@[to_dual (attr := grind =)]

中文:
定理 disjoint_of_subsingleton
  条件: [Subsingleton α]
  结论: Disjoint a b
  证明: fun x _ _ => le_of_eq (Subsingleton.elim x ⊥)

@[to_dual (attr := grind =)]

Depends on / 依赖: Subsingleton, Subsingleton.elim, le_of_eq
-/
theorem disjoint_of_subsingleton [Subsingleton α] : Disjoint a b :=
  fun x _ _ => le_of_eq (Subsingleton.elim x ⊥)

@[to_dual (attr := grind =)]
/--
theorem `disjoint_comm` / 定理 `disjoint_comm`

English:
theorem disjoint_comm
  statement: Disjoint a b ↔ Disjoint b a
  proof: forall_congr' fun _ => forall_comm

@[to_dual (attr := symm)]

中文:
定理 disjoint_comm
  结论: Disjoint a b ↔ Disjoint b a
  证明: forall_congr' fun _ => forall_comm

@[to_dual (attr := symm)]

Depends on / 依赖: forall_comm, forall_congr
-/
theorem disjoint_comm : Disjoint a b ↔ Disjoint b a :=
  forall_congr' fun _ => forall_comm

@[to_dual (attr := symm)]
/--
theorem `Disjoint.symm` / 定理 `Disjoint.symm`

English:
theorem Disjoint.symm
  given: ⦃a b
  statement: α⦄ : Disjoint a b -> Disjoint b a
  proof: disjoint_comm.1

@[to_dual]

中文:
定理 Disjoint.symm
  条件: ⦃a b
  结论: α⦄ : Disjoint a b -> Disjoint b a
  证明: disjoint_comm.1

@[to_dual]
-/
theorem Disjoint.symm ⦃a b : α⦄ : Disjoint a b -> Disjoint b a :=
  disjoint_comm.1

@[to_dual]
/--
Instance `symm_disjoint` / 实例 `symm_disjoint`

English:
instance symm_disjoint
  signature: : Std.Symm (Disjoint : α -> α -> Prop) where
  body: Disjoint.symm

@[to_dual (attr := deprecated (since := "2026-06-10"))] alias symmetric_disjoint := symm_disjoint

@[to_dual (attr := simp, grind ←)]

中文:
实例 symm_disjoint
  签名: : Std.Symm (Disjoint : α -> α -> 命题) where
  定义体: Disjoint.symm

@[to_dual (attr := deprecated (since := "2026-06-10"))] alias symmetric_disjoint := symm_disjoint

@[to_dual (attr := simp, grind ←)]

Depends on / 依赖: Disjoint, Disjoint.symm
-/
instance symm_disjoint : Std.Symm (Disjoint : α -> α -> Prop) where
  symm := Disjoint.symm

@[to_dual (attr := deprecated (since := "2026-06-10"))] alias symmetric_disjoint := symm_disjoint

@[to_dual (attr := simp, grind ←)]
/--
theorem `disjoint_bot_left` / 定理 `disjoint_bot_left`

English:
theorem disjoint_bot_left
  statement: Disjoint ⊥ a
  proof: fun _ hbot _ => hbot

@[to_dual (attr := simp)]

中文:
定理 disjoint_bot_left
  结论: Disjoint ⊥ a
  证明: fun _ hbot _ => hbot

@[to_dual (attr := simp)]
-/
theorem disjoint_bot_left : Disjoint ⊥ a := fun _ hbot _ => hbot

@[to_dual (attr := simp)]
/--
theorem `disjoint_bot_right` / 定理 `disjoint_bot_right`

English:
theorem disjoint_bot_right
  statement: Disjoint a ⊥
  proof: fun _ _ hbot => hbot

@[to_dual (attr := gcongr)]

中文:
定理 disjoint_bot_right
  结论: Disjoint a ⊥
  证明: fun _ _ hbot => hbot

@[to_dual (attr := gcongr)]
-/
theorem disjoint_bot_right : Disjoint a ⊥ := fun _ _ hbot => hbot

@[to_dual (attr := gcongr)]
/--
theorem `Disjoint.mono` / 定理 `Disjoint.mono`

English:
theorem Disjoint.mono
  given: (h₁ : a <= b) (h₂ : c <= d)
  statement: Disjoint b d -> Disjoint a c
  proof: fun h _ ha hc => h (ha.trans h₁) (hc.trans h₂)

@[to_dual]

中文:
定理 Disjoint.mono
  条件: (h₁ : a <= b) (h₂ : c <= d)
  结论: Disjoint b d -> Disjoint a c
  证明: fun h _ ha hc => h (ha.trans h₁) (hc.trans h₂)

@[to_dual]
-/
theorem Disjoint.mono (h₁ : a <= b) (h₂ : c <= d) : Disjoint b d -> Disjoint a c :=
  fun h _ ha hc => h (ha.trans h₁) (hc.trans h₂)

@[to_dual]
/--
theorem `Disjoint.mono_left` / 定理 `Disjoint.mono_left`

English:
theorem Disjoint.mono_left
  given: (h : a <= b)
  statement: Disjoint b c -> Disjoint a c
  proof: Disjoint.mono h le_rfl

grind_pattern Disjoint.mono_left => a <= b, Disjoint b c
grind_pattern Disjoint.mono_left => a <= b, Disjoint a c
grind_pattern Codisjoint.mono_left => a <= b, Codisjoint a c
grind_pattern Codisjoint.mono_left => a <= b, Codisjoint b c

@[to_dual]

中文:
定理 Disjoint.mono_left
  条件: (h : a <= b)
  结论: Disjoint b c -> Disjoint a c
  证明: Disjoint.mono h le_rfl

grind_pattern Disjoint.mono_left => a <= b, Disjoint b c
grind_pattern Disjoint.mono_left => a <= b, Disjoint a c
grind_pattern Codisjoint.mono_left => a <= b, Codisjoint a c
grind_pattern Codisjoint.mono_left => a <= b, Codisjoint b c

@[to_dual]

Depends on / 依赖: Disjoint, Disjoint.mono, le_rfl
-/
theorem Disjoint.mono_left (h : a <= b) : Disjoint b c -> Disjoint a c :=
  Disjoint.mono h le_rfl

grind_pattern Disjoint.mono_left => a <= b, Disjoint b c
grind_pattern Disjoint.mono_left => a <= b, Disjoint a c
grind_pattern Codisjoint.mono_left => a <= b, Codisjoint a c
grind_pattern Codisjoint.mono_left => a <= b, Codisjoint b c

@[to_dual]
/--
theorem `Disjoint.mono_right` / 定理 `Disjoint.mono_right`

English:
theorem Disjoint.mono_right
  given: (h : b <= c)
  statement: Disjoint a c -> Disjoint a b
  proof: Disjoint.mono le_rfl h

中文:
定理 Disjoint.mono_right
  条件: (h : b <= c)
  结论: Disjoint a c -> Disjoint a b
  证明: Disjoint.mono le_rfl h

Depends on / 依赖: Disjoint, Disjoint.mono, le_rfl
-/
theorem Disjoint.mono_right (h : b <= c) : Disjoint a c -> Disjoint a b :=
  Disjoint.mono le_rfl h

-- Note: we don't need separate `grind` patterns for `Disjoint.mono_right` because `grind`
-- will use `disjoint_comm`.

@[to_dual]
/--
theorem `Disjoint.out` / 定理 `Disjoint.out`

English:
theorem Disjoint.out
  given: (h : Disjoint a b) (x : α)
  statement: x <= a -> x <= b -> x = ⊥
  proof: fun h₁ h₂ => by simpa using h h₁ h₂

@[to_dual (attr := simp, grind =)]

中文:
定理 Disjoint.out
  条件: (h : Disjoint a b) (x : α)
  结论: x <= a -> x <= b -> x = ⊥
  证明: fun h₁ h₂ => by simpa using h h₁ h₂

@[to_dual (attr := simp, grind =)]
-/
theorem Disjoint.out (h : Disjoint a b) (x : α) : x <= a -> x <= b -> x = ⊥ :=
  fun h₁ h₂ => by simpa using h h₁ h₂

@[to_dual (attr := simp, grind =)]
/--
theorem `disjoint_self` / 定理 `disjoint_self`

English:
theorem disjoint_self
  statement: Disjoint a a ↔ a = ⊥
  proof: ⟨fun hd => bot_unique hd le_rfl le_rfl, fun h _ ha _ => ha.trans_eq h⟩

中文:
定理 disjoint_self
  结论: Disjoint a a ↔ a = ⊥
  证明: ⟨fun hd => bot_unique hd le_rfl le_rfl, fun h _ ha _ => ha.trans_eq h⟩

Depends on / 依赖: bot_unique, ha.trans_eq, le_rfl, trans_eq
-/
theorem disjoint_self : Disjoint a a ↔ a = ⊥ :=
⟨fun hd => bot_unique hd le_rfl le_rfl, fun h _ ha _ => ha.trans_eq h⟩

/- TODO: Rename `Disjoint.eq_bot` to `Disjoint.inf_eq` and `Disjoint.eq_bot_of_self` to
`Disjoint.eq_bot` -/
@[to_dual]
alias ⟨Disjoint.eq_bot_of_self, _⟩ := disjoint_self

@[to_dual]
/--
theorem `Disjoint.ne` / 定理 `Disjoint.ne`

English:
theorem Disjoint.ne
  given: (ha : a != ⊥) (hab : Disjoint a b)
  statement: a != b
  proof: fun h => ha disjoint_self.1 by rwa [← h] at hab

@[to_dual]

中文:
定理 Disjoint.ne
  条件: (ha : a != ⊥) (hab : Disjoint a b)
  结论: a != b
  证明: fun h => ha disjoint_self.1 by rwa [← h] at hab

@[to_dual]

Depends on / 依赖: disjoint_self
-/
theorem Disjoint.ne (ha : a != ⊥) (hab : Disjoint a b) : a != b :=
fun h => ha disjoint_self.1 by rwa [← h] at hab

@[to_dual]
/--
theorem `Disjoint.eq_bot_of_le` / 定理 `Disjoint.eq_bot_of_le`

English:
theorem Disjoint.eq_bot_of_le
  given: (hab : Disjoint a b) (h : a <= b)
  statement: a = ⊥
  proof: eq_bot_iff.2 hab le_rfl h

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, a <= b
grind_pattern Codisjoint.eq_top_of_le => Codisjoint a b, b <= a

@[to_dual]

中文:
定理 Disjoint.eq_bot_of_le
  条件: (hab : Disjoint a b) (h : a <= b)
  结论: a = ⊥
  证明: eq_bot_iff.2 hab le_rfl h

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, a <= b
grind_pattern Codisjoint.eq_top_of_le => Codisjoint a b, b <= a

@[to_dual]

Depends on / 依赖: eq_bot_iff, le_rfl
-/
theorem Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a <= b) : a = ⊥ :=
eq_bot_iff.2 hab le_rfl h

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, a <= b
grind_pattern Codisjoint.eq_top_of_le => Codisjoint a b, b <= a

@[to_dual]
/--
theorem `Disjoint.eq_bot_of_ge` / 定理 `Disjoint.eq_bot_of_ge`

English:
theorem Disjoint.eq_bot_of_ge
  given: (hab : Disjoint a b)
  statement: b <= a -> b = ⊥
  proof: hab.symm.eq_bot_of_le

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, b <= a
grind_pattern Codisjoint.eq_top_of_ge => Codisjoint a b, a <= b

中文:
定理 Disjoint.eq_bot_of_ge
  条件: (hab : Disjoint a b)
  结论: b <= a -> b = ⊥
  证明: hab.symm.eq_bot_of_le

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, b <= a
grind_pattern Codisjoint.eq_top_of_ge => Codisjoint a b, a <= b

Depends on / 依赖: eq_bot_of_le, hab.symm.eq_bot_of_le
-/
theorem Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b <= a -> b = ⊥ :=
  hab.symm.eq_bot_of_le

grind_pattern Disjoint.eq_bot_of_le => Disjoint a b, b <= a
grind_pattern Codisjoint.eq_top_of_ge => Codisjoint a b, a <= b

/--
lemma `Disjoint.eq_iff` / 引理 `Disjoint.eq_iff`

English:
lemma Disjoint.eq_iff
  given: (hab : Disjoint a b)
  statement: a = b ↔ a = ⊥ ∧ b = ⊥
  proof: by grind

中文:
引理 Disjoint.eq_iff
  条件: (hab : Disjoint a b)
  结论: a = b ↔ a = ⊥ ∧ b = ⊥
  证明: by grind
-/
@[to_dual] lemma Disjoint.eq_iff (hab : Disjoint a b) : a = b ↔ a = ⊥ ∧ b = ⊥ := by grind
/--
lemma `Disjoint.ne_iff` / 引理 `Disjoint.ne_iff`

English:
lemma Disjoint.ne_iff
  given: (hab : Disjoint a b)
  statement: a != b ↔ a != ⊥ ∨ b != ⊥
  proof: by grind

中文:
引理 Disjoint.ne_iff
  条件: (hab : Disjoint a b)
  结论: a != b ↔ a != ⊥ ∨ b != ⊥
  证明: by grind
-/
@[to_dual] lemma Disjoint.ne_iff (hab : Disjoint a b) : a != b ↔ a != ⊥ ∨ b != ⊥ := by grind

/--
theorem `disjoint_of_le_iff_left_eq_bot` / 定理 `disjoint_of_le_iff_left_eq_bot`

English:
theorem disjoint_of_le_iff_left_eq_bot
  given: (h : a <= b)
  proof: by grind

中文:
定理 disjoint_of_le_iff_left_eq_bot
  条件: (h : a <= b)
  证明: by grind
-/
theorem disjoint_of_le_iff_left_eq_bot (h : a <= b) :
    Disjoint a b ↔ a = ⊥ := by grind

end PartialOrderBot

section PartialBoundedOrder

variable [PartialOrder α] [BoundedOrder α] {a b : α}

@[to_dual (attr := simp, grind =)]
/--
theorem `disjoint_top` / 定理 `disjoint_top`

English:
theorem disjoint_top
  statement: Disjoint a ⊤ ↔ a = ⊥
  proof: ⟨fun h => bot_unique h le_rfl le_top, fun h _ ha _ => ha.trans_eq h⟩

@[to_dual (attr := simp, grind =)]

中文:
定理 disjoint_top
  结论: Disjoint a ⊤ ↔ a = ⊥
  证明: ⟨fun h => bot_unique h le_rfl le_top, fun h _ ha _ => ha.trans_eq h⟩

@[to_dual (attr := simp, grind =)]

Depends on / 依赖: bot_unique, ha.trans_eq, le_rfl, le_top, trans_eq
-/
theorem disjoint_top : Disjoint a ⊤ ↔ a = ⊥ :=
⟨fun h => bot_unique h le_rfl le_top, fun h _ ha _ => ha.trans_eq h⟩

@[to_dual (attr := simp, grind =)]
/--
theorem `top_disjoint` / 定理 `top_disjoint`

English:
theorem top_disjoint
  statement: Disjoint ⊤ a ↔ a = ⊥
  proof: ⟨fun h => bot_unique h le_top le_rfl, fun h _ _ ha => ha.trans_eq h⟩

@[to_dual]

中文:
定理 top_disjoint
  结论: Disjoint ⊤ a ↔ a = ⊥
  证明: ⟨fun h => bot_unique h le_top le_rfl, fun h _ _ ha => ha.trans_eq h⟩

@[to_dual]

Depends on / 依赖: bot_unique, ha.trans_eq, le_rfl, le_top, trans_eq
-/
theorem top_disjoint : Disjoint ⊤ a ↔ a = ⊥ :=
⟨fun h => bot_unique h le_top le_rfl, fun h _ _ ha => ha.trans_eq h⟩

@[to_dual]
/--
theorem `Disjoint.ne_top_of_ne_bot` / 定理 `Disjoint.ne_top_of_ne_bot`

English:
theorem Disjoint.ne_top_of_ne_bot
  given: (h : Disjoint a b) (ha : a != ⊥)
  statement: b != ⊤
  proof: by
  grind

中文:
定理 Disjoint.ne_top_of_ne_bot
  条件: (h : Disjoint a b) (ha : a != ⊥)
  结论: b != ⊤
  证明: by
  grind
-/
theorem Disjoint.ne_top_of_ne_bot (h : Disjoint a b) (ha : a != ⊥) : b != ⊤ := by
  grind

end PartialBoundedOrder

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a b c : α}

-- I would like to mark this as `@[grind =]`, but it results in excessive case splitting.
@[to_dual codisjoint_iff_le_sup]
/--
theorem `disjoint_iff_inf_le` / 定理 `disjoint_iff_inf_le`

English:
theorem disjoint_iff_inf_le
  statement: Disjoint a b ↔ a ⊓ b <= ⊥
  proof: ⟨fun hd => hd inf_le_left inf_le_right, fun h _ ha hb => (le_inf ha hb).trans h⟩

@[to_dual]

中文:
定理 disjoint_iff_inf_le
  结论: Disjoint a b ↔ a ⊓ b <= ⊥
  证明: ⟨fun hd => hd inf_le_left inf_le_right, fun h _ ha hb => (le_inf ha hb).trans h⟩

@[to_dual]

Depends on / 依赖: inf_le_left, inf_le_right, le_inf
-/
theorem disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥ :=
  ⟨fun hd => hd inf_le_left inf_le_right, fun h _ ha hb => (le_inf ha hb).trans h⟩

@[to_dual]
/--
theorem `disjoint_iff` / 定理 `disjoint_iff`

English:
theorem disjoint_iff
  statement: Disjoint a b ↔ a ⊓ b = ⊥
  proof: disjoint_iff_inf_le.trans le_bot_iff

@[to_dual (attr := simp)]

中文:
定理 disjoint_iff
  结论: Disjoint a b ↔ a ⊓ b = ⊥
  证明: disjoint_iff_inf_le.trans le_bot_iff

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.trans, le_bot_iff
-/
theorem disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥ :=
  disjoint_iff_inf_le.trans le_bot_iff

@[to_dual (attr := simp)]
/--
lemma `disjoint_subtype_iff` / 引理 `disjoint_subtype_iff`

English:
lemma disjoint_subtype_iff
  statement: {pr : α -> Prop} (Pinf : forall ⦃s t : α⦄, pr s -> pr t -> pr (s ⊓ t))
  proof: Subtype.semilatticeInf Pinf
    letI : OrderBot (Subtype pr) := Subtype.orderBot hbot
    Disjoint a b ↔ Disjoint a.val b.val := by
  let : SemilatticeInf (Subtype pr) := Subtype.semilatticeInf Pinf
  let : OrderBot (Subtype pr) := Subtype.orderBot hbot
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← 

中文:
引理 disjoint_subtype_iff
  结论: {pr : α -> 命题} (Pinf : 对任意 ⦃s t : α⦄, pr s -> pr t -> pr (s ⊓ t))
  证明: Subtype.semilatticeInf Pinf
    letI : OrderBot (Subtype pr) := Subtype.orderBot hbot
    Disjoint a b ↔ Disjoint a.val b.val := by
  let : SemilatticeInf (Subtype pr) := Subtype.semilatticeInf Pinf
  let : OrderBot (Subtype pr) := Subtype.orderBot hbot
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← 

Depends on / 依赖: Subtype, Subtype.semilatticeInf, semilatticeInf
-/
lemma disjoint_subtype_iff {pr : α -> Prop} (Pinf : forall ⦃s t : α⦄, pr s -> pr t -> pr (s ⊓ t))
    (hbot : pr (⊥ : α)) {a b : Subtype pr} :
    letI : SemilatticeInf (Subtype pr) := Subtype.semilatticeInf Pinf
    letI : OrderBot (Subtype pr) := Subtype.orderBot hbot
    Disjoint a b ↔ Disjoint a.val b.val := by
  let : SemilatticeInf (Subtype pr) := Subtype.semilatticeInf Pinf
  let : OrderBot (Subtype pr) := Subtype.orderBot hbot
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← Subtype.coe_inf Pinf]; rw [← Subtype.coe_bot hbot]
  exact Subtype.coe_inj.symm

@[to_dual top_le]
/--
theorem `Disjoint.le_bot` / 定理 `Disjoint.le_bot`

English:
theorem Disjoint.le_bot
  statement: Disjoint a b -> a ⊓ b <= ⊥
  proof: disjoint_iff_inf_le.mp

@[to_dual]

中文:
定理 Disjoint.le_bot
  结论: Disjoint a b -> a ⊓ b <= ⊥
  证明: disjoint_iff_inf_le.mp

@[to_dual]

Depends on / 依赖: disjoint_iff_inf_le, disjoint_iff_inf_le.mp
-/
theorem Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥ :=
  disjoint_iff_inf_le.mp

@[to_dual]
/--
theorem `Disjoint.eq_bot` / 定理 `Disjoint.eq_bot`

English:
theorem Disjoint.eq_bot
  statement: Disjoint a b -> a ⊓ b = ⊥
  proof: bot_unique ∘ Disjoint.le_bot

@[to_dual]

中文:
定理 Disjoint.eq_bot
  结论: Disjoint a b -> a ⊓ b = ⊥
  证明: bot_unique ∘ Disjoint.le_bot

@[to_dual]

Depends on / 依赖: Disjoint, Disjoint.le_bot, bot_unique, le_bot
-/
theorem Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥ :=
  bot_unique ∘ Disjoint.le_bot

@[to_dual]
/--
theorem `disjoint_assoc` / 定理 `disjoint_assoc`

English:
theorem disjoint_assoc
  statement: Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c)
  proof: by
  grind [disjoint_iff_inf_le]

@[to_dual]

中文:
定理 disjoint_assoc
  结论: Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c)
  证明: by
  grind [disjoint_iff_inf_le]

@[to_dual]

Depends on / 依赖: disjoint_iff_inf_le
-/
theorem disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c) := by
  grind [disjoint_iff_inf_le]

@[to_dual]
/--
theorem `disjoint_left_comm` / 定理 `disjoint_left_comm`

English:
theorem disjoint_left_comm
  statement: Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c)
  proof: by
  grind [disjoint_iff_inf_le]

@[to_dual]

中文:
定理 disjoint_left_comm
  结论: Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c)
  证明: by
  grind [disjoint_iff_inf_le]

@[to_dual]

Depends on / 依赖: disjoint_iff_inf_le
-/
theorem disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c) := by
  grind [disjoint_iff_inf_le]

@[to_dual]
/--
theorem `disjoint_right_comm` / 定理 `disjoint_right_comm`

English:
theorem disjoint_right_comm
  statement: Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b
  proof: by
  grind [disjoint_iff_inf_le]

中文:
定理 disjoint_right_comm
  结论: Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b
  证明: by
  grind [disjoint_iff_inf_le]

Depends on / 依赖: disjoint_iff_inf_le
-/
theorem disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b := by
  grind [disjoint_iff_inf_le]

variable (c)

@[to_dual]
/--
theorem `Disjoint.inf_left` / 定理 `Disjoint.inf_left`

English:
theorem Disjoint.inf_left
  given: (h : Disjoint a b)
  statement: Disjoint (a ⊓ c) b
  proof: h.mono_left inf_le_left

@[to_dual]

中文:
定理 Disjoint.inf_left
  条件: (h : Disjoint a b)
  结论: Disjoint (a ⊓ c) b
  证明: h.mono_left inf_le_left

@[to_dual]

Depends on / 依赖: h.mono_left, inf_le_left, mono_left
-/
theorem Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ c) b :=
  h.mono_left inf_le_left

@[to_dual]
/--
theorem `Disjoint.inf_left'` / 定理 `Disjoint.inf_left'`

English:
theorem Disjoint.inf_left'
  given: (h : Disjoint a b)
  statement: Disjoint (c ⊓ a) b
  proof: h.mono_left inf_le_right

@[to_dual]

中文:
定理 Disjoint.inf_left'
  条件: (h : Disjoint a b)
  结论: Disjoint (c ⊓ a) b
  证明: h.mono_left inf_le_right

@[to_dual]

Depends on / 依赖: h.mono_left, inf_le_right, mono_left
-/
theorem Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c ⊓ a) b :=
  h.mono_left inf_le_right

@[to_dual]
/--
theorem `Disjoint.inf_right` / 定理 `Disjoint.inf_right`

English:
theorem Disjoint.inf_right
  given: (h : Disjoint a b)
  statement: Disjoint a (b ⊓ c)
  proof: h.mono_right inf_le_left

@[to_dual]

中文:
定理 Disjoint.inf_right
  条件: (h : Disjoint a b)
  结论: Disjoint a (b ⊓ c)
  证明: h.mono_right inf_le_left

@[to_dual]

Depends on / 依赖: h.mono_right, inf_le_left, mono_right
-/
theorem Disjoint.inf_right (h : Disjoint a b) : Disjoint a (b ⊓ c) :=
  h.mono_right inf_le_left

@[to_dual]
/--
theorem `Disjoint.inf_right'` / 定理 `Disjoint.inf_right'`

English:
theorem Disjoint.inf_right'
  given: (h : Disjoint a b)
  statement: Disjoint a (c ⊓ b)
  proof: h.mono_right inf_le_right

中文:
定理 Disjoint.inf_right'
  条件: (h : Disjoint a b)
  结论: Disjoint a (c ⊓ b)
  证明: h.mono_right inf_le_right

Depends on / 依赖: h.mono_right, inf_le_right, mono_right
-/
theorem Disjoint.inf_right' (h : Disjoint a b) : Disjoint a (c ⊓ b) :=
  h.mono_right inf_le_right

variable {c}

@[to_dual]
/--
theorem `Disjoint.of_disjoint_inf_of_le` / 定理 `Disjoint.of_disjoint_inf_of_le`

English:
theorem Disjoint.of_disjoint_inf_of_le
  given: (h : Disjoint (a ⊓ b) c) (hle : a <= c)
  statement: Disjoint a b
  proof: disjoint_iff.2 h.eq_bot_of_le inf_le_of_left_le hle

@[to_dual]

中文:
定理 Disjoint.of_disjoint_inf_of_le
  条件: (h : Disjoint (a ⊓ b) c) (hle : a <= c)
  结论: Disjoint a b
  证明: disjoint_iff.2 h.eq_bot_of_le inf_le_of_left_le hle

@[to_dual]

Depends on / 依赖: disjoint_iff, eq_bot_of_le, h.eq_bot_of_le, inf_le_of_left_le
-/
theorem Disjoint.of_disjoint_inf_of_le (h : Disjoint (a ⊓ b) c) (hle : a <= c) : Disjoint a b :=
disjoint_iff.2 h.eq_bot_of_le inf_le_of_left_le hle

@[to_dual]
/--
theorem `Disjoint.of_disjoint_inf_of_le'` / 定理 `Disjoint.of_disjoint_inf_of_le'`

English:
theorem Disjoint.of_disjoint_inf_of_le'
  given: (h : Disjoint (a ⊓ b) c) (hle : b <= c)
  statement: Disjoint a b
  proof: disjoint_iff.2 h.eq_bot_of_le inf_le_of_right_le hle

中文:
定理 Disjoint.of_disjoint_inf_of_le'
  条件: (h : Disjoint (a ⊓ b) c) (hle : b <= c)
  结论: Disjoint a b
  证明: disjoint_iff.2 h.eq_bot_of_le inf_le_of_right_le hle

Depends on / 依赖: disjoint_iff, eq_bot_of_le, h.eq_bot_of_le, inf_le_of_right_le
-/
theorem Disjoint.of_disjoint_inf_of_le' (h : Disjoint (a ⊓ b) c) (hle : b <= c) : Disjoint a b :=
disjoint_iff.2 h.eq_bot_of_le inf_le_of_right_le hle

end SemilatticeInfBot

@[to_dual sup_lt_right_of_left_ne_bot]
/--
theorem `Disjoint.right_lt_sup_of_left_ne_bot` / 定理 `Disjoint.right_lt_sup_of_left_ne_bot`

English:
theorem Disjoint.right_lt_sup_of_left_ne_bot
  statement: [SemilatticeSup α] [OrderBot α] {a b : α}
  proof: le_sup_right.lt_of_ne fun eq => ha (le_bot_iff.mp <| h le_rfl <| sup_eq_right.mp eq.symm)

中文:
定理 Disjoint.right_lt_sup_of_left_ne_bot
  结论: [SemilatticeSup α] [OrderBot α] {a b : α}
  证明: le_sup_right.lt_of_ne fun eq => ha (le_bot_iff.mp <| h le_rfl <| sup_eq_right.mp eq.symm)

Depends on / 依赖: eq.symm, le_bot_iff, le_bot_iff.mp, le_rfl, le_sup_right, le_sup_right.lt_of_ne, lt_of_ne, sup_eq_right, sup_eq_right.mp
-/
theorem Disjoint.right_lt_sup_of_left_ne_bot [SemilatticeSup α] [OrderBot α] {a b : α}
    (h : Disjoint a b) (ha : a != ⊥) : b < a ⊔ b :=
  le_sup_right.lt_of_ne fun eq => ha (le_bot_iff.mp <| h le_rfl <| sup_eq_right.mp eq.symm)

section DistribLatticeBot

variable [DistribLattice α] [OrderBot α] {a b c : α}

@[simp]
/--
theorem `disjoint_sup_left` / 定理 `disjoint_sup_left`

English:
theorem disjoint_sup_left
  statement: Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c
  proof: by
  simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]

@[simp]

中文:
定理 disjoint_sup_left
  结论: Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c
  证明: by
  simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]

@[simp]

Depends on / 依赖: disjoint_iff, inf_sup_right, sup_eq_bot_iff
-/
theorem disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c := by
  simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]

@[simp]
/--
theorem `disjoint_sup_right` / 定理 `disjoint_sup_right`

English:
theorem disjoint_sup_right
  statement: Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c
  proof: by
  simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]

中文:
定理 disjoint_sup_right
  结论: Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c
  证明: by
  simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]

Depends on / 依赖: disjoint_iff, inf_sup_left, sup_eq_bot_iff
-/
theorem disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c := by
  simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]

/--
theorem `Disjoint.sup_left` / 定理 `Disjoint.sup_left`

English:
theorem Disjoint.sup_left
  given: (ha : Disjoint a c) (hb : Disjoint b c)
  statement: Disjoint (a ⊔ b) c
  proof: disjoint_sup_left.2 ⟨ha, hb⟩

中文:
定理 Disjoint.sup_left
  条件: (ha : Disjoint a c) (hb : Disjoint b c)
  结论: Disjoint (a ⊔ b) c
  证明: disjoint_sup_left.2 ⟨ha, hb⟩

Depends on / 依赖: disjoint_sup_left
-/
theorem Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint b c) : Disjoint (a ⊔ b) c :=
  disjoint_sup_left.2 ⟨ha, hb⟩

/--
theorem `Disjoint.sup_right` / 定理 `Disjoint.sup_right`

English:
theorem Disjoint.sup_right
  given: (hb : Disjoint a b) (hc : Disjoint a c)
  statement: Disjoint a (b ⊔ c)
  proof: disjoint_sup_right.2 ⟨hb, hc⟩

中文:
定理 Disjoint.sup_right
  条件: (hb : Disjoint a b) (hc : Disjoint a c)
  结论: Disjoint a (b ⊔ c)
  证明: disjoint_sup_right.2 ⟨hb, hc⟩

Depends on / 依赖: disjoint_sup_right
-/
theorem Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoint a c) : Disjoint a (b ⊔ c) :=
  disjoint_sup_right.2 ⟨hb, hc⟩

/--
theorem `Disjoint.left_le_of_le_sup_right` / 定理 `Disjoint.left_le_of_le_sup_right`

English:
theorem Disjoint.left_le_of_le_sup_right
  given: (h : a <= b ⊔ c) (hd : Disjoint a c)
  statement: a <= b
  proof: le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) sup_le h le_sup_right

中文:
定理 Disjoint.left_le_of_le_sup_right
  条件: (h : a <= b ⊔ c) (hd : Disjoint a c)
  结论: a <= b
  证明: le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) sup_le h le_sup_right

Depends on / 依赖: bot_le, hd.le_bot, le_bot, le_of_inf_le_sup_le, le_sup_right, le_trans, sup_le
-/
theorem Disjoint.left_le_of_le_sup_right (h : a <= b ⊔ c) (hd : Disjoint a c) : a <= b :=
le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) sup_le h le_sup_right

/--
theorem `Disjoint.left_le_of_le_sup_left` / 定理 `Disjoint.left_le_of_le_sup_left`

English:
theorem Disjoint.left_le_of_le_sup_left
  given: (h : a <= c ⊔ b) (hd : Disjoint a c)
  statement: a <= b
  proof: hd.left_le_of_le_sup_right by rwa [sup_comm]

中文:
定理 Disjoint.left_le_of_le_sup_left
  条件: (h : a <= c ⊔ b) (hd : Disjoint a c)
  结论: a <= b
  证明: hd.left_le_of_le_sup_right by rwa [sup_comm]

Depends on / 依赖: hd.left_le_of_le_sup_right, left_le_of_le_sup_right, sup_comm
-/
theorem Disjoint.left_le_of_le_sup_left (h : a <= c ⊔ b) (hd : Disjoint a c) : a <= b :=
hd.left_le_of_le_sup_right by rwa [sup_comm]

end DistribLatticeBot

end Disjoint

section Codisjoint

section DistribLatticeTop

variable [DistribLattice α] [OrderTop α] {a b c : α}

@[simp]
/--
theorem `codisjoint_inf_left` / 定理 `codisjoint_inf_left`

English:
theorem codisjoint_inf_left
  statement: Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b c
  proof: by
  simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]

@[simp]

中文:
定理 codisjoint_inf_left
  结论: Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b c
  证明: by
  simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]

@[simp]

Depends on / 依赖: codisjoint_iff, inf_eq_top_iff, sup_inf_right
-/
theorem codisjoint_inf_left : Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b c := by
  simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]

@[simp]
/--
theorem `codisjoint_inf_right` / 定理 `codisjoint_inf_right`

English:
theorem codisjoint_inf_right
  statement: Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint a c
  proof: by
  simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]

中文:
定理 codisjoint_inf_right
  结论: Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint a c
  证明: by
  simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]

Depends on / 依赖: codisjoint_iff, inf_eq_top_iff, sup_inf_left
-/
theorem codisjoint_inf_right : Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint a c := by
  simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]

/--
theorem `Codisjoint.inf_left` / 定理 `Codisjoint.inf_left`

English:
theorem Codisjoint.inf_left
  given: (ha : Codisjoint a c) (hb : Codisjoint b c)
  statement: Codisjoint (a ⊓ b) c
  proof: codisjoint_inf_left.2 ⟨ha, hb⟩

中文:
定理 Codisjoint.inf_left
  条件: (ha : Codisjoint a c) (hb : Codisjoint b c)
  结论: Codisjoint (a ⊓ b) c
  证明: codisjoint_inf_left.2 ⟨ha, hb⟩

Depends on / 依赖: codisjoint_inf_left
-/
theorem Codisjoint.inf_left (ha : Codisjoint a c) (hb : Codisjoint b c) : Codisjoint (a ⊓ b) c :=
  codisjoint_inf_left.2 ⟨ha, hb⟩

/--
theorem `Codisjoint.inf_right` / 定理 `Codisjoint.inf_right`

English:
theorem Codisjoint.inf_right
  given: (hb : Codisjoint a b) (hc : Codisjoint a c)
  statement: Codisjoint a (b ⊓ c)
  proof: codisjoint_inf_right.2 ⟨hb, hc⟩

中文:
定理 Codisjoint.inf_right
  条件: (hb : Codisjoint a b) (hc : Codisjoint a c)
  结论: Codisjoint a (b ⊓ c)
  证明: codisjoint_inf_right.2 ⟨hb, hc⟩

Depends on / 依赖: codisjoint_inf_right
-/
theorem Codisjoint.inf_right (hb : Codisjoint a b) (hc : Codisjoint a c) : Codisjoint a (b ⊓ c) :=
  codisjoint_inf_right.2 ⟨hb, hc⟩

/--
theorem `Codisjoint.left_le_of_le_inf_right` / 定理 `Codisjoint.left_le_of_le_inf_right`

English:
theorem Codisjoint.left_le_of_le_inf_right
  given: (h : a ⊓ b <= c) (hd : Codisjoint b c)
  statement: a <= c
  proof: @Disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm

中文:
定理 Codisjoint.left_le_of_le_inf_right
  条件: (h : a ⊓ b <= c) (hd : Codisjoint b c)
  结论: a <= c
  证明: @Disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm

Depends on / 依赖: Disjoint, Disjoint.left_le_of_le_sup_right, hd.symm, left_le_of_le_sup_right
-/
theorem Codisjoint.left_le_of_le_inf_right (h : a ⊓ b <= c) (hd : Codisjoint b c) : a <= c :=
  @Disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm

/--
theorem `Codisjoint.left_le_of_le_inf_left` / 定理 `Codisjoint.left_le_of_le_inf_left`

English:
theorem Codisjoint.left_le_of_le_inf_left
  given: (h : b ⊓ a <= c) (hd : Codisjoint b c)
  statement: a <= c
  proof: hd.left_le_of_le_inf_right by rwa [inf_comm]

中文:
定理 Codisjoint.left_le_of_le_inf_left
  条件: (h : b ⊓ a <= c) (hd : Codisjoint b c)
  结论: a <= c
  证明: hd.left_le_of_le_inf_right by rwa [inf_comm]

Depends on / 依赖: hd.left_le_of_le_inf_right, inf_comm, left_le_of_le_inf_right
-/
theorem Codisjoint.left_le_of_le_inf_left (h : b ⊓ a <= c) (hd : Codisjoint b c) : a <= c :=
hd.left_le_of_le_inf_right by rwa [inf_comm]

end DistribLatticeTop

end Codisjoint

open OrderDual

@[to_dual]
/--
theorem `Disjoint.dual` / 定理 `Disjoint.dual`

English:
theorem Disjoint.dual
  given: [PartialOrder α] [OrderBot α] {a b : α}
  proof: id

@[to_dual (attr := simp, grind =)]

中文:
定理 Disjoint.dual
  条件: [PartialOrder α] [OrderBot α] {a b : α}
  证明: id

@[to_dual (attr := simp, grind =)]
-/
theorem Disjoint.dual [PartialOrder α] [OrderBot α] {a b : α} :
    Disjoint a b -> Codisjoint (toDual a) (toDual b) :=
  id

@[to_dual (attr := simp, grind =)]
/--
theorem `disjoint_toDual_iff` / 定理 `disjoint_toDual_iff`

English:
theorem disjoint_toDual_iff
  given: [PartialOrder α] [OrderTop α] {a b : α}
  proof: Iff.rfl

@[to_dual (attr := simp, grind =)]

中文:
定理 disjoint_toDual_iff
  条件: [PartialOrder α] [OrderTop α] {a b : α}
  证明: Iff.rfl

@[to_dual (attr := simp, grind =)]

Depends on / 依赖: Iff.rfl
-/
theorem disjoint_toDual_iff [PartialOrder α] [OrderTop α] {a b : α} :
    Disjoint (toDual a) (toDual b) ↔ Codisjoint a b :=
  Iff.rfl

@[to_dual (attr := simp, grind =)]
/--
theorem `disjoint_ofDual_iff` / 定理 `disjoint_ofDual_iff`

English:
theorem disjoint_ofDual_iff
  given: [PartialOrder α] [OrderBot α] {a b : αᵒᵈ}
  proof: Iff.rfl

中文:
定理 disjoint_ofDual_iff
  条件: [PartialOrder α] [OrderBot α] {a b : αᵒᵈ}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem disjoint_ofDual_iff [PartialOrder α] [OrderBot α] {a b : αᵒᵈ} :
    Disjoint (ofDual a) (ofDual b) ↔ Codisjoint a b :=
  Iff.rfl

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] {a b c : α}

@[to_dual]
/--
theorem `Disjoint.le_of_codisjoint` / 定理 `Disjoint.le_of_codisjoint`

English:
theorem Disjoint.le_of_codisjoint
  given: (hab : Disjoint a b) (hbc : Codisjoint b c)
  statement: a <= c
  proof: by
  rw [← @inf_top_eq _ _ _ a]; rw [← @bot_sup_eq _ _ _ c]; rw [← hab.eq_bot]; rw [← hbc.eq_top]; rw [sup_inf_right]
  exact inf_le_inf_right _ le_sup_left

中文:
定理 Disjoint.le_of_codisjoint
  条件: (hab : Disjoint a b) (hbc : Codisjoint b c)
  结论: a <= c
  证明: by
  rw [← @inf_top_eq _ _ _ a]; rw [← @bot_sup_eq _ _ _ c]; rw [← hab.eq_bot]; rw [← hbc.eq_top]; rw [sup_inf_right]
  exact inf_le_inf_right _ le_sup_left

Depends on / 依赖: bot_sup_eq, eq_bot, eq_top, hab.eq_bot, hbc.eq_top, inf_le_inf_right, inf_top_eq, le_sup_left, sup_inf_right
-/
theorem Disjoint.le_of_codisjoint (hab : Disjoint a b) (hbc : Codisjoint b c) : a <= c := by
  rw [← @inf_top_eq _ _ _ a]; rw [← @bot_sup_eq _ _ _ c]; rw [← hab.eq_bot]; rw [← hbc.eq_top]; rw [sup_inf_right]
  exact inf_le_inf_right _ le_sup_left

end DistribLattice

section IsCompl

/--
Definition of `IsCompl` / `IsCompl` 的定义

English:
structure IsCompl
  parameters: [PartialOrder α] [BoundedOrder α] (x y : α)
  axioms and operations (2):
    - disjoint : Disjoint x y
    - codisjoint : Codisjoint x y

中文:
结构 IsCompl
  参数: [PartialOrder α] [BoundedOrder α] (x y : α)
  公理与运算 (2 个):
    - disjoint : Disjoint x y
    - codisjoint : Codisjoint x y

Depends on / 依赖: IsCompl, IsCompl.mk, codisjoint, disjoint
-/
structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
  /-- If `x` and `y` are to be complementary in an order, they should be disjoint. -/
  protected disjoint : Disjoint x y
  /-- If `x` and `y` are to be complementary in an order, they should be codisjoint. -/
  protected codisjoint : Codisjoint x y

attribute [to_dual existing] IsCompl.disjoint
attribute [to_dual self (reorder := disjoint codisjoint)] IsCompl.mk

@[to_dual isCompl_iff']
/--
theorem `isCompl_iff` / 定理 `isCompl_iff`

English:
theorem isCompl_iff
  given: [PartialOrder α] [BoundedOrder α] {a b : α}
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isCompl_iff
  条件: [PartialOrder α] [BoundedOrder α] {a b : α}
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
theorem isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} :
    IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

namespace IsCompl

section BoundedPartialOrder

variable [PartialOrder α] [BoundedOrder α] {x y : α}

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : IsCompl x y)
  statement: IsCompl y x
  proof: ⟨h.1.symm, h.2.symm⟩

@[grind =]

中文:
定理 symm
  条件: (h : IsCompl x y)
  结论: IsCompl y x
  证明: ⟨h.1.symm, h.2.symm⟩

@[grind =]
-/
protected theorem symm (h : IsCompl x y) : IsCompl y x :=
  ⟨h.1.symm, h.2.symm⟩

@[grind =]
/--
lemma `_root_.isCompl_comm` / 引理 `_root_.isCompl_comm`

English:
lemma _root_.isCompl_comm
  statement: IsCompl x y ↔ IsCompl y x
  proof: ⟨IsCompl.symm, IsCompl.symm⟩

中文:
引理 _root_.isCompl_comm
  结论: IsCompl x y ↔ IsCompl y x
  证明: ⟨IsCompl.symm, IsCompl.symm⟩

Depends on / 依赖: IsCompl, IsCompl.symm
-/
lemma _root_.isCompl_comm : IsCompl x y ↔ IsCompl y x := ⟨IsCompl.symm, IsCompl.symm⟩

/--
theorem `dual` / 定理 `dual`

English:
theorem dual
  given: (h : IsCompl x y)
  statement: IsCompl (toDual x) (toDual y)
  proof: ⟨h.2, h.1⟩

中文:
定理 dual
  条件: (h : IsCompl x y)
  结论: IsCompl (toDual x) (toDual y)
  证明: ⟨h.2, h.1⟩
-/
theorem dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y) :=
  ⟨h.2, h.1⟩

/--
theorem `ofDual` / 定理 `ofDual`

English:
theorem ofDual
  given: {a b : αᵒᵈ} (h : IsCompl a b)
  statement: IsCompl (ofDual a) (ofDual b)
  proof: ⟨h.2, h.1⟩

中文:
定理 ofDual
  条件: {a b : αᵒᵈ} (h : IsCompl a b)
  结论: IsCompl (ofDual a) (ofDual b)
  证明: ⟨h.2, h.1⟩
-/
theorem ofDual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a) (ofDual b) :=
  ⟨h.2, h.1⟩

end BoundedPartialOrder

section BoundedLattice

variable [Lattice α] [BoundedOrder α] {x y : α}

@[to_dual self (reorder := h₁ h₂)]
/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: (h₁ : x ⊓ y <= ⊥) (h₂ : ⊤ <= x ⊔ y)
  statement: IsCompl x y
  proof: ⟨by grind [disjoint_iff_inf_le], by grind [codisjoint_iff_le_sup]⟩

@[to_dual self (reorder := h₁ h₂)]

中文:
定理 of_le
  条件: (h₁ : x ⊓ y <= ⊥) (h₂ : ⊤ <= x ⊔ y)
  结论: IsCompl x y
  证明: ⟨by grind [disjoint_iff_inf_le], by grind [codisjoint_iff_le_sup]⟩

@[to_dual self (reorder := h₁ h₂)]

Depends on / 依赖: codisjoint_iff_le_sup, disjoint_iff_inf_le
-/
theorem of_le (h₁ : x ⊓ y <= ⊥) (h₂ : ⊤ <= x ⊔ y) : IsCompl x y :=
  ⟨by grind [disjoint_iff_inf_le], by grind [codisjoint_iff_le_sup]⟩

@[to_dual self (reorder := h₁ h₂)]
/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤)
  statement: IsCompl x y
  proof: ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩

@[to_dual]

中文:
定理 of_eq
  条件: (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤)
  结论: IsCompl x y
  证明: ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩

@[to_dual]

Depends on / 依赖: codisjoint_iff, codisjoint_iff.mpr, disjoint_iff, disjoint_iff.mpr
-/
theorem of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y :=
  ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩

@[to_dual]
/--
theorem `inf_eq_bot` / 定理 `inf_eq_bot`

English:
theorem inf_eq_bot
  given: (h : IsCompl x y)
  statement: x ⊓ y = ⊥
  proof: h.disjoint.eq_bot

中文:
定理 inf_eq_bot
  条件: (h : IsCompl x y)
  结论: x ⊓ y = ⊥
  证明: h.disjoint.eq_bot

Depends on / 依赖: disjoint, eq_bot, h.disjoint.eq_bot
-/
theorem inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥ :=
  h.disjoint.eq_bot

end BoundedLattice

variable [DistribLattice α] [BoundedOrder α] {a b x y z : α}

/--
theorem `inf_left_le_of_le_sup_right` / 定理 `inf_left_le_of_le_sup_right`

English:
theorem inf_left_le_of_le_sup_right
  given: (h : IsCompl x y) (hle : a <= b ⊔ y)
  statement: a ⊓ x <= b
  proof: calc
    a ⊓ x <= (b ⊔ y) ⊓ x := inf_le_inf hle le_rfl
    _ = b ⊓ x ⊔ y ⊓ x := inf_sup_right _ _ _
    _ = b ⊓ x := by rw [h.symm.inf_eq_bot, sup_bot_eq]
    _ <= b := inf_le_left

中文:
定理 inf_left_le_of_le_sup_right
  条件: (h : IsCompl x y) (hle : a <= b ⊔ y)
  结论: a ⊓ x <= b
  证明: calc
    a ⊓ x <= (b ⊔ y) ⊓ x := inf_le_inf hle le_rfl
    _ = b ⊓ x ⊔ y ⊓ x := inf_sup_right _ _ _
    _ = b ⊓ x := by rw [h.symm.inf_eq_bot, sup_bot_eq]
    _ <= b := inf_le_left

Depends on / 依赖: h.symm.inf_eq_bot, inf_eq_bot, inf_le_inf, inf_le_left, inf_sup_right, le_rfl, sup_bot_eq
-/
theorem inf_left_le_of_le_sup_right (h : IsCompl x y) (hle : a <= b ⊔ y) : a ⊓ x <= b :=
  calc
    a ⊓ x <= (b ⊔ y) ⊓ x := inf_le_inf hle le_rfl
    _ = b ⊓ x ⊔ y ⊓ x := inf_sup_right _ _ _
    _ = b ⊓ x := by rw [h.symm.inf_eq_bot, sup_bot_eq]
    _ <= b := inf_le_left

/--
theorem `le_sup_right_iff_inf_left_le` / 定理 `le_sup_right_iff_inf_left_le`

English:
theorem le_sup_right_iff_inf_left_le
  given: {a b} (h : IsCompl x y)
  statement: a <= b ⊔ y ↔ a ⊓ x <= b
  proof: ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩

中文:
定理 le_sup_right_iff_inf_left_le
  条件: {a b} (h : IsCompl x y)
  结论: a <= b ⊔ y ↔ a ⊓ x <= b
  证明: ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩

Depends on / 依赖: h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right, inf_left_le_of_le_sup_right
-/
theorem le_sup_right_iff_inf_left_le {a b} (h : IsCompl x y) : a <= b ⊔ y ↔ a ⊓ x <= b :=
  ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩

/--
theorem `inf_left_eq_bot_iff` / 定理 `inf_left_eq_bot_iff`

English:
theorem inf_left_eq_bot_iff
  given: (h : IsCompl y z)
  statement: x ⊓ y = ⊥ ↔ x <= z
  proof: by
  rw [← le_bot_iff]; rw [← h.le_sup_right_iff_inf_left_le]; rw [bot_sup_eq]

中文:
定理 inf_left_eq_bot_iff
  条件: (h : IsCompl y z)
  结论: x ⊓ y = ⊥ ↔ x <= z
  证明: by
  rw [← le_bot_iff]; rw [← h.le_sup_right_iff_inf_left_le]; rw [bot_sup_eq]

Depends on / 依赖: bot_sup_eq, h.le_sup_right_iff_inf_left_le, le_bot_iff, le_sup_right_iff_inf_left_le
-/
theorem inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓ y = ⊥ ↔ x <= z := by
  rw [← le_bot_iff]; rw [← h.le_sup_right_iff_inf_left_le]; rw [bot_sup_eq]

/--
theorem `inf_right_eq_bot_iff` / 定理 `inf_right_eq_bot_iff`

English:
theorem inf_right_eq_bot_iff
  given: (h : IsCompl y z)
  statement: x ⊓ z = ⊥ ↔ x <= y
  proof: h.symm.inf_left_eq_bot_iff

中文:
定理 inf_right_eq_bot_iff
  条件: (h : IsCompl y z)
  结论: x ⊓ z = ⊥ ↔ x <= y
  证明: h.symm.inf_left_eq_bot_iff

Depends on / 依赖: h.symm.inf_left_eq_bot_iff, inf_left_eq_bot_iff
-/
theorem inf_right_eq_bot_iff (h : IsCompl y z) : x ⊓ z = ⊥ ↔ x <= y :=
  h.symm.inf_left_eq_bot_iff

/--
theorem `disjoint_left_iff` / 定理 `disjoint_left_iff`

English:
theorem disjoint_left_iff
  given: (h : IsCompl y z)
  statement: Disjoint x y ↔ x <= z
  proof: by
  rw [disjoint_iff]
  exact h.inf_left_eq_bot_iff

中文:
定理 disjoint_left_iff
  条件: (h : IsCompl y z)
  结论: Disjoint x y ↔ x <= z
  证明: by
  rw [disjoint_iff]
  exact h.inf_left_eq_bot_iff

Depends on / 依赖: disjoint_iff, h.inf_left_eq_bot_iff, inf_left_eq_bot_iff
-/
theorem disjoint_left_iff (h : IsCompl y z) : Disjoint x y ↔ x <= z := by
  rw [disjoint_iff]
  exact h.inf_left_eq_bot_iff

/--
theorem `disjoint_right_iff` / 定理 `disjoint_right_iff`

English:
theorem disjoint_right_iff
  given: (h : IsCompl y z)
  statement: Disjoint x z ↔ x <= y
  proof: h.symm.disjoint_left_iff

中文:
定理 disjoint_right_iff
  条件: (h : IsCompl y z)
  结论: Disjoint x z ↔ x <= y
  证明: h.symm.disjoint_left_iff

Depends on / 依赖: disjoint_left_iff, h.symm.disjoint_left_iff
-/
theorem disjoint_right_iff (h : IsCompl y z) : Disjoint x z ↔ x <= y :=
  h.symm.disjoint_left_iff

/--
theorem `le_left_iff` / 定理 `le_left_iff`

English:
theorem le_left_iff
  given: (h : IsCompl x y)
  statement: z <= x ↔ Disjoint z y
  proof: h.disjoint_right_iff.symm

中文:
定理 le_left_iff
  条件: (h : IsCompl x y)
  结论: z <= x ↔ Disjoint z y
  证明: h.disjoint_right_iff.symm

Depends on / 依赖: disjoint_right_iff, h.disjoint_right_iff.symm
-/
theorem le_left_iff (h : IsCompl x y) : z <= x ↔ Disjoint z y :=
  h.disjoint_right_iff.symm

/--
theorem `le_right_iff` / 定理 `le_right_iff`

English:
theorem le_right_iff
  given: (h : IsCompl x y)
  statement: z <= y ↔ Disjoint z x
  proof: h.symm.le_left_iff

中文:
定理 le_right_iff
  条件: (h : IsCompl x y)
  结论: z <= y ↔ Disjoint z x
  证明: h.symm.le_left_iff

Depends on / 依赖: h.symm.le_left_iff, le_left_iff
-/
theorem le_right_iff (h : IsCompl x y) : z <= y ↔ Disjoint z x :=
  h.symm.le_left_iff

/--
theorem `left_le_iff` / 定理 `left_le_iff`

English:
theorem left_le_iff
  given: (h : IsCompl x y)
  statement: x <= z ↔ Codisjoint z y
  proof: h.dual.le_left_iff

中文:
定理 left_le_iff
  条件: (h : IsCompl x y)
  结论: x <= z ↔ Codisjoint z y
  证明: h.dual.le_left_iff

Depends on / 依赖: h.dual.le_left_iff, le_left_iff
-/
theorem left_le_iff (h : IsCompl x y) : x <= z ↔ Codisjoint z y :=
  h.dual.le_left_iff

/--
theorem `right_le_iff` / 定理 `right_le_iff`

English:
theorem right_le_iff
  given: (h : IsCompl x y)
  statement: y <= z ↔ Codisjoint z x
  proof: h.symm.left_le_iff

中文:
定理 right_le_iff
  条件: (h : IsCompl x y)
  结论: y <= z ↔ Codisjoint z x
  证明: h.symm.left_le_iff

Depends on / 依赖: h.symm.left_le_iff, left_le_iff
-/
theorem right_le_iff (h : IsCompl x y) : y <= z ↔ Codisjoint z x :=
  h.symm.left_le_iff

/--
theorem `Antitone` / 定理 `Antitone`

English:
theorem Antitone
  given: {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x <= x')
  statement: y' <= y
  proof: h'.right_le_iff.2 h.symm.codisjoint.mono_right hx

中文:
定理 Antitone
  条件: {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x <= x')
  结论: y' <= y
  证明: h'.right_le_iff.2 h.symm.codisjoint.mono_right hx
-/
protected theorem Antitone {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x <= x') : y' <= y :=
h'.right_le_iff.2 h.symm.codisjoint.mono_right hx

/--
theorem `right_unique` / 定理 `right_unique`

English:
theorem right_unique
  given: (hxy : IsCompl x y) (hxz : IsCompl x z)
  statement: y = z
  proof: le_antisymm (hxz.Antitone hxy <| le_refl x) (hxy.Antitone hxz <| le_refl x)

中文:
定理 right_unique
  条件: (hxy : IsCompl x y) (hxz : IsCompl x z)
  结论: y = z
  证明: le_antisymm (hxz.Antitone hxy <| le_refl x) (hxy.Antitone hxz <| le_refl x)

Depends on / 依赖: Antitone, hxy.Antitone, hxz.Antitone, le_antisymm, le_refl
-/
theorem right_unique (hxy : IsCompl x y) (hxz : IsCompl x z) : y = z :=
  le_antisymm (hxz.Antitone hxy <| le_refl x) (hxy.Antitone hxz <| le_refl x)

/--
theorem `left_unique` / 定理 `left_unique`

English:
theorem left_unique
  given: (hxz : IsCompl x z) (hyz : IsCompl y z)
  statement: x = y
  proof: hxz.symm.right_unique hyz.symm

中文:
定理 left_unique
  条件: (hxz : IsCompl x z) (hyz : IsCompl y z)
  结论: x = y
  证明: hxz.symm.right_unique hyz.symm

Depends on / 依赖: hxz.symm.right_unique, hyz.symm, right_unique
-/
theorem left_unique (hxz : IsCompl x z) (hyz : IsCompl y z) : x = y :=
  hxz.symm.right_unique hyz.symm

/--
theorem `sup_inf` / 定理 `sup_inf`

English:
theorem sup_inf
  given: {x' y'} (h : IsCompl x y) (h' : IsCompl x' y')
  statement: IsCompl (x ⊔ x') (y ⊓ y')
  proof: of_eq
    (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
      h'.inf_eq_bot, inf_bot_eq])
    (by rw [sup_inf_left, sup_comm x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
      sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])

中文:
定理 sup_inf
  条件: {x' y'} (h : IsCompl x y) (h' : IsCompl x' y')
  结论: IsCompl (x ⊔ x') (y ⊓ y')
  证明: of_eq
    (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
      h'.inf_eq_bot, inf_bot_eq])
    (by rw [sup_inf_left, sup_comm x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
      sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])

Depends on / 依赖: bot_inf_eq, bot_sup_eq, h.inf_eq_bot, h.sup_eq_top, inf_assoc, inf_bot_eq, inf_eq_bot, inf_left_comm, inf_sup_right, of_eq, sup_assoc, sup_comm, sup_eq_top, sup_inf_left, sup_left_comm, sup_top_eq, top_inf_eq
-/
theorem sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊔ x') (y ⊓ y') :=
  of_eq
    (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
      h'.inf_eq_bot, inf_bot_eq])
    (by rw [sup_inf_left, sup_comm x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
      sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])

/--
theorem `inf_sup` / 定理 `inf_sup`

English:
theorem inf_sup
  given: {x' y'} (h : IsCompl x y) (h' : IsCompl x' y')
  statement: IsCompl (x ⊓ x') (y ⊔ y')
  proof: (h.symm.sup_inf h'.symm).symm

中文:
定理 inf_sup
  条件: {x' y'} (h : IsCompl x y) (h' : IsCompl x' y')
  结论: IsCompl (x ⊓ x') (y ⊔ y')
  证明: (h.symm.sup_inf h'.symm).symm

Depends on / 依赖: h.symm.sup_inf, sup_inf
-/
theorem inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊓ x') (y ⊔ y') :=
  (h.symm.sup_inf h'.symm).symm

end IsCompl

namespace Prod

variable {β : Type*} [PartialOrder α] [PartialOrder β]

@[grind =]
/--
theorem `disjoint_iff` / 定理 `disjoint_iff`

English:
theorem disjoint_iff
  given: [OrderBot α] [OrderBot β] {x y : α × β}
  proof: by
  constructor
  · intro h
    refine ⟨fun a hx hy => (@h (a, ⊥) ⟨hx, ?_⟩ ⟨hy, ?_⟩).1,
      fun b hx hy => (@h (⊥, b) ⟨?_, hx⟩ ⟨?_, hy⟩).2⟩
    all_goals exact bot_le
  · rintro ⟨ha, hb⟩ z hza hzb
    exact ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩

@[grind =]

中文:
定理 disjoint_iff
  条件: [OrderBot α] [OrderBot β] {x y : α × β}
  证明: by
  constructor
  · intro h
    refine ⟨fun a hx hy => (@h (a, ⊥) ⟨hx, ?_⟩ ⟨hy, ?_⟩).1,
      fun b hx hy => (@h (⊥, b) ⟨?_, hx⟩ ⟨?_, hy⟩).2⟩
    all_goals exact bot_le
  · rintro ⟨ha, hb⟩ z hza hzb
    exact ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩

@[grind =]
-/
protected theorem disjoint_iff [OrderBot α] [OrderBot β] {x y : α × β} :
    Disjoint x y ↔ Disjoint x.1 y.1 ∧ Disjoint x.2 y.2 := by
  constructor
  · intro h
    refine ⟨fun a hx hy => (@h (a, ⊥) ⟨hx, ?_⟩ ⟨hy, ?_⟩).1,
      fun b hx hy => (@h (⊥, b) ⟨?_, hx⟩ ⟨?_, hy⟩).2⟩
    all_goals exact bot_le
  · rintro ⟨ha, hb⟩ z hza hzb
    exact ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩

@[grind =]
/--
theorem `codisjoint_iff` / 定理 `codisjoint_iff`

English:
theorem codisjoint_iff
  given: [OrderTop α] [OrderTop β] {x y : α × β}
  proof: @Prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _

@[grind =]

中文:
定理 codisjoint_iff
  条件: [OrderTop α] [OrderTop β] {x y : α × β}
  证明: @Prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _

@[grind =]
-/
protected theorem codisjoint_iff [OrderTop α] [OrderTop β] {x y : α × β} :
    Codisjoint x y ↔ Codisjoint x.1 y.1 ∧ Codisjoint x.2 y.2 :=
  @Prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _

@[grind =]
/--
theorem `isCompl_iff` / 定理 `isCompl_iff`

English:
theorem isCompl_iff
  given: [BoundedOrder α] [BoundedOrder β] {x y : α × β}
  proof: by
  simp_rw [isCompl_iff, Prod.disjoint_iff, Prod.codisjoint_iff, and_and_and_comm]

中文:
定理 isCompl_iff
  条件: [BoundedOrder α] [BoundedOrder β] {x y : α × β}
  证明: by
  simp_rw [isCompl_iff, Prod.disjoint_iff, Prod.codisjoint_iff, and_and_and_comm]
-/
protected theorem isCompl_iff [BoundedOrder α] [BoundedOrder β] {x y : α × β} :
    IsCompl x y ↔ IsCompl x.1 y.1 ∧ IsCompl x.2 y.2 := by
  simp_rw [isCompl_iff, Prod.disjoint_iff, Prod.codisjoint_iff, and_and_and_comm]

end Prod

section

variable [Lattice α] [BoundedOrder α] {a b x : α}

@[simp, grind =]
/--
theorem `isCompl_toDual_iff` / 定理 `isCompl_toDual_iff`

English:
theorem isCompl_toDual_iff
  statement: IsCompl (toDual a) (toDual b) ↔ IsCompl a b
  proof: ⟨IsCompl.ofDual, IsCompl.dual⟩

@[simp, grind =]

中文:
定理 isCompl_toDual_iff
  结论: IsCompl (toDual a) (toDual b) ↔ IsCompl a b
  证明: ⟨IsCompl.ofDual, IsCompl.dual⟩

@[simp, grind =]

Depends on / 依赖: IsCompl, IsCompl.dual, IsCompl.ofDual, ofDual
-/
theorem isCompl_toDual_iff : IsCompl (toDual a) (toDual b) ↔ IsCompl a b :=
  ⟨IsCompl.ofDual, IsCompl.dual⟩

@[simp, grind =]
/--
theorem `isCompl_ofDual_iff` / 定理 `isCompl_ofDual_iff`

English:
theorem isCompl_ofDual_iff
  given: {a b : αᵒᵈ}
  statement: IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b
  proof: ⟨IsCompl.dual, IsCompl.ofDual⟩

中文:
定理 isCompl_ofDual_iff
  条件: {a b : αᵒᵈ}
  结论: IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b
  证明: ⟨IsCompl.dual, IsCompl.ofDual⟩

Depends on / 依赖: IsCompl, IsCompl.dual, IsCompl.ofDual, ofDual
-/
theorem isCompl_ofDual_iff {a b : αᵒᵈ} : IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b :=
  ⟨IsCompl.dual, IsCompl.ofDual⟩

/--
theorem `isCompl_bot_top` / 定理 `isCompl_bot_top`

English:
theorem isCompl_bot_top
  statement: IsCompl (⊥ : α) ⊤
  proof: IsCompl.of_eq (bot_inf_eq _) (sup_top_eq _)

中文:
定理 isCompl_bot_top
  结论: IsCompl (⊥ : α) ⊤
  证明: IsCompl.of_eq (bot_inf_eq _) (sup_top_eq _)

Depends on / 依赖: IsCompl, IsCompl.of_eq, bot_inf_eq, of_eq, sup_top_eq
-/
theorem isCompl_bot_top : IsCompl (⊥ : α) ⊤ :=
  IsCompl.of_eq (bot_inf_eq _) (sup_top_eq _)

/--
theorem `isCompl_top_bot` / 定理 `isCompl_top_bot`

English:
theorem isCompl_top_bot
  statement: IsCompl (⊤ : α) ⊥
  proof: IsCompl.of_eq (inf_bot_eq _) (top_sup_eq _)

中文:
定理 isCompl_top_bot
  结论: IsCompl (⊤ : α) ⊥
  证明: IsCompl.of_eq (inf_bot_eq _) (top_sup_eq _)

Depends on / 依赖: IsCompl, IsCompl.of_eq, inf_bot_eq, of_eq, top_sup_eq
-/
theorem isCompl_top_bot : IsCompl (⊤ : α) ⊥ :=
  IsCompl.of_eq (inf_bot_eq _) (top_sup_eq _)

/--
theorem `eq_top_of_isCompl_bot` / 定理 `eq_top_of_isCompl_bot`

English:
theorem eq_top_of_isCompl_bot
  given: (h : IsCompl x ⊥)
  statement: x = ⊤
  proof: by rw [← sup_bot_eq x, h.sup_eq_top]

中文:
定理 eq_top_of_isCompl_bot
  条件: (h : IsCompl x ⊥)
  结论: x = ⊤
  证明: by rw [← sup_bot_eq x, h.sup_eq_top]

Depends on / 依赖: h.sup_eq_top, sup_bot_eq, sup_eq_top
-/
theorem eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤ := by rw [← sup_bot_eq x, h.sup_eq_top]

/--
theorem `eq_top_of_bot_isCompl` / 定理 `eq_top_of_bot_isCompl`

English:
theorem eq_top_of_bot_isCompl
  given: (h : IsCompl ⊥ x)
  statement: x = ⊤
  proof: eq_top_of_isCompl_bot h.symm

中文:
定理 eq_top_of_bot_isCompl
  条件: (h : IsCompl ⊥ x)
  结论: x = ⊤
  证明: eq_top_of_isCompl_bot h.symm

Depends on / 依赖: eq_top_of_isCompl_bot, h.symm
-/
theorem eq_top_of_bot_isCompl (h : IsCompl ⊥ x) : x = ⊤ :=
  eq_top_of_isCompl_bot h.symm

/--
theorem `eq_bot_of_isCompl_top` / 定理 `eq_bot_of_isCompl_top`

English:
theorem eq_bot_of_isCompl_top
  given: (h : IsCompl x ⊤)
  statement: x = ⊥
  proof: eq_top_of_isCompl_bot h.dual

中文:
定理 eq_bot_of_isCompl_top
  条件: (h : IsCompl x ⊤)
  结论: x = ⊥
  证明: eq_top_of_isCompl_bot h.dual

Depends on / 依赖: eq_top_of_isCompl_bot, h.dual
-/
theorem eq_bot_of_isCompl_top (h : IsCompl x ⊤) : x = ⊥ :=
  eq_top_of_isCompl_bot h.dual

/--
theorem `eq_bot_of_top_isCompl` / 定理 `eq_bot_of_top_isCompl`

English:
theorem eq_bot_of_top_isCompl
  given: (h : IsCompl ⊤ x)
  statement: x = ⊥
  proof: eq_top_of_bot_isCompl h.dual

中文:
定理 eq_bot_of_top_isCompl
  条件: (h : IsCompl ⊤ x)
  结论: x = ⊥
  证明: eq_top_of_bot_isCompl h.dual

Depends on / 依赖: eq_top_of_bot_isCompl, h.dual
-/
theorem eq_bot_of_top_isCompl (h : IsCompl ⊤ x) : x = ⊥ :=
  eq_top_of_bot_isCompl h.dual

end

section IsComplemented

section Lattice

variable [Lattice α] [BoundedOrder α]

/--
Definition of `IsComplemented` / `IsComplemented` 的定义

English:
definition IsComplemented
  signature: (a : α)
  body: exists b, IsCompl a b

中文:
定义 IsComplemented
  签名: (a : α)
  定义体: exists b, IsCompl a b

Depends on / 依赖: IsCompl
-/
def IsComplemented (a : α) : Prop :=
  exists b, IsCompl a b

/--
theorem `isComplemented_bot` / 定理 `isComplemented_bot`

English:
theorem isComplemented_bot
  statement: IsComplemented (⊥ : α)
  proof: ⟨⊤, isCompl_bot_top⟩

中文:
定理 isComplemented_bot
  结论: IsComplemented (⊥ : α)
  证明: ⟨⊤, isCompl_bot_top⟩

Depends on / 依赖: isCompl_bot_top
-/
theorem isComplemented_bot : IsComplemented (⊥ : α) :=
  ⟨⊤, isCompl_bot_top⟩

/--
theorem `isComplemented_top` / 定理 `isComplemented_top`

English:
theorem isComplemented_top
  statement: IsComplemented (⊤ : α)
  proof: ⟨⊥, isCompl_top_bot⟩

中文:
定理 isComplemented_top
  结论: IsComplemented (⊤ : α)
  证明: ⟨⊥, isCompl_top_bot⟩

Depends on / 依赖: isCompl_top_bot
-/
theorem isComplemented_top : IsComplemented (⊤ : α) :=
  ⟨⊥, isCompl_top_bot⟩

end Lattice

variable [DistribLattice α] [BoundedOrder α] {a b : α}

/--
theorem `IsComplemented.sup` / 定理 `IsComplemented.sup`

English:
theorem IsComplemented.sup
  statement: IsComplemented a -> IsComplemented b -> IsComplemented (a ⊔ b)
  proof: fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊓ b', ha.sup_inf hb⟩

中文:
定理 IsComplemented.sup
  结论: IsComplemented a -> IsComplemented b -> IsComplemented (a ⊔ b)
  证明: fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊓ b', ha.sup_inf hb⟩

Depends on / 依赖: ha.sup_inf, sup_inf
-/
theorem IsComplemented.sup : IsComplemented a -> IsComplemented b -> IsComplemented (a ⊔ b) :=
  fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊓ b', ha.sup_inf hb⟩

/--
theorem `IsComplemented.inf` / 定理 `IsComplemented.inf`

English:
theorem IsComplemented.inf
  statement: IsComplemented a -> IsComplemented b -> IsComplemented (a ⊓ b)
  proof: fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊔ b', ha.inf_sup hb⟩

中文:
定理 IsComplemented.inf
  结论: IsComplemented a -> IsComplemented b -> IsComplemented (a ⊓ b)
  证明: fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊔ b', ha.inf_sup hb⟩

Depends on / 依赖: ha.inf_sup, inf_sup
-/
theorem IsComplemented.inf : IsComplemented a -> IsComplemented b -> IsComplemented (a ⊓ b) :=
  fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊔ b', ha.inf_sup hb⟩

end IsComplemented

/--
Definition of `ComplementedLattice` / `ComplementedLattice` 的定义

English:
class ComplementedLattice
  parameters: (α) [Lattice α] [BoundedOrder α]
  axioms and operations (1):
    - exists_isCompl : forall a : α, exists b : α, IsCompl a b

中文:
类 ComplementedLattice
  参数: (α) [Lattice α] [BoundedOrder α]
  公理与运算 (1 个):
    - exists_isCompl : 对任意 a : α, 存在 b : α, IsCompl a b
-/
class ComplementedLattice (α) [Lattice α] [BoundedOrder α] : Prop where
  /-- In a `ComplementedLattice`, every element admits a complement. -/
  exists_isCompl : forall a : α, exists b : α, IsCompl a b

/--
lemma `complementedLattice_iff` / 引理 `complementedLattice_iff`

English:
lemma complementedLattice_iff
  given: (α) [Lattice α] [BoundedOrder α]
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
引理 complementedLattice_iff
  条件: (α) [Lattice α] [BoundedOrder α]
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
lemma complementedLattice_iff (α) [Lattice α] [BoundedOrder α] :
    ComplementedLattice α ↔ forall a : α, exists b : α, IsCompl a b :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

export ComplementedLattice (exists_isCompl)

-- This was previously a global instance,
-- but it doesn't appear to be used and has been implicated in slow typeclass resolutions.
/--
lemma `Subsingleton.instComplementedLattice` / 引理 `Subsingleton.instComplementedLattice`

English:
lemma Subsingleton.instComplementedLattice
  proof: by
  refine ⟨fun a => ⟨⊥, disjoint_bot_right, ?_⟩⟩
  rw [Subsingleton.elim ⊥ ⊤]
  exact codisjoint_top_right

中文:
引理 Subsingleton.instComplementedLattice
  证明: by
  refine ⟨fun a => ⟨⊥, disjoint_bot_right, ?_⟩⟩
  rw [Subsingleton.elim ⊥ ⊤]
  exact codisjoint_top_right

Depends on / 依赖: Subsingleton, Subsingleton.elim, codisjoint_top_right, disjoint_bot_right
-/
lemma Subsingleton.instComplementedLattice
    [Lattice α] [BoundedOrder α] [Subsingleton α] : ComplementedLattice α := by
  refine ⟨fun a => ⟨⊥, disjoint_bot_right, ?_⟩⟩
  rw [Subsingleton.elim ⊥ ⊤]
  exact codisjoint_top_right

namespace ComplementedLattice

variable [Lattice α] [BoundedOrder α] [ComplementedLattice α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ComplementedLattice αᵒᵈ
  body: ⟨fun a =>
    let ⟨b, hb⟩ := exists_isCompl (show α from a)
    ⟨b, hb.dual⟩⟩

中文:
实例 :
  签名: ComplementedLattice αᵒᵈ
  定义体: ⟨fun a =>
    let ⟨b, hb⟩ := exists_isCompl (show α from a)
    ⟨b, hb.dual⟩⟩

Depends on / 依赖: exists_isCompl, hb.dual
-/
instance : ComplementedLattice αᵒᵈ :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_isCompl (show α from a)
    ⟨b, hb.dual⟩⟩

end ComplementedLattice

-- TODO: Define as a sublattice?
/--
Definition of `Complementeds` / `Complementeds` 的定义

English:
abbreviation Complementeds
  signature: (α : Type*) [Lattice α] [BoundedOrder α]
  body: {a : α // IsComplemented a}

中文:
缩写 Complementeds
  签名: (α : 类型) [Lattice α] [BoundedOrder α]
  定义体: {a : α // IsComplemented a}

Depends on / 依赖: IsComplemented
-/
abbrev Complementeds (α : Type*) [Lattice α] [BoundedOrder α] : Type _ :=
  {a : α // IsComplemented a}

namespace Complementeds

section Lattice

variable [Lattice α] [BoundedOrder α] {a b : Complementeds α}

/--
Instance `hasCoeT` / 实例 `hasCoeT`

English:
instance hasCoeT
  signature: : CoeTC (Complementeds α) α
  body: ⟨Subtype.val⟩

中文:
实例 hasCoeT
  签名: : CoeTC (Complementeds α) α
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance hasCoeT : CoeTC (Complementeds α) α := ⟨Subtype.val⟩

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Complementeds α -> α)
  proof: Subtype.coe_injective

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: Injective ((↑) : Complementeds α -> α)
  证明: Subtype.coe_injective

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_injective : Injective ((↑) : Complementeds α -> α) := Subtype.coe_injective

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (a : α) = b ↔ a = b
  proof: Subtype.coe_inj

@[norm_cast]

中文:
定理 coe_inj
  结论: (a : α) = b ↔ a = b
  证明: Subtype.coe_inj

@[norm_cast]

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj
-/
theorem coe_inj : (a : α) = b ↔ a = b := Subtype.coe_inj

@[norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (a : α) <= b ↔ a <= b
  proof: by simp

@[norm_cast]

中文:
定理 coe_le_coe
  结论: (a : α) <= b ↔ a <= b
  证明: by simp

@[norm_cast]
-/
theorem coe_le_coe : (a : α) <= b ↔ a <= b := by simp

@[norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (a : α) < b ↔ a < b
  proof: by simp

中文:
定理 coe_lt_coe
  结论: (a : α) < b ↔ a < b
  证明: by simp
-/
theorem coe_lt_coe : (a : α) < b ↔ a < b := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (Complementeds α)
  body: Subtype.boundedOrder isComplemented_bot isComplemented_top

@[simp, norm_cast]

中文:
实例 :
  签名: BoundedOrder (Complementeds α)
  定义体: Subtype.boundedOrder isComplemented_bot isComplemented_top

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.boundedOrder, boundedOrder, isComplemented_bot, isComplemented_top
-/
instance : BoundedOrder (Complementeds α) :=
  Subtype.boundedOrder isComplemented_bot isComplemented_top

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : Complementeds α) : α) = ⊥
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: ((⊥ : Complementeds α) : α) = ⊥
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : ((⊥ : Complementeds α) : α) = ⊥ := rfl

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : Complementeds α) : α) = ⊤
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : Complementeds α) : α) = ⊤
  证明: rfl
-/
theorem coe_top : ((⊤ : Complementeds α) : α) = ⊤ := rfl

/--
theorem `mk_bot` / 定理 `mk_bot`

English:
theorem mk_bot
  statement: (⟨⊥, isComplemented_bot⟩ : Complementeds α) = ⊥
  proof: by simp

中文:
定理 mk_bot
  结论: (⟨⊥, isComplemented_bot⟩ : Complementeds α) = ⊥
  证明: by simp
-/
theorem mk_bot : (⟨⊥, isComplemented_bot⟩ : Complementeds α) = ⊥ := by simp

/--
theorem `mk_top` / 定理 `mk_top`

English:
theorem mk_top
  statement: (⟨⊤, isComplemented_top⟩ : Complementeds α) = ⊤
  proof: by simp

中文:
定理 mk_top
  结论: (⟨⊤, isComplemented_top⟩ : Complementeds α) = ⊤
  证明: by simp
-/
theorem mk_top : (⟨⊤, isComplemented_top⟩ : Complementeds α) = ⊤ := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Complementeds α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: Inhabited (Complementeds α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Complementeds α) := ⟨⊥⟩

end Lattice

variable [DistribLattice α] [BoundedOrder α] {a b : Complementeds α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Complementeds α)
  body: ⟨fun a b => ⟨a ⊔ b, a.2.sup b.2⟩⟩

中文:
实例 :
  签名: Max (Complementeds α)
  定义体: ⟨fun a b => ⟨a ⊔ b, a.2.sup b.2⟩⟩
-/
instance : Max (Complementeds α) :=
  ⟨fun a b => ⟨a ⊔ b, a.2.sup b.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Complementeds α)
  body: ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Min (Complementeds α)
  定义体: ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

@[simp, norm_cast]
-/
instance : Min (Complementeds α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (a b : Complementeds α)
  statement: ↑(a ⊔ b) = (a : α) ⊔ b
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sup
  条件: (a b : Complementeds α)
  结论: ↑(a ⊔ b) = (a : α) ⊔ b
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sup (a b : Complementeds α) : ↑(a ⊔ b) = (a : α) ⊔ b := rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (a b : Complementeds α)
  statement: ↑(a ⊓ b) = (a : α) ⊓ b
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (a b : Complementeds α)
  结论: ↑(a ⊓ b) = (a : α) ⊓ b
  证明: rfl

@[simp]
-/
theorem coe_inf (a b : Complementeds α) : ↑(a ⊓ b) = (a : α) ⊓ b := rfl

@[simp]
/--
theorem `mk_sup_mk` / 定理 `mk_sup_mk`

English:
theorem mk_sup_mk
  given: {a b : α} (ha : IsComplemented a) (hb : IsComplemented b)
  proof: rfl

@[simp]

中文:
定理 mk_sup_mk
  条件: {a b : α} (ha : IsComplemented a) (hb : IsComplemented b)
  证明: rfl

@[simp]
-/
theorem mk_sup_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) :
    (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊔ b, ha.sup hb⟩ := rfl

@[simp]
/--
theorem `mk_inf_mk` / 定理 `mk_inf_mk`

English:
theorem mk_inf_mk
  given: {a b : α} (ha : IsComplemented a) (hb : IsComplemented b)
  proof: rfl

中文:
定理 mk_inf_mk
  条件: {a b : α} (ha : IsComplemented a) (hb : IsComplemented b)
  证明: rfl
-/
theorem mk_inf_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) :
    (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊓ b, ha.inf hb⟩ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice (Complementeds α)
  body: Complementeds.coe_injective.distribLattice _ .rfl .rfl coe_sup coe_inf

@[simp, norm_cast]

中文:
实例 :
  签名: DistribLattice (Complementeds α)
  定义体: Complementeds.coe_injective.distribLattice _ .rfl .rfl coe_sup coe_inf

@[simp, norm_cast]

Depends on / 依赖: Complementeds, Complementeds.coe_injective.distribLattice, coe_inf, coe_injective, coe_sup, distribLattice
-/
instance : DistribLattice (Complementeds α) :=
  Complementeds.coe_injective.distribLattice _ .rfl .rfl coe_sup coe_inf

@[simp, norm_cast]
/--
theorem `disjoint_coe` / 定理 `disjoint_coe`

English:
theorem disjoint_coe
  statement: Disjoint (a : α) b ↔ Disjoint a b
  proof: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← coe_inf]; rw [← coe_bot]; rw [coe_inj]

@[simp, norm_cast]

中文:
定理 disjoint_coe
  结论: Disjoint (a : α) b ↔ Disjoint a b
  证明: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← coe_inf]; rw [← coe_bot]; rw [coe_inj]

@[simp, norm_cast]

Depends on / 依赖: coe_bot, coe_inf, coe_inj, disjoint_iff
-/
theorem disjoint_coe : Disjoint (a : α) b ↔ Disjoint a b := by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← coe_inf]; rw [← coe_bot]; rw [coe_inj]

@[simp, norm_cast]
/--
theorem `codisjoint_coe` / 定理 `codisjoint_coe`

English:
theorem codisjoint_coe
  statement: Codisjoint (a : α) b ↔ Codisjoint a b
  proof: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← coe_sup]; rw [← coe_top]; rw [coe_inj]

@[simp, norm_cast]

中文:
定理 codisjoint_coe
  结论: Codisjoint (a : α) b ↔ Codisjoint a b
  证明: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← coe_sup]; rw [← coe_top]; rw [coe_inj]

@[simp, norm_cast]

Depends on / 依赖: HahnSeries, HahnSeries.ofPowerSeries_injective, IsLocalization, IsLocalization.of_le, PowerSeries, PowerSeries.X, PowerSeries.X_ne_zero, Submonoid, Submonoid.powers, X_ne_zero, codisjoint_iff, coe_inj, coe_sup, coe_top, isUnit_of_mem_nonZeroDivisors, map_mem_nonZeroDivisors, ofPowerSeries_injective, of_le, powers, powers_le_nonZeroDivisors_of_noZeroDivisors
-/
theorem codisjoint_coe : Codisjoint (a : α) b ↔ Codisjoint a b := by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← coe_sup]; rw [← coe_top]; rw [coe_inj]

@[simp, norm_cast]
/--
theorem `isCompl_coe` / 定理 `isCompl_coe`

English:
theorem isCompl_coe
  statement: IsCompl (a : α) b ↔ IsCompl a b
  proof: by
  simp_rw [isCompl_iff, disjoint_coe, codisjoint_coe]

中文:
定理 isCompl_coe
  结论: IsCompl (a : α) b ↔ IsCompl a b
  证明: by
  simp_rw [isCompl_iff, disjoint_coe, codisjoint_coe]

Depends on / 依赖: codisjoint_coe, disjoint_coe, isCompl_iff, simp_rw
-/
theorem isCompl_coe : IsCompl (a : α) b ↔ IsCompl a b := by
  simp_rw [isCompl_iff, disjoint_coe, codisjoint_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ComplementedLattice (Complementeds α)
  body: ⟨fun ⟨a, b, h⟩ => ⟨⟨b, a, h.symm⟩, isCompl_coe.1 h⟩⟩

中文:
实例 :
  签名: ComplementedLattice (Complementeds α)
  定义体: ⟨fun ⟨a, b, h⟩ => ⟨⟨b, a, h.symm⟩, isCompl_coe.1 h⟩⟩

Depends on / 依赖: h.symm, isCompl_coe
-/
instance : ComplementedLattice (Complementeds α) :=
  ⟨fun ⟨a, b, h⟩ => ⟨⟨b, a, h.symm⟩, isCompl_coe.1 h⟩⟩

end Complementeds
end IsCompl
