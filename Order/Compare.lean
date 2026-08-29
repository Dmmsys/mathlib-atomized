/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Ordering.Basic
public import Mathlib.Order.OrderDual

/-!
# Comparison

This file provides basic results about orderings and comparison in linear orders.


## Definitions

* `CmpLE`: An `Ordering` from `≤`.
* `Ordering.Compares`: Turns an `Ordering` into `<` and `=` propositions.
* `linearOrderOfCompares`: Constructs a `LinearOrder` instance from the fact that any two
  elements that are not one strictly less than the other either way are equal.
-/

@[expose] public section


variable {α β : Type*}

/--
Definition of `cmpLE` / `cmpLE` 的定义

English:
definition cmpLE
  signature: {α} [LE α] [DecidableLE α] (x y : α)
  body: if x <= y then if y <= x then Ordering.eq else Ordering.lt else Ordering.gt

中文:
定义 cmpLE
  签名: {α} [LE α] [DecidableLE α] (x y : α)
  定义体: if x <= y then if y <= x then Ordering.eq else Ordering.lt else Ordering.gt

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt
-/
def cmpLE {α} [LE α] [DecidableLE α] (x y : α) : Ordering :=
  if x <= y then if y <= x then Ordering.eq else Ordering.lt else Ordering.gt

/--
theorem `cmpLE_swap` / 定理 `cmpLE_swap`

English:
theorem cmpLE_swap
  given: {α} [LE α] [@Std.Total α (· <= ·)] [DecidableLE α] (x y : α)
  proof: by
  by_cases xy : x <= y <;> by_cases yx : y <= x <;> simp [cmpLE, *, Ordering.swap]
  cases not_or_intro xy yx (total_of _ _ _)

中文:
定理 cmpLE_swap
  条件: {α} [LE α] [@Std.全 α (· <= ·)] [DecidableLE α] (x y : α)
  证明: by
  by_cases xy : x <= y <;> by_cases yx : y <= x <;> simp [cmpLE, *, Ordering.swap]
  cases not_or_intro xy yx (total_of _ _ _)

Depends on / 依赖: Ordering, Ordering.swap, not_or_intro, total_of
-/
theorem cmpLE_swap {α} [LE α] [@Std.Total α (· <= ·)] [DecidableLE α] (x y : α) :
    (cmpLE x y).swap = cmpLE y x := by
  by_cases xy : x <= y <;> by_cases yx : y <= x <;> simp [cmpLE, *, Ordering.swap]
  cases not_or_intro xy yx (total_of _ _ _)

/--
theorem `cmpLE_eq_cmp` / 定理 `cmpLE_eq_cmp`

English:
theorem cmpLE_eq_cmp
  statement: {α} [Preorder α] [@Std.Total α (· <= ·)] [DecidableLE α] [DecidableLT α]
  proof: by
  by_cases xy : x <= y <;> by_cases yx : y <= x <;> simp [cmpLE, lt_iff_le_not_ge, *, cmp, cmpUsing]
  cases not_or_intro xy yx (total_of _ _ _)

中文:
定理 cmpLE_eq_cmp
  结论: {α} [预序 α] [@Std.全 α (· <= ·)] [DecidableLE α] [DecidableLT α]
  证明: by
  by_cases xy : x <= y <;> by_cases yx : y <= x <;> simp [cmpLE, lt_iff_le_not_ge, *, cmp, cmpUsing]
  cases not_or_intro xy yx (total_of _ _ _)

Depends on / 依赖: cmpUsing, lt_iff_le_not_ge, not_or_intro, total_of
-/
theorem cmpLE_eq_cmp {α} [Preorder α] [@Std.Total α (· <= ·)] [DecidableLE α] [DecidableLT α]
    (x y : α) : cmpLE x y = cmp x y := by
  by_cases xy : x <= y <;> by_cases yx : y <= x <;> simp [cmpLE, lt_iff_le_not_ge, *, cmp, cmpUsing]
  cases not_or_intro xy yx (total_of _ _ _)

namespace Ordering

/--
theorem `compares_swap` / 定理 `compares_swap`

English:
theorem compares_swap
  given: [LT α] {a b : α} {o : Ordering}
  statement: o.swap.Compares a b ↔ o.Compares b a
  proof: by
  cases o
  · exact Iff.rfl
  · exact eq_comm
  · exact Iff.rfl

alias ⟨Compares.of_swap, Compares.swap⟩ := compares_swap

中文:
定理 compares_swap
  条件: [LT α] {a b : α} {o : Ordering}
  结论: o.swap.Compares a b ↔ o.Compares b a
  证明: by
  cases o
  · exact Iff.rfl
  · exact eq_comm
  · exact Iff.rfl

alias ⟨Compares.of_swap, Compares.swap⟩ := compares_swap

Depends on / 依赖: Iff.rfl, eq_comm
-/
theorem compares_swap [LT α] {a b : α} {o : Ordering} : o.swap.Compares a b ↔ o.Compares b a := by
  cases o
  · exact Iff.rfl
  · exact eq_comm
  · exact Iff.rfl

alias ⟨Compares.of_swap, Compares.swap⟩ := compares_swap

/--
theorem `swap_eq_iff_eq_swap` / 定理 `swap_eq_iff_eq_swap`

English:
theorem swap_eq_iff_eq_swap
  given: {o o' : Ordering}
  statement: o.swap = o' ↔ o = o'.swap
  proof: by
  rw [← swap_inj]; rw [swap_swap]

中文:
定理 swap_eq_iff_eq_swap
  条件: {o o' : Ordering}
  结论: o.swap = o' ↔ o = o'.swap
  证明: by
  rw [← swap_inj]; rw [swap_swap]

Depends on / 依赖: swap_inj, swap_swap
-/
theorem swap_eq_iff_eq_swap {o o' : Ordering} : o.swap = o' ↔ o = o'.swap := by
  rw [← swap_inj]; rw [swap_swap]

/--
theorem `Compares.eq_lt` / 定理 `Compares.eq_lt`

English:
theorem Compares.eq_lt
  given: [Preorder α]
  statement: forall {o} {a b : α}, Compares o a b -> (o = lt ↔ a < b)

中文:
定理 Compares.eq_lt
  条件: [预序 α]
  结论: 对任意 {o} {a b : α}, Compares o a b -> (o = lt ↔ a < b)
-/
theorem Compares.eq_lt [Preorder α] : forall {o} {a b : α}, Compares o a b -> (o = lt ↔ a < b)
  | lt, _, _, h => ⟨fun _ => h, fun _ => rfl⟩
  | eq, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h' h).elim⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (lt_asymm h h').elim⟩

/--
theorem `Compares.ne_lt` / 定理 `Compares.ne_lt`

English:
theorem Compares.ne_lt
  given: [Preorder α]
  statement: forall {o} {a b : α}, Compares o a b -> (o != lt ↔ b <= a)

中文:
定理 Compares.ne_lt
  条件: [预序 α]
  结论: 对任意 {o} {a b : α}, Compares o a b -> (o != lt ↔ b <= a)
-/
theorem Compares.ne_lt [Preorder α] : forall {o} {a b : α}, Compares o a b -> (o != lt ↔ b <= a)
  | lt, _, _, h => ⟨absurd rfl, fun h' => (not_le_of_gt h h').elim⟩
  | eq, _, _, h => ⟨fun _ => ge_of_eq h, fun _ h => by injection h⟩
  | gt, _, _, h => ⟨fun _ => le_of_lt h, fun _ h => by injection h⟩

/--
theorem `Compares.eq_eq` / 定理 `Compares.eq_eq`

English:
theorem Compares.eq_eq
  given: [Preorder α]
  statement: forall {o} {a b : α}, Compares o a b -> (o = eq ↔ a = b)

中文:
定理 Compares.eq_eq
  条件: [预序 α]
  结论: 对任意 {o} {a b : α}, Compares o a b -> (o = eq ↔ a = b)
-/
theorem Compares.eq_eq [Preorder α] : forall {o} {a b : α}, Compares o a b -> (o = eq ↔ a = b)
  | lt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h h').elim⟩
  | eq, _, _, h => ⟨fun _ => h, fun _ => rfl⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_gt h h').elim⟩

/--
theorem `Compares.eq_gt` / 定理 `Compares.eq_gt`

English:
theorem Compares.eq_gt
  given: [Preorder α] {o} {a b : α} (h : Compares o a b)
  statement: o = gt ↔ b < a
  proof: swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

中文:
定理 Compares.eq_gt
  条件: [预序 α] {o} {a b : α} (h : Compares o a b)
  结论: o = gt ↔ b < a
  证明: swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

Depends on / 依赖: eq_lt, h.swap.eq_lt, swap_eq_iff_eq_swap, swap_eq_iff_eq_swap.symm.trans
-/
theorem Compares.eq_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o = gt ↔ b < a :=
  swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

/--
theorem `Compares.ne_gt` / 定理 `Compares.ne_gt`

English:
theorem Compares.ne_gt
  given: [Preorder α] {o} {a b : α} (h : Compares o a b)
  statement: o != gt ↔ a <= b
  proof: (not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt

中文:
定理 Compares.ne_gt
  条件: [预序 α] {o} {a b : α} (h : Compares o a b)
  结论: o != gt ↔ a <= b
  证明: (not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt

Depends on / 依赖: h.swap.ne_lt, ne_lt, not_congr, swap_eq_iff_eq_swap, swap_eq_iff_eq_swap.symm
-/
theorem Compares.ne_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o != gt ↔ a <= b :=
  (not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt

/--
theorem `Compares.le_total` / 定理 `Compares.le_total`

English:
theorem Compares.le_total
  given: [Preorder α] {a b : α}
  statement: forall {o}, Compares o a b -> a <= b ∨ b <= a

中文:
定理 Compares.le_total
  条件: [预序 α] {a b : α}
  结论: 对任意 {o}, Compares o a b -> a <= b ∨ b <= a
-/
theorem Compares.le_total [Preorder α] {a b : α} : forall {o}, Compares o a b -> a <= b ∨ b <= a
  | lt, h => Or.inl (le_of_lt h)
  | eq, h => Or.inl (le_of_eq h)
  | gt, h => Or.inr (le_of_lt h)

/--
theorem `Compares.le_antisymm` / 定理 `Compares.le_antisymm`

English:
theorem Compares.le_antisymm
  given: [Preorder α] {a b : α}
  statement: forall {o}, Compares o a b -> a <= b -> b <= a -> a = b

中文:
定理 Compares.le_antisymm
  条件: [预序 α] {a b : α}
  结论: 对任意 {o}, Compares o a b -> a <= b -> b <= a -> a = b
-/
theorem Compares.le_antisymm [Preorder α] {a b : α} : forall {o}, Compares o a b -> a <= b -> b <= a -> a = b
  | lt, h, _, hba => (not_le_of_gt h hba).elim
  | eq, h, _, _ => h
  | gt, h, hab, _ => (not_le_of_gt h hab).elim

/--
theorem `Compares.inj` / 定理 `Compares.inj`

English:
theorem Compares.inj
  given: [Preorder α] {o₁}

中文:
定理 Compares.inj
  条件: [预序 α] {o₁}
-/
theorem Compares.inj [Preorder α] {o₁} :
    forall {o₂} {a b : α}, Compares o₁ a b -> Compares o₂ a b -> o₁ = o₂
  | lt, _, _, h₁, h₂ => h₁.eq_lt.2 h₂
  | eq, _, _, h₁, h₂ => h₁.eq_eq.2 h₂
  | gt, _, _, h₁, h₂ => h₁.eq_gt.2 h₂

/--
theorem `compares_iff_of_compares_impl` / 定理 `compares_iff_of_compares_impl`

English:
theorem compares_iff_of_compares_impl
  statement: [LinearOrder α] [Preorder β] {a b : α} {a' b' : β}
  proof: by
  refine ⟨h, fun ho => ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · have hab : Compares Ordering.lt a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.eq a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.gt a b := hab
    rwa [ho.inj (h hab)]

中文:
定理 compares_iff_of_compares_impl
  结论: [线性序 α] [预序 β] {a b : α} {a' b' : β}
  证明: by
  refine ⟨h, fun ho => ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · have hab : Compares Ordering.lt a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.eq a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.gt a b := hab
    rwa [ho.inj (h hab)]

Depends on / 依赖: Compares, Ordering, Ordering.eq, Ordering.gt, Ordering.lt, ho.inj, lt_trichotomy
-/
theorem compares_iff_of_compares_impl [LinearOrder α] [Preorder β] {a b : α} {a' b' : β}
    (h : forall {o}, Compares o a b -> Compares o a' b') (o) : Compares o a b ↔ Compares o a' b' := by
  refine ⟨h, fun ho => ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · have hab : Compares Ordering.lt a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.eq a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.gt a b := hab
    rwa [ho.inj (h hab)]

end Ordering

open Ordering OrderDual

@[simp]
/--
theorem `toDual_compares_toDual` / 定理 `toDual_compares_toDual`

English:
theorem toDual_compares_toDual
  given: [LT α] {a b : α} {o : Ordering}
  proof: by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

@[simp]

中文:
定理 toDual_compares_toDual
  条件: [LT α] {a b : α} {o : Ordering}
  证明: by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

@[simp]

Depends on / 依赖: Iff.rfl, eq_comm, exacts
-/
theorem toDual_compares_toDual [LT α] {a b : α} {o : Ordering} :
    Compares o (toDual a) (toDual b) ↔ Compares o b a := by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

@[simp]
/--
theorem `ofDual_compares_ofDual` / 定理 `ofDual_compares_ofDual`

English:
theorem ofDual_compares_ofDual
  given: [LT α] {a b : αᵒᵈ} {o : Ordering}
  proof: by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

中文:
定理 ofDual_compares_ofDual
  条件: [LT α] {a b : αᵒᵈ} {o : Ordering}
  证明: by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

Depends on / 依赖: Iff.rfl, eq_comm, exacts
-/
theorem ofDual_compares_ofDual [LT α] {a b : αᵒᵈ} {o : Ordering} :
    Compares o (ofDual a) (ofDual b) ↔ Compares o b a := by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

/--
theorem `cmp_compares` / 定理 `cmp_compares`

English:
theorem cmp_compares
  given: [LinearOrder α] (a b : α)
  statement: (cmp a b).Compares a b
  proof: by
  obtain h | h | h := lt_trichotomy a b <;> simp [cmp, cmpUsing, h, h.not_gt]

中文:
定理 cmp_compares
  条件: [线性序 α] (a b : α)
  结论: (cmp a b).Compares a b
  证明: by
  obtain h | h | h := lt_trichotomy a b <;> simp [cmp, cmpUsing, h, h.not_gt]

Depends on / 依赖: cmpUsing, h.not_gt, lt_trichotomy, not_gt
-/
theorem cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compares a b := by
  obtain h | h | h := lt_trichotomy a b <;> simp [cmp, cmpUsing, h, h.not_gt]

/--
theorem `Ordering.Compares.cmp_eq` / 定理 `Ordering.Compares.cmp_eq`

English:
theorem Ordering.Compares.cmp_eq
  given: [LinearOrder α] {a b : α} {o : Ordering} (h : o.Compares a b)
  proof: (cmp_compares a b).inj h

@[simp]

中文:
定理 Ordering.Compares.cmp_eq
  条件: [线性序 α] {a b : α} {o : Ordering} (h : o.Compares a b)
  证明: (cmp_compares a b).inj h

@[simp]

Depends on / 依赖: cmp_compares
-/
theorem Ordering.Compares.cmp_eq [LinearOrder α] {a b : α} {o : Ordering} (h : o.Compares a b) :
    cmp a b = o :=
  (cmp_compares a b).inj h

@[simp]
/--
theorem `cmp_swap` / 定理 `cmp_swap`

English:
theorem cmp_swap
  given: [Preorder α] [DecidableLT α] (a b : α)
  statement: (cmp a b).swap = cmp b a
  proof: by
  unfold cmp cmpUsing
  by_cases h : a < b <;> by_cases h₂ : b < a <;> simp_all [lt_asymm]

@[simp]

中文:
定理 cmp_swap
  条件: [预序 α] [DecidableLT α] (a b : α)
  结论: (cmp a b).swap = cmp b a
  证明: by
  unfold cmp cmpUsing
  by_cases h : a < b <;> by_cases h₂ : b < a <;> simp_all [lt_asymm]

@[simp]

Depends on / 依赖: cmpUsing, lt_asymm
-/
theorem cmp_swap [Preorder α] [DecidableLT α] (a b : α) : (cmp a b).swap = cmp b a := by
  unfold cmp cmpUsing
  by_cases h : a < b <;> by_cases h₂ : b < a <;> simp_all [lt_asymm]

@[simp]
/--
theorem `cmpLE_toDual` / 定理 `cmpLE_toDual`

English:
theorem cmpLE_toDual
  given: [LE α] [DecidableLE α] (x y : α)
  statement: cmpLE (toDual x) (toDual y) = cmpLE y x
  proof: rfl

@[simp]

中文:
定理 cmpLE_toDual
  条件: [LE α] [DecidableLE α] (x y : α)
  结论: cmpLE (toDual x) (toDual y) = cmpLE y x
  证明: rfl

@[simp]
-/
theorem cmpLE_toDual [LE α] [DecidableLE α] (x y : α) : cmpLE (toDual x) (toDual y) = cmpLE y x :=
  rfl

@[simp]
/--
theorem `cmpLE_ofDual` / 定理 `cmpLE_ofDual`

English:
theorem cmpLE_ofDual
  given: [LE α] [DecidableLE α] (x y : αᵒᵈ)
  statement: cmpLE (ofDual x) (ofDual y) = cmpLE y x
  proof: rfl

@[simp]

中文:
定理 cmpLE_ofDual
  条件: [LE α] [DecidableLE α] (x y : αᵒᵈ)
  结论: cmpLE (ofDual x) (ofDual y) = cmpLE y x
  证明: rfl

@[simp]
-/
theorem cmpLE_ofDual [LE α] [DecidableLE α] (x y : αᵒᵈ) : cmpLE (ofDual x) (ofDual y) = cmpLE y x :=
  rfl

@[simp]
/--
theorem `cmp_toDual` / 定理 `cmp_toDual`

English:
theorem cmp_toDual
  given: [LT α] [DecidableLT α] (x y : α)
  statement: cmp (toDual x) (toDual y) = cmp y x
  proof: rfl

@[simp]

中文:
定理 cmp_toDual
  条件: [LT α] [DecidableLT α] (x y : α)
  结论: cmp (toDual x) (toDual y) = cmp y x
  证明: rfl

@[simp]
-/
theorem cmp_toDual [LT α] [DecidableLT α] (x y : α) : cmp (toDual x) (toDual y) = cmp y x :=
  rfl

@[simp]
/--
theorem `cmp_ofDual` / 定理 `cmp_ofDual`

English:
theorem cmp_ofDual
  given: [LT α] [DecidableLT α] (x y : αᵒᵈ)
  statement: cmp (ofDual x) (ofDual y) = cmp y x
  proof: rfl

中文:
定理 cmp_ofDual
  条件: [LT α] [DecidableLT α] (x y : αᵒᵈ)
  结论: cmp (ofDual x) (ofDual y) = cmp y x
  证明: rfl
-/
theorem cmp_ofDual [LT α] [DecidableLT α] (x y : αᵒᵈ) : cmp (ofDual x) (ofDual y) = cmp y x :=
  rfl

/-- Generate a linear order structure from a preorder and `cmp` function. -/
@[instance_reducible]
/--
Definition of `linearOrderOfCompares` / `linearOrderOfCompares` 的定义

English:
definition linearOrderOfCompares
  signature: [Preorder α] (cmp : α -> α -> Ordering)
  body: let H : DecidableLE α := fun a b => decidable_of_iff _ (h a b).ne_gt
  { (inferInstance : Preorder α) with
    le_antisymm := fun a b => (h a b).le_antisymm,
    le_total := fun a b => (h a b).le_total,
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := H,
    toDecidableLT := fun a b 

中文:
定义 linearOrderOfCompares
  签名: [预序 α] (cmp : α -> α -> Ordering)
  定义体: let H : DecidableLE α := fun a b => decidable_of_iff _ (h a b).ne_gt
  { (inferInstance : Preorder α) with
    le_antisymm := fun a b => (h a b).le_antisymm,
    le_total := fun a b => (h a b).le_total,
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := H,
    toDecidableLT := fun a b 

Depends on / 依赖: DecidableLE, Preorder, decidable_of_iff, eq_eq, eq_lt, le_antisymm, le_total, maxOfLe, minOfLe, ne_gt, toDecidableEq, toDecidableLE, toDecidableLT
-/
def linearOrderOfCompares [Preorder α] (cmp : α -> α -> Ordering)
    (h : forall a b, (cmp a b).Compares a b) : LinearOrder α :=
  let H : DecidableLE α := fun a b => decidable_of_iff _ (h a b).ne_gt
  { (inferInstance : Preorder α) with
    le_antisymm := fun a b => (h a b).le_antisymm,
    le_total := fun a b => (h a b).le_total,
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := H,
    toDecidableLT := fun a b => decidable_of_iff _ (h a b).eq_lt,
    toDecidableEq := fun a b => decidable_of_iff _ (h a b).eq_eq }

variable [LinearOrder α] (x y : α)

@[simp]
/--
theorem `cmp_eq_lt_iff` / 定理 `cmp_eq_lt_iff`

English:
theorem cmp_eq_lt_iff
  statement: cmp x y = Ordering.lt ↔ x < y
  proof: Ordering.Compares.eq_lt (cmp_compares x y)

@[simp]

中文:
定理 cmp_eq_lt_iff
  结论: cmp x y = Ordering.lt ↔ x < y
  证明: Ordering.Compares.eq_lt (cmp_compares x y)

@[simp]

Depends on / 依赖: Compares, Ordering, Ordering.Compares.eq_lt, cmp_compares, eq_lt
-/
theorem cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y :=
  Ordering.Compares.eq_lt (cmp_compares x y)

@[simp]
/--
theorem `cmp_eq_eq_iff` / 定理 `cmp_eq_eq_iff`

English:
theorem cmp_eq_eq_iff
  statement: cmp x y = Ordering.eq ↔ x = y
  proof: Ordering.Compares.eq_eq (cmp_compares x y)

@[simp]

中文:
定理 cmp_eq_eq_iff
  结论: cmp x y = Ordering.eq ↔ x = y
  证明: Ordering.Compares.eq_eq (cmp_compares x y)

@[simp]

Depends on / 依赖: Compares, Ordering, Ordering.Compares.eq_eq, cmp_compares, eq_eq
-/
theorem cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y :=
  Ordering.Compares.eq_eq (cmp_compares x y)

@[simp]
/--
theorem `cmp_eq_gt_iff` / 定理 `cmp_eq_gt_iff`

English:
theorem cmp_eq_gt_iff
  statement: cmp x y = Ordering.gt ↔ y < x
  proof: Ordering.Compares.eq_gt (cmp_compares x y)

@[simp]

中文:
定理 cmp_eq_gt_iff
  结论: cmp x y = Ordering.gt ↔ y < x
  证明: Ordering.Compares.eq_gt (cmp_compares x y)

@[simp]

Depends on / 依赖: Compares, Ordering, Ordering.Compares.eq_gt, cmp_compares, eq_gt
-/
theorem cmp_eq_gt_iff : cmp x y = Ordering.gt ↔ y < x :=
  Ordering.Compares.eq_gt (cmp_compares x y)

@[simp]
/--
theorem `cmp_self_eq_eq` / 定理 `cmp_self_eq_eq`

English:
theorem cmp_self_eq_eq
  statement: cmp x x = Ordering.eq
  proof: by rw [cmp_eq_eq_iff]

中文:
定理 cmp_self_eq_eq
  结论: cmp x x = Ordering.eq
  证明: by rw [cmp_eq_eq_iff]

Depends on / 依赖: cmp_eq_eq_iff
-/
theorem cmp_self_eq_eq : cmp x x = Ordering.eq := by rw [cmp_eq_eq_iff]

variable {x y} {β : Type*} [LinearOrder β] {x' y' : β}

/--
theorem `cmp_eq_cmp_symm` / 定理 `cmp_eq_cmp_symm`

English:
theorem cmp_eq_cmp_symm
  statement: cmp x y = cmp x' y' ↔ cmp y x = cmp y' x'
  proof: ⟨fun h => by rwa [← cmp_swap x', ← cmp_swap, swap_inj],
   fun h => by rwa [← cmp_swap y', ← cmp_swap, swap_inj]⟩

中文:
定理 cmp_eq_cmp_symm
  结论: cmp x y = cmp x' y' ↔ cmp y x = cmp y' x'
  证明: ⟨fun h => by rwa [← cmp_swap x', ← cmp_swap, swap_inj],
   fun h => by rwa [← cmp_swap y', ← cmp_swap, swap_inj]⟩

Depends on / 依赖: cmp_swap, swap_inj
-/
theorem cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
  ⟨fun h => by rwa [← cmp_swap x', ← cmp_swap, swap_inj],
   fun h => by rwa [← cmp_swap y', ← cmp_swap, swap_inj]⟩

/--
theorem `lt_iff_lt_of_cmp_eq_cmp` / 定理 `lt_iff_lt_of_cmp_eq_cmp`

English:
theorem lt_iff_lt_of_cmp_eq_cmp
  given: (h : cmp x y = cmp x' y')
  statement: x < y ↔ x' < y'
  proof: by
  rw [← cmp_eq_lt_iff]; rw [← cmp_eq_lt_iff]; rw [h]

中文:
定理 lt_iff_lt_of_cmp_eq_cmp
  条件: (h : cmp x y = cmp x' y')
  结论: x < y ↔ x' < y'
  证明: by
  rw [← cmp_eq_lt_iff]; rw [← cmp_eq_lt_iff]; rw [h]

Depends on / 依赖: cmp_eq_lt_iff
-/
theorem lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y' := by
  rw [← cmp_eq_lt_iff]; rw [← cmp_eq_lt_iff]; rw [h]

/--
theorem `le_iff_le_of_cmp_eq_cmp` / 定理 `le_iff_le_of_cmp_eq_cmp`

English:
theorem le_iff_le_of_cmp_eq_cmp
  given: (h : cmp x y = cmp x' y')
  statement: x <= y ↔ x' <= y'
  proof: by
  rw [← not_lt]; rw [← not_lt]
  apply not_congr
  apply lt_iff_lt_of_cmp_eq_cmp
  rwa [cmp_eq_cmp_symm]

中文:
定理 le_iff_le_of_cmp_eq_cmp
  条件: (h : cmp x y = cmp x' y')
  结论: x <= y ↔ x' <= y'
  证明: by
  rw [← not_lt]; rw [← not_lt]
  apply not_congr
  apply lt_iff_lt_of_cmp_eq_cmp
  rwa [cmp_eq_cmp_symm]

Depends on / 依赖: cmp_eq_cmp_symm, lt_iff_lt_of_cmp_eq_cmp, not_congr, not_lt
-/
theorem le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x <= y ↔ x' <= y' := by
  rw [← not_lt]; rw [← not_lt]
  apply not_congr
  apply lt_iff_lt_of_cmp_eq_cmp
  rwa [cmp_eq_cmp_symm]

/--
theorem `eq_iff_eq_of_cmp_eq_cmp` / 定理 `eq_iff_eq_of_cmp_eq_cmp`

English:
theorem eq_iff_eq_of_cmp_eq_cmp
  given: (h : cmp x y = cmp x' y')
  statement: x = y ↔ x' = y'
  proof: by
  rw [le_antisymm_iff]; rw [le_antisymm_iff]; rw [le_iff_le_of_cmp_eq_cmp h]; rw [le_iff_le_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 h)]

中文:
定理 eq_iff_eq_of_cmp_eq_cmp
  条件: (h : cmp x y = cmp x' y')
  结论: x = y ↔ x' = y'
  证明: by
  rw [le_antisymm_iff]; rw [le_antisymm_iff]; rw [le_iff_le_of_cmp_eq_cmp h]; rw [le_iff_le_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 h)]

Depends on / 依赖: cmp_eq_cmp_symm, le_antisymm_iff, le_iff_le_of_cmp_eq_cmp
-/
theorem eq_iff_eq_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x = y ↔ x' = y' := by
  rw [le_antisymm_iff]; rw [le_antisymm_iff]; rw [le_iff_le_of_cmp_eq_cmp h]; rw [le_iff_le_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 h)]

/--
theorem `LT.lt.cmp_eq_lt` / 定理 `LT.lt.cmp_eq_lt`

English:
theorem LT.lt.cmp_eq_lt
  given: (h : x < y)
  statement: cmp x y = Ordering.lt
  proof: (cmp_eq_lt_iff _ _).2 h

中文:
定理 LT.lt.cmp_eq_lt
  条件: (h : x < y)
  结论: cmp x y = Ordering.lt
  证明: (cmp_eq_lt_iff _ _).2 h

Depends on / 依赖: cmp_eq_lt_iff
-/
theorem LT.lt.cmp_eq_lt (h : x < y) : cmp x y = Ordering.lt :=
  (cmp_eq_lt_iff _ _).2 h

/--
theorem `LT.lt.cmp_eq_gt` / 定理 `LT.lt.cmp_eq_gt`

English:
theorem LT.lt.cmp_eq_gt
  given: (h : x < y)
  statement: cmp y x = Ordering.gt
  proof: (cmp_eq_gt_iff _ _).2 h

中文:
定理 LT.lt.cmp_eq_gt
  条件: (h : x < y)
  结论: cmp y x = Ordering.gt
  证明: (cmp_eq_gt_iff _ _).2 h

Depends on / 依赖: cmp_eq_gt_iff
-/
theorem LT.lt.cmp_eq_gt (h : x < y) : cmp y x = Ordering.gt :=
  (cmp_eq_gt_iff _ _).2 h

/--
theorem `Eq.cmp_eq_eq` / 定理 `Eq.cmp_eq_eq`

English:
theorem Eq.cmp_eq_eq
  given: (h : x = y)
  statement: cmp x y = Ordering.eq
  proof: (cmp_eq_eq_iff _ _).2 h

中文:
定理 相等.cmp_eq_eq
  条件: (h : x = y)
  结论: cmp x y = Ordering.eq
  证明: (cmp_eq_eq_iff _ _).2 h

Depends on / 依赖: cmp_eq_eq_iff
-/
theorem Eq.cmp_eq_eq (h : x = y) : cmp x y = Ordering.eq :=
  (cmp_eq_eq_iff _ _).2 h

/--
theorem `Eq.cmp_eq_eq'` / 定理 `Eq.cmp_eq_eq'`

English:
theorem Eq.cmp_eq_eq'
  given: (h : x = y)
  statement: cmp y x = Ordering.eq
  proof: h.symm.cmp_eq_eq

中文:
定理 相等.cmp_eq_eq'
  条件: (h : x = y)
  结论: cmp y x = Ordering.eq
  证明: h.symm.cmp_eq_eq

Depends on / 依赖: cmp_eq_eq, h.symm.cmp_eq_eq
-/
theorem Eq.cmp_eq_eq' (h : x = y) : cmp y x = Ordering.eq :=
  h.symm.cmp_eq_eq
