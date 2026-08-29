/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Ordmap.Ordnode
public import Mathlib.Tactic.Abel

/-!
# Invariants for the verification of `Ordnode`

An `Ordnode`, defined in `Mathlib/Data/Ordmap/Ordnode.lean`, is an inductive type which describes a
tree which stores the `size` at internal nodes.

In this file we define the correctness invariant of an `Ordnode`, comprising:

* `Ordnode.Sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `Ordnode.Balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `Ordnode.Bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬(b ≤ a)`. We enforce this using `Ordnode.Bounded` which includes also a global
  upper and lower bound.

This whole file is in the `Ordnode` namespace, because we first have to prove the correctness of
all the operations (and defining what correctness means here is somewhat subtle).
The actual `Ordset` operations are in `Mathlib/Data/Ordmap/Ordset.lean`.

## TODO

This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `Ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming
-/

@[expose] public section


variable {α : Type*}

namespace Ordnode



/--
theorem `not_le_delta` / 定理 `not_le_delta`

English:
theorem not_le_delta
  given: {s} (H : 1 <= s)
  statement: ¬s <= delta * 0
  proof: not_le_of_gt H

中文:
定理 not_le_delta
  条件: {s} (H : 1 <= s)
  结论: ¬s <= delta * 0
  证明: not_le_of_gt H

Depends on / 依赖: not_le_of_gt
-/
theorem not_le_delta {s} (H : 1 <= s) : ¬s <= delta * 0 :=
  not_le_of_gt H

/--
theorem `delta_lt_false` / 定理 `delta_lt_false`

English:
theorem delta_lt_false
  given: {a b : Nat} (h₁ : delta * a < b) (h₂ : delta * b < a)
  statement: False
  proof: not_le_of_gt (lt_trans (mul_lt_mul_of_pos_left h₁ <| by decide) h₂) by
    simpa [mul_assoc] using Nat.mul_le_mul_right a (by decide : 1 <= delta * delta)

中文:
定理 delta_lt_false
  条件: {a b : 自然数} (h₁ : delta * a < b) (h₂ : delta * b < a)
  结论: 假
  证明: not_le_of_gt (lt_trans (mul_lt_mul_of_pos_left h₁ <| by decide) h₂) by
    simpa [mul_assoc] using Nat.mul_le_mul_right a (by decide : 1 <= delta * delta)

Depends on / 依赖: Nat.mul_le_mul_right, lt_trans, mul_assoc, mul_le_mul_right, mul_lt_mul_of_pos_left, not_le_of_gt
-/
theorem delta_lt_false {a b : Nat} (h₁ : delta * a < b) (h₂ : delta * b < a) : False :=
not_le_of_gt (lt_trans (mul_lt_mul_of_pos_left h₁ <| by decide) h₂) by
    simpa [mul_assoc] using Nat.mul_le_mul_right a (by decide : 1 <= delta * delta)

/-! ### `singleton` -/


/-! ### `size` and `empty` -/


/--
Definition of `realSize` / `realSize` 的定义

English:
definition realSize
  signature: : Ordnode α -> Nat

中文:
定义 realSize
  签名: : Ordnode α -> 自然数
-/
def realSize : Ordnode α -> Nat
  | nil => 0
  | node _ l _ r => realSize l + realSize r + 1

/-! ### `Sized` -/


/--
Definition of `Sized` / `Sized` 的定义

English:
definition Sized
  signature: : Ordnode α -> Prop

中文:
定义 Sized
  签名: : Ordnode α -> 命题
-/
def Sized : Ordnode α -> Prop
  | nil => True
  | node s l _ r => s = size l + size r + 1 ∧ Sized l ∧ Sized r

/--
theorem `Sized.node'` / 定理 `Sized.node'`

English:
theorem Sized.node'
  given: {l x r} (hl : @Sized α l) (hr : Sized r)
  statement: Sized (node' l x r)
  proof: ⟨rfl, hl, hr⟩

中文:
定理 Sized.node'
  条件: {l x r} (hl : @Sized α l) (hr : Sized r)
  结论: Sized (node' l x r)
  证明: ⟨rfl, hl, hr⟩
-/
theorem Sized.node' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (node' l x r) :=
  ⟨rfl, hl, hr⟩

/--
theorem `Sized.eq_node'` / 定理 `Sized.eq_node'`

English:
theorem Sized.eq_node'
  given: {s l x r} (h : @Sized α (node s l x r))
  statement: node s l x r = .node' l x r
  proof: by
  rw [h.1]

中文:
定理 Sized.eq_node'
  条件: {s l x r} (h : @Sized α (node s l x r))
  结论: node s l x r = .node' l x r
  证明: by
  rw [h.1]
-/
theorem Sized.eq_node' {s l x r} (h : @Sized α (node s l x r)) : node s l x r = .node' l x r := by
  rw [h.1]

/--
theorem `Sized.size_eq` / 定理 `Sized.size_eq`

English:
theorem Sized.size_eq
  given: {s l x r} (H : Sized (@node α s l x r))
  proof: H.1

@[elab_as_elim]

中文:
定理 Sized.size_eq
  条件: {s l x r} (H : Sized (@node α s l x r))
  证明: H.1

@[elab_as_elim]
-/
theorem Sized.size_eq {s l x r} (H : Sized (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.1

@[elab_as_elim]
/--
theorem `Sized.induction` / 定理 `Sized.induction`

English:
theorem Sized.induction
  statement: {t} (hl : @Sized α t) {C : Ordnode α -> Prop} (H0 : C nil)
  proof: by
  induction t with
  | nil => exact H0
  | node _ _ _ _ t_ih_l t_ih_r =>
    rw [hl.eq_node']
    exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)

中文:
定理 Sized.induction
  结论: {t} (hl : @Sized α t) {C : Ordnode α -> 命题} (H0 : C nil)
  证明: by
  induction t with
  | nil => exact H0
  | node _ _ _ _ t_ih_l t_ih_r =>
    rw [hl.eq_node']
    exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)

Depends on / 依赖: eq_node, hl.eq_node, t_ih_l, t_ih_r
-/
theorem Sized.induction {t} (hl : @Sized α t) {C : Ordnode α -> Prop} (H0 : C nil)
    (H1 : forall l x r, C l -> C r -> C (.node' l x r)) : C t := by
  induction t with
  | nil => exact H0
  | node _ _ _ _ t_ih_l t_ih_r =>
    rw [hl.eq_node']
    exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)

/--
theorem `size_eq_realSize` / 定理 `size_eq_realSize`

English:
theorem size_eq_realSize
  statement: forall {t : Ordnode α}, Sized t -> size t = realSize t

中文:
定理 size_eq_realSize
  结论: 对任意 {t : Ordnode α}, Sized t -> size t = realSize t
-/
theorem size_eq_realSize : forall {t : Ordnode α}, Sized t -> size t = realSize t
  | nil, _ => rfl
  | node s l x r, ⟨h₁, h₂, h₃⟩ => by
    rw [size]; rw [h₁]; rw [size_eq_realSize h₂]; rw [size_eq_realSize h₃]; rfl

@[simp]
/--
theorem `Sized.size_eq_zero` / 定理 `Sized.size_eq_zero`

English:
theorem Sized.size_eq_zero
  given: {t : Ordnode α} (ht : Sized t)
  statement: size t = 0 ↔ t = nil
  proof: by
  cases t <;> [simp; simp [ht.1]]

中文:
定理 Sized.size_eq_zero
  条件: {t : Ordnode α} (ht : Sized t)
  结论: size t = 0 ↔ t = nil
  证明: by
  cases t <;> [simp; simp [ht.1]]
-/
theorem Sized.size_eq_zero {t : Ordnode α} (ht : Sized t) : size t = 0 ↔ t = nil := by
  cases t <;> [simp; simp [ht.1]]

/--
theorem `Sized.pos` / 定理 `Sized.pos`

English:
theorem Sized.pos
  given: {s l x r} (h : Sized (@node α s l x r))
  statement: 0 < s
  proof: by
  rw [h.1]; apply Nat.le_add_left

中文:
定理 Sized.pos
  条件: {s l x r} (h : Sized (@node α s l x r))
  结论: 0 < s
  证明: by
  rw [h.1]; apply Nat.le_add_left

Depends on / 依赖: Nat.le_add_left, le_add_left
-/
theorem Sized.pos {s l x r} (h : Sized (@node α s l x r)) : 0 < s := by
  rw [h.1]; apply Nat.le_add_left



/--
theorem `dual_dual` / 定理 `dual_dual`

English:
theorem dual_dual
  statement: forall t : Ordnode α, dual (dual t) = t

中文:
定理 dual_dual
  结论: 对任意 t : Ordnode α, dual (dual t) = t
-/
theorem dual_dual : forall t : Ordnode α, dual (dual t) = t
  | nil => rfl
  | node s l x r => by rw [dual, dual, dual_dual l, dual_dual r]

@[simp]
/--
theorem `size_dual` / 定理 `size_dual`

English:
theorem size_dual
  given: (t : Ordnode α)
  statement: size (dual t) = size t
  proof: by cases t <;> rfl

中文:
定理 size_dual
  条件: (t : Ordnode α)
  结论: size (dual t) = size t
  证明: by cases t <;> rfl

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis, AlgEquiv, AlgEquiv.ofBijective_apply, Algebra, Algebra.adjoin.powerBasis, Minpoly, Minpoly.toAdjoin, PowerBasis, PowerBasis.map_gen, _gen, adjoin, equivAdjoin, liftAlgHom_root, map_gen, ofBijective_apply, powerBasis, toAdjoin
-/
theorem size_dual (t : Ordnode α) : size (dual t) = size t := by cases t <;> rfl

/-! `Balanced` -/


/--
Definition of `BalancedSz` / `BalancedSz` 的定义

English:
definition BalancedSz
  signature: (l r : Nat)
  body: l + r <= 1 ∨ l <= delta * r ∧ r <= delta * l

中文:
定义 BalancedSz
  签名: (l r : 自然数)
  定义体: l + r <= 1 ∨ l <= delta * r ∧ r <= delta * l
-/
def BalancedSz (l r : Nat) : Prop :=
  l + r <= 1 ∨ l <= delta * r ∧ r <= delta * l

/--
Instance `BalancedSz.dec` / 实例 `BalancedSz.dec`

English:
instance BalancedSz.dec
  signature: : DecidableRel BalancedSz
  body: fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

中文:
实例 BalancedSz.dec
  签名: : DecidableRel BalancedSz
  定义体: fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

Depends on / 依赖: Decidable
-/
instance BalancedSz.dec : DecidableRel BalancedSz := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/--
Definition of `Balanced` / `Balanced` 的定义

English:
definition Balanced
  signature: : Ordnode α -> Prop

中文:
定义 Balanced
  签名: : Ordnode α -> 命题

Depends on / 依赖: PowerBasis, PowerBasis.ofAdjoinEqTop, ofAdjoinEqTop
-/
def Balanced : Ordnode α -> Prop
  | nil => True
  | node _ l _ r => BalancedSz (size l) (size r) ∧ Balanced l ∧ Balanced r

/--
Instance `Balanced.dec` / 实例 `Balanced.dec`

English:
instance Balanced.dec
  signature: : DecidablePred (@Balanced α)
  body: Balanced.dec l
    haveI := Balanced.dec r
inferInstanceAs Decidable (BalancedSz l.size r.size ∧ l.Balanced ∧ r.Balanced)

@[symm]

中文:
实例 Balanced.dec
  签名: : DecidablePred (@Balanced α)
  定义体: Balanced.dec l
    haveI := Balanced.dec r
inferInstanceAs Decidable (BalancedSz l.size r.size ∧ l.Balanced ∧ r.Balanced)

@[symm]

Depends on / 依赖: Balanced, Balanced.dec
-/
instance Balanced.dec : DecidablePred (@Balanced α)
| nil => inferInstanceAs Decidable True
  | node _ l _ r =>
    haveI := Balanced.dec l
    haveI := Balanced.dec r
inferInstanceAs Decidable (BalancedSz l.size r.size ∧ l.Balanced ∧ r.Balanced)

@[symm]
/--
theorem `BalancedSz.symm` / 定理 `BalancedSz.symm`

English:
theorem BalancedSz.symm
  given: {l r : Nat}
  statement: BalancedSz l r -> BalancedSz r l
  proof: Or.imp (by rw [add_comm]; exact id) And.symm

中文:
定理 BalancedSz.symm
  条件: {l r : 自然数}
  结论: BalancedSz l r -> BalancedSz r l
  证明: Or.imp (by rw [add_comm]; exact id) And.symm

Depends on / 依赖: And.symm, Or.imp, add_comm
-/
theorem BalancedSz.symm {l r : Nat} : BalancedSz l r -> BalancedSz r l :=
  Or.imp (by rw [add_comm]; exact id) And.symm

/--
theorem `balancedSz_zero` / 定理 `balancedSz_zero`

English:
theorem balancedSz_zero
  given: {l : Nat}
  statement: BalancedSz l 0 ↔ l <= 1
  proof: by
  simp +contextual [BalancedSz]

中文:
定理 balancedSz_zero
  条件: {l : 自然数}
  结论: BalancedSz l 0 ↔ l <= 1
  证明: by
  simp +contextual [BalancedSz]

Depends on / 依赖: BalancedSz, contextual
-/
theorem balancedSz_zero {l : Nat} : BalancedSz l 0 ↔ l <= 1 := by
  simp +contextual [BalancedSz]

/--
theorem `balancedSz_up` / 定理 `balancedSz_up`

English:
theorem balancedSz_up
  statement: {l r₁ r₂ : Nat} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ r₂ <= delta * l)
  proof: by
  refine or_iff_not_imp_left.2 fun h => ?_
  refine ⟨?_, h₂.resolve_left h⟩
  cases H with
  | inl H =>
    cases r₂
    · cases h (le_trans (Nat.add_le_add_left (Nat.zero_le _) _) H)
    · exact le_trans (le_trans (Nat.le_add_right _ _) H) (Nat.le_add_left 1 _)
  | inr H =>
    exact le_trans H.

中文:
定理 balancedSz_up
  结论: {l r₁ r₂ : 自然数} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ r₂ <= delta * l)
  证明: by
  refine or_iff_not_imp_left.2 fun h => ?_
  refine ⟨?_, h₂.resolve_left h⟩
  cases H with
  | inl H =>
    cases r₂
    · cases h (le_trans (Nat.add_le_add_left (Nat.zero_le _) _) H)
    · exact le_trans (le_trans (Nat.le_add_right _ _) H) (Nat.le_add_left 1 _)
  | inr H =>
    exact le_trans H.

Depends on / 依赖: Nat.add_le_add_left, Nat.le_add_left, Nat.le_add_right, Nat.mul_le_mul_left, Nat.zero_le, add_le_add_left, le_add_left, le_add_right, le_trans, mul_le_mul_left, or_iff_not_imp_left, resolve_left, zero_le
-/
theorem balancedSz_up {l r₁ r₂ : Nat} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ r₂ <= delta * l)
    (H : BalancedSz l r₁) : BalancedSz l r₂ := by
  refine or_iff_not_imp_left.2 fun h => ?_
  refine ⟨?_, h₂.resolve_left h⟩
  cases H with
  | inl H =>
    cases r₂
    · cases h (le_trans (Nat.add_le_add_left (Nat.zero_le _) _) H)
    · exact le_trans (le_trans (Nat.le_add_right _ _) H) (Nat.le_add_left 1 _)
  | inr H =>
    exact le_trans H.1 (Nat.mul_le_mul_left _ h₁)

/--
theorem `balancedSz_down` / 定理 `balancedSz_down`

English:
theorem balancedSz_down
  statement: {l r₁ r₂ : Nat} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ l <= delta * r₁)
  proof: have : l + r₂ <= 1 -> BalancedSz l r₁ := fun H => Or.inl (le_trans (Nat.add_le_add_left h₁ _) H)
  Or.casesOn H this fun H => Or.casesOn h₂ this fun h₂ => Or.inr ⟨h₂, le_trans h₁ H.2⟩

中文:
定理 balancedSz_down
  结论: {l r₁ r₂ : 自然数} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ l <= delta * r₁)
  证明: have : l + r₂ <= 1 -> BalancedSz l r₁ := fun H => Or.inl (le_trans (Nat.add_le_add_left h₁ _) H)
  Or.casesOn H this fun H => Or.casesOn h₂ this fun h₂ => Or.inr ⟨h₂, le_trans h₁ H.2⟩

Depends on / 依赖: BalancedSz, Nat.add_le_add_left, Or.casesOn, Or.inl, Or.inr, add_le_add_left, casesOn, le_trans
-/
theorem balancedSz_down {l r₁ r₂ : Nat} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ l <= delta * r₁)
    (H : BalancedSz l r₂) : BalancedSz l r₁ :=
  have : l + r₂ <= 1 -> BalancedSz l r₁ := fun H => Or.inl (le_trans (Nat.add_le_add_left h₁ _) H)
  Or.casesOn H this fun H => Or.casesOn h₂ this fun h₂ => Or.inr ⟨h₂, le_trans h₁ H.2⟩

/--
theorem `Balanced.dual` / 定理 `Balanced.dual`

English:
theorem Balanced.dual
  statement: forall {t : Ordnode α}, Balanced t -> Balanced (dual t)

中文:
定理 Balanced.dual
  结论: 对任意 {t : Ordnode α}, Balanced t -> Balanced (dual t)
-/
theorem Balanced.dual : forall {t : Ordnode α}, Balanced t -> Balanced (dual t)
  | nil, _ => ⟨⟩
  | node _ l _ r, ⟨b, bl, br⟩ => ⟨by rw [size_dual, size_dual]; exact b.symm, br.dual, bl.dual⟩

/-! ### `rotate` and `balance` -/


/--
Definition of `node3L` / `node3L` 的定义

English:
definition node3L
  signature: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  body: node' (node' l x m) y r

中文:
定义 node3L
  签名: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  定义体: node' (node' l x m) y r
-/
def node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' (node' l x m) y r

/--
Definition of `node3R` / `node3R` 的定义

English:
definition node3R
  signature: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  body: node' l x (node' m y r)

中文:
定义 node3R
  签名: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  定义体: node' l x (node' m y r)
-/
def node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' l x (node' m y r)

/--
Definition of `node4L` / `node4L` 的定义

English:
definition node4L
  signature: : Ordnode α -> α -> Ordnode α -> α -> Ordnode α -> Ordnode α

中文:
定义 node4L
  签名: : Ordnode α -> α -> Ordnode α -> α -> Ordnode α -> Ordnode α
-/
def node4L : Ordnode α -> α -> Ordnode α -> α -> Ordnode α -> Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3L l x nil z r

-- should not happen
/--
Definition of `node4R` / `node4R` 的定义

English:
definition node4R
  signature: : Ordnode α -> α -> Ordnode α -> α -> Ordnode α -> Ordnode α

中文:
定义 node4R
  签名: : Ordnode α -> α -> Ordnode α -> α -> Ordnode α -> Ordnode α
-/
def node4R : Ordnode α -> α -> Ordnode α -> α -> Ordnode α -> Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3R l x nil z r

-- should not happen
/--
Definition of `rotateL` / `rotateL` 的定义

English:
definition rotateL
  signature: : Ordnode α -> α -> Ordnode α -> Ordnode α

中文:
定义 rotateL
  签名: : Ordnode α -> α -> Ordnode α -> Ordnode α
-/
def rotateL : Ordnode α -> α -> Ordnode α -> Ordnode α
  | l, x, node _ m y r => if size m < ratio * size r then node3L l x m y r else node4L l x m y r
  | l, x, nil => node' l x nil

/--
theorem `rotateL_node` / 定理 `rotateL_node`

English:
theorem rotateL_node
  given: (l : Ordnode α) (x : α) (sz : Nat) (m : Ordnode α) (y : α) (r : Ordnode α)
  proof: rfl

中文:
定理 rotateL_node
  条件: (l : Ordnode α) (x : α) (sz : 自然数) (m : Ordnode α) (y : α) (r : Ordnode α)
  证明: rfl
-/
theorem rotateL_node (l : Ordnode α) (x : α) (sz : Nat) (m : Ordnode α) (y : α) (r : Ordnode α) :
    rotateL l x (node sz m y r) =
      if size m < ratio * size r then node3L l x m y r else node4L l x m y r :=
  rfl

/--
theorem `rotateL_nil` / 定理 `rotateL_nil`

English:
theorem rotateL_nil
  given: (l : Ordnode α) (x : α)
  statement: rotateL l x nil = node' l x nil
  proof: rfl

中文:
定理 rotateL_nil
  条件: (l : Ordnode α) (x : α)
  结论: rotateL l x nil = node' l x nil
  证明: rfl
-/
theorem rotateL_nil (l : Ordnode α) (x : α) : rotateL l x nil = node' l x nil :=
  rfl

-- should not happen
/--
Definition of `rotateR` / `rotateR` 的定义

English:
definition rotateR
  signature: : Ordnode α -> α -> Ordnode α -> Ordnode α

中文:
定义 rotateR
  签名: : Ordnode α -> α -> Ordnode α -> Ordnode α
-/
def rotateR : Ordnode α -> α -> Ordnode α -> Ordnode α
  | node _ l x m, y, r => if size m < ratio * size l then node3R l x m y r else node4R l x m y r
  | nil, y, r => node' nil y r

/--
theorem `rotateR_node` / 定理 `rotateR_node`

English:
theorem rotateR_node
  given: (sz : Nat) (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  proof: rfl

中文:
定理 rotateR_node
  条件: (sz : 自然数) (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  证明: rfl
-/
theorem rotateR_node (sz : Nat) (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    rotateR (node sz l x m) y r =
      if size m < ratio * size l then node3R l x m y r else node4R l x m y r :=
  rfl

/--
theorem `rotateR_nil` / 定理 `rotateR_nil`

English:
theorem rotateR_nil
  given: (y : α) (r : Ordnode α)
  statement: rotateR nil y r = node' nil y r
  proof: rfl

中文:
定理 rotateR_nil
  条件: (y : α) (r : Ordnode α)
  结论: rotateR nil y r = node' nil y r
  证明: rfl
-/
theorem rotateR_nil (y : α) (r : Ordnode α) : rotateR nil y r = node' nil y r :=
  rfl

-- should not happen
/--
Definition of `balanceL'` / `balanceL'` 的定义

English:
definition balanceL'
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: if size l + size r <= 1 then node' l x r
  else if size l > delta * size r then rotateR l x r else node' l x r

中文:
定义 balanceL'
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: if size l + size r <= 1 then node' l x r
  else if size l > delta * size r then rotateR l x r else node' l x r

Depends on / 依赖: rotateR
-/
def balanceL' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r <= 1 then node' l x r
  else if size l > delta * size r then rotateR l x r else node' l x r

/--
Definition of `balanceR'` / `balanceR'` 的定义

English:
definition balanceR'
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: if size l + size r <= 1 then node' l x r
  else if size r > delta * size l then rotateL l x r else node' l x r

中文:
定义 balanceR'
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: if size l + size r <= 1 then node' l x r
  else if size r > delta * size l then rotateL l x r else node' l x r

Depends on / 依赖: rotateL
-/
def balanceR' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r <= 1 then node' l x r
  else if size r > delta * size l then rotateL l x r else node' l x r

/--
Definition of `balance'` / `balance'` 的定义

English:
definition balance'
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: if size l + size r <= 1 then node' l x r
  else
    if size r > delta * size l then rotateL l x r
    else if size l > delta * size r then rotateR l x r else node' l x r

中文:
定义 balance'
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: if size l + size r <= 1 then node' l x r
  else
    if size r > delta * size l then rotateL l x r
    else if size l > delta * size r then rotateR l x r else node' l x r

Depends on / 依赖: rotateL, rotateR
-/
def balance' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r <= 1 then node' l x r
  else
    if size r > delta * size l then rotateL l x r
    else if size l > delta * size r then rotateR l x r else node' l x r

/--
theorem `dual_node'` / 定理 `dual_node'`

English:
theorem dual_node'
  given: (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: by simp [node', add_comm]

中文:
定理 dual_node'
  条件: (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: by simp [node', add_comm]

Depends on / 依赖: add_comm
-/
theorem dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (node' l x r) = node' (dual r) x (dual l) := by simp [node', add_comm]

/--
theorem `dual_node3L` / 定理 `dual_node3L`

English:
theorem dual_node3L
  given: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  proof: by
  simp [node3L, node3R, add_comm]

中文:
定理 dual_node3L
  条件: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  证明: by
  simp [node3L, node3R, add_comm]

Depends on / 依赖: add_comm, node3L, node3R
-/
theorem dual_node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3L l x m y r) = node3R (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, add_comm]

/--
theorem `dual_node3R` / 定理 `dual_node3R`

English:
theorem dual_node3R
  given: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  proof: by
  simp [node3L, node3R, add_comm]

中文:
定理 dual_node3R
  条件: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  证明: by
  simp [node3L, node3R, add_comm]

Depends on / 依赖: add_comm, node3L, node3R
-/
theorem dual_node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3R l x m y r) = node3L (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, add_comm]

/--
theorem `dual_node4L` / 定理 `dual_node4L`

English:
theorem dual_node4L
  given: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  proof: by
  cases m <;> simp [node4L, node4R, node3R, dual_node3L, add_comm]

中文:
定理 dual_node4L
  条件: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  证明: by
  cases m <;> simp [node4L, node4R, node3R, dual_node3L, add_comm]

Depends on / 依赖: add_comm, dual_node3L, node3R, node4L, node4R
-/
theorem dual_node4L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4L l x m y r) = node4R (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3R, dual_node3L, add_comm]

/--
theorem `dual_node4R` / 定理 `dual_node4R`

English:
theorem dual_node4R
  given: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  proof: by
  cases m <;> simp [node4L, node4R, node3L, dual_node3R, add_comm]

中文:
定理 dual_node4R
  条件: (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α)
  证明: by
  cases m <;> simp [node4L, node4R, node3L, dual_node3R, add_comm]

Depends on / 依赖: add_comm, dual_node3R, node3L, node4L, node4R
-/
theorem dual_node4R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4R l x m y r) = node4L (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3L, dual_node3R, add_comm]

/--
theorem `dual_rotateL` / 定理 `dual_rotateL`

English:
theorem dual_rotateL
  given: (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: by
  cases r <;> simp [rotateL, rotateR]; split_ifs <;>
    simp [dual_node3L, dual_node4L, node3R]

中文:
定理 dual_rotateL
  条件: (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: by
  cases r <;> simp [rotateL, rotateR]; split_ifs <;>
    simp [dual_node3L, dual_node4L, node3R]

Depends on / 依赖: dual_node3L, dual_node4L, node3R, rotateL, rotateR, split_ifs
-/
theorem dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateL l x r) = rotateR (dual r) x (dual l) := by
  cases r <;> simp [rotateL, rotateR]; split_ifs <;>
    simp [dual_node3L, dual_node4L, node3R]

/--
theorem `dual_rotateR` / 定理 `dual_rotateR`

English:
theorem dual_rotateR
  given: (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: by
  rw [← dual_dual (rotateL _ _ _)]; rw [dual_rotateL]; rw [dual_dual]; rw [dual_dual]

中文:
定理 dual_rotateR
  条件: (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: by
  rw [← dual_dual (rotateL _ _ _)]; rw [dual_rotateL]; rw [dual_dual]; rw [dual_dual]

Depends on / 依赖: dual_dual, dual_rotateL, rotateL
-/
theorem dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateR l x r) = rotateL (dual r) x (dual l) := by
  rw [← dual_dual (rotateL _ _ _)]; rw [dual_rotateL]; rw [dual_dual]; rw [dual_dual]

/--
theorem `dual_balance'` / 定理 `dual_balance'`

English:
theorem dual_balance'
  given: (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: by
  simp [balance', add_comm]; split_ifs with h h_1 h_2 <;>
    simp [dual_rotateL, dual_rotateR, add_comm]
  cases delta_lt_false h_1 h_2

中文:
定理 dual_balance'
  条件: (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: by
  simp [balance', add_comm]; split_ifs with h h_1 h_2 <;>
    simp [dual_rotateL, dual_rotateR, add_comm]
  cases delta_lt_false h_1 h_2

Depends on / 依赖: add_comm, balance, delta_lt_false, dual_rotateL, dual_rotateR, split_ifs
-/
theorem dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balance' l x r) = balance' (dual r) x (dual l) := by
  simp [balance', add_comm]; split_ifs with h h_1 h_2 <;>
    simp [dual_rotateL, dual_rotateR, add_comm]
  cases delta_lt_false h_1 h_2

/--
theorem `dual_balanceL` / 定理 `dual_balanceL`

English:
theorem dual_balanceL
  given: (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: by
  unfold balanceL balanceR
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
      dsimp only [dual, id] <;> try rfl
    split_ifs with h <;> repeat simp [add_comm]
  · obtain - | 

中文:
定理 dual_balanceL
  条件: (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: by
  unfold balanceL balanceR
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
      dsimp only [dual, id] <;> try rfl
    split_ifs with h <;> repeat simp [add_comm]
  · obtain - | 

Depends on / 依赖: add_comm, balanceL, balanceR, repeat, split_ifs
-/
theorem dual_balanceL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceL l x r) = balanceR (dual r) x (dual l) := by
  unfold balanceL balanceR
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
      dsimp only [dual, id] <;> try rfl
    split_ifs with h <;> repeat simp [add_comm]
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    dsimp only [dual, id]
    split_ifs; swap; · simp [add_comm]
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;> try rfl
    dsimp only [dual, id]
    split_ifs with h <;> simp [add_comm]

/--
theorem `dual_balanceR` / 定理 `dual_balanceR`

English:
theorem dual_balanceR
  given: (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: by
  rw [← dual_dual (balanceL _ _ _)]; rw [dual_balanceL]; rw [dual_dual]; rw [dual_dual]

中文:
定理 dual_balanceR
  条件: (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: by
  rw [← dual_dual (balanceL _ _ _)]; rw [dual_balanceL]; rw [dual_dual]; rw [dual_dual]

Depends on / 依赖: balanceL, dual_balanceL, dual_dual
-/
theorem dual_balanceR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceR l x r) = balanceL (dual r) x (dual l) := by
  rw [← dual_dual (balanceL _ _ _)]; rw [dual_balanceL]; rw [dual_dual]; rw [dual_dual]

/--
theorem `Sized.node3L` / 定理 `Sized.node3L`

English:
theorem Sized.node3L
  given: {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r)
  proof: (hl.node' hm).node' hr

中文:
定理 Sized.node3L
  条件: {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r)
  证明: (hl.node' hm).node' hr

Depends on / 依赖: hl.node
-/
theorem Sized.node3L {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node3L l x m y r) :=
  (hl.node' hm).node' hr

/--
theorem `Sized.node3R` / 定理 `Sized.node3R`

English:
theorem Sized.node3R
  given: {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r)
  proof: hl.node' (hm.node' hr)

中文:
定理 Sized.node3R
  条件: {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r)
  证明: hl.node' (hm.node' hr)

Depends on / 依赖: hl.node, hm.node
-/
theorem Sized.node3R {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node3R l x m y r) :=
  hl.node' (hm.node' hr)

/--
theorem `Sized.node4L` / 定理 `Sized.node4L`

English:
theorem Sized.node4L
  given: {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r)
  proof: by
  cases m <;> [exact (hl.node' hm).node' hr; exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

中文:
定理 Sized.node4L
  条件: {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r)
  证明: by
  cases m <;> [exact (hl.node' hm).node' hr; exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

Depends on / 依赖: hl.node
-/
theorem Sized.node4L {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node4L l x m y r) := by
  cases m <;> [exact (hl.node' hm).node' hr; exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

/--
theorem `node3L_size` / 定理 `node3L_size`

English:
theorem node3L_size
  given: {l x m y r}
  statement: size (@node3L α l x m y r) = size l + size m + size r + 2
  proof: by
  dsimp [node3L, node', size]; rw [add_right_comm _ 1]

中文:
定理 node3L_size
  条件: {l x m y r}
  结论: size (@node3L α l x m y r) = size l + size m + size r + 2
  证明: by
  dsimp [node3L, node', size]; rw [add_right_comm _ 1]

Depends on / 依赖: add_right_comm, node3L
-/
theorem node3L_size {l x m y r} : size (@node3L α l x m y r) = size l + size m + size r + 2 := by
  dsimp [node3L, node', size]; rw [add_right_comm _ 1]

/--
theorem `node3R_size` / 定理 `node3R_size`

English:
theorem node3R_size
  given: {l x m y r}
  statement: size (@node3R α l x m y r) = size l + size m + size r + 2
  proof: by
  dsimp [node3R, node', size]; rw [← add_assoc, ← add_assoc]

中文:
定理 node3R_size
  条件: {l x m y r}
  结论: size (@node3R α l x m y r) = size l + size m + size r + 2
  证明: by
  dsimp [node3R, node', size]; rw [← add_assoc, ← add_assoc]

Depends on / 依赖: add_assoc, node3R
-/
theorem node3R_size {l x m y r} : size (@node3R α l x m y r) = size l + size m + size r + 2 := by
  dsimp [node3R, node', size]; rw [← add_assoc, ← add_assoc]

/--
theorem `node4L_size` / 定理 `node4L_size`

English:
theorem node4L_size
  given: {l x m y r} (hm : Sized m)
  proof: by
  cases m
  · simp [node4L, node3L, node']
    abel
  · simp [node4L, node', size, hm.1]; abel

中文:
定理 node4L_size
  条件: {l x m y r} (hm : Sized m)
  证明: by
  cases m
  · simp [node4L, node3L, node']
    abel
  · simp [node4L, node', size, hm.1]; abel

Depends on / 依赖: node3L, node4L
-/
theorem node4L_size {l x m y r} (hm : Sized m) :
    size (@node4L α l x m y r) = size l + size m + size r + 2 := by
  cases m
  · simp [node4L, node3L, node']
    abel
  · simp [node4L, node', size, hm.1]; abel

/--
theorem `Sized.dual` / 定理 `Sized.dual`

English:
theorem Sized.dual
  statement: forall {t : Ordnode α}, Sized t -> Sized (dual t)

中文:
定理 Sized.dual
  结论: 对任意 {t : Ordnode α}, Sized t -> Sized (dual t)
-/
theorem Sized.dual : forall {t : Ordnode α}, Sized t -> Sized (dual t)
  | nil, _ => ⟨⟩
  | node _ l _ r, ⟨rfl, sl, sr⟩ => ⟨by simp [size_dual, add_comm], Sized.dual sr, Sized.dual sl⟩

/--
theorem `Sized.dual_iff` / 定理 `Sized.dual_iff`

English:
theorem Sized.dual_iff
  given: {t : Ordnode α}
  statement: Sized (.dual t) ↔ Sized t
  proof: ⟨fun h => by rw [← dual_dual t]; exact h.dual, Sized.dual⟩

中文:
定理 Sized.dual_iff
  条件: {t : Ordnode α}
  结论: Sized (.dual t) ↔ Sized t
  证明: ⟨fun h => by rw [← dual_dual t]; exact h.dual, Sized.dual⟩

Depends on / 依赖: Sized.dual, dual_dual, h.dual
-/
theorem Sized.dual_iff {t : Ordnode α} : Sized (.dual t) ↔ Sized t :=
  ⟨fun h => by rw [← dual_dual t]; exact h.dual, Sized.dual⟩

/--
theorem `Sized.rotateL` / 定理 `Sized.rotateL`

English:
theorem Sized.rotateL
  given: {l x r} (hl : @Sized α l) (hr : Sized r)
  statement: Sized (rotateL l x r)
  proof: by
  cases r; · exact hl.node' hr
  rw [Ordnode.rotateL_node]; split_ifs
  · exact hl.node3L hr.2.1 hr.2.2
  · exact hl.node4L hr.2.1 hr.2.2

中文:
定理 Sized.rotateL
  条件: {l x r} (hl : @Sized α l) (hr : Sized r)
  结论: Sized (rotateL l x r)
  证明: by
  cases r; · exact hl.node' hr
  rw [Ordnode.rotateL_node]; split_ifs
  · exact hl.node3L hr.2.1 hr.2.2
  · exact hl.node4L hr.2.1 hr.2.2

Depends on / 依赖: Ordnode, Ordnode.rotateL_node, hl.node, hl.node3L, hl.node4L, node3L, node4L, rotateL_node, split_ifs
-/
theorem Sized.rotateL {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateL l x r) := by
  cases r; · exact hl.node' hr
  rw [Ordnode.rotateL_node]; split_ifs
  · exact hl.node3L hr.2.1 hr.2.2
  · exact hl.node4L hr.2.1 hr.2.2

/--
theorem `Sized.rotateR` / 定理 `Sized.rotateR`

English:
theorem Sized.rotateR
  given: {l x r} (hl : @Sized α l) (hr : Sized r)
  statement: Sized (rotateR l x r)
  proof: Sized.dual_iff.1 by rw [dual_rotateR]; exact hr.dual.rotateL hl.dual

中文:
定理 Sized.rotateR
  条件: {l x r} (hl : @Sized α l) (hr : Sized r)
  结论: Sized (rotateR l x r)
  证明: Sized.dual_iff.1 by rw [dual_rotateR]; exact hr.dual.rotateL hl.dual

Depends on / 依赖: Sized.dual_iff, dual_iff, dual_rotateR, hl.dual, hr.dual.rotateL, rotateL
-/
theorem Sized.rotateR {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateR l x r) :=
Sized.dual_iff.1 by rw [dual_rotateR]; exact hr.dual.rotateL hl.dual

/--
theorem `Sized.rotateL_size` / 定理 `Sized.rotateL_size`

English:
theorem Sized.rotateL_size
  given: {l x r} (hm : Sized r)
  proof: by
  cases r <;> simp [Ordnode.rotateL]
  simp only [hm.1]
  split_ifs <;> simp [node3L_size, node4L_size hm.2.1] <;> abel

中文:
定理 Sized.rotateL_size
  条件: {l x r} (hm : Sized r)
  证明: by
  cases r <;> simp [Ordnode.rotateL]
  simp only [hm.1]
  split_ifs <;> simp [node3L_size, node4L_size hm.2.1] <;> abel

Depends on / 依赖: Ordnode, Ordnode.rotateL, node3L_size, node4L_size, rotateL, split_ifs
-/
theorem Sized.rotateL_size {l x r} (hm : Sized r) :
    size (@Ordnode.rotateL α l x r) = size l + size r + 1 := by
  cases r <;> simp [Ordnode.rotateL]
  simp only [hm.1]
  split_ifs <;> simp [node3L_size, node4L_size hm.2.1] <;> abel

/--
theorem `Sized.rotateR_size` / 定理 `Sized.rotateR_size`

English:
theorem Sized.rotateR_size
  given: {l x r} (hl : Sized l)
  proof: by
  rw [← size_dual]; rw [dual_rotateR]; rw [hl.dual.rotateL_size]; rw [size_dual]; rw [size_dual]; rw [add_comm (size l)]

中文:
定理 Sized.rotateR_size
  条件: {l x r} (hl : Sized l)
  证明: by
  rw [← size_dual]; rw [dual_rotateR]; rw [hl.dual.rotateL_size]; rw [size_dual]; rw [size_dual]; rw [add_comm (size l)]

Depends on / 依赖: add_comm, dual_rotateR, hl.dual.rotateL_size, rotateL_size, size_dual
-/
theorem Sized.rotateR_size {l x r} (hl : Sized l) :
    size (@Ordnode.rotateR α l x r) = size l + size r + 1 := by
  rw [← size_dual]; rw [dual_rotateR]; rw [hl.dual.rotateL_size]; rw [size_dual]; rw [size_dual]; rw [add_comm (size l)]

/--
theorem `Sized.balance'` / 定理 `Sized.balance'`

English:
theorem Sized.balance'
  given: {l x r} (hl : @Sized α l) (hr : Sized r)
  statement: Sized (balance' l x r)
  proof: by
  unfold Ordnode.balance'; split_ifs
  · exact hl.node' hr
  · exact hl.rotateL hr
  · exact hl.rotateR hr
  · exact hl.node' hr

中文:
定理 Sized.balance'
  条件: {l x r} (hl : @Sized α l) (hr : Sized r)
  结论: Sized (balance' l x r)
  证明: by
  unfold Ordnode.balance'; split_ifs
  · exact hl.node' hr
  · exact hl.rotateL hr
  · exact hl.rotateR hr
  · exact hl.node' hr

Depends on / 依赖: Ordnode, Ordnode.balance, balance, hl.node, hl.rotateL, hl.rotateR, rotateL, rotateR, split_ifs
-/
theorem Sized.balance' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (balance' l x r) := by
  unfold Ordnode.balance'; split_ifs
  · exact hl.node' hr
  · exact hl.rotateL hr
  · exact hl.rotateR hr
  · exact hl.node' hr

/--
theorem `size_balance'` / 定理 `size_balance'`

English:
theorem size_balance'
  given: {l x r} (hl : @Sized α l) (hr : Sized r)
  proof: by
  unfold balance'; split_ifs
  · rfl
  · exact hr.rotateL_size
  · exact hl.rotateR_size
  · rfl

中文:
定理 size_balance'
  条件: {l x r} (hl : @Sized α l) (hr : Sized r)
  证明: by
  unfold balance'; split_ifs
  · rfl
  · exact hr.rotateL_size
  · exact hl.rotateR_size
  · rfl

Depends on / 依赖: balance, hl.rotateR_size, hr.rotateL_size, rotateL_size, rotateR_size, split_ifs
-/
theorem size_balance' {l x r} (hl : @Sized α l) (hr : Sized r) :
    size (@balance' α l x r) = size l + size r + 1 := by
  unfold balance'; split_ifs
  · rfl
  · exact hr.rotateL_size
  · exact hl.rotateR_size
  · rfl



/--
theorem `All.imp` / 定理 `All.imp`

English:
theorem All.imp
  given: {P Q : α -> Prop} (H : forall a, P a -> Q a)
  statement: forall {t}, All P t -> All Q t

中文:
定理 All.imp
  条件: {P Q : α -> 命题} (H : 对任意 a, P a -> Q a)
  结论: 对任意 {t}, All P t -> All Q t
-/
theorem All.imp {P Q : α -> Prop} (H : forall a, P a -> Q a) : forall {t}, All P t -> All Q t
  | nil, _ => ⟨⟩
  | node _ _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨h₁.imp H, H _ h₂, h₃.imp H⟩

/--
theorem `Any.imp` / 定理 `Any.imp`

English:
theorem Any.imp
  given: {P Q : α -> Prop} (H : forall a, P a -> Q a)
  statement: forall {t}, Any P t -> Any Q t

中文:
定理 Any.imp
  条件: {P Q : α -> 命题} (H : 对任意 a, P a -> Q a)
  结论: 对任意 {t}, Any P t -> Any Q t
-/
theorem Any.imp {P Q : α -> Prop} (H : forall a, P a -> Q a) : forall {t}, Any P t -> Any Q t
  | nil => id
| node _ _ _ _ => Or.imp (Any.imp H) Or.imp (H _) (Any.imp H)

/--
theorem `all_singleton` / 定理 `all_singleton`

English:
theorem all_singleton
  given: {P : α -> Prop} {x : α}
  statement: All P (singleton x) ↔ P x
  proof: ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩

中文:
定理 all_singleton
  条件: {P : α -> 命题} {x : α}
  结论: All P (singleton x) ↔ P x
  证明: ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩
-/
theorem all_singleton {P : α -> Prop} {x : α} : All P (singleton x) ↔ P x :=
  ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩

/--
theorem `any_singleton` / 定理 `any_singleton`

English:
theorem any_singleton
  given: {P : α -> Prop} {x : α}
  statement: Any P (singleton x) ↔ P x
  proof: ⟨by rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩); exact h, fun h => Or.inr (Or.inl h)⟩

中文:
定理 any_singleton
  条件: {P : α -> 命题} {x : α}
  结论: Any P (singleton x) ↔ P x
  证明: ⟨by rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩); exact h, fun h => Or.inr (Or.inl h)⟩

Depends on / 依赖: Or.inl, Or.inr
-/
theorem any_singleton {P : α -> Prop} {x : α} : Any P (singleton x) ↔ P x :=
  ⟨by rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩); exact h, fun h => Or.inr (Or.inl h)⟩

/--
theorem `all_dual` / 定理 `all_dual`

English:
theorem all_dual
  given: {P : α -> Prop}
  statement: forall {t : Ordnode α}, All P (dual t) ↔ All P t

中文:
定理 all_dual
  条件: {P : α -> 命题}
  结论: 对任意 {t : Ordnode α}, All P (dual t) ↔ All P t
-/
theorem all_dual {P : α -> Prop} : forall {t : Ordnode α}, All P (dual t) ↔ All P t
  | nil => Iff.rfl
  | node _ _l _x _r =>
    ⟨fun ⟨hr, hx, hl⟩ => ⟨all_dual.1 hl, hx, all_dual.1 hr⟩, fun ⟨hl, hx, hr⟩ =>
      ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩

/--
theorem `all_iff_forall` / 定理 `all_iff_forall`

English:
theorem all_iff_forall
  given: {P : α -> Prop}
  statement: forall {t}, All P t ↔ forall x, Emem x t -> P x

中文:
定理 all_iff_对任意
  条件: {P : α -> 命题}
  结论: 对任意 {t}, All P t ↔ 对任意 x, Emem x t -> P x
-/
theorem all_iff_forall {P : α -> Prop} : forall {t}, All P t ↔ forall x, Emem x t -> P x
  | nil => (iff_true_intro <| by rintro _ ⟨⟩).symm
  | node _ l x r => by simp [All, Emem, all_iff_forall, Any, or_imp, forall_and]

/--
theorem `any_iff_exists` / 定理 `any_iff_exists`

English:
theorem any_iff_exists
  given: {P : α -> Prop}
  statement: forall {t}, Any P t ↔ exists x, Emem x t ∧ P x

中文:
定理 any_iff_存在
  条件: {P : α -> 命题}
  结论: 对任意 {t}, Any P t ↔ 存在 x, Emem x t ∧ P x
-/
theorem any_iff_exists {P : α -> Prop} : forall {t}, Any P t ↔ exists x, Emem x t ∧ P x
  | nil => ⟨by rintro ⟨⟩, by rintro ⟨_, ⟨⟩, _⟩⟩
  | node _ l x r => by simp only [Emem]; simp [Any, any_iff_exists, or_and_right, exists_or]

/--
theorem `emem_iff_all` / 定理 `emem_iff_all`

English:
theorem emem_iff_all
  given: {x : α} {t}
  statement: Emem x t ↔ forall P, All P t -> P x
  proof: ⟨fun h _ al => all_iff_forall.1 al _ h, fun H => H _ all_iff_forall.2 fun _ => id⟩

中文:
定理 emem_iff_all
  条件: {x : α} {t}
  结论: Emem x t ↔ 对任意 P, All P t -> P x
  证明: ⟨fun h _ al => all_iff_forall.1 al _ h, fun H => H _ all_iff_forall.2 fun _ => id⟩

Depends on / 依赖: all_iff_forall
-/
theorem emem_iff_all {x : α} {t} : Emem x t ↔ forall P, All P t -> P x :=
⟨fun h _ al => all_iff_forall.1 al _ h, fun H => H _ all_iff_forall.2 fun _ => id⟩

/--
theorem `all_node'` / 定理 `all_node'`

English:
theorem all_node'
  given: {P l x r}
  statement: @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r
  proof: Iff.rfl

中文:
定理 all_node'
  条件: {P l x r}
  结论: @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem all_node' {P l x r} : @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r :=
  Iff.rfl

/--
theorem `all_node3L` / 定理 `all_node3L`

English:
theorem all_node3L
  given: {P l x m y r}
  proof: by
  simp [node3L, all_node', and_assoc]

中文:
定理 all_node3L
  条件: {P l x m y r}
  证明: by
  simp [node3L, all_node', and_assoc]

Depends on / 依赖: all_node, and_assoc, node3L
-/
theorem all_node3L {P l x m y r} :
    @All α P (node3L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  simp [node3L, all_node', and_assoc]

/--
theorem `all_node3R` / 定理 `all_node3R`

English:
theorem all_node3R
  given: {P l x m y r}
  proof: Iff.rfl

中文:
定理 all_node3R
  条件: {P l x m y r}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem all_node3R {P l x m y r} :
    @All α P (node3R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r :=
  Iff.rfl

/--
theorem `all_node4L` / 定理 `all_node4L`

English:
theorem all_node4L
  given: {P l x m y r}
  proof: by
  cases m <;> simp [node4L, all_node', All, all_node3L, and_assoc]

中文:
定理 all_node4L
  条件: {P l x m y r}
  证明: by
  cases m <;> simp [node4L, all_node', All, all_node3L, and_assoc]

Depends on / 依赖: all_node, all_node3L, and_assoc, node4L
-/
theorem all_node4L {P l x m y r} :
    @All α P (node4L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [node4L, all_node', All, all_node3L, and_assoc]

/--
theorem `all_node4R` / 定理 `all_node4R`

English:
theorem all_node4R
  given: {P l x m y r}
  proof: by
  cases m <;> simp [node4R, all_node', All, all_node3R, and_assoc]

中文:
定理 all_node4R
  条件: {P l x m y r}
  证明: by
  cases m <;> simp [node4R, all_node', All, all_node3R, and_assoc]

Depends on / 依赖: all_node, all_node3R, and_assoc, node4R
-/
theorem all_node4R {P l x m y r} :
    @All α P (node4R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [node4R, all_node', All, all_node3R, and_assoc]

/--
theorem `all_rotateL` / 定理 `all_rotateL`

English:
theorem all_rotateL
  given: {P l x r}
  statement: @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r
  proof: by
  cases r <;> simp [rotateL, all_node']; split_ifs <;>
    simp [all_node3L, all_node4L, All]

中文:
定理 all_rotateL
  条件: {P l x r}
  结论: @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r
  证明: by
  cases r <;> simp [rotateL, all_node']; split_ifs <;>
    simp [all_node3L, all_node4L, All]

Depends on / 依赖: all_node, all_node3L, all_node4L, rotateL, split_ifs
-/
theorem all_rotateL {P l x r} : @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r := by
  cases r <;> simp [rotateL, all_node']; split_ifs <;>
    simp [all_node3L, all_node4L, All]

/--
theorem `all_rotateR` / 定理 `all_rotateR`

English:
theorem all_rotateR
  given: {P l x r}
  statement: @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r
  proof: by
  rw [← all_dual]; rw [dual_rotateR]; rw [all_rotateL]; simp [all_dual, and_comm, and_left_comm, and_assoc]

中文:
定理 all_rotateR
  条件: {P l x r}
  结论: @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r
  证明: by
  rw [← all_dual]; rw [dual_rotateR]; rw [all_rotateL]; simp [all_dual, and_comm, and_left_comm, and_assoc]

Depends on / 依赖: all_dual, all_rotateL, and_assoc, and_comm, and_left_comm, dual_rotateR
-/
theorem all_rotateR {P l x r} : @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [← all_dual]; rw [dual_rotateR]; rw [all_rotateL]; simp [all_dual, and_comm, and_left_comm, and_assoc]

/--
theorem `all_balance'` / 定理 `all_balance'`

English:
theorem all_balance'
  given: {P l x r}
  statement: @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P r
  proof: by
  rw [balance']; split_ifs <;> simp [all_node', all_rotateL, all_rotateR]

中文:
定理 all_balance'
  条件: {P l x r}
  结论: @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P r
  证明: by
  rw [balance']; split_ifs <;> simp [all_node', all_rotateL, all_rotateR]

Depends on / 依赖: all_node, all_rotateL, all_rotateR, balance, split_ifs
-/
theorem all_balance' {P l x r} : @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balance']; split_ifs <;> simp [all_node', all_rotateL, all_rotateR]



/--
theorem `foldr_cons_eq_toList` / 定理 `foldr_cons_eq_toList`

English:
theorem foldr_cons_eq_toList
  statement: forall (t : Ordnode α) (r : List α), t.foldr List.cons r = toList t ++ r

中文:
定理 foldr_cons_eq_toList
  结论: 对任意 (t : Ordnode α) (r : 列表 α), t.foldr 列表.cons r = toList t ++ r
-/
theorem foldr_cons_eq_toList : forall (t : Ordnode α) (r : List α), t.foldr List.cons r = toList t ++ r
  | nil, _ => rfl
  | node _ l x r, r' => by
    rw [foldr]; rw [foldr_cons_eq_toList l]; rw [foldr_cons_eq_toList r]; rw [← List.cons_append]; rw [← List.append_assoc]; rw [← foldr_cons_eq_toList l]; rfl

@[simp]
/--
theorem `toList_nil` / 定理 `toList_nil`

English:
theorem toList_nil
  statement: toList (@nil α) = []
  proof: rfl

@[simp]

中文:
定理 toList_nil
  结论: toList (@nil α) = []
  证明: rfl

@[simp]
-/
theorem toList_nil : toList (@nil α) = [] :=
  rfl

@[simp]
/--
theorem `toList_node` / 定理 `toList_node`

English:
theorem toList_node
  given: (s l x r)
  statement: toList (@node α s l x r) = toList l ++ x :: toList r
  proof: by
  rw [toList]; rw [foldr]; rw [foldr_cons_eq_toList]; rfl

中文:
定理 toList_node
  条件: (s l x r)
  结论: toList (@node α s l x r) = toList l ++ x :: toList r
  证明: by
  rw [toList]; rw [foldr]; rw [foldr_cons_eq_toList]; rfl

Depends on / 依赖: foldr_cons_eq_toList, toList
-/
theorem toList_node (s l x r) : toList (@node α s l x r) = toList l ++ x :: toList r := by
  rw [toList]; rw [foldr]; rw [foldr_cons_eq_toList]; rfl

/--
theorem `emem_iff_mem_toList` / 定理 `emem_iff_mem_toList`

English:
theorem emem_iff_mem_toList
  given: {x : α} {t}
  statement: Emem x t ↔ x in toList t
  proof: by
  unfold Emem; induction t <;> simp [Any, *]

中文:
定理 emem_iff_mem_toList
  条件: {x : α} {t}
  结论: Emem x t ↔ x in toList t
  证明: by
  unfold Emem; induction t <;> simp [Any, *]
-/
theorem emem_iff_mem_toList {x : α} {t} : Emem x t ↔ x in toList t := by
  unfold Emem; induction t <;> simp [Any, *]

/--
theorem `length_toList'` / 定理 `length_toList'`

English:
theorem length_toList'
  statement: forall t : Ordnode α, (toList t).length = t.realSize

中文:
定理 length_toList'
  结论: 对任意 t : Ordnode α, (toList t).length = t.realSize
-/
theorem length_toList' : forall t : Ordnode α, (toList t).length = t.realSize
  | nil => rfl
  | node _ l _ r => by
    rw [toList_node]; rw [List.length_append]; rw [List.length_cons]; rw [length_toList' l]; rw [length_toList' r]; rfl

/--
theorem `length_toList` / 定理 `length_toList`

English:
theorem length_toList
  given: {t : Ordnode α} (h : Sized t)
  statement: (toList t).length = t.size
  proof: by
  rw [length_toList']; rw [size_eq_realSize h]

中文:
定理 length_toList
  条件: {t : Ordnode α} (h : Sized t)
  结论: (toList t).length = t.size
  证明: by
  rw [length_toList']; rw [size_eq_realSize h]

Depends on / 依赖: length_toList, size_eq_realSize
-/
theorem length_toList {t : Ordnode α} (h : Sized t) : (toList t).length = t.size := by
  rw [length_toList']; rw [size_eq_realSize h]

/--
theorem `equiv_iff` / 定理 `equiv_iff`

English:
theorem equiv_iff
  given: {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂)
  proof: and_iff_right_of_imp fun h => by rw [← length_toList h₁, h, length_toList h₂]

中文:
定理 equiv_iff
  条件: {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂)
  证明: and_iff_right_of_imp fun h => by rw [← length_toList h₁, h, length_toList h₂]

Depends on / 依赖: and_iff_right_of_imp, length_toList
-/
theorem equiv_iff {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂) :
    Equiv t₁ t₂ ↔ toList t₁ = toList t₂ :=
  and_iff_right_of_imp fun h => by rw [← length_toList h₁, h, length_toList h₂]



/--
theorem `pos_size_of_mem` / 定理 `pos_size_of_mem`

English:
theorem pos_size_of_mem
  statement: [LE α] [DecidableLE α] {x : α} {t : Ordnode α} (h : Sized t)
  proof: by cases t; · { contradiction }; · { simp [h.1] }

中文:
定理 pos_size_of_mem
  结论: [LE α] [DecidableLE α] {x : α} {t : Ordnode α} (h : Sized t)
  证明: by cases t; · { contradiction }; · { simp [h.1] }
-/
theorem pos_size_of_mem [LE α] [DecidableLE α] {x : α} {t : Ordnode α} (h : Sized t)
    (h_mem : x in t) : 0 < size t := by cases t; · { contradiction }; · { simp [h.1] }



/--
theorem `findMin'_dual` / 定理 `findMin'_dual`

English:
theorem findMin'_dual
  statement: forall (t) (x : α), findMin' (dual t) x = findMax' x t

中文:
定理 findMin'_dual
  结论: 对任意 (t) (x : α), findMin' (dual t) x = findMax' x t
-/
theorem findMin'_dual : forall (t) (x : α), findMin' (dual t) x = findMax' x t
  | nil, _ => rfl
  | node _ _ x r, _ => findMin'_dual r x

/--
theorem `findMax'_dual` / 定理 `findMax'_dual`

English:
theorem findMax'_dual
  given: (t) (x : α)
  statement: findMax' x (dual t) = findMin' t x
  proof: by
  rw [← findMin'_dual]; rw [dual_dual]

中文:
定理 findMax'_dual
  条件: (t) (x : α)
  结论: findMax' x (dual t) = findMin' t x
  证明: by
  rw [← findMin'_dual]; rw [dual_dual]

Depends on / 依赖: _dual, dual_dual, findMin
-/
theorem findMax'_dual (t) (x : α) : findMax' x (dual t) = findMin' t x := by
  rw [← findMin'_dual]; rw [dual_dual]

/--
theorem `findMin_dual` / 定理 `findMin_dual`

English:
theorem findMin_dual
  statement: forall t : Ordnode α, findMin (dual t) = findMax t

中文:
定理 findMin_dual
  结论: 对任意 t : Ordnode α, findMin (dual t) = findMax t
-/
theorem findMin_dual : forall t : Ordnode α, findMin (dual t) = findMax t
  | nil => rfl
| node _ _ _ _ => congr_arg some findMin'_dual _ _

/--
theorem `findMax_dual` / 定理 `findMax_dual`

English:
theorem findMax_dual
  given: (t : Ordnode α)
  statement: findMax (dual t) = findMin t
  proof: by
  rw [← findMin_dual]; rw [dual_dual]

中文:
定理 findMax_dual
  条件: (t : Ordnode α)
  结论: findMax (dual t) = findMin t
  证明: by
  rw [← findMin_dual]; rw [dual_dual]

Depends on / 依赖: dual_dual, findMin_dual
-/
theorem findMax_dual (t : Ordnode α) : findMax (dual t) = findMin t := by
  rw [← findMin_dual]; rw [dual_dual]

/--
theorem `dual_eraseMin` / 定理 `dual_eraseMin`

English:
theorem dual_eraseMin
  statement: forall t : Ordnode α, dual (eraseMin t) = eraseMax (dual t)

中文:
定理 dual_eraseMin
  结论: 对任意 t : Ordnode α, dual (eraseMin t) = eraseMax (dual t)
-/
theorem dual_eraseMin : forall t : Ordnode α, dual (eraseMin t) = eraseMax (dual t)
  | nil => rfl
  | node _ nil _ _ => rfl
  | node _ (node sz l' y r') x r => by
    rw [eraseMin]; rw [dual_balanceR]; rw [dual_eraseMin (node sz l' y r')]; rw [dual]; rw [dual]; rw [dual]; rw [eraseMax]

/--
theorem `dual_eraseMax` / 定理 `dual_eraseMax`

English:
theorem dual_eraseMax
  given: (t : Ordnode α)
  statement: dual (eraseMax t) = eraseMin (dual t)
  proof: by
  rw [← dual_dual (eraseMin _)]; rw [dual_eraseMin]; rw [dual_dual]

中文:
定理 dual_eraseMax
  条件: (t : Ordnode α)
  结论: dual (eraseMax t) = eraseMin (dual t)
  证明: by
  rw [← dual_dual (eraseMin _)]; rw [dual_eraseMin]; rw [dual_dual]

Depends on / 依赖: dual_dual, dual_eraseMin, eraseMin
-/
theorem dual_eraseMax (t : Ordnode α) : dual (eraseMax t) = eraseMin (dual t) := by
  rw [← dual_dual (eraseMin _)]; rw [dual_eraseMin]; rw [dual_dual]

/--
theorem `splitMin_eq` / 定理 `splitMin_eq`

English:
theorem splitMin_eq

中文:
定理 splitMin_eq
-/
theorem splitMin_eq :
    forall (s l) (x : α) (r), splitMin' l x r = (findMin' l x, eraseMin (node s l x r))
  | _, nil, _, _ => rfl
  | _, node ls ll lx lr, x, r => by rw [splitMin', splitMin_eq ls ll lx lr, findMin', eraseMin]

/--
theorem `splitMax_eq` / 定理 `splitMax_eq`

English:
theorem splitMax_eq

中文:
定理 splitMax_eq
-/
theorem splitMax_eq :
    forall (s l) (x : α) (r), splitMax' l x r = (eraseMax (node s l x r), findMax' x r)
  | _, _, _, nil => rfl
  | _, l, x, node ls ll lx lr => by rw [splitMax', splitMax_eq ls ll lx lr, findMax', eraseMax]

@[elab_as_elim]
/--
theorem `findMin'_all` / 定理 `findMin'_all`

English:
theorem findMin'_all
  given: {P : α -> Prop}
  statement: forall (t) (x : α), All P t -> P x -> P (findMin' t x)

中文:
定理 findMin'_all
  条件: {P : α -> 命题}
  结论: 对任意 (t) (x : α), All P t -> P x -> P (findMin' t x)
-/
theorem findMin'_all {P : α -> Prop} : forall (t) (x : α), All P t -> P x -> P (findMin' t x)
  | nil, _x, _, hx => hx
  | node _ ll lx _, _, ⟨h₁, h₂, _⟩, _ => findMin'_all ll lx h₁ h₂

@[elab_as_elim]
/--
theorem `findMax'_all` / 定理 `findMax'_all`

English:
theorem findMax'_all
  given: {P : α -> Prop}
  statement: forall (x : α) (t), P x -> All P t -> P (findMax' x t)

中文:
定理 findMax'_all
  条件: {P : α -> 命题}
  结论: 对任意 (x : α) (t), P x -> All P t -> P (findMax' x t)
-/
theorem findMax'_all {P : α -> Prop} : forall (x : α) (t), P x -> All P t -> P (findMax' x t)
  | _x, nil, hx, _ => hx
  | _, node _ _ lx lr, _, ⟨_, h₂, h₃⟩ => findMax'_all lx lr h₂ h₃

/-! ### `glue` -/


/-! ### `merge` -/


@[simp]
/--
theorem `merge_nil_left` / 定理 `merge_nil_left`

English:
theorem merge_nil_left
  given: (t : Ordnode α)
  statement: merge t nil = t
  proof: by cases t <;> rfl

@[simp]

中文:
定理 merge_nil_left
  条件: (t : Ordnode α)
  结论: merge t nil = t
  证明: by cases t <;> rfl

@[simp]
-/
theorem merge_nil_left (t : Ordnode α) : merge t nil = t := by cases t <;> rfl

@[simp]
/--
theorem `merge_nil_right` / 定理 `merge_nil_right`

English:
theorem merge_nil_right
  given: (t : Ordnode α)
  statement: merge nil t = t
  proof: rfl

@[simp]

中文:
定理 merge_nil_right
  条件: (t : Ordnode α)
  结论: merge nil t = t
  证明: rfl

@[simp]
-/
theorem merge_nil_right (t : Ordnode α) : merge nil t = t :=
  rfl

@[simp]
/--
theorem `merge_node` / 定理 `merge_node`

English:
theorem merge_node
  given: {ls ll lx lr rs rl rx rr}
  proof: rfl

中文:
定理 merge_node
  条件: {ls ll lx lr rs rl rx rr}
  证明: rfl
-/
theorem merge_node {ls ll lx lr rs rl rx rr} :
    merge (@node α ls ll lx lr) (node rs rl rx rr) =
      if delta * ls < rs then balanceL (merge (node ls ll lx lr) rl) rx rr
      else if delta * rs < ls then balanceR ll lx (merge lr (node rs rl rx rr))
      else glue (node ls ll lx lr) (node rs rl rx rr) :=
  rfl

/-! ### `insert` -/


set_option backward.isDefEq.respectTransparency false in
/--
theorem `dual_insert` / 定理 `dual_insert`

English:
theorem dual_insert
  given: [LE α] [@Std.Total α (· <= ·)] [DecidableLE α] (x : α)
  proof: rfl
    rw [Ordnode.insert]; rw [dual]; rw [Ordnode.insert]; rw [this]; rw [← cmpLE_swap x y]
    cases cmpLE x y <;>
      simp [Ordering.swap, dual_balanceL, dual_balanceR, dual_insert]

中文:
定理 dual_insert
  条件: [LE α] [@Std.全 α (· <= ·)] [DecidableLE α] (x : α)
  证明: rfl
    rw [Ordnode.insert]; rw [dual]; rw [Ordnode.insert]; rw [this]; rw [← cmpLE_swap x y]
    cases cmpLE x y <;>
      simp [Ordering.swap, dual_balanceL, dual_balanceR, dual_insert]
-/
theorem dual_insert [LE α] [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) :
    forall t : Ordnode α, dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t)
  | nil => rfl
  | node _ l y r => by
    have : @cmpLE αᵒᵈ _ _ x y = cmpLE y x := rfl
    rw [Ordnode.insert]; rw [dual]; rw [Ordnode.insert]; rw [this]; rw [← cmpLE_swap x y]
    cases cmpLE x y <;>
      simp [Ordering.swap, dual_balanceL, dual_balanceR, dual_insert]

/-! ### `balance` properties -/


set_option backward.isDefEq.respectTransparency false in
/--
theorem `balance_eq_balance'` / 定理 `balance_eq_balance'`

English:
theorem balance_eq_balance'
  statement: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
  proof: by
  obtain - | ⟨ls, ll, lx, lr⟩ := l
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rfl
    · rw [sr.eq_node'] at hr ⊢
      obtain - | ⟨rls, rll, rlx, rlr⟩ := rl <;> obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr <;>
        dsimp +instances [balance, balance']
      · rfl
      · have : size rrl = 0 ∧ size rr

中文:
定理 balance_eq_balance'
  结论: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
  证明: by
  obtain - | ⟨ls, ll, lx, lr⟩ := l
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rfl
    · rw [sr.eq_node'] at hr ⊢
      obtain - | ⟨rls, rll, rlx, rlr⟩ := rl <;> obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr <;>
        dsimp +instances [balance, balance']
      · rfl
      · have : size rrl = 0 ∧ size rr

Depends on / 依赖: Nat.le_zero, Nat.succ_le_succ_iff, add_eq_zero, balance, balancedSz_zero, eq_node, instances, le_zero, size_eq_zero, sr.eq_node, succ_le_succ_iff
-/
theorem balance_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r) : @balance α l x r = balance' l x r := by
  obtain - | ⟨ls, ll, lx, lr⟩ := l
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rfl
    · rw [sr.eq_node'] at hr ⊢
      obtain - | ⟨rls, rll, rlx, rlr⟩ := rl <;> obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr <;>
        dsimp +instances [balance, balance']
      · rfl
      · have : size rrl = 0 ∧ size rrr = 0 := by
          have := balancedSz_zero.1 hr.1.symm
          rwa [size, sr.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sr.2.2.2.1.size_eq_zero.1 this.1
        cases sr.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : rrs = 1 := sr.2.2.1
        rw [if_neg]; rw [rotateL_node]; rw [if_pos]; · rfl
        all_goals (try dsimp only [size]); decide
      · have : size rll = 0 ∧ size rlr = 0 := by
          have := balancedSz_zero.1 hr.1
          rwa [size, sr.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sr.2.1.2.1.size_eq_zero.1 this.1
        cases sr.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : rls = 1 := sr.2.1.1
        rw [if_neg]; rw [rotateL_node]; rw [if_neg]; · rfl
        all_goals (try dsimp only [size]); decide
      · symm; rw [zero_add, if_neg, rotateL]
        · dsimp only [size_node]; split_ifs
          · simp [node3L, node']; abel
          · simp [node4L, node', sr.2.1.1]; abel
        · exact not_le_of_gt (Nat.succ_lt_succ (add_pos sr.2.1.pos sr.2.2.pos))
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rw [sl.eq_node'] at hl ⊢
      obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
        dsimp [balance, balance']
      · rfl
      · have : size lrl = 0 ∧ size lrr = 0 := by
          have := balancedSz_zero.1 hl.1.symm
          rwa [size, sl.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sl.2.2.2.1.size_eq_zero.1 this.1
        cases sl.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : lrs = 1 := sl.2.2.1
        rw [if_neg]; rw [rotateR_node]; rw [if_neg]; · rfl
        all_goals (try dsimp only [size]); decide
      · have : size lll = 0 ∧ size llr = 0 := by
          have := balancedSz_zero.1 hl.1
          rwa [size, sl.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sl.2.1.2.1.size_eq_zero.1 this.1
        cases sl.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : lls = 1 := sl.2.1.1
        rw [if_neg]; rw [rotateR_node]; rw [if_pos]; · rfl
        all_goals (try dsimp only [size]); decide
      · symm; rw [if_neg, rotateR]
        · dsimp only [size_node]; split_ifs
          · simp [node3R, node']; abel
          · simp [node4R, node', sl.2.2.1]; abel
        · exact not_le_of_gt (Nat.succ_lt_succ (add_pos sl.2.1.pos sl.2.2.pos))
    · simp only [balance, id_eq, balance', size_node, gt_iff_lt]
      symm; rw [if_neg]
      · split_ifs with h h_1
        · have rd : delta <= size rl + size rr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sl.pos) h
            rwa [sr.1, Nat.lt_succ_iff] at this
          obtain - | ⟨rls, rll, rlx, rlr⟩ := rl
          · rw [size, zero_add] at rd
            exact absurd (le_trans rd (balancedSz_zero.1 hr.1.symm)) (by decide)
          obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr
          · exact absurd (le_trans rd (balancedSz_zero.1 hr.1)) (by decide)
          dsimp [rotateL]; split_ifs
          · simp [node3L, node', sr.1]; abel
          · simp [node4L, node', sr.1, sr.2.1.1]; abel
        · have ld : delta <= size ll + size lr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sr.pos) h_1
            rwa [sl.1, Nat.lt_succ_iff] at this
          obtain - | ⟨lls, lll, llx, llr⟩ := ll
          · rw [size, zero_add] at ld
            exact absurd (le_trans ld (balancedSz_zero.1 hl.1.symm)) (by decide)
          obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr
          · exact absurd (le_trans ld (balancedSz_zero.1 hl.1)) (by decide)
          dsimp [rotateR]; split_ifs
          · simp [node3R, node', sl.1]; abel
          · simp [node4R, node', sl.1, sl.2.2.1]; abel
        · simp [node']
      · exact not_le_of_gt (add_le_add (Nat.succ_le_of_lt sl.pos) (Nat.succ_le_of_lt sr.pos))

/--
theorem `balanceL_eq_balance` / 定理 `balanceL_eq_balance`

English:
theorem balanceL_eq_balance
  statement: {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 -> size r <= 1)
  proof: by
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · rfl
  · obtain - | ⟨ls, ll, lx, lr⟩ := l
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_

中文:
定理 balanceL_eq_balance
  结论: {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 -> size r <= 1)
  证明: by
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · rfl
  · obtain - | ⟨ls, ll, lx, lr⟩ := l
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_

Depends on / 依赖: Nat.le_zero, Nat.succ_le_succ_iff, add_comm, add_eq_zero, balance, balanceL, eq_node, le_zero, not_lt_of_ge, replace, size_eq_zero, sl.pos, split_ifs, sr.eq_node, sr.pos, succ_le_succ_iff
-/
theorem balanceL_eq_balance {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 -> size r <= 1)
    (H2 : 1 <= size l -> 1 <= size r -> size r <= delta * size l) :
    @balanceL α l x r = balance l x r := by
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · rfl
  · obtain - | ⟨ls, ll, lx, lr⟩ := l
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_zero.1 this.2
      rw [sr.eq_node']; rfl
    · replace H2 : ¬rs > delta * ls := not_lt_of_ge (H2 sl.pos sr.pos)
      simp [balanceL, balance, H2]; split_ifs <;> simp [add_comm]

/--
Definition of `Raised` / `Raised` 的定义

English:
definition Raised
  signature: (n m : Nat)
  body: m = n ∨ m = n + 1

中文:
定义 Raised
  签名: (n m : 自然数)
  定义体: m = n ∨ m = n + 1
-/
def Raised (n m : Nat) : Prop :=
  m = n ∨ m = n + 1

/--
theorem `raised_iff` / 定理 `raised_iff`

English:
theorem raised_iff
  given: {n m}
  statement: Raised n m ↔ n <= m ∧ m <= n + 1
  proof: by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, Nat.le_succ _⟩
    · exact ⟨Nat.le_succ _, le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with (rfl | h₁)
    · exact Or.inl rfl
    · exact Or.inr (le_antisymm h₂ h₁)

中文:
定理 raised_iff
  条件: {n m}
  结论: Raised n m ↔ n <= m ∧ m <= n + 1
  证明: by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, Nat.le_succ _⟩
    · exact ⟨Nat.le_succ _, le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with (rfl | h₁)
    · exact Or.inl rfl
    · exact Or.inr (le_antisymm h₂ h₁)

Depends on / 依赖: Nat.le_succ, Or.inl, Or.inr, eq_or_lt_of_le, le_antisymm, le_rfl, le_succ
-/
theorem raised_iff {n m} : Raised n m ↔ n <= m ∧ m <= n + 1 := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, Nat.le_succ _⟩
    · exact ⟨Nat.le_succ _, le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with (rfl | h₁)
    · exact Or.inl rfl
    · exact Or.inr (le_antisymm h₂ h₁)

/--
theorem `Raised.dist_le` / 定理 `Raised.dist_le`

English:
theorem Raised.dist_le
  given: {n m} (H : Raised n m)
  statement: Nat.dist n m <= 1
  proof: by
  obtain ⟨H1, H2⟩ := raised_iff.1 H; rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

中文:
定理 Raised.dist_le
  条件: {n m} (H : Raised n m)
  结论: 自然数.dist n m <= 1
  证明: by
  obtain ⟨H1, H2⟩ := raised_iff.1 H; rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

Depends on / 依赖: Nat.dist_eq_sub_of_le, dist_eq_sub_of_le, raised_iff, tsub_le_iff_left
-/
theorem Raised.dist_le {n m} (H : Raised n m) : Nat.dist n m <= 1 := by
  obtain ⟨H1, H2⟩ := raised_iff.1 H; rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

/--
theorem `Raised.dist_le'` / 定理 `Raised.dist_le'`

English:
theorem Raised.dist_le'
  given: {n m} (H : Raised n m)
  statement: Nat.dist m n <= 1
  proof: by
  rw [Nat.dist_comm]; exact H.dist_le

中文:
定理 Raised.dist_le'
  条件: {n m} (H : Raised n m)
  结论: 自然数.dist m n <= 1
  证明: by
  rw [Nat.dist_comm]; exact H.dist_le

Depends on / 依赖: H.dist_le, Nat.dist_comm, dist_comm, dist_le
-/
theorem Raised.dist_le' {n m} (H : Raised n m) : Nat.dist m n <= 1 := by
  rw [Nat.dist_comm]; exact H.dist_le

/--
theorem `Raised.add_left` / 定理 `Raised.add_left`

English:
theorem Raised.add_left
  given: (k) {n m} (H : Raised n m)
  statement: Raised (k + n) (k + m)
  proof: by
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

中文:
定理 Raised.add_left
  条件: (k) {n m} (H : Raised n m)
  结论: Raised (k + n) (k + m)
  证明: by
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

Depends on / 依赖: Or.inl, Or.inr
-/
theorem Raised.add_left (k) {n m} (H : Raised n m) : Raised (k + n) (k + m) := by
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
theorem `Raised.add_right` / 定理 `Raised.add_right`

English:
theorem Raised.add_right
  given: (k) {n m} (H : Raised n m)
  statement: Raised (n + k) (m + k)
  proof: by
  rw [add_comm]; rw [add_comm m]; exact H.add_left _

中文:
定理 Raised.add_right
  条件: (k) {n m} (H : Raised n m)
  结论: Raised (n + k) (m + k)
  证明: by
  rw [add_comm]; rw [add_comm m]; exact H.add_left _

Depends on / 依赖: H.add_left, add_comm, add_left
-/
theorem Raised.add_right (k) {n m} (H : Raised n m) : Raised (n + k) (m + k) := by
  rw [add_comm]; rw [add_comm m]; exact H.add_left _

/--
theorem `Raised.right` / 定理 `Raised.right`

English:
theorem Raised.right
  given: {l x₁ x₂ r₁ r₂} (H : Raised (size r₁) (size r₂))
  proof: by
  rw [node']; rw [size_node]; rw [size_node]; generalize size r₂ = m at H ⊢
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

中文:
定理 Raised.right
  条件: {l x₁ x₂ r₁ r₂} (H : Raised (size r₁) (size r₂))
  证明: by
  rw [node']; rw [size_node]; rw [size_node]; generalize size r₂ = m at H ⊢
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

Depends on / 依赖: Or.inl, Or.inr, generalize, size_node
-/
theorem Raised.right {l x₁ x₂ r₁ r₂} (H : Raised (size r₁) (size r₂)) :
    Raised (size (@node' α l x₁ r₁)) (size (@node' α l x₂ r₂)) := by
  rw [node']; rw [size_node]; rw [size_node]; generalize size r₂ = m at H ⊢
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
theorem `balanceL_eq_balance'` / 定理 `balanceL_eq_balance'`

English:
theorem balanceL_eq_balance'
  statement: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
  proof: by
  rw [← balance_eq_balance' hl hr sl sr]; rw [balanceL_eq_balance sl sr]
  · intro l0; rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balancedSz_zero.1 H.symm
    exact le_trans (raised_iff.1 e).1 (balancedSz_zero.1 H.symm)
  · intro l1 _
    rcases H with (⟨l', e, 

中文:
定理 balanceL_eq_balance'
  结论: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
  证明: by
  rw [← balance_eq_balance' hl hr sl sr]; rw [balanceL_eq_balance sl sr]
  · intro l0; rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balancedSz_zero.1 H.symm
    exact le_trans (raised_iff.1 e).1 (balancedSz_zero.1 H.symm)
  · intro l1 _
    rcases H with (⟨l', e, 

Depends on / 依赖: H.symm, Nat.le_add_left, Nat.mul_le_mul_left, balanceL_eq_balance, balance_eq_balance, balancedSz_zero, le_add_left, le_trans, mul_le_mul_left, mul_pos, raised_iff
-/
theorem balanceL_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H :
      (exists l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        exists r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    @balanceL α l x r = balance' l x r := by
  rw [← balance_eq_balance' hl hr sl sr]; rw [balanceL_eq_balance sl sr]
  · intro l0; rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balancedSz_zero.1 H.symm
    exact le_trans (raised_iff.1 e).1 (balancedSz_zero.1 H.symm)
  · intro l1 _
    rcases H with (⟨l', e, H | ⟨_, H₂⟩⟩ | ⟨r', e, H | ⟨_, H₂⟩⟩)
    · exact le_trans (le_trans (Nat.le_add_left _ _) H) (mul_pos (by decide) l1 : (0 : Nat) < _)
    · exact le_trans H₂ (Nat.mul_le_mul_left _ (raised_iff.1 e).1)
    · cases raised_iff.1 e; unfold delta; lia
    · exact le_trans (raised_iff.1 e).1 H₂

/--
theorem `balance_sz_dual` / 定理 `balance_sz_dual`

English:
theorem balance_sz_dual
  statement: {l r}
  proof: by
  rw [size_dual]; rw [size_dual]
  exact
    H.symm.imp (Exists.imp fun _ => And.imp_right BalancedSz.symm)
      (Exists.imp fun _ => And.imp_right BalancedSz.symm)

中文:
定理 balance_sz_dual
  结论: {l r}
  证明: by
  rw [size_dual]; rw [size_dual]
  exact
    H.symm.imp (Exists.imp fun _ => And.imp_right BalancedSz.symm)
      (Exists.imp fun _ => And.imp_right BalancedSz.symm)

Depends on / 依赖: And.imp_right, BalancedSz, BalancedSz.symm, Exists, Exists.imp, H.symm.imp, imp_right, size_dual
-/
theorem balance_sz_dual {l r}
    (H : (exists l', Raised (@size α l) l' ∧ BalancedSz l' (@size α r)) ∨
        exists r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    (exists l', Raised l' (size (dual r)) ∧ BalancedSz l' (size (dual l))) ∨
      exists r', Raised (size (dual l)) r' ∧ BalancedSz (size (dual r)) r' := by
  rw [size_dual]; rw [size_dual]
  exact
    H.symm.imp (Exists.imp fun _ => And.imp_right BalancedSz.symm)
      (Exists.imp fun _ => And.imp_right BalancedSz.symm)

/--
theorem `size_balanceL` / 定理 `size_balanceL`

English:
theorem size_balanceL
  statement: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  proof: by
  rw [balanceL_eq_balance' hl hr sl sr H]; rw [size_balance' sl sr]

中文:
定理 size_balanceL
  结论: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  证明: by
  rw [balanceL_eq_balance' hl hr sl sr H]; rw [size_balance' sl sr]

Depends on / 依赖: balanceL_eq_balance, size_balance
-/
theorem size_balanceL {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (exists l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        exists r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    size (@balanceL α l x r) = size l + size r + 1 := by
  rw [balanceL_eq_balance' hl hr sl sr H]; rw [size_balance' sl sr]

/--
theorem `all_balanceL` / 定理 `all_balanceL`

English:
theorem all_balanceL
  statement: {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  proof: by
  rw [balanceL_eq_balance' hl hr sl sr H]; rw [all_balance']

中文:
定理 all_balanceL
  结论: {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  证明: by
  rw [balanceL_eq_balance' hl hr sl sr H]; rw [all_balance']

Depends on / 依赖: all_balance, balanceL_eq_balance
-/
theorem all_balanceL {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H :
      (exists l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        exists r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    All P (@balanceL α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balanceL_eq_balance' hl hr sl sr H]; rw [all_balance']

/--
theorem `balanceR_eq_balance'` / 定理 `balanceR_eq_balance'`

English:
theorem balanceR_eq_balance'
  statement: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
  proof: by
  rw [← dual_dual (balanceR l x r)]; rw [dual_balanceR]; rw [balanceL_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H)]; rw [← dual_balance']; rw [dual_dual]

中文:
定理 balanceR_eq_balance'
  结论: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
  证明: by
  rw [← dual_dual (balanceR l x r)]; rw [dual_balanceR]; rw [balanceL_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H)]; rw [← dual_balance']; rw [dual_dual]

Depends on / 依赖: balanceL_eq_balance, balanceR, balance_sz_dual, dual_balance, dual_balanceR, dual_dual, hl.dual, hr.dual, sl.dual, sr.dual
-/
theorem balanceR_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H : (exists l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        exists r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    @balanceR α l x r = balance' l x r := by
  rw [← dual_dual (balanceR l x r)]; rw [dual_balanceR]; rw [balanceL_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H)]; rw [← dual_balance']; rw [dual_dual]

/--
theorem `size_balanceR` / 定理 `size_balanceR`

English:
theorem size_balanceR
  statement: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  proof: by
  rw [balanceR_eq_balance' hl hr sl sr H]; rw [size_balance' sl sr]

中文:
定理 size_balanceR
  结论: {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  证明: by
  rw [balanceR_eq_balance' hl hr sl sr H]; rw [size_balance' sl sr]

Depends on / 依赖: balanceR_eq_balance, size_balance
-/
theorem size_balanceR {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (exists l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        exists r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    size (@balanceR α l x r) = size l + size r + 1 := by
  rw [balanceR_eq_balance' hl hr sl sr H]; rw [size_balance' sl sr]

/--
theorem `all_balanceR` / 定理 `all_balanceR`

English:
theorem all_balanceR
  statement: {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  proof: by
  rw [balanceR_eq_balance' hl hr sl sr H]; rw [all_balance']

中文:
定理 all_balanceR
  结论: {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
  证明: by
  rw [balanceR_eq_balance' hl hr sl sr H]; rw [all_balance']

Depends on / 依赖: all_balance, balanceR_eq_balance
-/
theorem all_balanceR {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H :
      (exists l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        exists r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    All P (@balanceR α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balanceR_eq_balance' hl hr sl sr H]; rw [all_balance']

section Bounded

variable [Preorder α]

/--
Definition of `Bounded` / `Bounded` 的定义

English:
definition Bounded
  signature: : Ordnode α -> WithBot α -> WithTop α -> Prop

中文:
定义 有界
  签名: : Ordnode α -> WithBot α -> WithTop α -> 命题
-/
def Bounded : Ordnode α -> WithBot α -> WithTop α -> Prop
  | nil, some a, some b => a < b
  | nil, _, _ => True
  | node _ l x r, o₁, o₂ => Bounded l o₁ x ∧ Bounded r (↑x) o₂

/--
theorem `Bounded.dual` / 定理 `Bounded.dual`

English:
theorem Bounded.dual

中文:
定理 有界.dual
-/
theorem Bounded.dual :
    forall {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ -> @Bounded αᵒᵈ _ (dual t) o₂ o₁
  | nil, o₁, o₂, h => by cases o₁ <;> cases o₂ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨Or.dual, ol.dual⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Bounded.dual_iff` / 定理 `Bounded.dual_iff`

English:
theorem Bounded.dual_iff
  given: {t : Ordnode α} {o₁ o₂}
  proof: ⟨Bounded.dual, fun h => by
    have := Bounded.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

中文:
定理 有界.dual_iff
  条件: {t : Ordnode α} {o₁ o₂}
  证明: ⟨Bounded.dual, fun h => by
    have := Bounded.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

Depends on / 依赖: Bounded, Bounded.dual, OrderDual, OrderDual.Preorder.dual_dual, Preorder, dual_dual
-/
theorem Bounded.dual_iff {t : Ordnode α} {o₁ o₂} :
    Bounded t o₁ o₂ ↔ @Bounded αᵒᵈ _ (.dual t) o₂ o₁ :=
  ⟨Bounded.dual, fun h => by
    have := Bounded.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

/--
theorem `Bounded.weak_left` / 定理 `Bounded.weak_left`

English:
theorem Bounded.weak_left
  statement: forall {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ -> Bounded t ⊥ o₂

中文:
定理 有界.weak_left
  结论: 对任意 {t : Ordnode α} {o₁ o₂}, 有界 t o₁ o₂ -> 有界 t ⊥ o₂
-/
theorem Bounded.weak_left : forall {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ -> Bounded t ⊥ o₂
  | nil, o₁, o₂, h => by cases o₂ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨ol.weak_left, Or⟩

/--
theorem `Bounded.weak_right` / 定理 `Bounded.weak_right`

English:
theorem Bounded.weak_right
  statement: forall {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ -> Bounded t o₁ ⊤

中文:
定理 有界.weak_right
  结论: 对任意 {t : Ordnode α} {o₁ o₂}, 有界 t o₁ o₂ -> 有界 t o₁ ⊤
-/
theorem Bounded.weak_right : forall {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ -> Bounded t o₁ ⊤
  | nil, o₁, o₂, h => by cases o₁ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨ol, Or.weak_right⟩

/--
theorem `Bounded.weak` / 定理 `Bounded.weak`

English:
theorem Bounded.weak
  given: {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂)
  statement: Bounded t ⊥ ⊤
  proof: h.weak_left.weak_right

中文:
定理 有界.weak
  条件: {t : Ordnode α} {o₁ o₂} (h : 有界 t o₁ o₂)
  结论: 有界 t ⊥ ⊤
  证明: h.weak_left.weak_right

Depends on / 依赖: h.weak_left.weak_right, weak_left, weak_right
-/
theorem Bounded.weak {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂) : Bounded t ⊥ ⊤ :=
  h.weak_left.weak_right

/--
theorem `Bounded.mono_left` / 定理 `Bounded.mono_left`

English:
theorem Bounded.mono_left
  given: {x y : α} (xy : x <= y)

中文:
定理 有界.mono_left
  条件: {x y : α} (xy : x <= y)
-/
theorem Bounded.mono_left {x y : α} (xy : x <= y) :
    forall {t : Ordnode α} {o}, Bounded t y o -> Bounded t x o
  | nil, none, _ => ⟨⟩
  | nil, some _, h => lt_of_le_of_lt xy h
  | node _ _ _ _, _o, ⟨ol, or⟩ => ⟨ol.mono_left xy, or⟩

/--
theorem `Bounded.mono_right` / 定理 `Bounded.mono_right`

English:
theorem Bounded.mono_right
  given: {x y : α} (xy : x <= y)

中文:
定理 有界.mono_right
  条件: {x y : α} (xy : x <= y)
-/
theorem Bounded.mono_right {x y : α} (xy : x <= y) :
    forall {t : Ordnode α} {o}, Bounded t o x -> Bounded t o y
  | nil, none, _ => ⟨⟩
  | nil, some _, h => lt_of_lt_of_le h xy
  | node _ _ _ _, _o, ⟨ol, or⟩ => ⟨ol, or.mono_right xy⟩

/--
theorem `Bounded.to_lt` / 定理 `Bounded.to_lt`

English:
theorem Bounded.to_lt
  statement: forall {t : Ordnode α} {x y : α}, Bounded t x y -> x < y

中文:
定理 有界.to_lt
  结论: 对任意 {t : Ordnode α} {x y : α}, 有界 t x y -> x < y
-/
theorem Bounded.to_lt : forall {t : Ordnode α} {x y : α}, Bounded t x y -> x < y
  | nil, _, _, h => h
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ => lt_trans h₁.to_lt h₂.to_lt

/--
theorem `Bounded.to_nil` / 定理 `Bounded.to_nil`

English:
theorem Bounded.to_nil
  given: {t : Ordnode α}
  statement: forall {o₁ o₂}, Bounded t o₁ o₂ -> Bounded nil o₁ o₂

中文:
定理 有界.to_nil
  条件: {t : Ordnode α}
  结论: 对任意 {o₁ o₂}, 有界 t o₁ o₂ -> 有界 nil o₁ o₂
-/
theorem Bounded.to_nil {t : Ordnode α} : forall {o₁ o₂}, Bounded t o₁ o₂ -> Bounded nil o₁ o₂
  | none, _, _ => ⟨⟩
  | some _, none, _ => ⟨⟩
  | some _, some _, h => h.to_lt

/--
theorem `Bounded.trans_left` / 定理 `Bounded.trans_left`

English:
theorem Bounded.trans_left
  given: {t₁ t₂ : Ordnode α} {x : α}

中文:
定理 有界.trans_left
  条件: {t₁ t₂ : Ordnode α} {x : α}
-/
theorem Bounded.trans_left {t₁ t₂ : Ordnode α} {x : α} :
    forall {o₁ o₂}, Bounded t₁ o₁ x -> Bounded t₂ x o₂ -> Bounded t₂ o₁ o₂
  | none, _, _, h₂ => h₂.weak_left
  | some _, _, h₁, h₂ => h₂.mono_left (le_of_lt h₁.to_lt)

/--
theorem `Bounded.trans_right` / 定理 `Bounded.trans_right`

English:
theorem Bounded.trans_right
  given: {t₁ t₂ : Ordnode α} {x : α}

中文:
定理 有界.trans_right
  条件: {t₁ t₂ : Ordnode α} {x : α}
-/
theorem Bounded.trans_right {t₁ t₂ : Ordnode α} {x : α} :
    forall {o₁ o₂}, Bounded t₁ o₁ x -> Bounded t₂ x o₂ -> Bounded t₁ o₁ o₂
  | _, none, h₁, _ => h₁.weak_right
  | _, some _, h₁, h₂ => h₁.mono_right (le_of_lt h₂.to_lt)

/--
theorem `Bounded.mem_lt` / 定理 `Bounded.mem_lt`

English:
theorem Bounded.mem_lt
  statement: forall {t o} {x : α}, Bounded t o x -> All (· < x) t

中文:
定理 有界.mem_lt
  结论: 对任意 {t o} {x : α}, 有界 t o x -> All (· < x) t
-/
theorem Bounded.mem_lt : forall {t o} {x : α}, Bounded t o x -> All (· < x) t
  | nil, _, _, _ => ⟨⟩
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ =>
    ⟨h₁.mem_lt.imp fun _ h => lt_trans h h₂.to_lt, h₂.to_lt, h₂.mem_lt⟩

/--
theorem `Bounded.mem_gt` / 定理 `Bounded.mem_gt`

English:
theorem Bounded.mem_gt
  statement: forall {t o} {x : α}, Bounded t x o -> All (· > x) t

中文:
定理 有界.mem_gt
  结论: 对任意 {t o} {x : α}, 有界 t x o -> All (· > x) t
-/
theorem Bounded.mem_gt : forall {t o} {x : α}, Bounded t x o -> All (· > x) t
  | nil, _, _, _ => ⟨⟩
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ => ⟨h₁.mem_gt, h₁.to_lt, h₂.mem_gt.imp fun _ => lt_trans h₁.to_lt⟩

/--
theorem `Bounded.of_lt` / 定理 `Bounded.of_lt`

English:
theorem Bounded.of_lt

中文:
定理 有界.of_lt
-/
theorem Bounded.of_lt :
    forall {t o₁ o₂} {x : α}, Bounded t o₁ o₂ -> Bounded nil o₁ x -> All (· < x) t -> Bounded t o₁ x
  | nil, _, _, _, _, hn, _ => hn
  | node _ _ _ _, _, _, _, ⟨h₁, h₂⟩, _, ⟨_, al₂, al₃⟩ => ⟨h₁, h₂.of_lt al₂ al₃⟩

/--
theorem `Bounded.of_gt` / 定理 `Bounded.of_gt`

English:
theorem Bounded.of_gt

中文:
定理 有界.of_gt
-/
theorem Bounded.of_gt :
    forall {t o₁ o₂} {x : α}, Bounded t o₁ o₂ -> Bounded nil x o₂ -> All (· > x) t -> Bounded t x o₂
  | nil, _, _, _, _, hn, _ => hn
  | node _ _ _ _, _, _, _, ⟨h₁, h₂⟩, _, ⟨al₁, al₂, _⟩ => ⟨h₁.of_gt al₂ al₁, h₂⟩

/--
theorem `Bounded.to_sep` / 定理 `Bounded.to_sep`

English:
theorem Bounded.to_sep
  statement: {t₁ t₂ o₁ o₂} {x : α}
  proof: by
  refine h₁.mem_lt.imp fun y yx => ?_
  exact h₂.mem_gt.imp fun z xz => lt_trans yx xz

中文:
定理 有界.to_sep
  结论: {t₁ t₂ o₁ o₂} {x : α}
  证明: by
  refine h₁.mem_lt.imp fun y yx => ?_
  exact h₂.mem_gt.imp fun z xz => lt_trans yx xz

Depends on / 依赖: lt_trans, mem_gt, mem_gt.imp, mem_lt, mem_lt.imp
-/
theorem Bounded.to_sep {t₁ t₂ o₁ o₂} {x : α}
    (h₁ : Bounded t₁ o₁ (x : WithTop α)) (h₂ : Bounded t₂ (x : WithBot α) o₂) :
    t₁.All fun y => t₂.All fun z : α => y < z := by
  refine h₁.mem_lt.imp fun y yx => ?_
  exact h₂.mem_gt.imp fun z xz => lt_trans yx xz

end Bounded

end Ordnode
