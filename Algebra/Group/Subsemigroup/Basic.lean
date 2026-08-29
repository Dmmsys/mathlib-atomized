/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Data.Set.Lattice.Image

/-!
# Subsemigroups: `CompleteLattice` structure

This file defines a `CompleteLattice` structure on `Subsemigroup`s,
and define the closure of a set as the minimal subsemigroup that includes this set.

## Main definitions

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.
* `Subsemigroup.closure` : semigroup closure of a set, i.e.,
  the least subsemigroup that includes the set.
* `Subsemigroup.gi` : `closure : Set M → Subsemigroup M` and coercion `coe : Subsemigroup M → Set M`
  form a `GaloisInsertion`;

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `Subsemigroup M` does not actually require `Semigroup M`,
instead requiring only the weaker `Mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

@[expose] public section

assert_not_exists MonoidWithZero

-- Only needed for notation
variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

namespace Subsemigroup

variable (S : Subsemigroup M)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Subsemigroup M)
  body: ⟨fun s =>
    { carrier := ⋂ t in s, ↑t
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 下确界集 (子半群 M)
  定义体: ⟨fun s =>
    { carrier := ⋂ t in s, ↑t
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.mem_biInter, Set.mem_iInter, carrier, i.mul_mem, mem_biInter, mul_mem
-/
instance : InfSet (Subsemigroup M) :=
  ⟨fun s =>
    { carrier := ⋂ t in s, ↑t
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Subsemigroup M))
  statement: ((sInf S : Subsemigroup M) : Set M) = ⋂ s in S, ↑s
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_sInf
  条件: (S : 集合 (子半群 M))
  结论: ((sInf S : 子半群 M) : 集合 M) = ⋂ s in S, ↑s
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_sInf (S : Set (Subsemigroup M)) : ((sInf S : Subsemigroup M) : Set M) = ⋂ s in S, ↑s :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Subsemigroup M)} {x : M}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[to_additive (attr := simp)]

中文:
定理 mem_sInf
  条件: {S : 集合 (子半群 M)} {x : M}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (Subsemigroup M)} {x : M} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[to_additive (attr := simp)]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> Subsemigroup M} {x : M}
  statement: x in ⨅ i, S i ↔ forall i, x in S i
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 子半群 M} {x : M}
  结论: x in ⨅ i, S i ↔ 对任意 i, x in S i
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> Subsemigroup M} {x : M} : x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> Subsemigroup M}
  statement: (↑(⨅ i, S i) : Set M) = ⋂ i, S i
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 子半群 M}
  结论: (↑(⨅ i, S i) : 集合 M) = ⋂ i, S i
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- subsemigroups of a monoid form a complete lattice. -/
@[to_additive /-- The `AddSubsemigroup`s of an `AddMonoid` form a complete lattice. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subsemigroup M)
  body: { completeLatticeOfInf (Subsemigroup M) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ hx => (notMem_bot hx).elim
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sIn

中文:
实例 :
  签名: 完备格 (子半群 M)
  定义体: { completeLatticeOfInf (Subsemigroup M) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ hx => (notMem_bot hx).elim
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sIn

Depends on / 依赖: And.left, And.right, InfSet, InfSet.sInf, IsGLB.of_image, SetLike, SetLike.coe_subset_coe, Subsemigroup, bot_le, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_biInf, le_inf, le_top, mem_top, notMem_bot, of_image
-/
instance : CompleteLattice (Subsemigroup M) :=
  { completeLatticeOfInf (Subsemigroup M) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun _ _ hx => (notMem_bot hx).elim
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/-- The `Subsemigroup` generated by a set. -/
@[to_additive /-- The `AddSubsemigroup` generated by a set -/]
/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set M)
  body: sInf { S | s subseteq S }

@[to_additive]

中文:
定义 closure
  签名: (s : 集合 M)
  定义体: sInf { S | s subseteq S }

@[to_additive]

Depends on / 依赖: subseteq
-/
def closure (s : Set M) : Subsemigroup M :=
  sInf { S | s subseteq S }

@[to_additive]
/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : M}
  statement: x in closure s ↔ forall S : Subsemigroup M, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : M}
  结论: x in closure s ↔ 对任意 S : 子半群 M, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : M} : x in closure s ↔ forall S : Subsemigroup M, s subseteq S -> x in S :=
  mem_sInf

/-- The subsemigroup generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 (rule_sets := [SetLike]))
  /-- The `AddSubsemigroup` generated by a set includes the set. -/]
/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  statement: s subseteq closure s
  proof: fun _ hx => mem_closure.2 fun _ hS => hS hx

@[to_additive (attr := aesop 80% (rule_sets := [SetLike]))]

中文:
定理 subset_closure
  结论: s subseteq closure s
  证明: fun _ hx => mem_closure.2 fun _ hS => hS hx

@[to_additive (attr := aesop 80% (rule_sets := [SetLike]))]

Depends on / 依赖: mem_closure
-/
theorem subset_closure : s subseteq closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[to_additive (attr := aesop 80% (rule_sets := [SetLike]))]
/--
theorem `mem_closure_of_mem` / 定理 `mem_closure_of_mem`

English:
theorem mem_closure_of_mem
  given: {s : Set M} {x : M} (hx : x in s)
  statement: x in closure s
  proof: subset_closure hx

@[to_additive]

中文:
定理 mem_closure_of_mem
  条件: {s : 集合 M} {x : M} (hx : x in s)
  结论: x in closure s
  证明: subset_closure hx

@[to_additive]

Depends on / 依赖: subset_closure
-/
theorem mem_closure_of_mem {s : Set M} {x : M} (hx : x in s) : x in closure s := subset_closure hx

@[to_additive]
/--
theorem `notMem_of_notMem_closure` / 定理 `notMem_of_notMem_closure`

English:
theorem notMem_of_notMem_closure
  given: {P : M} (hP : P ∉ closure s)
  statement: P ∉ s
  proof: fun h =>
  hP (subset_closure h)

中文:
定理 notMem_of_notMem_closure
  条件: {P : M} (hP : P ∉ closure s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure h)
-/
theorem notMem_of_notMem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

variable {S}

open Set

/-- A subsemigroup `S` includes `closure s` if and only if it includes `s`. -/
@[to_additive (attr := simp)
  /-- An additive subsemigroup `S` includes `closure s` if and only if it includes `s` -/]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  statement: closure s <= S ↔ s subseteq S
  proof: ⟨Subset.trans subset_closure, fun h => sInf_le h⟩

中文:
定理 closure_le
  结论: closure s <= S ↔ s subseteq S
  证明: ⟨Subset.trans subset_closure, fun h => sInf_le h⟩

Depends on / 依赖: Subset, Subset.trans, sInf_le, subset_closure
-/
theorem closure_le : closure s <= S ↔ s subseteq S :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩

/-- subsemigroup closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive (attr := gcongr) /-- Additive subsemigroup closure of a set is monotone in its
argument: if `s ⊆ t`, then `closure s ≤ closure t` -/]
/--
theorem `closure_mono` / 定理 `closure_mono`

English:
theorem closure_mono
  given: ⦃s t
  statement: Set M⦄ (h : s subseteq t) : closure s <= closure t
  proof: closure_le.2 Subset.trans h subset_closure

@[to_additive]

中文:
定理 closure_mono
  条件: ⦃s t
  结论: 集合 M⦄ (h : s subseteq t) : closure s <= closure t
  证明: closure_le.2 Subset.trans h subset_closure

@[to_additive]

Depends on / 依赖: Subset, Subset.trans, closure_le, subset_closure
-/
theorem closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : closure s <= closure t :=
closure_le.2 Subset.trans h subset_closure

@[to_additive]
/--
theorem `closure_eq_of_le` / 定理 `closure_eq_of_le`

English:
theorem closure_eq_of_le
  given: (h₁ : s subseteq S) (h₂ : S <= closure s)
  statement: closure s = S
  proof: le_antisymm (closure_le.2 h₁) h₂

中文:
定理 closure_eq_of_le
  条件: (h₁ : s subseteq S) (h₂ : S <= closure s)
  结论: closure s = S
  证明: le_antisymm (closure_le.2 h₁) h₂

Depends on / 依赖: closure_le, le_antisymm
-/
theorem closure_eq_of_le (h₁ : s subseteq S) (h₂ : S <= closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for additive closure membership. If
  `p` holds for all elements of `s`, and is preserved under addition, then `p` holds for all
  elements of the additive closure of `s`. -/]
/--
theorem `closure_induction` / 定理 `closure_induction`

English:
theorem closure_induction
  statement: {p : (x : M) -> x in closure s -> Prop}
  proof: let S : Subsemigroup M :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (S := S)

中文:
定理 closure_induction
  结论: {p : (x : M) -> x in closure s -> 命题}
  证明: let S : Subsemigroup M :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (S := S)

Depends on / 依赖: Subsemigroup, carrier, closure_le, mul_mem, subset_closure
-/
theorem closure_induction {p : (x : M) -> x in closure s -> Prop}
    (mem : forall (x) (h : x in s), p x (subset_closure h))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closure s) :
    p x hx :=
  let S : Subsemigroup M :=
    { carrier := { x | exists hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (S := S)

/-- An induction principle for closure membership for predicates with two arguments. -/
@[to_additive (attr := elab_as_elim) /-- An induction principle for additive closure membership for
  predicates with two arguments. -/]
/--
theorem `closure_induction₂` / 定理 `closure_induction₂`

English:
theorem closure_induction₂
  statement: {p : (x y : M) -> x in closure s -> y in closure s -> Prop}
  proof: by
  induction hx using closure_induction with
  | mem z hz => induction hy using closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

中文:
定理 closure_induction₂
  结论: {p : (x y : M) -> x in closure s -> y in closure s -> 命题}
  证明: by
  induction hx using closure_induction with
  | mem z hz => induction hy using closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

Depends on / 依赖: closure_induction, mul_left, mul_right
-/
theorem closure_induction₂ {p : (x y : M) -> x in closure s -> y in closure s -> Prop}
    (mem : forall (x) (y) (hx : x in s) (hy : y in s), p x y (subset_closure hx) (subset_closure hy))
    (mul_left : forall x y z hx hy hz, p x z hx hz -> p y z hy hz -> p (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz, p z x hz hx -> p z y hz hy -> p z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x in closure s) (hy : y in closure s) : p x y hx hy := by
  induction hx using closure_induction with
  | mem z hz => induction hy using closure_induction with
    | mem _ h => exact mem _ _ hz h
    | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ hy h₁ h₂

/-- If `s` is a dense set in a magma `M`, `Subsemigroup.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim) /-- If `s` is a dense set in an additive monoid `M`,
  `AddSubsemigroup.closure s = ⊤`, then in order to prove that some predicate `p` holds
  for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify that `p x` and `p y` imply
  `p (x + y)`. -/]
/--
theorem `dense_induction` / 定理 `dense_induction`

English:
theorem dense_induction
  statement: {p : M -> Prop} (s : Set M) (closure : closure s = ⊤)
  proof: by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

中文:
定理 dense_induction
  结论: {p : M -> 命题} (s : 集合 M) (closure : closure s = ⊤)
  证明: by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

Depends on / 依赖: closure, closure.symm, closure_induction, mem_top
-/
theorem dense_induction {p : M -> Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : forall x in s, p x) (mul : forall x y, p x -> p y -> p (x * y)) (x : M) :
    p x := by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/-! The argument `s : Set M` is explicit in `Subsemigroup.dense_induction` because the type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` without creating
metavariables, as in the following example. -/

example {p : M -> Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : forall x in s, p x) (mul : forall x y, p x -> p y -> p (x * y)) (x : M) :
    p x := by
  induction x using dense_induction s with
  | closure => exact closure
  | mem x hx => exact mem x hx
  | mul _ _ h₁ h₂ => exact mul _ _ h₁ h₂

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive /-- `closure` forms a Galois insertion with the coercion to set. -/]
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure M _) SetLike.coe
  body: GaloisConnection.toGaloisInsertion (fun _ _ => closure_le) fun _ => subset_closure

中文:
定义 gi
  签名: : Galois嵌入 (@closure M _) 集合状.coe
  定义体: GaloisConnection.toGaloisInsertion (fun _ _ => closure_le) fun _ => subset_closure
-/
protected def gi : GaloisInsertion (@closure M _) SetLike.coe :=
  GaloisConnection.toGaloisInsertion (fun _ _ => closure_le) fun _ => subset_closure

variable {M}

/-- Closure of a subsemigroup `S` equals `S`. -/
@[to_additive (attr := simp) /-- Additive closure of an additive subsemigroup `S` equals `S` -/]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  statement: closure (S : Set M) = S
  proof: (Subsemigroup.gi M).l_u_eq S

@[to_additive (attr := simp)]

中文:
定理 closure_eq
  结论: closure (S : 集合 M) = S
  证明: (Subsemigroup.gi M).l_u_eq S

@[to_additive (attr := simp)]

Depends on / 依赖: Subsemigroup, Subsemigroup.gi, l_u_eq
-/
theorem closure_eq : closure (S : Set M) = S :=
  (Subsemigroup.gi M).l_u_eq S

@[to_additive (attr := simp)]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set M) = ⊥
  proof: (Subsemigroup.gi M).gc.l_bot

@[to_additive (attr := simp)]

中文:
定理 closure_empty
  结论: closure (∅ : 集合 M) = ⊥
  证明: (Subsemigroup.gi M).gc.l_bot

@[to_additive (attr := simp)]

Depends on / 依赖: Subsemigroup, Subsemigroup.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Subsemigroup.gi M).gc.l_bot

@[to_additive (attr := simp)]
/--
theorem `closure_univ` / 定理 `closure_univ`

English:
theorem closure_univ
  statement: closure (univ : Set M) = ⊤
  proof: @coe_top M _ ▸ closure_eq ⊤

@[to_additive]

中文:
定理 closure_univ
  结论: closure (univ : 集合 M) = ⊤
  证明: @coe_top M _ ▸ closure_eq ⊤

@[to_additive]

Depends on / 依赖: closure_eq, coe_top
-/
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤

@[to_additive]
/--
theorem `closure_union` / 定理 `closure_union`

English:
theorem closure_union
  given: (s t : Set M)
  statement: closure (s union t) = closure s ⊔ closure t
  proof: (Subsemigroup.gi M).gc.l_sup

@[to_additive]

中文:
定理 closure_union
  条件: (s t : 集合 M)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (Subsemigroup.gi M).gc.l_sup

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set M) : closure (s union t) = closure s ⊔ closure t :=
  (Subsemigroup.gi M).gc.l_sup

@[to_additive]
/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set M)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (Subsemigroup.gi M).gc.l_iSup

@[to_additive]

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> 集合 M)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (Subsemigroup.gi M).gc.l_iSup

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemigroup.gi M).gc.l_iSup

@[to_additive]
/--
theorem `closure_singleton_le_iff_mem` / 定理 `closure_singleton_le_iff_mem`

English:
theorem closure_singleton_le_iff_mem
  given: (m : M) (p : Subsemigroup M)
  statement: closure {m} <= p ↔ m in p
  proof: by
  rw [closure_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]

@[to_additive]

中文:
定理 closure_singleton_le_iff_mem
  条件: (m : M) (p : 子半群 M)
  结论: closure {m} <= p ↔ m in p
  证明: by
  rw [closure_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]

@[to_additive]

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, singleton_subset_iff
-/
theorem closure_singleton_le_iff_mem (m : M) (p : Subsemigroup M) : closure {m} <= p ↔ m in p := by
  rw [closure_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]

@[to_additive]
/--
theorem `mem_iSup` / 定理 `mem_iSup`

English:
theorem mem_iSup
  given: {ι : Sort*} (p : ι -> Subsemigroup M) {m : M}
  proof: by
  rw [← closure_singleton_le_iff_mem]; rw [le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]

中文:
定理 mem_iSup
  条件: {ι : 类型层*} (p : ι -> 子半群 M) {m : M}
  证明: by
  rw [← closure_singleton_le_iff_mem]; rw [le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]

Depends on / 依赖: closure_singleton_le_iff_mem, le_iSup_iff
-/
theorem mem_iSup {ι : Sort*} (p : ι -> Subsemigroup M) {m : M} :
    (m in ⨆ i, p i) ↔ forall N, (forall i, p i <= N) -> m in N := by
  rw [← closure_singleton_le_iff_mem]; rw [le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]
/--
theorem `iSup_eq_closure` / 定理 `iSup_eq_closure`

English:
theorem iSup_eq_closure
  given: {ι : Sort*} (p : ι -> Subsemigroup M)
  proof: by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]

中文:
定理 iSup_eq_closure
  条件: {ι : 类型层*} (p : ι -> 子半群 M)
  证明: by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]

Depends on / 依赖: Subsemigroup, Subsemigroup.closure_eq, Subsemigroup.closure_iUnion, closure_eq, closure_iUnion, simp_rw
-/
theorem iSup_eq_closure {ι : Sort*} (p : ι -> Subsemigroup M) :
    ⨆ i, p i = Subsemigroup.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Subsemigroup.closure_iUnion, Subsemigroup.closure_eq]

end Subsemigroup

namespace MulHom

variable [Mul N]

open Subsemigroup

/-- If two mul homomorphisms are equal on a set, then they are equal on its subsemigroup closure. -/
@[to_additive /-- If two add homomorphisms are equal on a set,
  then they are equal on its additive subsemigroup closure. -/]
/--
theorem `eqOn_closure` / 定理 `eqOn_closure`

English:
theorem eqOn_closure
  given: {f g : M ->ₙ* N} {s : Set M} (h : Set.EqOn f g s)
  proof: show closure s <= f.eqLocus g from closure_le.2 h

@[to_additive]

中文:
定理 eqOn_closure
  条件: {f g : M ->ₙ* N} {s : 集合 M} (h : 集合.EqOn f g s)
  证明: show closure s <= f.eqLocus g from closure_le.2 h

@[to_additive]

Depends on / 依赖: closure, closure_le, eqLocus, f.eqLocus
-/
theorem eqOn_closure {f g : M ->ₙ* N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocus g from closure_le.2 h

@[to_additive]
/--
theorem `eq_of_eqOn_dense` / 定理 `eq_of_eqOn_dense`

English:
theorem eq_of_eqOn_dense
  given: {s : Set M} (hs : closure s = ⊤) {f g : M ->ₙ* N} (h : s.EqOn f g)
  proof: eq_of_eqOn_top hs ▸ eqOn_closure h

中文:
定理 eq_of_eqOn_dense
  条件: {s : 集合 M} (hs : closure s = ⊤) {f g : M ->ₙ* N} (h : s.EqOn f g)
  证明: eq_of_eqOn_top hs ▸ eqOn_closure h

Depends on / 依赖: eqOn_closure, eq_of_eqOn_top
-/
theorem eq_of_eqOn_dense {s : Set M} (hs : closure s = ⊤) {f g : M ->ₙ* N} (h : s.EqOn f g) :
    f = g :=
eq_of_eqOn_top hs ▸ eqOn_closure h

end MulHom

end NonAssoc

section Assoc

namespace MulHom

open Subsemigroup

/-- Let `s` be a subset of a semigroup `M` such that the closure of `s` is the whole semigroup.
Then `MulHom.ofDense` defines a mul homomorphism from `M` asking for a proof
of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive]
/--
Definition of `ofDense` / `ofDense` 的定义

English:
definition ofDense
  signature: {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
  body: f
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) y x

中文:
定义 ofDense
  签名: {M N} [半群 M] [半群 N] {s : 集合 M} (f : M -> N) (hs : closure s = ⊤)
  定义体: f
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) y x
-/
def ofDense {M N} [Semigroup M] [Semigroup N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
    (hmul : forall (x), forall y in s, f (x * y) = f x * f y) :
    M ->ₙ* N where
  toFun := f
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy)
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) y x

/-- Let `s` be a subset of an additive semigroup `M` such that the closure of `s` is the whole
semigroup. Then `AddHom.ofDense` defines an additive homomorphism from `M` asking for a proof
of `f (x + y) = f x + f y` only for `y ∈ s`. -/
add_decl_doc AddHom.ofDense

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_ofDense` / 定理 `coe_ofDense`

English:
theorem coe_ofDense
  statement: [Semigroup M] [Semigroup N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
  proof: rfl

中文:
定理 coe_ofDense
  结论: [半群 M] [半群 N] {s : 集合 M} (f : M -> N) (hs : closure s = ⊤)
  证明: rfl
-/
theorem coe_ofDense [Semigroup M] [Semigroup N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
    (hmul) : (ofDense f hs hmul : M -> N) = f :=
  rfl

end MulHom

end Assoc
