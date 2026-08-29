/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Submonoids: `CompleteLattice` structure

This file defines a `CompleteLattice` structure on `Submonoid`s, define the closure of a set as the
minimal submonoid that includes this set, and prove a few results about extending properties from a
dense set (i.e. a set with `closure s = ⊤`) to the whole monoid, see `Submonoid.dense_induction` and
`MonoidHom.ofClosureEqTopLeft`/`MonoidHom.ofClosureEqTopRight`.

## Main definitions

For each of the following definitions in the `Submonoid` namespace, there is a corresponding
definition in the `AddSubmonoid` namespace.

* `Submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `Submonoid`.
* `Submonoid.closure` : monoid closure of a set, i.e., the least submonoid that includes the set.
* `Submonoid.gi` : `closure : Set M → Submonoid M` and coercion `coe : Submonoid M → Set M`
  form a `GaloisInsertion`;
* `MonoidHom.eqLocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `MonoidHom.ofClosureEqTopRight`: if a map `f : M → N` between two monoids satisfies
  `f 1 = 1` and `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid
  homomorphism. E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is
  an additive monoid homomorphism.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `Submonoid M` does not actually require `Monoid M`, instead requiring only the weaker
`MulOneClass M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `Submonoid` is implemented by extending `Subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M : Type*} {N : Type*}
variable {A : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}
variable [AddZeroClass A] {t : Set A}

namespace Submonoid

variable (S : Submonoid M)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Submonoid M)
  body: ⟨fun s =>
    { carrier := ⋂ t in s, ↑t
      one_mem' := Set.mem_biInter fun i _ => i.one_mem
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: 下确界集 (子幺半群 M)
  定义体: ⟨fun s =>
    { carrier := ⋂ t in s, ↑t
      one_mem' := Set.mem_biInter fun i _ => i.one_mem
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.mem_biInter, Set.mem_iInter, carrier, i.mul_mem, i.one_mem, mem_biInter, mul_mem, one_mem
-/
instance : InfSet (Submonoid M) :=
  ⟨fun s =>
    { carrier := ⋂ t in s, ↑t
      one_mem' := Set.mem_biInter fun i _ => i.one_mem
      mul_mem' := fun hx hy =>
        Set.mem_biInter fun i h =>
          i.mul_mem (by apply Set.mem_iInter₂.1 hx i h) (by apply Set.mem_iInter₂.1 hy i h) }⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Submonoid M))
  statement: ((sInf S : Submonoid M) : Set M) = ⋂ s in S, ↑s
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_sInf
  条件: (S : 集合 (子幺半群 M))
  结论: ((sInf S : 子幺半群 M) : 集合 M) = ⋂ s in S, ↑s
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_sInf (S : Set (Submonoid M)) : ((sInf S : Submonoid M) : Set M) = ⋂ s in S, ↑s :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Submonoid M)} {x : M}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

@[to_additive (attr := simp)]

中文:
定理 mem_sInf
  条件: {S : 集合 (子幺半群 M)} {x : M}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (Submonoid M)} {x : M} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

@[to_additive (attr := simp)]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> Submonoid M} {x : M}
  statement: x in ⨅ i, S i ↔ forall i, x in S i
  proof: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> 子幺半群 M} {x : M}
  结论: x in ⨅ i, S i ↔ 对任意 i, x in S i
  证明: by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> Submonoid M} {x : M} : x in ⨅ i, S i ↔ forall i, x in S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> Submonoid M}
  statement: (↑(⨅ i, S i) : Set M) = ⋂ i, S i
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> 子幺半群 M}
  结论: (↑(⨅ i, S i) : 集合 M) = ⋂ i, S i
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive /-- The `AddSubmonoid`s of an `AddMonoid` form a complete lattice. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Submonoid M)
  body: { (completeLatticeOfInf (Submonoid M)) fun _ =>
      .of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S _ hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

中文:
实例 :
  签名: 完备格 (子幺半群 M)
  定义体: { (completeLatticeOfInf (Submonoid M)) fun _ =>
      .of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S _ hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

Depends on / 依赖: And.left, And.right, InfSet, InfSet.sInf, S.one_mem, SetLike, SetLike.coe_subset_coe, Submonoid, bot_le, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_biInf, le_inf, le_top, mem_bot, mem_top, of_image, one_mem
-/
instance : CompleteLattice (Submonoid M) :=
  { (completeLatticeOfInf (Submonoid M)) fun _ =>
      .of_image SetLike.coe_subset_coe isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S _ hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _ _ _ ha hb _ hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/-- The `Submonoid` generated by a set. -/
@[to_additive /-- The `AddSubmonoid` generated by a set -/]
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
def closure (s : Set M) : Submonoid M :=
  sInf { S | s subseteq S }

@[to_additive]
/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : M}
  statement: x in closure s ↔ forall S : Submonoid M, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : M}
  结论: x in closure s ↔ 对任意 S : 子幺半群 M, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : M} : x in closure s ↔ forall S : Submonoid M, s subseteq S -> x in S :=
  mem_sInf

/-- The submonoid generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 (rule_sets := [SetLike]))
  /-- The `AddSubmonoid` generated by a set includes the set. -/]
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

/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[to_additive (attr := simp)
/-- An additive submonoid `S` includes `closure s` if and only if it includes `s`. -/]
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

/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive (attr := gcongr)
  /-- Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
  then `closure s ≤ closure t`. -/]
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

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[to_additive (attr := elab_as_elim)
  /-- An induction principle for additive closure membership. If `p` holds for `0` and all
  elements of `s`, and is preserved under addition, then `p` holds for all elements of the
  additive closure of `s`. -/]
/--
theorem `closure_induction` / 定理 `closure_induction`

English:
theorem closure_induction
  statement: {s : Set M} {motive : (x : M) -> x in closure s -> Prop}
  proof: let S : Submonoid M :=
    { carrier := { x | exists hx, motive x hx }
      one_mem' := ⟨_, one⟩
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (S := S)

中文:
定理 closure_induction
  结论: {s : 集合 M} {motive : (x : M) -> x in closure s -> 命题}
  证明: let S : Submonoid M :=
    { carrier := { x | exists hx, motive x hx }
      one_mem' := ⟨_, one⟩
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (S := S)

Depends on / 依赖: Submonoid, carrier, closure_le, motive, mul_mem, one_mem, subset_closure
-/
theorem closure_induction {s : Set M} {motive : (x : M) -> x in closure s -> Prop}
    (mem : forall (x) (h : x in s), motive x (subset_closure h)) (one : motive 1 (one_mem _))
    (mul : forall x y hx hy, motive x hx -> motive y hy -> motive (x * y) (mul_mem hx hy)) {x}
    (hx : x in closure s) : motive x hx :=
  let S : Submonoid M :=
    { carrier := { x | exists hx, motive x hx }
      one_mem' := ⟨_, one⟩
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx closure_le (S := S)

/-- An induction principle for closure membership for predicates with two arguments. -/
@[to_additive (attr := elab_as_elim)
  /-- An induction principle for additive closure membership for predicates with two arguments. -/]
/--
theorem `closure_induction₂` / 定理 `closure_induction₂`

English:
theorem closure_induction₂
  statement: {motive : (x y : M) -> x in closure s -> y in closure s -> Prop}
  proof: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂

中文:
定理 closure_induction₂
  结论: {motive : (x y : M) -> x in closure s -> y in closure s -> 命题}
  证明: by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂

Depends on / 依赖: closure_induction, mul_left, mul_right, one_left, one_right, subset_closure
-/
theorem closure_induction₂ {motive : (x y : M) -> x in closure s -> y in closure s -> Prop}
    (mem : forall (x) (y) (hx : x in s) (hy : y in s), motive x y (subset_closure hx) (subset_closure hy))
    (one_left : forall x hx, motive 1 x (one_mem _) hx) (one_right : forall x hx, motive x 1 hx (one_mem _))
    (mul_left : forall x y z hx hy hz,
      motive x z hx hz -> motive y z hy hz -> motive (x * y) z (mul_mem hx hy) hz)
    (mul_right : forall x y z hx hy hz,
      motive z x hz hx -> motive z y hz hy -> motive z (x * y) hz (mul_mem hx hy))
    {x y : M} (hx : x in closure s) (hy : y in closure s) : motive x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂

/-- If `s` is a dense set in a monoid `M`, `Submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[to_additive (attr := elab_as_elim)
  /-- If `s` is a dense set in an additive monoid `M`, `AddSubmonoid.closure s = ⊤`, then in
  order to prove that some predicate `p` holds for all `x : M` it suffices to verify `p x` for
  `x ∈ s`, verify `p 0`, and verify that `p x` and `p y` imply `p (x + y)`. -/]
/--
theorem `dense_induction` / 定理 `dense_induction`

English:
theorem dense_induction
  statement: {motive : M -> Prop} (s : Set M) (closure : closure s = ⊤)
  proof: by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | one => exact one
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

中文:
定理 dense_induction
  结论: {motive : M -> 命题} (s : 集合 M) (closure : closure s = ⊤)
  证明: by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | one => exact one
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

Depends on / 依赖: closure, closure.symm, closure_induction, mem_top
-/
theorem dense_induction {motive : M -> Prop} (s : Set M) (closure : closure s = ⊤)
    (mem : forall x in s, motive x) (one : motive 1) (mul : forall x y, motive x -> motive y -> motive (x * y))
    (x : M) : motive x := by
  induction closure.symm ▸ mem_top x using closure_induction with
  | mem _ h => exact mem _ h
  | one => exact one
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/-! The argument `s : Set M` is explicit in `Submonoid.dense_induction` because the type of the
induction variable, namely `x : M`, does not reference `x`. Making `s` explicit allows the user
to apply the induction principle while deferring the proof of `closure s = ⊤` without creating
metavariables, as in the following example. -/

example {p : M -> Prop} (s : Set M) (closure : closure s = ⊤) (mem : forall x in s, p x)
    (one : p 1) (mul : forall x y, p x -> p y -> p (x * y)) (x : M) : p x := by
  induction x using dense_induction s with
  | closure => exact closure
  | mem x hx => exact mem x hx
  | one => exact one
  | mul _ _ h₁ h₂ => exact mul _ _ h₁ h₂

/--
lemma `closure_eq_one_union` / 引理 `closure_eq_one_union`

English:
lemma closure_eq_one_union
  given: (s : Set M)
  proof: by
  apply le_antisymm
  · intro x hx
    induction hx using closure_induction with
| mem x hx => exact Or.inr Subsemigroup.subset_closure hx
| one => exact Or.inl by simp
    | mul x hx y hy hx hy =>
      push _ in _ at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all [mul_mem]
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (closure s)
    · exact Subsemigroup.closure_le.mpr subset_closure hx

中文:
引理 closure_eq_one_union
  条件: (s : 集合 M)
  证明: by
  apply le_antisymm
  · intro x hx
    induction hx using closure_induction with
| mem x hx => exact Or.inr Subsemigroup.subset_closure hx
| one => exact Or.inl by simp
    | mul x hx y hy hx hy =>
      push _ in _ at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all [mul_mem]
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (closure s)
    · exact Subsemigroup.closure_le.mpr subset_closure hx

Depends on / 依赖: And.intro, Or.inl, Or.inr, Subsemigroup, Subsemigroup.closure_le.mpr, Subsemigroup.subset_closure, all_goals, closure, closure_induction, closure_le, le_antisymm, mul_mem, one_mem, subset_closure
-/
lemma closure_eq_one_union (s : Set M) :
    closure s = {(1 : M)} union (Subsemigroup.closure s : Set M) := by
  apply le_antisymm
  · intro x hx
    induction hx using closure_induction with
| mem x hx => exact Or.inr Subsemigroup.subset_closure hx
| one => exact Or.inl by simp
    | mul x hx y hy hx hy =>
      push _ in _ at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all [mul_mem]
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (closure s)
    · exact Subsemigroup.closure_le.mpr subset_closure hx

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive /-- `closure` forms a Galois insertion with the coercion to set. -/]
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure M _) SetLike.coe where
  body: closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : Galois嵌入 (@closure M _) 集合状.coe where
  定义体: closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
-/
protected def gi : GaloisInsertion (@closure M _) SetLike.coe where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {M}

/-- Closure of a submonoid `S` equals `S`. -/
@[to_additive (attr := simp) /-- Additive closure of an additive submonoid `S` equals `S` -/]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  statement: closure (S : Set M) = S
  proof: (Submonoid.gi M).l_u_eq S

@[to_additive (attr := simp)]

中文:
定理 closure_eq
  结论: closure (S : 集合 M) = S
  证明: (Submonoid.gi M).l_u_eq S

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.gi, l_u_eq
-/
theorem closure_eq : closure (S : Set M) = S :=
  (Submonoid.gi M).l_u_eq S

@[to_additive (attr := simp)]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure (∅ : Set M) = ⊥
  proof: (Submonoid.gi M).gc.l_bot

@[to_additive (attr := simp)]

中文:
定理 closure_empty
  结论: closure (∅ : 集合 M) = ⊥
  证明: (Submonoid.gi M).gc.l_bot

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Submonoid.gi M).gc.l_bot

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
  proof: (Submonoid.gi M).gc.l_sup

@[to_additive]

中文:
定理 closure_union
  条件: (s t : 集合 M)
  结论: closure (s union t) = closure s ⊔ closure t
  证明: (Submonoid.gi M).gc.l_sup

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set M) : closure (s union t) = closure s ⊔ closure t :=
  (Submonoid.gi M).gc.l_sup

@[to_additive]
/--
theorem `sup_eq_closure` / 定理 `sup_eq_closure`

English:
theorem sup_eq_closure
  given: (N N' : Submonoid M)
  statement: N ⊔ N' = closure ((N : Set M) union (N' : Set M))
  proof: by
  simp_rw [closure_union, closure_eq]

@[to_additive]

中文:
定理 sup_eq_closure
  条件: (N N' : 子幺半群 M)
  结论: N ⊔ N' = closure ((N : 集合 M) union (N' : 集合 M))
  证明: by
  simp_rw [closure_union, closure_eq]

@[to_additive]

Depends on / 依赖: closure_eq, closure_union, simp_rw
-/
theorem sup_eq_closure (N N' : Submonoid M) : N ⊔ N' = closure ((N : Set M) union (N' : Set M)) := by
  simp_rw [closure_union, closure_eq]

@[to_additive]
/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set M)
  statement: closure (⋃ i, s i) = ⨆ i, closure (s i)
  proof: (Submonoid.gi M).gc.l_iSup

@[to_additive]

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> 集合 M)
  结论: closure (⋃ i, s i) = ⨆ i, closure (s i)
  证明: (Submonoid.gi M).gc.l_iSup

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Submonoid.gi M).gc.l_iSup

@[to_additive]
/--
theorem `closure_singleton_le_iff_mem` / 定理 `closure_singleton_le_iff_mem`

English:
theorem closure_singleton_le_iff_mem
  given: (m : M) (p : Submonoid M)
  statement: closure {m} <= p ↔ m in p
  proof: by
  rw [closure_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]

@[to_additive (attr := simp)]

中文:
定理 closure_singleton_le_iff_mem
  条件: (m : M) (p : 子幺半群 M)
  结论: closure {m} <= p ↔ m in p
  证明: by
  rw [closure_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_le, mem_coe, singleton_subset_iff
-/
theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} <= p ↔ m in p := by
  rw [closure_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]

@[to_additive (attr := simp)]
/--
theorem `closure_insert_one` / 定理 `closure_insert_one`

English:
theorem closure_insert_one
  given: (s : Set M)
  statement: closure (insert 1 s) = closure s
  proof: by
  rw [insert_eq]; rw [closure_union]; rw [sup_eq_right]; rw [closure_singleton_le_iff_mem]
  apply one_mem

@[to_additive]

中文:
定理 closure_insert_one
  条件: (s : 集合 M)
  结论: closure (insert 1 s) = closure s
  证明: by
  rw [insert_eq]; rw [closure_union]; rw [sup_eq_right]; rw [closure_singleton_le_iff_mem]
  apply one_mem

@[to_additive]

Depends on / 依赖: closure_singleton_le_iff_mem, closure_union, insert_eq, one_mem, sup_eq_right
-/
theorem closure_insert_one (s : Set M) : closure (insert 1 s) = closure s := by
  rw [insert_eq]; rw [closure_union]; rw [sup_eq_right]; rw [closure_singleton_le_iff_mem]
  apply one_mem

@[to_additive]
/--
theorem `mem_iSup` / 定理 `mem_iSup`

English:
theorem mem_iSup
  given: {ι : Sort*} (p : ι -> Submonoid M) {m : M}
  proof: by
  rw [← closure_singleton_le_iff_mem]; rw [le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]

中文:
定理 mem_iSup
  条件: {ι : 类型层*} (p : ι -> 子幺半群 M) {m : M}
  证明: by
  rw [← closure_singleton_le_iff_mem]; rw [le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]

Depends on / 依赖: closure_singleton_le_iff_mem, le_iSup_iff
-/
theorem mem_iSup {ι : Sort*} (p : ι -> Submonoid M) {m : M} :
    (m in ⨆ i, p i) ↔ forall N, (forall i, p i <= N) -> m in N := by
  rw [← closure_singleton_le_iff_mem]; rw [le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

@[to_additive]
/--
theorem `iSup_eq_closure` / 定理 `iSup_eq_closure`

English:
theorem iSup_eq_closure
  given: {ι : Sort*} (p : ι -> Submonoid M)
  proof: by
  simp_rw [Submonoid.closure_iUnion, Submonoid.closure_eq]

@[to_additive]

中文:
定理 iSup_eq_closure
  条件: {ι : 类型层*} (p : ι -> 子幺半群 M)
  证明: by
  simp_rw [Submonoid.closure_iUnion, Submonoid.closure_eq]

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.closure_eq, Submonoid.closure_iUnion, closure_eq, closure_iUnion, simp_rw
-/
theorem iSup_eq_closure {ι : Sort*} (p : ι -> Submonoid M) :
    ⨆ i, p i = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_iUnion, Submonoid.closure_eq]

@[to_additive]
/--
theorem `disjoint_def` / 定理 `disjoint_def`

English:
theorem disjoint_def
  given: {p₁ p₂ : Submonoid M}
  proof: by
  simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]

@[to_additive]

中文:
定理 disjoint_def
  条件: {p₁ p₂ : 子幺半群 M}
  证明: by
  simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]

@[to_additive]

Depends on / 依赖: SetLike, SetLike.le_def, and_imp, disjoint_iff_inf_le, le_def, mem_bot, mem_inf, simp_rw
-/
theorem disjoint_def {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ forall {x : M}, x in p₁ -> x in p₂ -> x = 1 := by
  simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]

@[to_additive]
/--
theorem `disjoint_def'` / 定理 `disjoint_def'`

English:
theorem disjoint_def'
  given: {p₁ p₂ : Submonoid M}
  proof: disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩

中文:
定理 disjoint_def'
  条件: {p₁ p₂ : 子幺半群 M}
  证明: disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩

Depends on / 依赖: disjoint_def, disjoint_def.trans, hxy.symm
-/
theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ forall {x y : M}, x in p₁ -> y in p₂ -> x = y -> x = 1 :=
disjoint_def.trans ⟨fun h _ _ hx hy hxy => h hx hxy.symm ▸ hy, fun h _ hx hx' => h hx hx' rfl⟩

variable {t : Set M}

@[to_additive] -- this must not be a simp-lemma as the conclusion applies to `hts`, causing loops
/--
lemma `closure_sdiff_eq_closure` / 引理 `closure_sdiff_eq_closure`

English:
lemma closure_sdiff_eq_closure
  given: (hts : t subseteq closure (s \ t))
  statement: closure (s \ t) = closure s
  proof: by
refine (closure_mono Set.sdiff_subset).antisymm closure_le.mpr fun x hxs => ?_
  by_cases hxt : x in t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
exact fun N hN => hN Set.mem_sdiff_of_mem hxs hxt

@[to_additive (attr := simp)]

中文:
引理 closure_sdiff_eq_closure
  条件: (hts : t subseteq closure (s \ t))
  结论: closure (s \ t) = closure s
  证明: by
refine (closure_mono Set.sdiff_subset).antisymm closure_le.mpr fun x hxs => ?_
  by_cases hxt : x in t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
exact fun N hN => hN Set.mem_sdiff_of_mem hxs hxt

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mem_sdiff_of_mem, Set.sdiff_subset, SetLike, SetLike.mem_coe, Submonoid, Submonoid.mem_closure, antisymm, closure_le, closure_le.mpr, closure_mono, mem_closure, mem_coe, mem_sdiff_of_mem, sdiff_subset
-/
lemma closure_sdiff_eq_closure (hts : t subseteq closure (s \ t)) : closure (s \ t) = closure s := by
refine (closure_mono Set.sdiff_subset).antisymm closure_le.mpr fun x hxs => ?_
  by_cases hxt : x in t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
exact fun N hN => hN Set.mem_sdiff_of_mem hxs hxt

@[to_additive (attr := simp)]
/--
lemma `closure_sdiff_singleton_one` / 引理 `closure_sdiff_singleton_one`

English:
lemma closure_sdiff_singleton_one
  given: (s : Set M)
  statement: closure (s \ {1}) = closure s
  proof: closure_sdiff_eq_closure by simp [one_mem]

中文:
引理 closure_sdiff_singleton_one
  条件: (s : 集合 M)
  结论: closure (s \ {1}) = closure s
  证明: closure_sdiff_eq_closure by simp [one_mem]

Depends on / 依赖: closure_sdiff_eq_closure, one_mem
-/
lemma closure_sdiff_singleton_one (s : Set M) : closure (s \ {1}) = closure s :=
closure_sdiff_eq_closure by simp [one_mem]

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive
  /-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid
  closure. -/]
/--
theorem `eqOn_closureM` / 定理 `eqOn_closureM`

English:
theorem eqOn_closureM
  given: {f g : M ->* N} {s : Set M} (h : Set.EqOn f g s)
  statement: Set.EqOn f g (closure s)
  proof: show closure s <= f.eqLocusM g from closure_le.2 h

@[to_additive]

中文:
定理 eqOn_closureM
  条件: {f g : M ->* N} {s : 集合 M} (h : 集合.EqOn f g s)
  结论: 集合.EqOn f g (closure s)
  证明: show closure s <= f.eqLocusM g from closure_le.2 h

@[to_additive]

Depends on / 依赖: closure, closure_le, eqLocusM, f.eqLocusM
-/
theorem eqOn_closureM {f g : M ->* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s <= f.eqLocusM g from closure_le.2 h

@[to_additive]
/--
theorem `eq_of_eqOn_denseM` / 定理 `eq_of_eqOn_denseM`

English:
theorem eq_of_eqOn_denseM
  given: {s : Set M} (hs : closure s = ⊤) {f g : M ->* N} (h : s.EqOn f g)
  proof: eq_of_eqOn_topM hs ▸ eqOn_closureM h

中文:
定理 eq_of_eqOn_denseM
  条件: {s : 集合 M} (hs : closure s = ⊤) {f g : M ->* N} (h : s.EqOn f g)
  证明: eq_of_eqOn_topM hs ▸ eqOn_closureM h

Depends on / 依赖: eqOn_closureM, eq_of_eqOn_topM
-/
theorem eq_of_eqOn_denseM {s : Set M} (hs : closure s = ⊤) {f g : M ->* N} (h : s.EqOn f g) :
    f = g :=
eq_of_eqOn_topM hs ▸ eqOn_closureM h

end MonoidHom

end NonAssoc

section Assoc

variable [Monoid M] [Monoid N] {s : Set M}

section IsUnit

/-- The submonoid consisting of the units of a monoid -/
@[to_additive /-- The additive submonoid consisting of the additive units of an additive monoid -/]
/--
Definition of `IsUnit.submonoid` / `IsUnit.submonoid` 的定义

English:
definition IsUnit.submonoid
  signature: (M : Type*) [Monoid M]
  body: Set.ofPred IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_ofPred_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred_eq] at *
    exact IsUnit.mul ha hb

@[to_additive]

中文:
定义 是单位.submonoid
  签名: (M : 类型) [幺半群 M]
  定义体: Set.ofPred IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_ofPred_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred_eq] at *
    exact IsUnit.mul ha hb

@[to_additive]

Depends on / 依赖: IsUnit, Set.ofPred, ofPred
-/
def IsUnit.submonoid (M : Type*) [Monoid M] : Submonoid M where
  carrier := Set.ofPred IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_ofPred_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred_eq] at *
    exact IsUnit.mul ha hb

@[to_additive]
/--
theorem `IsUnit.mem_submonoid_iff` / 定理 `IsUnit.mem_submonoid_iff`

English:
theorem IsUnit.mem_submonoid_iff
  given: {M : Type*} [Monoid M] (a : M)
  proof: by
  change a in Set.ofPred IsUnit ↔ IsUnit a
  rw [Set.mem_ofPred_eq]

中文:
定理 是单位.mem_submonoid_iff
  条件: {M : 类型} [幺半群 M] (a : M)
  证明: by
  change a in Set.ofPred IsUnit ↔ IsUnit a
  rw [Set.mem_ofPred_eq]

Depends on / 依赖: IsUnit, Set.mem_ofPred_eq, Set.ofPred, mem_ofPred_eq, ofPred
-/
theorem IsUnit.mem_submonoid_iff {M : Type*} [Monoid M] (a : M) :
    a in IsUnit.submonoid M ↔ IsUnit a := by
  change a in Set.ofPred IsUnit ↔ IsUnit a
  rw [Set.mem_ofPred_eq]

end IsUnit

/--
lemma `Submonoid.commute_coe_coe` / 引理 `Submonoid.commute_coe_coe`

English:
lemma Submonoid.commute_coe_coe
  statement: {S M : Type*} [Mul M] [SetLike S M]
  proof: by
  simp [commute_iff_eq, Subtype.ext_iff]

中文:
引理 子幺半群.commute_coe_coe
  结论: {S M : 类型} [乘法 M] [集合状 S M]
  证明: by
  simp [commute_iff_eq, Subtype.ext_iff]
-/
@[simp] lemma Submonoid.commute_coe_coe {S M : Type*} [Mul M] [SetLike S M]
    [MulMemClass S M] {s : S} {x y : s} : Commute (x : M) (y : M) ↔ Commute x y := by
  simp [commute_iff_eq, Subtype.ext_iff]

namespace MonoidHom

open Submonoid

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopLeft` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `x ∈ s`. -/
@[to_additive
  /-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
  the whole monoid. Then `AddMonoidHom.ofClosureEqTopLeft` defines an additive monoid
  homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `x ∈ s`. -/]
/--
Definition of `ofClosureMEqTopLeft` / `ofClosureMEqTopLeft` 的定义

English:
definition ofClosureMEqTopLeft
  signature: {M N} [Monoid M] [Monoid N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
  body: f
  map_one' := h1
  map_mul' x :=
    dense_induction (motive := _) _ hs hmul fun y => by rw [one_mul, h1, one_mul]
      (fun a b ha hb y => by rw [mul_assoc, ha, ha, hb, mul_assoc]) x

@[to_additive (attr := simp, norm_cast)]

中文:
定义 ofClosureMEqTopLeft
  签名: {M N} [幺半群 M] [幺半群 N] {s : 集合 M} (f : M -> N) (hs : closure s = ⊤)
  定义体: f
  map_one' := h1
  map_mul' x :=
    dense_induction (motive := _) _ hs hmul fun y => by rw [one_mul, h1, one_mul]
      (fun a b ha hb y => by rw [mul_assoc, ha, ha, hb, mul_assoc]) x

@[to_additive (attr := simp, norm_cast)]
-/
def ofClosureMEqTopLeft {M N} [Monoid M] [Monoid N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : forall x in s, forall (y), f (x * y) = f x * f y) :
    M ->* N where
  toFun := f
  map_one' := h1
  map_mul' x :=
    dense_induction (motive := _) _ hs hmul fun y => by rw [one_mul, h1, one_mul]
      (fun a b ha hb y => by rw [mul_assoc, ha, ha, hb, mul_assoc]) x

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_ofClosureMEqTopLeft` / 定理 `coe_ofClosureMEqTopLeft`

English:
theorem coe_ofClosureMEqTopLeft
  given: (f : M -> N) (hs : closure s = ⊤) (h1 hmul)
  proof: rfl

中文:
定理 coe_ofClosureMEqTopLeft
  条件: (f : M -> N) (hs : closure s = ⊤) (h1 hmul)
  证明: rfl
-/
theorem coe_ofClosureMEqTopLeft (f : M -> N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopLeft f hs h1 hmul) = f :=
  rfl

/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `MonoidHom.ofClosureEqTopRight` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive
  /-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is
  the whole monoid. Then `AddMonoidHom.ofClosureEqTopRight` defines an additive monoid
  homomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `y ∈ s`. -/]
/--
Definition of `ofClosureMEqTopRight` / `ofClosureMEqTopRight` 的定义

English:
definition ofClosureMEqTopRight
  signature: {M N} [Monoid M] [Monoid N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
  body: f
  map_one' := h1
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy) (by simp [h1])
      (fun y₁ y₂ (h₁ : forall _, f _ = f _ * f _) (h₂ : forall _, f _ = f _ * f _) x => by
        simp [← mul_assoc, h₁, h₂]) y x

@[to_additive (attr := simp, norm_cast)]

中文:
定义 ofClosureMEqTopRight
  签名: {M N} [幺半群 M] [幺半群 N] {s : 集合 M} (f : M -> N) (hs : closure s = ⊤)
  定义体: f
  map_one' := h1
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy) (by simp [h1])
      (fun y₁ y₂ (h₁ : forall _, f _ = f _ * f _) (h₂ : forall _, f _ = f _ * f _) x => by
        simp [← mul_assoc, h₁, h₂]) y x

@[to_additive (attr := simp, norm_cast)]
-/
def ofClosureMEqTopRight {M N} [Monoid M] [Monoid N] {s : Set M} (f : M -> N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : forall (x), forall y in s, f (x * y) = f x * f y) :
    M ->* N where
  toFun := f
  map_one' := h1
  map_mul' x y :=
    dense_induction _ hs (fun y hy x => hmul x y hy) (by simp [h1])
      (fun y₁ y₂ (h₁ : forall _, f _ = f _ * f _) (h₂ : forall _, f _ = f _ * f _) x => by
        simp [← mul_assoc, h₁, h₂]) y x

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_ofClosureMEqTopRight` / 定理 `coe_ofClosureMEqTopRight`

English:
theorem coe_ofClosureMEqTopRight
  given: (f : M -> N) (hs : closure s = ⊤) (h1 hmul)
  proof: rfl

中文:
定理 coe_ofClosureMEqTopRight
  条件: (f : M -> N) (hs : closure s = ⊤) (h1 hmul)
  证明: rfl
-/
theorem coe_ofClosureMEqTopRight (f : M -> N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopRight f hs h1 hmul) = f :=
  rfl

end MonoidHom

end Assoc
