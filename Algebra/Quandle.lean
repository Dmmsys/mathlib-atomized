/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property. If `R` is a rack and `act : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
act (act x y) = act x * act y * (act x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `act x x = x` for all `x`.

One example of a quandle (not yet in mathlib) is the action of a Lie
algebra on itself, defined by `act x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians. David Joyce introduced quandles in his thesis
[Joyce1982] to define an algebraic invariant of knot and link
complements that is analogous to the fundamental group of the
exterior, and he showed that the quandle associated to an oriented
knot is invariant up to orientation-reversed mirror image. Racks were
used by Fenn and Rourke for framed codimension-2 knots and
links in [FennRourke1992]. Unital shelves are discussed in [crans2017].

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `Shelf` is a type with a self-distributive action
* `UnitalShelf` is a shelf with a left and right unit
* `Rack` is a shelf whose action for each element is invertible
* `Quandle` is a rack whose action for an element fixes that element
* `Quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `ShelfHom` is homomorphisms of shelves, racks, and quandles.
* `Rack.EnvelGroup` gives the universal group the rack maps to as a conjugation quandle.
* `Rack.oppositeRack` gives the rack with the action replaced by its inverse.

## Main statements
* `Rack.EnvelGroup` is left adjoint to `Quandle.Conj` (`toEnvelGroup.map`).
  The universality statements are `toEnvelGroup.univ` and `toEnvelGroup.univ_uniq`.

## Implementation notes
"Unital racks" are uninteresting (see `Rack.assoc_iff_id`, `UnitalShelf.assoc`), so we do not
define them.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `Shelf.act x y`
* `x ◃⁻¹ y` is `Rack.inv_act x y`
* `S →◃ S'` is `ShelfHom S S'`

Use `open quandles` to use these.

## TODO

* If `g` is the Lie algebra of a Lie group `G`, then `(x ◃ y) = Ad (exp x) x` forms a quandle.
* If `X` is a symmetric space, then each point has a corresponding involution that acts on `X`,
  forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements
  of a module over `Z[t,t⁻¹]`.
* If `G` is a group, `H` a subgroup, and `z` in `H`, then there is a quandle `(G/H;z)` defined by
  `yH ◃ xH = yzy⁻¹xH`. Every homogeneous quandle (i.e., a quandle `Q` whose automorphism group acts
  transitively on `Q` as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/

@[expose] public section


open MulOpposite

universe u v

/--
Definition of `Shelf` / `Shelf` 的定义

English:
class Shelf
  parameters: (α : Type u)
  axioms and operations (2):
    - act : α -> α -> α
    - self_distrib : forall {x y z : α}, act x (act y z) = act (act x y) (act x z)

中文:
类 Shelf
  参数: (α : 类型u)
  公理与运算 (2 个):
    - act : α -> α -> α
    - self_distrib : 对任意 {x y z : α}, act x (act y z) = act (act x y) (act x z)
-/
class Shelf (α : Type u) where
  /-- The action of the `Shelf` over `α` -/
  act : α -> α -> α
  /-- A verification that `act` is self-distributive -/
  self_distrib : forall {x y z : α}, act x (act y z) = act (act x y) (act x z)

/--
Definition of `UnitalShelf` / `UnitalShelf` 的定义

English:
class UnitalShelf
  parameters: (α : Type u)
  extends: Shelf α, One α
  axioms and operations (2):
    - one_act : forall a : α, act 1 a = a
    - act_one : forall a : α, act a 1 = a

中文:
类 UnitalShelf
  参数: (α : 类型u)
  继承: Shelf α, One α
  公理与运算 (2 个):
    - one_act : 对任意 a : α, act 1 a = a
    - act_one : 对任意 a : α, act a 1 = a
-/
class UnitalShelf (α : Type u) extends Shelf α, One α where
  one_act : forall a : α, act 1 a = a
  act_one : forall a : α, act a 1 = a

attribute [instance 100] UnitalShelf.toOne

/-- The type of homomorphisms between shelves.
This is also the notion of rack and quandle homomorphisms.
-/
@[ext]
/--
Definition of `ShelfHom` / `ShelfHom` 的定义

English:
structure ShelfHom
  parameters: (S₁ : Type*) (S₂ : Type*) [Shelf S₁] [Shelf S₂]
  axioms and operations (2):
    - toFun : S₁ -> S₂
    - map_act' : forall {x y : S₁}, toFun (Shelf.act x y) = Shelf.act (toFun x) (toFun y)

中文:
结构 ShelfHom
  参数: (S₁ : 类型) (S₂ : 类型) [Shelf S₁] [Shelf S₂]
  公理与运算 (2 个):
    - toFun : S₁ -> S₂
    - map_act' : 对任意 {x y : S₁}, toFun (Shelf.act x y) = Shelf.act (toFun x) (toFun y)
-/
structure ShelfHom (S₁ : Type*) (S₂ : Type*) [Shelf S₁] [Shelf S₂] where
  /-- The function under the Shelf Homomorphism -/
  toFun : S₁ -> S₂
  /-- The homomorphism property of a Shelf Homomorphism -/
  map_act' : forall {x y : S₁}, toFun (Shelf.act x y) = Shelf.act (toFun x) (toFun y)

/--
Definition of `Rack` / `Rack` 的定义

English:
class Rack
  parameters: (α : Type u)
  extends: Shelf α
  axioms and operations (3):
    - invAct : α -> α -> α
    - left_inv : forall x, Function.LeftInverse (invAct x) (act x)
    - right_inv : forall x, Function.RightInverse (invAct x) (act x)

中文:
类 Rack
  参数: (α : 类型u)
  继承: Shelf α
  公理与运算 (3 个):
    - invAct : α -> α -> α
    - left_inv : 对任意 x, Function.LeftInverse (invAct x) (act x)
    - right_inv : 对任意 x, Function.RightInverse (invAct x) (act x)
-/
class Rack (α : Type u) extends Shelf α where
  /-- The inverse actions of the elements -/
  invAct : α -> α -> α
  /-- Proof of left inverse -/
  left_inv : forall x, Function.LeftInverse (invAct x) (act x)
  /-- Proof of right inverse -/
  right_inv : forall x, Function.RightInverse (invAct x) (act x)

/-- Action of a Shelf -/
scoped[Quandles] infixr:65 " ◃ " => Shelf.act

/-- Inverse Action of a Rack -/
scoped[Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct

/-- Shelf Homomorphism -/
scoped[Quandles] infixr:25 " ->◃ " => ShelfHom

open Quandles

namespace UnitalShelf
open Shelf

variable {S : Type*} [UnitalShelf S]

/--
lemma `act_act_self_eq` / 引理 `act_act_self_eq`

English:
lemma act_act_self_eq
  given: (x y : S)
  statement: (x ◃ y) ◃ x = x ◃ y
  proof: by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [act_one]
  rw [h]; rw [← Shelf.self_distrib]; rw [act_one]

中文:
引理 act_act_self_eq
  条件: (x y : S)
  结论: (x ◃ y) ◃ x = x ◃ y
  证明: by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [act_one]
  rw [h]; rw [← Shelf.self_distrib]; rw [act_one]

Depends on / 依赖: Shelf.self_distrib, act_one, self_distrib
-/
lemma act_act_self_eq (x y : S) : (x ◃ y) ◃ x = x ◃ y := by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [act_one]
  rw [h]; rw [← Shelf.self_distrib]; rw [act_one]

/--
lemma `act_idem` / 引理 `act_idem`

English:
lemma act_idem
  given: (x : S)
  statement: (x ◃ x) = x
  proof: by rw [← act_one x, ← Shelf.self_distrib, act_one]

中文:
引理 act_idem
  条件: (x : S)
  结论: (x ◃ x) = x
  证明: by rw [← act_one x, ← Shelf.self_distrib, act_one]

Depends on / 依赖: Shelf.self_distrib, act_one, self_distrib
-/
lemma act_idem (x : S) : (x ◃ x) = x := by rw [← act_one x, ← Shelf.self_distrib, act_one]

/--
lemma `act_self_act_eq` / 引理 `act_self_act_eq`

English:
lemma act_self_act_eq
  given: (x y : S)
  statement: x ◃ (x ◃ y) = x ◃ y
  proof: by
  have h : x ◃ (x ◃ y) = (x ◃ 1) ◃ (x ◃ y) := by rw [act_one]
  rw [h]; rw [← Shelf.self_distrib]; rw [one_act]

中文:
引理 act_self_act_eq
  条件: (x y : S)
  结论: x ◃ (x ◃ y) = x ◃ y
  证明: by
  have h : x ◃ (x ◃ y) = (x ◃ 1) ◃ (x ◃ y) := by rw [act_one]
  rw [h]; rw [← Shelf.self_distrib]; rw [one_act]

Depends on / 依赖: Shelf.self_distrib, act_one, one_act, self_distrib
-/
lemma act_self_act_eq (x y : S) : x ◃ (x ◃ y) = x ◃ y := by
  have h : x ◃ (x ◃ y) = (x ◃ 1) ◃ (x ◃ y) := by rw [act_one]
  rw [h]; rw [← Shelf.self_distrib]; rw [one_act]

/--
lemma `assoc` / 引理 `assoc`

English:
lemma assoc
  given: (x y z : S)
  statement: (x ◃ y) ◃ z = x ◃ y ◃ z
  proof: by
  rw [self_distrib]; rw [self_distrib]; rw [act_act_self_eq]; rw [act_self_act_eq]

中文:
引理 assoc
  条件: (x y z : S)
  结论: (x ◃ y) ◃ z = x ◃ y ◃ z
  证明: by
  rw [self_distrib]; rw [self_distrib]; rw [act_act_self_eq]; rw [act_self_act_eq]

Depends on / 依赖: act_act_self_eq, act_self_act_eq, self_distrib
-/
lemma assoc (x y z : S) : (x ◃ y) ◃ z = x ◃ y ◃ z := by
  rw [self_distrib]; rw [self_distrib]; rw [act_act_self_eq]; rw [act_self_act_eq]

end UnitalShelf

namespace Rack

variable {R : Type*} [Rack R]

export Shelf (self_distrib)

/--
Definition of `act'` / `act'` 的定义

English:
definition act'
  signature: (x : R)
  body: Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x

@[simp]

中文:
定义 act'
  签名: (x : R)
  定义体: Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x

@[simp]

Depends on / 依赖: Shelf.act
-/
def act' (x : R) : R ≃ R where
  toFun := Shelf.act x
  invFun := invAct x
  left_inv := left_inv x
  right_inv := right_inv x

@[simp]
/--
theorem `act'_apply` / 定理 `act'_apply`

English:
theorem act'_apply
  given: (x y : R)
  statement: act' x y = x ◃ y
  proof: rfl

@[simp]

中文:
定理 act'_apply
  条件: (x y : R)
  结论: act' x y = x ◃ y
  证明: rfl

@[simp]
-/
theorem act'_apply (x y : R) : act' x y = x ◃ y :=
  rfl

@[simp]
/--
theorem `act'_symm_apply` / 定理 `act'_symm_apply`

English:
theorem act'_symm_apply
  given: (x y : R)
  statement: (act' x).symm y = x ◃⁻¹ y
  proof: rfl

@[simp]

中文:
定理 act'_symm_apply
  条件: (x y : R)
  结论: (act' x).symm y = x ◃⁻¹ y
  证明: rfl

@[simp]
-/
theorem act'_symm_apply (x y : R) : (act' x).symm y = x ◃⁻¹ y :=
  rfl

@[simp]
/--
theorem `invAct_apply` / 定理 `invAct_apply`

English:
theorem invAct_apply
  given: (x y : R)
  statement: (act' x)⁻¹ y = x ◃⁻¹ y
  proof: rfl

@[simp]

中文:
定理 invAct_apply
  条件: (x y : R)
  结论: (act' x)⁻¹ y = x ◃⁻¹ y
  证明: rfl

@[simp]
-/
theorem invAct_apply (x y : R) : (act' x)⁻¹ y = x ◃⁻¹ y :=
  rfl

@[simp]
/--
theorem `invAct_act_eq` / 定理 `invAct_act_eq`

English:
theorem invAct_act_eq
  given: (x y : R)
  statement: x ◃⁻¹ x ◃ y = y
  proof: left_inv x y

@[simp]

中文:
定理 invAct_act_eq
  条件: (x y : R)
  结论: x ◃⁻¹ x ◃ y = y
  证明: left_inv x y

@[simp]

Depends on / 依赖: left_inv
-/
theorem invAct_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y :=
  left_inv x y

@[simp]
/--
theorem `act_invAct_eq` / 定理 `act_invAct_eq`

English:
theorem act_invAct_eq
  given: (x y : R)
  statement: x ◃ x ◃⁻¹ y = y
  proof: right_inv x y

中文:
定理 act_invAct_eq
  条件: (x y : R)
  结论: x ◃ x ◃⁻¹ y = y
  证明: right_inv x y

Depends on / 依赖: right_inv
-/
theorem act_invAct_eq (x y : R) : x ◃ x ◃⁻¹ y = y :=
  right_inv x y

/--
theorem `left_cancel` / 定理 `left_cancel`

English:
theorem left_cancel
  given: (x : R) {y y' : R}
  statement: x ◃ y = x ◃ y' ↔ y = y'
  proof: by
  constructor
  · apply (act' x).injective
  rintro rfl
  rfl

中文:
定理 left_cancel
  条件: (x : R) {y y' : R}
  结论: x ◃ y = x ◃ y' ↔ y = y'
  证明: by
  constructor
  · apply (act' x).injective
  rintro rfl
  rfl

Depends on / 依赖: injective
-/
theorem left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' := by
  constructor
  · apply (act' x).injective
  rintro rfl
  rfl

/--
theorem `left_cancel_inv` / 定理 `left_cancel_inv`

English:
theorem left_cancel_inv
  given: (x : R) {y y' : R}
  statement: x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y'
  proof: by
  constructor
  · apply (act' x).symm.injective
  rintro rfl
  rfl

中文:
定理 left_cancel_inv
  条件: (x : R) {y y' : R}
  结论: x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y'
  证明: by
  constructor
  · apply (act' x).symm.injective
  rintro rfl
  rfl

Depends on / 依赖: injective, symm.injective
-/
theorem left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' := by
  constructor
  · apply (act' x).symm.injective
  rintro rfl
  rfl

/--
theorem `self_distrib_inv` / 定理 `self_distrib_inv`

English:
theorem self_distrib_inv
  given: {x y z : R}
  statement: x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z
  proof: by
  rw [← left_cancel (x ◃⁻¹ y)]; rw [right_inv]; rw [← left_cancel x]; rw [right_inv]; rw [self_distrib]
  repeat' rw [right_inv]

中文:
定理 self_distrib_inv
  条件: {x y z : R}
  结论: x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z
  证明: by
  rw [← left_cancel (x ◃⁻¹ y)]; rw [right_inv]; rw [← left_cancel x]; rw [right_inv]; rw [self_distrib]
  repeat' rw [right_inv]

Depends on / 依赖: left_cancel, repeat, right_inv, self_distrib
-/
theorem self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ x ◃⁻¹ z := by
  rw [← left_cancel (x ◃⁻¹ y)]; rw [right_inv]; rw [← left_cancel x]; rw [right_inv]; rw [self_distrib]
  repeat' rw [right_inv]

/--
theorem `ad_conj` / 定理 `ad_conj`

English:
theorem ad_conj
  given: {R : Type*} [Rack R] (x y : R)
  statement: act' (x ◃ y) = act' x * act' y * (act' x)⁻¹
  proof: by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm

中文:
定理 ad_conj
  条件: {R : 类型} [Rack R] (x y : R)
  结论: act' (x ◃ y) = act' x * act' y * (act' x)⁻¹
  证明: by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm

Depends on / 依赖: eq_mul_inv_iff_mul_eq, self_distrib, self_distrib.symm
-/
theorem ad_conj {R : Type*} [Rack R] (x y : R) : act' (x ◃ y) = act' x * act' y * (act' x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm

/--
Instance `oppositeRack` / 实例 `oppositeRack`

English:
instance oppositeRack
  signature: : Rack Rᵐᵒᵖ where
  body: op (invAct (unop x) (unop y))
  self_distrib := by
    intro x y z
    induction x
    induction y
    induction z
    simp only [op_inj, unop_op]
    rw [self_distrib_inv]
  invAct x y := op (Shelf.act (unop x) (unop y))
  left_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
  ri

中文:
实例 oppositeRack
  签名: : Rack Rᵐᵒᵖ where
  定义体: op (invAct (unop x) (unop y))
  self_distrib := by
    intro x y z
    induction x
    induction y
    induction z
    simp only [op_inj, unop_op]
    rw [self_distrib_inv]
  invAct x y := op (Shelf.act (unop x) (unop y))
  left_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
  ri

Depends on / 依赖: invAct
-/
instance oppositeRack : Rack Rᵐᵒᵖ where
  act x y := op (invAct (unop x) (unop y))
  self_distrib := by
    intro x y z
    induction x
    induction y
    induction z
    simp only [op_inj, unop_op]
    rw [self_distrib_inv]
  invAct x y := op (Shelf.act (unop x) (unop y))
  left_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp
  right_inv := MulOpposite.rec' fun x => MulOpposite.rec' fun y => by simp

@[simp]
/--
theorem `op_act_op_eq` / 定理 `op_act_op_eq`

English:
theorem op_act_op_eq
  given: {x y : R}
  statement: op x ◃ op y = op (x ◃⁻¹ y)
  proof: rfl

@[simp]

中文:
定理 op_act_op_eq
  条件: {x y : R}
  结论: op x ◃ op y = op (x ◃⁻¹ y)
  证明: rfl

@[simp]
-/
theorem op_act_op_eq {x y : R} : op x ◃ op y = op (x ◃⁻¹ y) :=
  rfl

@[simp]
/--
theorem `op_invAct_op_eq` / 定理 `op_invAct_op_eq`

English:
theorem op_invAct_op_eq
  given: {x y : R}
  statement: op x ◃⁻¹ op y = op (x ◃ y)
  proof: rfl

@[simp]

中文:
定理 op_invAct_op_eq
  条件: {x y : R}
  结论: op x ◃⁻¹ op y = op (x ◃ y)
  证明: rfl

@[simp]
-/
theorem op_invAct_op_eq {x y : R} : op x ◃⁻¹ op y = op (x ◃ y) :=
  rfl

@[simp]
/--
theorem `self_act_act_eq` / 定理 `self_act_act_eq`

English:
theorem self_act_act_eq
  given: {x y : R}
  statement: (x ◃ x) ◃ y = x ◃ y
  proof: by rw [← right_inv x y, ← self_distrib]

@[simp]

中文:
定理 self_act_act_eq
  条件: {x y : R}
  结论: (x ◃ x) ◃ y = x ◃ y
  证明: by rw [← right_inv x y, ← self_distrib]

@[simp]

Depends on / 依赖: right_inv, self_distrib
-/
theorem self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y := by rw [← right_inv x y, ← self_distrib]

@[simp]
/--
theorem `self_invAct_invAct_eq` / 定理 `self_invAct_invAct_eq`

English:
theorem self_invAct_invAct_eq
  given: {x y : R}
  statement: (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y
  proof: by
  have h := @self_act_act_eq _ _ (op x) (op y)
  simpa using h

@[simp]

中文:
定理 self_invAct_invAct_eq
  条件: {x y : R}
  结论: (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y
  证明: by
  have h := @self_act_act_eq _ _ (op x) (op y)
  simpa using h

@[simp]

Depends on / 依赖: self_act_act_eq
-/
theorem self_invAct_invAct_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y := by
  have h := @self_act_act_eq _ _ (op x) (op y)
  simpa using h

@[simp]
/--
theorem `self_act_invAct_eq` / 定理 `self_act_invAct_eq`

English:
theorem self_act_invAct_eq
  given: {x y : R}
  statement: (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y
  proof: by
  rw [← left_cancel (x ◃ x)]
  rw [right_inv]
  rw [self_act_act_eq]
  rw [right_inv]

@[simp]

中文:
定理 self_act_invAct_eq
  条件: {x y : R}
  结论: (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y
  证明: by
  rw [← left_cancel (x ◃ x)]
  rw [right_inv]
  rw [self_act_act_eq]
  rw [right_inv]

@[simp]

Depends on / 依赖: left_cancel, right_inv, self_act_act_eq
-/
theorem self_act_invAct_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y := by
  rw [← left_cancel (x ◃ x)]
  rw [right_inv]
  rw [self_act_act_eq]
  rw [right_inv]

@[simp]
/--
theorem `self_invAct_act_eq` / 定理 `self_invAct_act_eq`

English:
theorem self_invAct_act_eq
  given: {x y : R}
  statement: (x ◃⁻¹ x) ◃ y = x ◃ y
  proof: by
  have h := @self_act_invAct_eq _ _ (op x) (op y)
  simpa using h

中文:
定理 self_invAct_act_eq
  条件: {x y : R}
  结论: (x ◃⁻¹ x) ◃ y = x ◃ y
  证明: by
  have h := @self_act_invAct_eq _ _ (op x) (op y)
  simpa using h

Depends on / 依赖: self_act_invAct_eq
-/
theorem self_invAct_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y := by
  have h := @self_act_invAct_eq _ _ (op x) (op y)
  simpa using h

/--
theorem `self_act_eq_iff_eq` / 定理 `self_act_eq_iff_eq`

English:
theorem self_act_eq_iff_eq
  given: {x y : R}
  statement: x ◃ x = y ◃ y ↔ x = y
  proof: by
  constructor; swap
  · rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  · rw [← left_cancel (x ◃ x), right_inv, self_act_act_eq]
  · rw [h, ← left_cancel (y ◃ y), right_inv, self_act_act_eq]

中文:
定理 self_act_eq_iff_eq
  条件: {x y : R}
  结论: x ◃ x = y ◃ y ↔ x = y
  证明: by
  constructor; swap
  · rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  · rw [← left_cancel (x ◃ x), right_inv, self_act_act_eq]
  · rw [h, ← left_cancel (y ◃ y), right_inv, self_act_act_eq]

Depends on / 依赖: left_cancel, right_inv, self_act_act_eq
-/
theorem self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  trans (x ◃ x) ◃⁻¹ x ◃ x
  · rw [← left_cancel (x ◃ x), right_inv, self_act_act_eq]
  · rw [h, ← left_cancel (y ◃ y), right_inv, self_act_act_eq]

/--
theorem `self_invAct_eq_iff_eq` / 定理 `self_invAct_eq_iff_eq`

English:
theorem self_invAct_eq_iff_eq
  given: {x y : R}
  statement: x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y
  proof: by
  have h := @self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h

中文:
定理 self_invAct_eq_iff_eq
  条件: {x y : R}
  结论: x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y
  证明: by
  have h := @self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h

Depends on / 依赖: self_act_eq_iff_eq
-/
theorem self_invAct_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y := by
  have h := @self_act_eq_iff_eq _ _ (op x) (op y)
  simpa using h

/--
Definition of `selfApplyEquiv` / `selfApplyEquiv` 的定义

English:
definition selfApplyEquiv
  signature: (R : Type*) [Rack R]
  body: x ◃ x
  invFun x := x ◃⁻¹ x
  left_inv x := by simp
  right_inv x := by simp

中文:
定义 selfApplyEquiv
  签名: (R : 类型) [Rack R]
  定义体: x ◃ x
  invFun x := x ◃⁻¹ x
  left_inv x := by simp
  right_inv x := by simp
-/
def selfApplyEquiv (R : Type*) [Rack R] : R ≃ R where
  toFun x := x ◃ x
  invFun x := x ◃⁻¹ x
  left_inv x := by simp
  right_inv x := by simp

/--
Definition of `IsInvolutory` / `IsInvolutory` 的定义

English:
definition IsInvolutory
  signature: (R : Type*) [Rack R]
  body: forall x : R, Function.Involutive (Shelf.act x)

中文:
定义 IsInvolutory
  签名: (R : 类型) [Rack R]
  定义体: forall x : R, Function.Involutive (Shelf.act x)

Depends on / 依赖: Function, Function.Involutive, Involutive, Shelf.act
-/
def IsInvolutory (R : Type*) [Rack R] : Prop :=
  forall x : R, Function.Involutive (Shelf.act x)

/--
theorem `involutory_invAct_eq_act` / 定理 `involutory_invAct_eq_act`

English:
theorem involutory_invAct_eq_act
  given: {R : Type*} [Rack R] (h : IsInvolutory R) (x y : R)
  proof: by
  rw [← left_cancel x]; rw [right_inv]; rw [h x]

中文:
定理 involutory_invAct_eq_act
  条件: {R : 类型} [Rack R] (h : IsInvolutory R) (x y : R)
  证明: by
  rw [← left_cancel x]; rw [right_inv]; rw [h x]

Depends on / 依赖: left_cancel, right_inv
-/
theorem involutory_invAct_eq_act {R : Type*} [Rack R] (h : IsInvolutory R) (x y : R) :
    x ◃⁻¹ y = x ◃ y := by
  rw [← left_cancel x]; rw [right_inv]; rw [h x]

/--
Definition of `IsAbelian` / `IsAbelian` 的定义

English:
definition IsAbelian
  signature: (R : Type*) [Rack R]
  body: forall x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w

中文:
定义 IsAbelian
  签名: (R : 类型) [Rack R]
  定义体: forall x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w
-/
def IsAbelian (R : Type*) [Rack R] : Prop :=
  forall x y z w : R, (x ◃ y) ◃ z ◃ w = (x ◃ z) ◃ y ◃ w

/--
theorem `assoc_iff_id` / 定理 `assoc_iff_id`

English:
theorem assoc_iff_id
  given: {R : Type*} [Rack R] {x y z : R}
  statement: x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z
  proof: by
  rw [self_distrib]
  rw [left_cancel]

中文:
定理 assoc_iff_id
  条件: {R : 类型} [Rack R] {x y z : R}
  结论: x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z
  证明: by
  rw [self_distrib]
  rw [left_cancel]

Depends on / 依赖: left_cancel, self_distrib
-/
theorem assoc_iff_id {R : Type*} [Rack R] {x y z : R} : x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z := by
  rw [self_distrib]
  rw [left_cancel]

end Rack

namespace ShelfHom

variable {S₁ : Type*} {S₂ : Type*} {S₃ : Type*} [Shelf S₁] [Shelf S₂] [Shelf S₃]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (S₁ ->◃ S₂) S₁ S₂
  body: toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

中文:
实例 :
  签名: FunLike (S₁ ->◃ S₂) S₁ S₂
  定义体: toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
-/
instance : FunLike (S₁ ->◃ S₂) S₁ S₂ where
  coe := toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : S₁ ->◃ S₂)
  statement: f.toFun = f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: (f : S₁ ->◃ S₂)
  结论: f.toFun = f
  证明: rfl

@[simp]
-/
@[simp] theorem toFun_eq_coe (f : S₁ ->◃ S₂) : f.toFun = f := rfl

@[simp]
/--
theorem `map_act` / 定理 `map_act`

English:
theorem map_act
  given: (f : S₁ ->◃ S₂) {x y : S₁}
  statement: f (x ◃ y) = f x ◃ f y
  proof: map_act' f

中文:
定理 map_act
  条件: (f : S₁ ->◃ S₂) {x y : S₁}
  结论: f (x ◃ y) = f x ◃ f y
  证明: map_act' f

Depends on / 依赖: map_act
-/
theorem map_act (f : S₁ ->◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y :=
  map_act' f

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (S : Type*) [Shelf S]
  body: fun x => x
  map_act' := by simp

中文:
定义 id
  签名: (S : 类型) [Shelf S]
  定义体: fun x => x
  map_act' := by simp
-/
def id (S : Type*) [Shelf S] : S ->◃ S where
  toFun := fun x => x
  map_act' := by simp

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: (S : Type*) [Shelf S]
  body: ⟨id S⟩

中文:
实例 inhabited
  签名: (S : 类型) [Shelf S]
  定义体: ⟨id S⟩
-/
instance inhabited (S : Type*) [Shelf S] : Inhabited (S ->◃ S) :=
  ⟨id S⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : S₂ ->◃ S₃) (f : S₁ ->◃ S₂)
  body: g.toFun ∘ f.toFun
  map_act' := by simp

@[simp]

中文:
定义 comp
  签名: (g : S₂ ->◃ S₃) (f : S₁ ->◃ S₂)
  定义体: g.toFun ∘ f.toFun
  map_act' := by simp

@[simp]

Depends on / 依赖: f.toFun, g.toFun
-/
def comp (g : S₂ ->◃ S₃) (f : S₁ ->◃ S₂) : S₁ ->◃ S₃ where
  toFun := g.toFun ∘ f.toFun
  map_act' := by simp

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : S₂ ->◃ S₃) (f : S₁ ->◃ S₂) (x : S₁)
  statement: (g.comp f) x = g (f x)
  proof: rfl

中文:
定理 comp_apply
  条件: (g : S₂ ->◃ S₃) (f : S₁ ->◃ S₂) (x : S₁)
  结论: (g.comp f) x = g (f x)
  证明: rfl
-/
theorem comp_apply (g : S₂ ->◃ S₃) (f : S₁ ->◃ S₂) (x : S₁) : (g.comp f) x = g (f x) :=
  rfl

end ShelfHom

/--
Definition of `Quandle` / `Quandle` 的定义

English:
class Quandle
  parameters: (α : Type*)
  extends: Rack α
  axioms and operations (1):
    - fix : forall {x : α}, act x x = x

中文:
类 Quandle
  参数: (α : 类型)
  继承: Rack α
  公理与运算 (1 个):
    - fix : 对任意 {x : α}, act x x = x
-/
class Quandle (α : Type*) extends Rack α where
  /-- The fixing property of a Quandle -/
  fix : forall {x : α}, act x x = x

namespace Quandle

open Rack

variable {Q : Type*} [Quandle Q]

attribute [simp] fix

@[simp]
/--
theorem `fix_inv` / 定理 `fix_inv`

English:
theorem fix_inv
  given: {x : Q}
  statement: x ◃⁻¹ x = x
  proof: by
  rw [← left_cancel x]
  simp

中文:
定理 fix_inv
  条件: {x : Q}
  结论: x ◃⁻¹ x = x
  证明: by
  rw [← left_cancel x]
  simp

Depends on / 依赖: left_cancel
-/
theorem fix_inv {x : Q} : x ◃⁻¹ x = x := by
  rw [← left_cancel x]
  simp

/--
Instance `oppositeQuandle` / 实例 `oppositeQuandle`

English:
instance oppositeQuandle
  signature: : Quandle Qᵐᵒᵖ where
  body: by
    intro x
    induction x
    simp

中文:
实例 oppositeQuandle
  签名: : Quandle Qᵐᵒᵖ where
  定义体: by
    intro x
    induction x
    simp
-/
instance oppositeQuandle : Quandle Qᵐᵒᵖ where
  fix := by
    intro x
    induction x
    simp

/--
Definition of `Conj` / `Conj` 的定义

English:
abbreviation Conj
  signature: (G : Type*)
  body: G

中文:
缩写 Conj
  签名: (G : 类型)
  定义体: G
-/
abbrev Conj (G : Type*) := G

/--
Instance `Conj.quandle` / 实例 `Conj.quandle`

English:
instance Conj.quandle
  signature: (G : Type*) [Group G]
  body: @MulAut.conj G _ x
  self_distrib := by
    intro x y z
    dsimp only [MulAut.conj_apply]
    simp [mul_assoc]
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    simp [mul_assoc]
  right_inv x y := by
    simp [mul_assoc]
  fix := by simp

@[simp, grind =]

中文:
实例 Conj.quandle
  签名: (G : 类型) [Group G]
  定义体: @MulAut.conj G _ x
  self_distrib := by
    intro x y z
    dsimp only [MulAut.conj_apply]
    simp [mul_assoc]
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    simp [mul_assoc]
  right_inv x y := by
    simp [mul_assoc]
  fix := by simp

@[simp, grind =]

Depends on / 依赖: MulAut, MulAut.conj
-/
instance Conj.quandle (G : Type*) [Group G] : Quandle (Conj G) where
  act x := @MulAut.conj G _ x
  self_distrib := by
    intro x y z
    dsimp only [MulAut.conj_apply]
    simp [mul_assoc]
  invAct x := (@MulAut.conj G _ x).symm
  left_inv x y := by
    simp [mul_assoc]
  right_inv x y := by
    simp [mul_assoc]
  fix := by simp

@[simp, grind =]
/--
theorem `conj_act_eq_conj` / 定理 `conj_act_eq_conj`

English:
theorem conj_act_eq_conj
  given: {G : Type*} [Group G] (x y : Conj G)
  proof: rfl

中文:
定理 conj_act_eq_conj
  条件: {G : 类型} [Group G] (x y : Conj G)
  证明: rfl
-/
theorem conj_act_eq_conj {G : Type*} [Group G] (x y : Conj G) :
    x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) :=
  rfl

/--
theorem `conj_swap` / 定理 `conj_swap`

English:
theorem conj_swap
  given: {G : Type*} [Group G] (x y : Conj G)
  statement: x ◃ y = y ↔ y ◃ x = x
  proof: by
  grind [eq_mul_inv_iff_mul_eq]

中文:
定理 conj_swap
  条件: {G : 类型} [Group G] (x y : Conj G)
  结论: x ◃ y = y ↔ y ◃ x = x
  证明: by
  grind [eq_mul_inv_iff_mul_eq]

Depends on / 依赖: eq_mul_inv_iff_mul_eq
-/
theorem conj_swap {G : Type*} [Group G] (x y : Conj G) : x ◃ y = y ↔ y ◃ x = x := by
  grind [eq_mul_inv_iff_mul_eq]

/--
Definition of `Conj.map` / `Conj.map` 的定义

English:
definition Conj.map
  signature: {G : Type*} {H : Type*} [Group G] [Group H] (f : G ->* H)
  body: f
  map_act' := by simp

中文:
定义 Conj.map
  签名: {G : 类型} {H : 类型} [Group G] [Group H] (f : G ->* H)
  定义体: f
  map_act' := by simp

Depends on / 依赖: Monoid, NonUnitalNonAssocSemiring
-/
def Conj.map {G : Type*} {H : Type*} [Group G] [Group H] (f : G ->* H) : Conj G ->◃ Conj H where
  toFun := f
  map_act' := by simp

/--
Definition of `Dihedral` / `Dihedral` 的定义

English:
definition Dihedral
  signature: (n : Nat)
  body: ZMod n

中文:
定义 Dihedral
  签名: (n : 自然数)
  定义体: ZMod n

Depends on / 依赖: CommSemiring, Semiring
-/
def Dihedral (n : Nat) :=
  ZMod n

/--
Definition of `dihedralAct` / `dihedralAct` 的定义

English:
definition dihedralAct
  signature: (n : Nat) (a : ZMod n)
  body: fun b => 2 * a - b

中文:
定义 dihedralAct
  签名: (n : 自然数) (a : ZMod n)
  定义体: fun b => 2 * a - b
-/
def dihedralAct (n : Nat) (a : ZMod n) : ZMod n -> ZMod n := fun b => 2 * a - b

/--
theorem `dihedralAct.inv` / 定理 `dihedralAct.inv`

English:
theorem dihedralAct.inv
  given: (n : Nat) (a : ZMod n)
  statement: Function.Involutive (dihedralAct n a)
  proof: by
  intro b
  dsimp only [dihedralAct]
  simp

中文:
定理 dihedralAct.inv
  条件: (n : 自然数) (a : ZMod n)
  结论: Function.Involutive (dihedralAct n a)
  证明: by
  intro b
  dsimp only [dihedralAct]
  simp

Depends on / 依赖: dihedralAct
-/
theorem dihedralAct.inv (n : Nat) (a : ZMod n) : Function.Involutive (dihedralAct n a) := by
  intro b
  dsimp only [dihedralAct]
  simp

set_option backward.isDefEq.respectTransparency false in
instance (n : Nat) : Quandle (Dihedral n) where
  act := dihedralAct n
  self_distrib := by
    intro x y z
    simp only [dihedralAct]
    ring_nf
  invAct := dihedralAct n
  left_inv x := (dihedralAct.inv n x).leftInverse
  right_inv x := (dihedralAct.inv n x).rightInverse
  fix := by
    intro x
    simp only [dihedralAct]
    ring_nf

end Quandle

namespace Rack

/--
Definition of `toConj` / `toConj` 的定义

English:
definition toConj
  signature: (R : Type*) [Rack R]
  body: act'
  map_act' := by
    intro x y
    exact ad_conj x y

中文:
定义 toConj
  签名: (R : 类型) [Rack R]
  定义体: act'
  map_act' := by
    intro x y
    exact ad_conj x y
-/
def toConj (R : Type*) [Rack R] : R ->◃ Quandle.Conj (R ≃ R) where
  toFun := act'
  map_act' := by
    intro x y
    exact ad_conj x y

section EnvelGroup

/-!
### Universal enveloping group of a rack

The universal enveloping group `EnvelGroup R` of a rack `R` is the
universal group such that every rack homomorphism `R →◃ conj G` is
induced by a unique group homomorphism `EnvelGroup R →* G`.
For quandles, Joyce called this group `AdConj R`.

The `EnvelGroup` functor is left adjoint to the `Conj` forgetful
functor, and the way we construct the enveloping group is via a
technique that should work for left adjoints of forgetful functors in
general. It involves thinking a little about 2-categories, but the
payoff is that the map `EnvelGroup R →* G` has a nice description.

Let's think of a group as being a one-object category. The first step
is to define `PreEnvelGroup`, which gives formal expressions for all
the 1-morphisms and includes the unit element, elements of `R`,
multiplication, and inverses. To introduce relations, the second step
is to define `PreEnvelGroupRel'`, which gives formal expressions
for all 2-morphisms between the 1-morphisms. The 2-morphisms include
associativity, multiplication by the unit, multiplication by inverses,
compatibility with multiplication and inverses (`congr_mul` and
`congr_inv`), the axioms for an equivalence relation, and,
importantly, the relationship between conjugation and the rack action
(see `Rack.ad_conj`).

None of this forms a 2-category yet, for example due to lack of
associativity of `trans`. The `PreEnvelGroupRel` relation is a
`Prop`-valued version of `PreEnvelGroupRel'`, and making it
`Prop`-valued essentially introduces enough 3-isomorphisms so that
every pair of compatible 2-morphisms is isomorphic. Now, while
composition in `PreEnvelGroup` does not strictly satisfy the category
axioms, `PreEnvelGroup` and `PreEnvelGroupRel'` do form a weak
2-category.

Since we just want a 1-category, the last step is to quotient
`PreEnvelGroup` by `PreEnvelGroupRel'`, and the result is the
group `EnvelGroup`.

For a homomorphism `f : R →◃ Conj G`, how does
`EnvelGroup.map f : EnvelGroup R →* G` work? Let's think of `G` as
being a 2-category with one object, a 1-morphism per element of `G`,
and a single 2-morphism called `Eq.refl` for each 1-morphism. We
define the map using a "higher `Quotient.lift`" -- not only do we
evaluate elements of `PreEnvelGroup` as expressions in `G` (this is
`toEnvelGroup.mapAux`), but we evaluate elements of
`PreEnvelGroup'` as expressions of 2-morphisms of `G` (this is
`toEnvelGroup.mapAux.well_def`). That is to say,
`toEnvelGroup.mapAux.well_def` recursively evaluates formal
expressions of 2-morphisms as equality proofs in `G`. Now that all
morphisms are accounted for, the map descends to a homomorphism
`EnvelGroup R →* G`.

Note: `Type`-valued relations are not common. The fact it is
`Type`-valued is what makes `toEnvelGroup.mapAux.well_def` have
well-founded recursion.
-/


/--
Inductive type `PreEnvelGroup` / 归纳类型 `PreEnvelGroup`

English:
inductive PreEnvelGroup
  parameters: (R : Type u)
  constructors (4):
    - unit: PreEnvelGroup R
    - incl: (x : R) : PreEnvelGroup R
    - mul: (a b : PreEnvelGroup R) : PreEnvelGroup R
    - inv: (a : PreEnvelGroup R) : PreEnvelGroup R

中文:
归纳类型 PreEnvelGroup
  参数: (R : 类型u)
  构造子 (4 个):
    - unit: PreEnvelGroup R
    - incl: (x : R) : PreEnvelGroup R
    - mul: (a b : PreEnvelGroup R) : PreEnvelGroup R
    - inv: (a : PreEnvelGroup R) : PreEnvelGroup R
-/
inductive PreEnvelGroup (R : Type u) : Type u
  | unit : PreEnvelGroup R
  | incl (x : R) : PreEnvelGroup R
  | mul (a b : PreEnvelGroup R) : PreEnvelGroup R
  | inv (a : PreEnvelGroup R) : PreEnvelGroup R

/--
Instance `PreEnvelGroup.inhabited` / 实例 `PreEnvelGroup.inhabited`

English:
instance PreEnvelGroup.inhabited
  signature: (R : Type u)
  body: ⟨PreEnvelGroup.unit⟩

中文:
实例 PreEnvelGroup.inhabited
  签名: (R : 类型u)
  定义体: ⟨PreEnvelGroup.unit⟩

Depends on / 依赖: PreEnvelGroup, PreEnvelGroup.unit
-/
instance PreEnvelGroup.inhabited (R : Type u) : Inhabited (PreEnvelGroup R) :=
  ⟨PreEnvelGroup.unit⟩

open PreEnvelGroup

/--
Inductive type `PreEnvelGroupRel'` / 归纳类型 `PreEnvelGroupRel'`

English:
inductive PreEnvelGroupRel'
  parameters: (R : Type u) [Rack R]
  constructors (10):
    - refl: {a : PreEnvelGroup R} : PreEnvelGroupRel' R a a
    - symm: {a b : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) : PreEnvelGroupRel' R b a
    - trans: {a b c : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) (hbc : PreEnvelGroupRel' R b c) : PreEnvelGroupRel' R a c
    - congr_mul: {a b a' b' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') (hb : PreEnvelGroupRel' R b b') : PreEnvelGroupRel' R (mul a b) (mul a' b')
    - congr_inv: {a a' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') : PreEnvelGroupRel' R (inv a) (inv a')
    - assoc: (a b c : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (mul a b) c) (mul a (mul b c))
    - one_mul: (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul unit a) a
    - mul_one: (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul a unit) a
    - inv_mul_cancel: (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (inv a) a) unit
    - act_incl: (x y : R) : PreEnvelGroupRel' R (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))

中文:
归纳类型 PreEnvelGroupRel'
  参数: (R : 类型u) [Rack R]
  构造子 (10 个):
    - refl: {a : PreEnvelGroup R} : PreEnvelGroupRel' R a a
    - symm: {a b : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) : PreEnvelGroupRel' R b a
    - trans: {a b c : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) (hbc : PreEnvelGroupRel' R b c) : PreEnvelGroupRel' R a c
    - congr_mul: {a b a' b' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') (hb : PreEnvelGroupRel' R b b') : PreEnvelGroupRel' R (mul a b) (mul a' b')
    - congr_inv: {a a' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') : PreEnvelGroupRel' R (inv a) (inv a')
    - assoc: (a b c : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (mul a b) c) (mul a (mul b c))
    - one_mul: (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul unit a) a
    - mul_one: (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul a unit) a
    - inv_mul_cancel: (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (inv a) a) unit
    - act_incl: (x y : R) : PreEnvelGroupRel' R (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))
-/
inductive PreEnvelGroupRel' (R : Type u) [Rack R] : PreEnvelGroup R -> PreEnvelGroup R -> Type u
  | refl {a : PreEnvelGroup R} : PreEnvelGroupRel' R a a
  | symm {a b : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b) : PreEnvelGroupRel' R b a
  | trans {a b c : PreEnvelGroup R} (hab : PreEnvelGroupRel' R a b)
    (hbc : PreEnvelGroupRel' R b c) : PreEnvelGroupRel' R a c
  | congr_mul {a b a' b' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a')
    (hb : PreEnvelGroupRel' R b b') : PreEnvelGroupRel' R (mul a b) (mul a' b')
  | congr_inv {a a' : PreEnvelGroup R} (ha : PreEnvelGroupRel' R a a') :
    PreEnvelGroupRel' R (inv a) (inv a')
  | assoc (a b c : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (mul a b) c) (mul a (mul b c))
  | one_mul (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul unit a) a
  | mul_one (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul a unit) a
  | inv_mul_cancel (a : PreEnvelGroup R) : PreEnvelGroupRel' R (mul (inv a) a) unit
  | act_incl (x y : R) :
    PreEnvelGroupRel' R (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))

/--
Instance `PreEnvelGroupRel'.inhabited` / 实例 `PreEnvelGroupRel'.inhabited`

English:
instance PreEnvelGroupRel'.inhabited
  signature: (R : Type u) [Rack R]
  body: ⟨PreEnvelGroupRel'.refl⟩

中文:
实例 PreEnvelGroupRel'.inhabited
  签名: (R : 类型u) [Rack R]
  定义体: ⟨PreEnvelGroupRel'.refl⟩

Depends on / 依赖: PreEnvelGroupRel
-/
instance PreEnvelGroupRel'.inhabited (R : Type u) [Rack R] :
    Inhabited (PreEnvelGroupRel' R unit unit) :=
  ⟨PreEnvelGroupRel'.refl⟩

/--
Inductive type `PreEnvelGroupRel` / 归纳类型 `PreEnvelGroupRel`

English:
inductive PreEnvelGroupRel
  parameters: (R : Type u) [Rack R]
  constructors (1):
    - rel: {a b : PreEnvelGroup R} (r : PreEnvelGroupRel' R a b) : PreEnvelGroupRel R a b

中文:
归纳类型 PreEnvelGroupRel
  参数: (R : 类型u) [Rack R]
  构造子 (1 个):
    - rel: {a b : PreEnvelGroup R} (r : PreEnvelGroupRel' R a b) : PreEnvelGroupRel R a b
-/
inductive PreEnvelGroupRel (R : Type u) [Rack R] : PreEnvelGroup R -> PreEnvelGroup R -> Prop
  | rel {a b : PreEnvelGroup R} (r : PreEnvelGroupRel' R a b) : PreEnvelGroupRel R a b

/--
theorem `PreEnvelGroupRel'.rel` / 定理 `PreEnvelGroupRel'.rel`

English:
theorem PreEnvelGroupRel'.rel
  given: {R : Type u} [Rack R] {a b : PreEnvelGroup R}
  proof: PreEnvelGroupRel.rel

@[refl]

中文:
定理 PreEnvelGroupRel'.rel
  条件: {R : 类型u} [Rack R] {a b : PreEnvelGroup R}
  证明: PreEnvelGroupRel.rel

@[refl]
-/
theorem PreEnvelGroupRel'.rel {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel' R a b -> PreEnvelGroupRel R a b := PreEnvelGroupRel.rel

@[refl]
/--
theorem `PreEnvelGroupRel.refl` / 定理 `PreEnvelGroupRel.refl`

English:
theorem PreEnvelGroupRel.refl
  given: {R : Type u} [Rack R] {a : PreEnvelGroup R}
  proof: PreEnvelGroupRel.rel PreEnvelGroupRel'.refl

@[symm]

中文:
定理 PreEnvelGroupRel.refl
  条件: {R : 类型u} [Rack R] {a : PreEnvelGroup R}
  证明: PreEnvelGroupRel.rel PreEnvelGroupRel'.refl

@[symm]

Depends on / 依赖: PreEnvelGroupRel, PreEnvelGroupRel.rel
-/
theorem PreEnvelGroupRel.refl {R : Type u} [Rack R] {a : PreEnvelGroup R} :
    PreEnvelGroupRel R a a :=
  PreEnvelGroupRel.rel PreEnvelGroupRel'.refl

@[symm]
/--
theorem `PreEnvelGroupRel.symm` / 定理 `PreEnvelGroupRel.symm`

English:
theorem PreEnvelGroupRel.symm
  given: {R : Type u} [Rack R] {a b : PreEnvelGroup R}

中文:
定理 PreEnvelGroupRel.symm
  条件: {R : 类型u} [Rack R] {a b : PreEnvelGroup R}
-/
theorem PreEnvelGroupRel.symm {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel R a b -> PreEnvelGroupRel R b a
  | ⟨r⟩ => r.symm.rel

@[trans]
/--
theorem `PreEnvelGroupRel.trans` / 定理 `PreEnvelGroupRel.trans`

English:
theorem PreEnvelGroupRel.trans
  given: {R : Type u} [Rack R] {a b c : PreEnvelGroup R}

中文:
定理 PreEnvelGroupRel.trans
  条件: {R : 类型u} [Rack R] {a b c : PreEnvelGroup R}

Depends on / 依赖: e.symm
-/
theorem PreEnvelGroupRel.trans {R : Type u} [Rack R] {a b c : PreEnvelGroup R} :
    PreEnvelGroupRel R a b -> PreEnvelGroupRel R b c -> PreEnvelGroupRel R a c
  | ⟨rab⟩, ⟨rbc⟩ => (rab.trans rbc).rel

/--
Instance `PreEnvelGroup.setoid` / 实例 `PreEnvelGroup.setoid`

English:
instance PreEnvelGroup.setoid
  signature: (R : Type*) [Rack R]
  body: PreEnvelGroupRel R
  iseqv := by
    constructor
    · apply PreEnvelGroupRel.refl
    · apply PreEnvelGroupRel.symm
    · apply PreEnvelGroupRel.trans

中文:
实例 PreEnvelGroup.setoid
  签名: (R : 类型) [Rack R]
  定义体: PreEnvelGroupRel R
  iseqv := by
    constructor
    · apply PreEnvelGroupRel.refl
    · apply PreEnvelGroupRel.symm
    · apply PreEnvelGroupRel.trans

Depends on / 依赖: PreEnvelGroupRel
-/
instance PreEnvelGroup.setoid (R : Type*) [Rack R] : Setoid (PreEnvelGroup R) where
  r := PreEnvelGroupRel R
  iseqv := by
    constructor
    · apply PreEnvelGroupRel.refl
    · apply PreEnvelGroupRel.symm
    · apply PreEnvelGroupRel.trans
/--
Definition of `EnvelGroup` / `EnvelGroup` 的定义

English:
definition EnvelGroup
  signature: (R : Type*) [Rack R]
  body: Quotient (PreEnvelGroup.setoid R)

中文:
定义 EnvelGroup
  签名: (R : 类型) [Rack R]
  定义体: Quotient (PreEnvelGroup.setoid R)

Depends on / 依赖: PreEnvelGroup, PreEnvelGroup.setoid, Quotient, setoid
-/
def EnvelGroup (R : Type*) [Rack R] :=
  Quotient (PreEnvelGroup.setoid R)

-- Define the `Group` instances in two steps so `inv` can be inferred correctly.
-- TODO: is there a non-invasive way of defining the instance directly?
instance (R : Type*) [Rack R] : DivInvMonoid (EnvelGroup R) where
  mul a b :=
    Quotient.liftOn₂ a b (fun a b => ⟦PreEnvelGroup.mul a b⟧) fun _ _ _ _ ⟨ha⟩ ⟨hb⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_mul ha hb).rel
  one := ⟦unit⟧
  inv a :=
    Quotient.liftOn a (fun a => ⟦PreEnvelGroup.inv a⟧) fun _ _ ⟨ha⟩ =>
      Quotient.sound (PreEnvelGroupRel'.congr_inv ha).rel
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun a b c => Quotient.sound (PreEnvelGroupRel'.assoc a b c).rel
  one_mul a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.one_mul a).rel
  mul_one a := Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.mul_one a).rel

instance (R : Type*) [Rack R] : Group (EnvelGroup R) :=
  { inv_mul_cancel := fun a =>
      Quotient.inductionOn a fun a => Quotient.sound (PreEnvelGroupRel'.inv_mul_cancel a).rel }

/--
Instance `EnvelGroup.inhabited` / 实例 `EnvelGroup.inhabited`

English:
instance EnvelGroup.inhabited
  signature: (R : Type*) [Rack R]
  body: ⟨1⟩

中文:
实例 EnvelGroup.inhabited
  签名: (R : 类型) [Rack R]
  定义体: ⟨1⟩
-/
instance EnvelGroup.inhabited (R : Type*) [Rack R] : Inhabited (EnvelGroup R) :=
  ⟨1⟩

/--
Definition of `toEnvelGroup` / `toEnvelGroup` 的定义

English:
definition toEnvelGroup
  signature: (R : Type*) [Rack R]
  body: ⟦incl x⟧
  map_act' := @fun x y => Quotient.sound (PreEnvelGroupRel'.act_incl x y).symm.rel

中文:
定义 toEnvelGroup
  签名: (R : 类型) [Rack R]
  定义体: ⟦incl x⟧
  map_act' := @fun x y => Quotient.sound (PreEnvelGroupRel'.act_incl x y).symm.rel
-/
def toEnvelGroup (R : Type*) [Rack R] : R ->◃ Quandle.Conj (EnvelGroup R) where
  toFun x := ⟦incl x⟧
  map_act' := @fun x y => Quotient.sound (PreEnvelGroupRel'.act_incl x y).symm.rel

/--
Definition of `toEnvelGroup.mapAux` / `toEnvelGroup.mapAux` 的定义

English:
definition toEnvelGroup.mapAux
  signature: {R : Type*} [Rack R] {G : Type*} [Group G] (f : R ->◃ Quandle.Conj G)

中文:
定义 toEnvelGroup.mapAux
  签名: {R : 类型} [Rack R] {G : 类型} [Group G] (f : R ->◃ Quandle.Conj G)
-/
def toEnvelGroup.mapAux {R : Type*} [Rack R] {G : Type*} [Group G] (f : R ->◃ Quandle.Conj G) :
    PreEnvelGroup R -> G
  | .unit => 1
  | .incl x => f x
  | .mul a b => toEnvelGroup.mapAux f a * toEnvelGroup.mapAux f b
  | .inv a => (toEnvelGroup.mapAux f a)⁻¹

namespace toEnvelGroup.mapAux

open PreEnvelGroupRel'

/--
theorem `well_def` / 定理 `well_def`

English:
theorem well_def
  given: {R : Type*} [Rack R] {G : Type*} [Group G] (f : R ->◃ Quandle.Conj G)

中文:
定理 well_def
  条件: {R : 类型} [Rack R] {G : 类型} [Group G] (f : R ->◃ Quandle.Conj G)
-/
theorem well_def {R : Type*} [Rack R] {G : Type*} [Group G] (f : R ->◃ Quandle.Conj G) :
    forall {a b : PreEnvelGroup R},
      PreEnvelGroupRel' R a b -> toEnvelGroup.mapAux f a = toEnvelGroup.mapAux f b
  | _, _, PreEnvelGroupRel'.refl => rfl
  | _, _, PreEnvelGroupRel'.symm h => (well_def f h).symm
  | _, _, PreEnvelGroupRel'.trans hac hcb => Eq.trans (well_def f hac) (well_def f hcb)
  | _, _, PreEnvelGroupRel'.congr_mul ha hb => by
    simp [toEnvelGroup.mapAux, well_def f ha, well_def f hb]
  | _, _, congr_inv ha => by simp [toEnvelGroup.mapAux, well_def f ha]
  | _, _, assoc a b c => by apply mul_assoc
  | _, _, PreEnvelGroupRel'.one_mul a => by simp [toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.mul_one a => by simp [toEnvelGroup.mapAux]
  | _, _, PreEnvelGroupRel'.inv_mul_cancel a => by simp [toEnvelGroup.mapAux]
  | _, _, act_incl x y => by simp [toEnvelGroup.mapAux]

end toEnvelGroup.mapAux

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toEnvelGroup.map` / `toEnvelGroup.map` 的定义

English:
definition toEnvelGroup.map
  signature: {R : Type*} [Rack R] {G : Type*} [Group G]
  body: { toFun := fun x =>
        Quotient.liftOn x (toEnvelGroup.mapAux f) fun _ _ ⟨hab⟩ =>
          toEnvelGroup.mapAux.well_def f hab
      map_one' := by
        change Quotient.liftOn ⟦Rack.PreEnvelGroup.unit⟧ (toEnvelGroup.mapAux f) _ = 1
        simp only [Quotient.lift_mk, mapAux]
      map_mul' 

中文:
定义 toEnvelGroup.map
  签名: {R : 类型} [Rack R] {G : 类型} [Group G]
  定义体: { toFun := fun x =>
        Quotient.liftOn x (toEnvelGroup.mapAux f) fun _ _ ⟨hab⟩ =>
          toEnvelGroup.mapAux.well_def f hab
      map_one' := by
        change Quotient.liftOn ⟦Rack.PreEnvelGroup.unit⟧ (toEnvelGroup.mapAux f) _ = 1
        simp only [Quotient.lift_mk, mapAux]
      map_mul' 

Depends on / 依赖: MonoidHom, MonoidHom.ext, PreEnvelGroup, Quandle, Quandle.Conj.map, Quotien, Quotient, Quotient.inductionOn, Quotient.liftOn, Quotient.lift_mk, Rack.PreEnvelGroup.unit, invFun, liftOn, lift_mk, mapAux, map_mul, map_one, right_inv, toEnvelGroup, toEnvelGroup.mapAux
-/
def toEnvelGroup.map {R : Type*} [Rack R] {G : Type*} [Group G] :
    (R ->◃ Quandle.Conj G) ≃ (EnvelGroup R ->* G) where
  toFun f :=
    { toFun := fun x =>
        Quotient.liftOn x (toEnvelGroup.mapAux f) fun _ _ ⟨hab⟩ =>
          toEnvelGroup.mapAux.well_def f hab
      map_one' := by
        change Quotient.liftOn ⟦Rack.PreEnvelGroup.unit⟧ (toEnvelGroup.mapAux f) _ = 1
        simp only [Quotient.lift_mk, mapAux]
      map_mul' := fun x y =>
        Quotient.inductionOn₂ x y fun x y => by
          change Quotient.liftOn ⟦mul x y⟧ (toEnvelGroup.mapAux f) _ = _
          simp [toEnvelGroup.mapAux] }
  invFun F := (Quandle.Conj.map F).comp (toEnvelGroup R)
  right_inv F :=
    MonoidHom.ext fun x =>
      Quotient.inductionOn x fun x => by
        induction x with
        | unit => exact F.map_one.symm
        | incl => rfl
        | mul x y ih_x ih_y =>
          have hm : ⟦x.mul y⟧ = @Mul.mul (EnvelGroup R) _ ⟦x⟧ ⟦y⟧ := rfl
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk]
          suffices forall x y, F (Mul.mul x y) = F (x) * F (y) by
            simp_all only [MonoidHom.coe_mk, OneHom.coe_mk, Quotient.lift_mk]
            rw [← ih_x]; rw [← ih_y]; rw [mapAux]
          exact F.map_mul
        | inv x ih_x =>
          have hm : ⟦x.inv⟧ = @Inv.inv (EnvelGroup R) _ ⟦x⟧ := rfl
          rw [hm]; rw [map_inv]; rw [map_inv]; rw [ih_x]

/--
theorem `toEnvelGroup.univ` / 定理 `toEnvelGroup.univ`

English:
theorem toEnvelGroup.univ
  given: (R : Type*) [Rack R] (G : Type*) [Group G] (f : R ->◃ Quandle.Conj G)
  proof: toEnvelGroup.map.symm_apply_apply f

中文:
定理 toEnvelGroup.univ
  条件: (R : 类型) [Rack R] (G : 类型) [Group G] (f : R ->◃ Quandle.Conj G)
  证明: toEnvelGroup.map.symm_apply_apply f

Depends on / 依赖: symm_apply_apply, toEnvelGroup, toEnvelGroup.map.symm_apply_apply
-/
theorem toEnvelGroup.univ (R : Type*) [Rack R] (G : Type*) [Group G] (f : R ->◃ Quandle.Conj G) :
    (Quandle.Conj.map (toEnvelGroup.map f)).comp (toEnvelGroup R) = f :=
  toEnvelGroup.map.symm_apply_apply f

/--
theorem `toEnvelGroup.univ_uniq` / 定理 `toEnvelGroup.univ_uniq`

English:
theorem toEnvelGroup.univ_uniq
  statement: (R : Type*) [Rack R] (G : Type*) [Group G]
  proof: h.symm ▸ (toEnvelGroup.map.apply_symm_apply g).symm

中文:
定理 toEnvelGroup.univ_uniq
  结论: (R : 类型) [Rack R] (G : 类型) [Group G]
  证明: h.symm ▸ (toEnvelGroup.map.apply_symm_apply g).symm

Depends on / 依赖: apply_symm_apply, h.symm, toEnvelGroup, toEnvelGroup.map.apply_symm_apply
-/
theorem toEnvelGroup.univ_uniq (R : Type*) [Rack R] (G : Type*) [Group G]
    (f : R ->◃ Quandle.Conj G) (g : EnvelGroup R ->* G)
    (h : f = (Quandle.Conj.map g).comp (toEnvelGroup R)) : g = toEnvelGroup.map f :=
  h.symm ▸ (toEnvelGroup.map.apply_symm_apply g).symm

/--
Definition of `envelAction` / `envelAction` 的定义

English:
definition envelAction
  signature: {R : Type*} [Rack R]
  body: toEnvelGroup.map (toConj R)

@[simp]

中文:
定义 envelAction
  签名: {R : 类型} [Rack R]
  定义体: toEnvelGroup.map (toConj R)

@[simp]

Depends on / 依赖: toConj, toEnvelGroup, toEnvelGroup.map
-/
def envelAction {R : Type*} [Rack R] : EnvelGroup R ->* R ≃ R :=
  toEnvelGroup.map (toConj R)

@[simp]
/--
theorem `envelAction_prop` / 定理 `envelAction_prop`

English:
theorem envelAction_prop
  given: {R : Type*} [Rack R] (x y : R)
  proof: rfl

中文:
定理 envelAction_prop
  条件: {R : 类型} [Rack R] (x y : R)
  证明: rfl
-/
theorem envelAction_prop {R : Type*} [Rack R] (x y : R) :
    envelAction (toEnvelGroup R x) y = x ◃ y :=
  rfl

end EnvelGroup

end Rack
