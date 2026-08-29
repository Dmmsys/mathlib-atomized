/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Data.Nat.Cast.Basic

import Mathlib.Data.Int.LeastGreatest

/-!
# Floor and ceil

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.
We also provide `positivity` extensions to handle floor and ceil.

## Main definitions

* `FloorSemiring`: An ordered semiring with natural-valued floor and ceil.
* `Nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.
* `Nat.ceil a`: Least natural `n` such that `a ≤ n`.

* `FloorRing`: A linearly ordered ring with integer-valued floor and ceil.
* `Int.floor a`: Greatest integer `z` such that `z ≤ a`.
* `Int.ceil a`: Least integer `z` such that `a ≤ z`.
* `Int.fract a`: Fractional part of `a`, defined as `a - floor a`.

## Notation

* `⌊a⌋₊` is `Nat.floor a`.
* `⌈a⌉₊` is `Nat.ceil a`.
* `⌊a⌋` is `Int.floor a`.
* `⌈a⌉` is `Int.ceil a`.

The index `₊` in the notations for `Nat.floor` and `Nat.ceil` is used in analogy to the notation
for `nnnorm`.

## TODO

`LinearOrder` can be relaxed to `PartialOrder` in many lemmas.

## Tags

rounding, floor, ceil
-/

@[expose] public section

assert_not_exists Finset

open Set

variable {F α β : Type*}

/-! ### Floor semiring -/

/--
Definition of `FloorSemiring` / `FloorSemiring` 的定义

English:
class FloorSemiring
  parameters: (α) [Semiring α] [PartialOrder α]
  axioms and operations (5):
    - floor : α -> Nat
    - ceil : α -> Nat
    - floor_of_neg({a : α} (ha : a < 0)) : floor a = 0
    - gc_floor({a : α} {n : Nat} (ha : 0 <= a)) : n <= floor a ↔ (n : α) <= a
    - gc_ceil : GaloisConnection ceil (↑)

中文:
类 FloorSemiring
  参数: (α) [半环 α] [偏序 α]
  公理与运算 (5 个):
    - floor : α -> 自然数
    - ceil : α -> 自然数
    - floor_of_neg({a : α} (ha : a < 0)) : floor a = 0
    - gc_floor({a : α} {n : 自然数} (ha : 0 <= a)) : n <= floor a ↔ (n : α) <= a
    - gc_ceil : GaloisConnection ceil (↑)
-/
class FloorSemiring (α) [Semiring α] [PartialOrder α] where
  /-- `FloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`. -/
  floor : α -> Nat
  /-- `FloorSemiring.ceil a` computes the least natural `n` such that `a ≤ (n : α)`. -/
  ceil : α -> Nat
  /-- `FloorSemiring.floor` of a negative element is zero. -/
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- A natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion to `α` is
  smaller than `a`. -/
  gc_floor {a : α} {n : Nat} (ha : 0 <= a) : n <= floor a ↔ (n : α) <= a
  /-- `FloorSemiring.ceil` is the lower adjoint of the coercion `↑ : ℕ → α`. -/
  gc_ceil : GaloisConnection ceil (↑)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorSemiring Nat
  body: id
  ceil := id
  floor_of_neg ha := (Nat.not_lt_zero _ ha).elim
  gc_floor _ := by
    rw [Nat.cast_id]; rw [id_def]
  gc_ceil n a := by
    rw [Nat.cast_id]; rw [id_def]

中文:
实例 :
  签名: FloorSemiring 自然数
  定义体: id
  ceil := id
  floor_of_neg ha := (Nat.not_lt_zero _ ha).elim
  gc_floor _ := by
    rw [Nat.cast_id]; rw [id_def]
  gc_ceil n a := by
    rw [Nat.cast_id]; rw [id_def]
-/
instance : FloorSemiring Nat where
  floor := id
  ceil := id
  floor_of_neg ha := (Nat.not_lt_zero _ ha).elim
  gc_floor _ := by
    rw [Nat.cast_id]; rw [id_def]
  gc_ceil n a := by
    rw [Nat.cast_id]; rw [id_def]

namespace FloorSemiring

variable [Semiring α] [PartialOrder α] [FloorSemiring α]

/--
theorem `natCast_mono` / 定理 `natCast_mono`

English:
theorem natCast_mono
  statement: Monotone (Nat.cast : Nat -> α)
  proof: fun _ _ h => (gc_ceil _ _).mp h.trans' (gc_ceil _ _).mpr (le_refl _)

中文:
定理 natCast_mono
  结论: 递增 (自然数.cast : 自然数 -> α)
  证明: fun _ _ h => (gc_ceil _ _).mp h.trans' (gc_ceil _ _).mpr (le_refl _)

Depends on / 依赖: gc_ceil, h.trans, le_refl
-/
theorem natCast_mono : Monotone (Nat.cast : Nat -> α) :=
fun _ _ h => (gc_ceil _ _).mp h.trans' (gc_ceil _ _).mpr (le_refl _)

/--
theorem `natCast_nonneg` / 定理 `natCast_nonneg`

English:
theorem natCast_nonneg
  given: (n : Nat)
  statement: 0 <= (n : α)
  proof: by
  simpa using natCast_mono n.zero_le

中文:
定理 natCast_nonneg
  条件: (n : 自然数)
  结论: 0 <= (n : α)
  证明: by
  simpa using natCast_mono n.zero_le

Depends on / 依赖: n.zero_le, natCast_mono, zero_le
-/
theorem natCast_nonneg (n : Nat) : 0 <= (n : α) := by
  simpa using natCast_mono n.zero_le

/--
theorem `natCast_strictMono` / 定理 `natCast_strictMono`

English:
theorem natCast_strictMono
  statement: StrictMono (Nat.cast : Nat -> α)
  proof: by
  refine strictMono_nat_of_lt_succ fun n => (natCast_mono (Nat.le_succ n)).lt_of_ne fun hn => ?_
  replace hn (k : Nat) : ((n + k : Nat) : α) = n := by
    induction k with | zero => rfl | succ k k_ih => grind
  have h : n + (floor (n : α) + 1) <= floor (n : α) := (gc_floor (natCast_nonneg n)).mp

中文:
定理 natCast_strictMono
  结论: 严格递增 (自然数.cast : 自然数 -> α)
  证明: by
  refine strictMono_nat_of_lt_succ fun n => (natCast_mono (Nat.le_succ n)).lt_of_ne fun hn => ?_
  replace hn (k : Nat) : ((n + k : Nat) : α) = n := by
    induction k with | zero => rfl | succ k k_ih => grind
  have h : n + (floor (n : α) + 1) <= floor (n : α) := (gc_floor (natCast_nonneg n)).mp

Depends on / 依赖: Nat.le_succ, gc_floor, k_ih, le_succ, lt_of_ne, natCast_mono, natCast_nonneg, replace, strictMono_nat_of_lt_succ
-/
theorem natCast_strictMono : StrictMono (Nat.cast : Nat -> α) := by
  refine strictMono_nat_of_lt_succ fun n => (natCast_mono (Nat.le_succ n)).lt_of_ne fun hn => ?_
  replace hn (k : Nat) : ((n + k : Nat) : α) = n := by
    induction k with | zero => rfl | succ k k_ih => grind
  have h : n + (floor (n : α) + 1) <= floor (n : α) := (gc_floor (natCast_nonneg n)).mpr (hn _).le
  grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ZeroLEOneClass α
  body: ⟨by simpa only [Nat.cast_one] using natCast_nonneg 1⟩

中文:
实例 :
  签名: ZeroLEOne类 α
  定义体: ⟨by simpa only [Nat.cast_one] using natCast_nonneg 1⟩

Depends on / 依赖: Nat.cast_one, cast_one, natCast_nonneg
-/
instance : ZeroLEOneClass α := ⟨by simpa only [Nat.cast_one] using natCast_nonneg 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharZero α
  body: ⟨natCast_strictMono.injective⟩

中文:
实例 :
  签名: 特征零 α
  定义体: ⟨natCast_strictMono.injective⟩

Depends on / 依赖: injective, natCast_strictMono, natCast_strictMono.injective
-/
instance : CharZero α := ⟨natCast_strictMono.injective⟩

end FloorSemiring

namespace Nat

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : Nat}

/--
Definition of `floor` / `floor` 的定义

English:
definition floor
  signature: : α -> Nat
  body: FloorSemiring.floor

中文:
定义 floor
  签名: : α -> 自然数
  定义体: FloorSemiring.floor

Depends on / 依赖: FloorSemiring, FloorSemiring.floor
-/
def floor : α -> Nat :=
  FloorSemiring.floor

/--
Definition of `ceil` / `ceil` 的定义

English:
definition ceil
  signature: : α -> Nat
  body: FloorSemiring.ceil

@[simp]

中文:
定义 ceil
  签名: : α -> 自然数
  定义体: FloorSemiring.ceil

@[simp]

Depends on / 依赖: FloorSemiring, FloorSemiring.ceil
-/
def ceil : α -> Nat :=
  FloorSemiring.ceil

@[simp]
/--
theorem `floor_nat` / 定理 `floor_nat`

English:
theorem floor_nat
  statement: (Nat.floor : Nat -> Nat) = id
  proof: rfl

@[simp]

中文:
定理 floor_nat
  结论: (自然数.floor : 自然数 -> 自然数) = id
  证明: rfl

@[simp]
-/
theorem floor_nat : (Nat.floor : Nat -> Nat) = id :=
  rfl

@[simp]
/--
theorem `ceil_nat` / 定理 `ceil_nat`

English:
theorem ceil_nat
  statement: (Nat.ceil : Nat -> Nat) = id
  proof: rfl

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

中文:
定理 ceil_nat
  结论: (自然数.ceil : 自然数 -> 自然数) = id
  证明: rfl

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a
-/
theorem ceil_nat : (Nat.ceil : Nat -> Nat) = id :=
  rfl

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

/--
theorem `le_floor_iff` / 定理 `le_floor_iff`

English:
theorem le_floor_iff
  given: (ha : 0 <= a)
  statement: n <= ⌊a⌋₊ ↔ (n : α) <= a
  proof: FloorSemiring.gc_floor ha

中文:
定理 le_floor_iff
  条件: (ha : 0 <= a)
  结论: n <= ⌊a⌋₊ ↔ (n : α) <= a
  证明: FloorSemiring.gc_floor ha

Depends on / 依赖: FloorSemiring, FloorSemiring.gc_floor, gc_floor
-/
theorem le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a :=
  FloorSemiring.gc_floor ha

/--
theorem `le_floor` / 定理 `le_floor`

English:
theorem le_floor
  given: (h : (n : α) <= a)
  statement: n <= ⌊a⌋₊
  proof: (le_floor_iff ((FloorSemiring.natCast_nonneg n).trans h)).2 h

中文:
定理 le_floor
  条件: (h : (n : α) <= a)
  结论: n <= ⌊a⌋₊
  证明: (le_floor_iff ((FloorSemiring.natCast_nonneg n).trans h)).2 h

Depends on / 依赖: FloorSemiring, FloorSemiring.natCast_nonneg, le_floor_iff, natCast_nonneg
-/
theorem le_floor (h : (n : α) <= a) : n <= ⌊a⌋₊ :=
  (le_floor_iff ((FloorSemiring.natCast_nonneg n).trans h)).2 h

/--
theorem `gc_ceil_coe` / 定理 `gc_ceil_coe`

English:
theorem gc_ceil_coe
  statement: GaloisConnection (ceil : α -> Nat) (↑)
  proof: FloorSemiring.gc_ceil

@[simp]

中文:
定理 gc_ceil_coe
  结论: GaloisConnection (ceil : α -> 自然数) (↑)
  证明: FloorSemiring.gc_ceil

@[simp]

Depends on / 依赖: FloorSemiring, FloorSemiring.gc_ceil, gc_ceil
-/
theorem gc_ceil_coe : GaloisConnection (ceil : α -> Nat) (↑) :=
  FloorSemiring.gc_ceil

@[simp]
/--
theorem `ceil_le` / 定理 `ceil_le`

English:
theorem ceil_le
  statement: ⌈a⌉₊ <= n ↔ a <= n
  proof: gc_ceil_coe _ _

中文:
定理 ceil_le
  结论: ⌈a⌉₊ <= n ↔ a <= n
  证明: gc_ceil_coe _ _

Depends on / 依赖: gc_ceil_coe
-/
theorem ceil_le : ⌈a⌉₊ <= n ↔ a <= n :=
  gc_ceil_coe _ _

end OrderedSemiring

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : Nat}

/--
theorem `lt_ceil` / 定理 `lt_ceil`

English:
theorem lt_ceil
  statement: n < ⌈a⌉₊ ↔ (n : α) < a
  proof: lt_iff_lt_of_le_iff_le ceil_le

@[simp]

中文:
定理 lt_ceil
  结论: n < ⌈a⌉₊ ↔ (n : α) < a
  证明: lt_iff_lt_of_le_iff_le ceil_le

@[simp]

Depends on / 依赖: ceil_le, lt_iff_lt_of_le_iff_le
-/
theorem lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le

@[simp]
/--
theorem `ceil_pos` / 定理 `ceil_pos`

English:
theorem ceil_pos
  statement: 0 < ⌈a⌉₊ ↔ 0 < a
  proof: by rw [lt_ceil, cast_zero]

中文:
定理 ceil_pos
  结论: 0 < ⌈a⌉₊ ↔ 0 < a
  证明: by rw [lt_ceil, cast_zero]

Depends on / 依赖: cast_zero, lt_ceil
-/
theorem ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a := by rw [lt_ceil, cast_zero]

end LinearOrderedSemiring

end Nat

/-! ### Floor rings -/

/--
Definition of `FloorRing` / `FloorRing` 的定义

English:
class FloorRing
  parameters: (α) [Ring α] [LinearOrder α]
  axioms and operations (4):
    - floor : α -> Int
    - ceil : α -> Int
    - gc_coe_floor : GaloisConnection (↑) floor
    - gc_ceil_coe : GaloisConnection ceil (↑)

中文:
类 Floor环
  参数: (α) [环 α] [线性序 α]
  公理与运算 (4 个):
    - floor : α -> 整数
    - ceil : α -> 整数
    - gc_coe_floor : GaloisConnection (↑) floor
    - gc_ceil_coe : GaloisConnection ceil (↑)

Depends on / 依赖: MulLeftMono, MulLeftMono.toPosMulMono, toPosMulMono
-/
class FloorRing (α) [Ring α] [LinearOrder α] where
  /-- `FloorRing.floor a` computes the greatest integer `z` such that `(z : α) ≤ a`. -/
  floor : α -> Int
  /-- `FloorRing.ceil a` computes the least integer `z` such that `a ≤ (z : α)`. -/
  ceil : α -> Int
  /-- `FloorRing.ceil` is the upper adjoint of the coercion `↑ : ℤ → α`. -/
  gc_coe_floor : GaloisConnection (↑) floor
  /-- `FloorRing.ceil` is the lower adjoint of the coercion `↑ : ℤ → α`. -/
  gc_ceil_coe : GaloisConnection ceil (↑)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FloorRing Int
  body: id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id]; rw [id_def]
  gc_ceil_coe a b := by
    rw [Int.cast_id]; rw [id_def]

中文:
实例 :
  签名: Floor环 整数
  定义体: id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id]; rw [id_def]
  gc_ceil_coe a b := by
    rw [Int.cast_id]; rw [id_def]

Depends on / 依赖: MulRightMono, MulRightMono.toMulPosMono, toMulPosMono
-/
instance : FloorRing Int where
  floor := id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id]; rw [id_def]
  gc_ceil_coe a b := by
    rw [Int.cast_id]; rw [id_def]

/-- A `FloorRing` constructor from the `floor` function alone. -/
@[instance_reducible]
/--
Definition of `FloorRing.ofFloor` / `FloorRing.ofFloor` 的定义

English:
definition FloorRing.ofFloor
  signature: (α) [Ring α] [LinearOrder α] [IsOrderedRing α] (floor : α -> Int)
  body: { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }

中文:
定义 Floor环.ofFloor
  签名: (α) [环 α] [线性序 α] [是Ordered环 α] (floor : α -> 整数)
  定义体: { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }

Depends on / 依赖: Int.cast_neg, MulLeftStrictMono, MulLeftStrictMono.toPosMulStrictMono, cast_neg, gc_ceil_coe, gc_coe_floor, neg_le, neg_le_neg_iff, toPosMulStrictMono
-/
def FloorRing.ofFloor (α) [Ring α] [LinearOrder α] [IsOrderedRing α] (floor : α -> Int)
    (gc_coe_floor : GaloisConnection (↑) floor) : FloorRing α :=
  { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }

/-- A `FloorRing` constructor from the `ceil` function alone. -/
@[instance_reducible]
/--
Definition of `FloorRing.ofCeil` / `FloorRing.ofCeil` 的定义

English:
definition FloorRing.ofCeil
  signature: (α) [Ring α] [LinearOrder α] [IsOrderedRing α] (ceil : α -> Int)
  body: { floor := fun a => -ceil (-a)
    ceil
    gc_coe_floor := fun a z => by rw [le_neg, gc_ceil_coe, Int.cast_neg, neg_le_neg_iff]
    gc_ceil_coe }

中文:
定义 Floor环.ofCeil
  签名: (α) [环 α] [线性序 α] [是Ordered环 α] (ceil : α -> 整数)
  定义体: { floor := fun a => -ceil (-a)
    ceil
    gc_coe_floor := fun a z => by rw [le_neg, gc_ceil_coe, Int.cast_neg, neg_le_neg_iff]
    gc_ceil_coe }

Depends on / 依赖: Int.cast_neg, MulRightStrictMono, MulRightStrictMono.toMulPosStrictMono, cast_neg, gc_ceil_coe, gc_coe_floor, le_neg, neg_le_neg_iff, toMulPosStrictMono
-/
def FloorRing.ofCeil (α) [Ring α] [LinearOrder α] [IsOrderedRing α] (ceil : α -> Int)
    (gc_ceil_coe : GaloisConnection ceil (↑)) : FloorRing α :=
  { floor := fun a => -ceil (-a)
    ceil
    gc_coe_floor := fun a z => by rw [le_neg, gc_ceil_coe, Int.cast_neg, neg_le_neg_iff]
    gc_ceil_coe }

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def floorAux
  body: by
  let n := Classical.indefiniteDescription _ above
  refine Int.greatestOfBdd (P := (· <= x)) n.1 (fun m hm => ?_) below
  rw [← Int.cast_le (R := α)]
  exact hm.trans n.2

中文:
定义 noncomputable
  签名: def floorAux
  定义体: by
  let n := Classical.indefiniteDescription _ above
  refine Int.greatestOfBdd (P := (· <= x)) n.1 (fun m hm => ?_) below
  rw [← Int.cast_le (R := α)]
  exact hm.trans n.2

Depends on / 依赖: MulLeftMono, MulLeftMono.toPosMulReflectLT, MulLeftReflectLT, toPosMulReflectLT
-/
private noncomputable def floorAux
    {α} [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {x : α}
    (below : exists n : Int, n <= x) (above : exists n : Int, x <= n) :
    {n : Int // n <= x ∧ forall m : Int, m <= x -> m <= n} := by
  let n := Classical.indefiniteDescription _ above
  refine Int.greatestOfBdd (P := (· <= x)) n.1 (fun m hm => ?_) below
  rw [← Int.cast_le (R := α)]
  exact hm.trans n.2

/--
theorem `exists_floor'` / 定理 `exists_floor'`

English:
theorem exists_floor'
  proof: by
  refine ⟨_, fun n => ⟨?_, (floorAux below above).2.2 _⟩⟩
  rw [← Int.cast_le (R := α)]
  exact le_trans' (floorAux below above).2.1

中文:
定理 存在_floor'
  证明: by
  refine ⟨_, fun n => ⟨?_, (floorAux below above).2.2 _⟩⟩
  rw [← Int.cast_le (R := α)]
  exact le_trans' (floorAux below above).2.1

Depends on / 依赖: Int.cast_le, MulRightMono, MulRightMono.toMulPosReflectLT, MulRightReflectLT, cast_le, floorAux, le_trans, toMulPosReflectLT
-/
theorem exists_floor'
    {α} [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] (x : α)
    (below : exists n : Int, n <= x) (above : exists n : Int, x <= n) :
    exists fl : Int, forall z : Int, z <= fl ↔ (z : α) <= x := by
  refine ⟨_, fun n => ⟨?_, (floorAux below above).2.2 _⟩⟩
  rw [← Int.cast_le (R := α)]
  exact le_trans' (floorAux below above).2.1

/-- Construct a `FloorRing` instance noncomputably, from the hypothesis that every element is
bounded above by a natural number. -/
@[no_expose, instance_reducible]
/--
Definition of `FloorRing.ofBounded` / `FloorRing.ofBounded` 的定义

English:
definition FloorRing.ofBounded
  body: have below (x : α) : exists n : Int, n <= x := by
    obtain ⟨n, hn⟩ := bounded (-x)
    use -n
    simpa [neg_le]
  have above (x : α) : exists n : Int, x <= n := by
    obtain ⟨n, hn⟩ := bounded x
    use n
    exact_mod_cast hn
  .ofFloor _ _ fun n x => (Classical.choose_spec (exists_floor' x (be

中文:
定义 Floor环.ofBounded
  定义体: have below (x : α) : exists n : Int, n <= x := by
    obtain ⟨n, hn⟩ := bounded (-x)
    use -n
    simpa [neg_le]
  have above (x : α) : exists n : Int, x <= n := by
    obtain ⟨n, hn⟩ := bounded x
    use n
    exact_mod_cast hn
  .ofFloor _ _ fun n x => (Classical.choose_spec (exists_floor' x (be

Depends on / 依赖: Classical, Classical.choose_spec, MulLeftReflectLE, MulLeftStrictMono, MulLeftStrictMono.toPosMulReflectLE, bounded, choose_spec, exists_floor, neg_le, ofFloor, toPosMulReflectLE
-/
noncomputable def FloorRing.ofBounded
    (α) [Ring α] [LinearOrder α] [IsOrderedRing α] [Nontrivial α]
    (bounded : forall x : α, exists n : Nat, x <= n) : FloorRing α :=
  have below (x : α) : exists n : Int, n <= x := by
    obtain ⟨n, hn⟩ := bounded (-x)
    use -n
    simpa [neg_le]
  have above (x : α) : exists n : Int, x <= n := by
    obtain ⟨n, hn⟩ := bounded x
    use n
    exact_mod_cast hn
  .ofFloor _ _ fun n x => (Classical.choose_spec (exists_floor' x (below x) (above x)) n).symm

namespace Int

variable [Ring α] [LinearOrder α] [FloorRing α] {z : Int} {a b : α}

/--
Definition of `floor` / `floor` 的定义

English:
definition floor
  signature: : α -> Int
  body: FloorRing.floor

中文:
定义 floor
  签名: : α -> 整数
  定义体: FloorRing.floor

Depends on / 依赖: FloorRing, FloorRing.floor, MulRightReflectLE, MulRightStrictMono, MulRightStrictMono.toMulPosReflectLE, toMulPosReflectLE
-/
def floor : α -> Int :=
  FloorRing.floor

/--
Definition of `ceil` / `ceil` 的定义

English:
definition ceil
  signature: : α -> Int
  body: FloorRing.ceil

中文:
定义 ceil
  签名: : α -> 整数
  定义体: FloorRing.ceil

Depends on / 依赖: FloorRing, FloorRing.ceil
-/
def ceil : α -> Int :=
  FloorRing.ceil

/--
Definition of `fract` / `fract` 的定义

English:
definition fract
  signature: (a : α)
  body: a - floor a

@[simp]

中文:
定义 fract
  签名: (a : α)
  定义体: a - floor a

@[simp]
-/
def fract (a : α) : α :=
  a - floor a

@[simp]
/--
theorem `floor_int` / 定理 `floor_int`

English:
theorem floor_int
  statement: (Int.floor : Int -> Int) = id
  proof: rfl

@[simp]

中文:
定理 floor_int
  结论: (整数.floor : 整数 -> 整数) = id
  证明: rfl

@[simp]
-/
theorem floor_int : (Int.floor : Int -> Int) = id :=
  rfl

@[simp]
/--
theorem `ceil_int` / 定理 `ceil_int`

English:
theorem ceil_int
  statement: (Int.ceil : Int -> Int) = id
  proof: rfl

@[simp]

中文:
定理 ceil_int
  结论: (整数.ceil : 整数 -> 整数) = id
  证明: rfl

@[simp]
-/
theorem ceil_int : (Int.ceil : Int -> Int) = id :=
  rfl

@[simp]
/--
theorem `fract_int` / 定理 `fract_int`

English:
theorem fract_int
  statement: (Int.fract : Int -> Int) = 0
  proof: funext fun x => by simp [fract]

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a

中文:
定理 fract_int
  结论: (整数.fract : 整数 -> 整数) = 0
  证明: funext fun x => by simp [fract]

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a
-/
theorem fract_int : (Int.fract : Int -> Int) = 0 :=
  funext fun x => by simp [fract]

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a

-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.

@[simp]
/--
theorem `floorRing_floor_eq` / 定理 `floorRing_floor_eq`

English:
theorem floorRing_floor_eq
  statement: @FloorRing.floor = @Int.floor
  proof: rfl

@[simp]

中文:
定理 floorRing_floor_eq
  结论: @Floor环.floor = @整数.floor
  证明: rfl

@[simp]
-/
theorem floorRing_floor_eq : @FloorRing.floor = @Int.floor :=
  rfl

@[simp]
/--
theorem `floorRing_ceil_eq` / 定理 `floorRing_ceil_eq`

English:
theorem floorRing_ceil_eq
  statement: @FloorRing.ceil = @Int.ceil
  proof: rfl

中文:
定理 floorRing_ceil_eq
  结论: @Floor环.ceil = @整数.ceil
  证明: rfl
-/
theorem floorRing_ceil_eq : @FloorRing.ceil = @Int.ceil :=
  rfl


/--
theorem `gc_coe_floor` / 定理 `gc_coe_floor`

English:
theorem gc_coe_floor
  statement: GaloisConnection ((↑) : Int -> α) floor
  proof: FloorRing.gc_coe_floor

中文:
定理 gc_coe_floor
  结论: GaloisConnection ((↑) : 整数 -> α) floor
  证明: FloorRing.gc_coe_floor

Depends on / 依赖: FloorRing, FloorRing.gc_coe_floor, gc_coe_floor
-/
theorem gc_coe_floor : GaloisConnection ((↑) : Int -> α) floor :=
  FloorRing.gc_coe_floor

/--
theorem `le_floor` / 定理 `le_floor`

English:
theorem le_floor
  statement: z <= ⌊a⌋ ↔ (z : α) <= a
  proof: (gc_coe_floor z a).symm

中文:
定理 le_floor
  结论: z <= ⌊a⌋ ↔ (z : α) <= a
  证明: (gc_coe_floor z a).symm

Depends on / 依赖: gc_coe_floor
-/
theorem le_floor : z <= ⌊a⌋ ↔ (z : α) <= a :=
  (gc_coe_floor z a).symm

/--
theorem `floor_lt` / 定理 `floor_lt`

English:
theorem floor_lt
  statement: ⌊a⌋ < z ↔ a < z
  proof: lt_iff_lt_of_le_iff_le le_floor

@[bound]

中文:
定理 floor_lt
  结论: ⌊a⌋ < z ↔ a < z
  证明: lt_iff_lt_of_le_iff_le le_floor

@[bound]

Depends on / 依赖: le_floor, lt_iff_lt_of_le_iff_le
-/
theorem floor_lt : ⌊a⌋ < z ↔ a < z :=
  lt_iff_lt_of_le_iff_le le_floor

@[bound]
/--
theorem `floor_le` / 定理 `floor_le`

English:
theorem floor_le
  given: (a : α)
  statement: (⌊a⌋ : α) <= a
  proof: gc_coe_floor.l_u_le a

中文:
定理 floor_le
  条件: (a : α)
  结论: (⌊a⌋ : α) <= a
  证明: gc_coe_floor.l_u_le a

Depends on / 依赖: gc_coe_floor, gc_coe_floor.l_u_le, l_u_le
-/
theorem floor_le (a : α) : (⌊a⌋ : α) <= a :=
  gc_coe_floor.l_u_le a

/--
theorem `floor_le_iff` / 定理 `floor_le_iff`

English:
theorem floor_le_iff
  statement: ⌊a⌋ <= z ↔ a < z + 1
  proof: by rw [← lt_add_one_iff, floor_lt]; norm_cast

中文:
定理 floor_le_iff
  结论: ⌊a⌋ <= z ↔ a < z + 1
  证明: by rw [← lt_add_one_iff, floor_lt]; norm_cast

Depends on / 依赖: floor_lt, lt_add_one_iff
-/
theorem floor_le_iff : ⌊a⌋ <= z ↔ a < z + 1 := by rw [← lt_add_one_iff, floor_lt]; norm_cast

/--
theorem `lt_floor_iff` / 定理 `lt_floor_iff`

English:
theorem lt_floor_iff
  statement: z < ⌊a⌋ ↔ z + 1 <= a
  proof: by rw [← add_one_le_iff, le_floor]; norm_cast

中文:
定理 lt_floor_iff
  结论: z < ⌊a⌋ ↔ z + 1 <= a
  证明: by rw [← add_one_le_iff, le_floor]; norm_cast

Depends on / 依赖: add_one_le_iff, le_floor
-/
theorem lt_floor_iff : z < ⌊a⌋ ↔ z + 1 <= a := by rw [← add_one_le_iff, le_floor]; norm_cast

/--
theorem `floor_nonneg` / 定理 `floor_nonneg`

English:
theorem floor_nonneg
  statement: 0 <= ⌊a⌋ ↔ 0 <= a
  proof: by rw [le_floor, Int.cast_zero]

中文:
定理 floor_nonneg
  结论: 0 <= ⌊a⌋ ↔ 0 <= a
  证明: by rw [le_floor, Int.cast_zero]

Depends on / 依赖: Int.cast_zero, cast_zero, le_floor
-/
theorem floor_nonneg : 0 <= ⌊a⌋ ↔ 0 <= a := by rw [le_floor, Int.cast_zero]

/--
theorem `floor_lt_zero` / 定理 `floor_lt_zero`

English:
theorem floor_lt_zero
  statement: ⌊a⌋ < 0 ↔ a < 0
  proof: by rw [floor_lt, Int.cast_zero]

中文:
定理 floor_lt_zero
  结论: ⌊a⌋ < 0 ↔ a < 0
  证明: by rw [floor_lt, Int.cast_zero]

Depends on / 依赖: Int.cast_zero, cast_zero, floor_lt
-/
theorem floor_lt_zero : ⌊a⌋ < 0 ↔ a < 0 := by rw [floor_lt, Int.cast_zero]


/--
theorem `gc_ceil_coe` / 定理 `gc_ceil_coe`

English:
theorem gc_ceil_coe
  statement: GaloisConnection ceil ((↑) : Int -> α)
  proof: FloorRing.gc_ceil_coe

中文:
定理 gc_ceil_coe
  结论: GaloisConnection ceil ((↑) : 整数 -> α)
  证明: FloorRing.gc_ceil_coe

Depends on / 依赖: FloorRing, FloorRing.gc_ceil_coe, gc_ceil_coe
-/
theorem gc_ceil_coe : GaloisConnection ceil ((↑) : Int -> α) :=
  FloorRing.gc_ceil_coe

/--
theorem `ceil_le` / 定理 `ceil_le`

English:
theorem ceil_le
  statement: ⌈a⌉ <= z ↔ a <= z
  proof: gc_ceil_coe a z

中文:
定理 ceil_le
  结论: ⌈a⌉ <= z ↔ a <= z
  证明: gc_ceil_coe a z

Depends on / 依赖: gc_ceil_coe
-/
theorem ceil_le : ⌈a⌉ <= z ↔ a <= z :=
  gc_ceil_coe a z

/--
theorem `lt_ceil` / 定理 `lt_ceil`

English:
theorem lt_ceil
  statement: z < ⌈a⌉ ↔ (z : α) < a
  proof: lt_iff_lt_of_le_iff_le ceil_le

@[bound]

中文:
定理 lt_ceil
  结论: z < ⌈a⌉ ↔ (z : α) < a
  证明: lt_iff_lt_of_le_iff_le ceil_le

@[bound]

Depends on / 依赖: ceil_le, lt_iff_lt_of_le_iff_le
-/
theorem lt_ceil : z < ⌈a⌉ ↔ (z : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le

@[bound]
/--
theorem `le_ceil` / 定理 `le_ceil`

English:
theorem le_ceil
  given: (a : α)
  statement: a <= ⌈a⌉
  proof: gc_ceil_coe.le_u_l a

中文:
定理 le_ceil
  条件: (a : α)
  结论: a <= ⌈a⌉
  证明: gc_ceil_coe.le_u_l a

Depends on / 依赖: gc_ceil_coe, gc_ceil_coe.le_u_l, le_u_l
-/
theorem le_ceil (a : α) : a <= ⌈a⌉ :=
  gc_ceil_coe.le_u_l a

/--
lemma `le_ceil_iff` / 引理 `le_ceil_iff`

English:
lemma le_ceil_iff
  statement: z <= ⌈a⌉ ↔ z - 1 < a
  proof: by rw [← sub_one_lt_iff, lt_ceil]; norm_cast

中文:
引理 le_ceil_iff
  结论: z <= ⌈a⌉ ↔ z - 1 < a
  证明: by rw [← sub_one_lt_iff, lt_ceil]; norm_cast

Depends on / 依赖: lt_ceil, sub_one_lt_iff
-/
lemma le_ceil_iff : z <= ⌈a⌉ ↔ z - 1 < a := by rw [← sub_one_lt_iff, lt_ceil]; norm_cast

/--
lemma `ceil_lt_iff` / 引理 `ceil_lt_iff`

English:
lemma ceil_lt_iff
  statement: ⌈a⌉ < z ↔ a <= z - 1
  proof: by rw [← le_sub_one_iff, ceil_le]; norm_cast

中文:
引理 ceil_lt_iff
  结论: ⌈a⌉ < z ↔ a <= z - 1
  证明: by rw [← le_sub_one_iff, ceil_le]; norm_cast

Depends on / 依赖: ceil_le, le_sub_one_iff
-/
lemma ceil_lt_iff : ⌈a⌉ < z ↔ a <= z - 1 := by rw [← le_sub_one_iff, ceil_le]; norm_cast

/--
theorem `ceil_nonpos` / 定理 `ceil_nonpos`

English:
theorem ceil_nonpos
  statement: ⌈a⌉ <= 0 ↔ a <= 0
  proof: by rw [ceil_le, cast_zero]

@[simp]

中文:
定理 ceil_nonpos
  结论: ⌈a⌉ <= 0 ↔ a <= 0
  证明: by rw [ceil_le, cast_zero]

@[simp]

Depends on / 依赖: cast_zero, ceil_le
-/
theorem ceil_nonpos : ⌈a⌉ <= 0 ↔ a <= 0 := by rw [ceil_le, cast_zero]

@[simp]
/--
theorem `ceil_pos` / 定理 `ceil_pos`

English:
theorem ceil_pos
  statement: 0 < ⌈a⌉ ↔ 0 < a
  proof: by rw [lt_ceil, cast_zero]

中文:
定理 ceil_pos
  结论: 0 < ⌈a⌉ ↔ 0 < a
  证明: by rw [lt_ceil, cast_zero]

Depends on / 依赖: cast_zero, lt_ceil
-/
theorem ceil_pos : 0 < ⌈a⌉ ↔ 0 < a := by rw [lt_ceil, cast_zero]

end Int

section FloorRingToSemiring

variable [Ring α] [LinearOrder α] [FloorRing α]

/-! #### A floor ring as a floor semiring -/

-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {_} ha := Int.toNat_of_nonpos (Int.floor_lt.mpr (ha.trans_eq Int.cast_zero.symm)).le
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_natCast]
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast]

/--
theorem `Int.floor_toNat` / 定理 `Int.floor_toNat`

English:
theorem Int.floor_toNat
  given: (a : α)
  statement: ⌊a⌋.toNat = ⌊a⌋₊
  proof: rfl

中文:
定理 整数.floor_to自然数
  条件: (a : α)
  结论: ⌊a⌋.to自然数 = ⌊a⌋₊
  证明: rfl
-/
theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl

/--
theorem `Int.ceil_toNat` / 定理 `Int.ceil_toNat`

English:
theorem Int.ceil_toNat
  given: (a : α)
  statement: ⌈a⌉.toNat = ⌈a⌉₊
  proof: rfl

@[simp]

中文:
定理 整数.ceil_to自然数
  条件: (a : α)
  结论: ⌈a⌉.to自然数 = ⌈a⌉₊
  证明: rfl

@[simp]
-/
theorem Int.ceil_toNat (a : α) : ⌈a⌉.toNat = ⌈a⌉₊ :=
  rfl

@[simp]
/--
theorem `Nat.floor_int` / 定理 `Nat.floor_int`

English:
theorem Nat.floor_int
  statement: (Nat.floor : Int -> Nat) = Int.toNat
  proof: rfl

@[simp]

中文:
定理 自然数.floor_int
  结论: (自然数.floor : 整数 -> 自然数) = 整数.to自然数
  证明: rfl

@[simp]
-/
theorem Nat.floor_int : (Nat.floor : Int -> Nat) = Int.toNat :=
  rfl

@[simp]
/--
theorem `Nat.ceil_int` / 定理 `Nat.ceil_int`

English:
theorem Nat.ceil_int
  statement: (Nat.ceil : Int -> Nat) = Int.toNat
  proof: rfl

中文:
定理 自然数.ceil_int
  结论: (自然数.ceil : 整数 -> 自然数) = 整数.to自然数
  证明: rfl
-/
theorem Nat.ceil_int : (Nat.ceil : Int -> Nat) = Int.toNat :=
  rfl

end FloorRingToSemiring

namespace FloorRing

/-! #### `Int.cast` is strictly monotone on floor rings -/

variable [Ring α] [LinearOrder α] [FloorRing α]

/--
theorem `intCast_mono` / 定理 `intCast_mono`

English:
theorem intCast_mono
  statement: Monotone (Int.cast : Int -> α)
  proof: fun _ _ h => (gc_ceil_coe _ _).mp h.trans' (gc_ceil_coe _ _).mpr (le_refl _)

中文:
定理 intCast_mono
  结论: 递增 (整数.cast : 整数 -> α)
  证明: fun _ _ h => (gc_ceil_coe _ _).mp h.trans' (gc_ceil_coe _ _).mpr (le_refl _)

Depends on / 依赖: gc_ceil_coe, h.trans, le_refl
-/
theorem intCast_mono : Monotone (Int.cast : Int -> α) :=
fun _ _ h => (gc_ceil_coe _ _).mp h.trans' (gc_ceil_coe _ _).mpr (le_refl _)

/--
theorem `intCast_strictMono` / 定理 `intCast_strictMono`

English:
theorem intCast_strictMono
  statement: StrictMono (Int.cast : Int -> α)
  proof: by
  obtain ⟨h⟩ : NeZero (1 : α) := inferInstance
  refine strictMono_int_of_lt_succ fun n => (intCast_mono (Int.le_add_one (le_refl _))).lt_of_ne ?_
  grind

中文:
定理 intCast_strictMono
  结论: 严格递增 (整数.cast : 整数 -> α)
  证明: by
  obtain ⟨h⟩ : NeZero (1 : α) := inferInstance
  refine strictMono_int_of_lt_succ fun n => (intCast_mono (Int.le_add_one (le_refl _))).lt_of_ne ?_
  grind

Depends on / 依赖: Int.le_add_one, NeZero, intCast_mono, le_add_one, le_refl, lt_of_ne, strictMono_int_of_lt_succ
-/
theorem intCast_strictMono : StrictMono (Int.cast : Int -> α) := by
  obtain ⟨h⟩ : NeZero (1 : α) := inferInstance
  refine strictMono_int_of_lt_succ fun n => (intCast_mono (Int.le_add_one (le_refl _))).lt_of_ne ?_
  grind

end FloorRing

namespace Int

variable [Ring α] [LinearOrder α] [FloorRing α] {z : Int} {a b : α}

@[bound]
/--
theorem `ceil_nonneg` / 定理 `ceil_nonneg`

English:
theorem ceil_nonneg
  given: (ha : 0 <= a)
  statement: 0 <= ⌈a⌉
  proof: by
  rw [← FloorRing.intCast_strictMono.le_iff_le (β := α)]; rw [Int.cast_zero]
  exact ha.trans (le_ceil a)

@[bound]

中文:
定理 ceil_nonneg
  条件: (ha : 0 <= a)
  结论: 0 <= ⌈a⌉
  证明: by
  rw [← FloorRing.intCast_strictMono.le_iff_le (β := α)]; rw [Int.cast_zero]
  exact ha.trans (le_ceil a)

@[bound]

Depends on / 依赖: FloorRing, FloorRing.intCast_strictMono.le_iff_le, Int.cast_zero, cast_zero, ha.trans, intCast_strictMono, le_ceil, le_iff_le
-/
theorem ceil_nonneg (ha : 0 <= a) : 0 <= ⌈a⌉ := by
  rw [← FloorRing.intCast_strictMono.le_iff_le (β := α)]; rw [Int.cast_zero]
  exact ha.trans (le_ceil a)

@[bound]
/--
theorem `floor_nonpos` / 定理 `floor_nonpos`

English:
theorem floor_nonpos
  given: (ha : a <= 0)
  statement: ⌊a⌋ <= 0
  proof: by
  rw [← FloorRing.intCast_strictMono.le_iff_le (β := α)]; rw [Int.cast_zero]
  exact (floor_le a).trans ha

中文:
定理 floor_nonpos
  条件: (ha : a <= 0)
  结论: ⌊a⌋ <= 0
  证明: by
  rw [← FloorRing.intCast_strictMono.le_iff_le (β := α)]; rw [Int.cast_zero]
  exact (floor_le a).trans ha

Depends on / 依赖: FloorRing, FloorRing.intCast_strictMono.le_iff_le, Int.cast_zero, cast_zero, floor_le, intCast_strictMono, le_iff_le
-/
theorem floor_nonpos (ha : a <= 0) : ⌊a⌋ <= 0 := by
  rw [← FloorRing.intCast_strictMono.le_iff_le (β := α)]; rw [Int.cast_zero]
  exact (floor_le a).trans ha

end Int
