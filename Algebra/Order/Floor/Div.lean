/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Order.Preorder.Finsupp

/-!
# Flooring, ceiling division

This file defines division rounded up and down.

The setup is an ordered monoid `α` acting on an ordered monoid `β`. If `a : α`, `b : β`, we would
like to be able to "divide" `b` by `a`, namely find `c : β` such that `a • c = b`.
This is of course not always possible, but in some cases at least there is a least `c` such that
`b ≤ a • c` and a greatest `c` such that `a • c ≤ b`. We call the first one the "ceiling division
of `b` by `a`" and the second one the "flooring division of `b` by `a`"

If `α` and `β` are both `ℕ`, then one can check that our flooring and ceiling divisions really are
the floor and ceil of the exact division.
If `α` is `ℕ` and `β` is the functions `ι → ℕ`, then the flooring and ceiling divisions are taken
pointwise.

In order theory terms, those operations are respectively the right and left adjoints to the map
`b ↦ a • b`.

## Main declarations

* `FloorDiv`: Typeclass for the existence of a flooring division, denoted `b ⌊/⌋ a`.
* `CeilDiv`: Typeclass for the existence of a ceiling division, denoted `b ⌈/⌉ a`.

Note in both cases we only allow dividing by positive inputs. We enforce the following junk values:
* `b ⌊/⌋ a = b ⌈/⌉ a = 0` if `a ≤ 0`
* `0 ⌊/⌋ a = 0 ⌈/⌉ a = 0`

## Notation

* `b ⌊/⌋ a` for the flooring division of `b` by `a`
* `b ⌈/⌉ a` for the ceiling division of `b` by `a`

## TODO

* `norm_num` extension
* Prove `⌈a / b⌉ = a ⌈/⌉ b` when `a, b : ℕ`
-/

@[expose] public section

variable {ι α β : Type*}

section OrderedAddCommMonoid
variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

/--
Definition of `FloorDiv` / `FloorDiv` 的定义

English:
class FloorDiv
  parameters: where
  axioms and operations (4):
    - floorDiv : β -> α -> β
    - floorDiv_gc(⦃a⦄) : 0 < a -> GaloisConnection (a • ·) (floorDiv · a)
    - floorDiv_nonpos(⦃a⦄) : a <= 0 -> forall b, floorDiv b a = 0
    - zero_floorDiv((a)) : floorDiv 0 a = 0

中文:
类 FloorDiv
  参数: where
  公理与运算 (4 个):
    - floorDiv : β -> α -> β
    - floorDiv_gc(⦃a⦄) : 0 < a -> GaloisConnection (a • ·) (floorDiv · a)
    - floorDiv_nonpos(⦃a⦄) : a <= 0 -> 对任意 b, floorDiv b a = 0
    - zero_floorDiv((a)) : floorDiv 0 a = 0
-/
class FloorDiv where
  /-- Flooring division. If `a > 0`, then `b ⌊/⌋ a` is the greatest `c` such that `a • c ≤ b`. -/
  floorDiv : β -> α -> β
  /-- Do not use this. Use `gc_floorDiv_smul` or `gc_floorDiv_mul` instead. -/
  protected floorDiv_gc ⦃a⦄ : 0 < a -> GaloisConnection (a • ·) (floorDiv · a)
  /-- Do not use this. Use `floorDiv_nonpos` instead. -/
  protected floorDiv_nonpos ⦃a⦄ : a <= 0 -> forall b, floorDiv b a = 0
  /-- Do not use this. Use `zero_floorDiv` instead. -/
  protected zero_floorDiv (a) : floorDiv 0 a = 0

/--
Definition of `CeilDiv` / `CeilDiv` 的定义

English:
class CeilDiv
  parameters: where
  axioms and operations (4):
    - ceilDiv : β -> α -> β
    - ceilDiv_gc(⦃a⦄) : 0 < a -> GaloisConnection (ceilDiv · a) (a • ·)
    - ceilDiv_nonpos(⦃a⦄) : a <= 0 -> forall b, ceilDiv b a = 0
    - zero_ceilDiv((a)) : ceilDiv 0 a = 0

中文:
类 CeilDiv
  参数: where
  公理与运算 (4 个):
    - ceilDiv : β -> α -> β
    - ceilDiv_gc(⦃a⦄) : 0 < a -> GaloisConnection (ceilDiv · a) (a • ·)
    - ceilDiv_nonpos(⦃a⦄) : a <= 0 -> 对任意 b, ceilDiv b a = 0
    - zero_ceilDiv((a)) : ceilDiv 0 a = 0
-/
class CeilDiv where
  /-- Ceiling division. If `a > 0`, then `b ⌈/⌉ a` is the least `c` such that `b ≤ a • c`. -/
  ceilDiv : β -> α -> β
  /-- Do not use this. Use `gc_smul_ceilDiv` or `gc_mul_ceilDiv` instead. -/
  protected ceilDiv_gc ⦃a⦄ : 0 < a -> GaloisConnection (ceilDiv · a) (a • ·)
  /-- Do not use this. Use `ceilDiv_nonpos` instead. -/
  protected ceilDiv_nonpos ⦃a⦄ : a <= 0 -> forall b, ceilDiv b a = 0
  /-- Do not use this. Use `zero_ceilDiv` instead. -/
  protected zero_ceilDiv (a) : ceilDiv 0 a = 0

@[inherit_doc] infixl:70 " ⌊/⌋ " => FloorDiv.floorDiv
@[inherit_doc] infixl:70 " ⌈/⌉ " => CeilDiv.ceilDiv

variable {α β}

section FloorDiv
variable [FloorDiv α β] {a : α} {b c : β}

/--
lemma `gc_floorDiv_smul` / 引理 `gc_floorDiv_smul`

English:
lemma gc_floorDiv_smul
  given: (ha : 0 < a)
  statement: GaloisConnection (a • · : β -> β) (· ⌊/⌋ a)
  proof: FloorDiv.floorDiv_gc ha

中文:
引理 gc_floorDiv_smul
  条件: (ha : 0 < a)
  结论: GaloisConnection (a • · : β -> β) (· ⌊/⌋ a)
  证明: FloorDiv.floorDiv_gc ha

Depends on / 依赖: FloorDiv, FloorDiv.floorDiv_gc, floorDiv_gc
-/
lemma gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • · : β -> β) (· ⌊/⌋ a) :=
  FloorDiv.floorDiv_gc ha

/--
lemma `le_floorDiv_iff_smul_le` / 引理 `le_floorDiv_iff_smul_le`

English:
lemma le_floorDiv_iff_smul_le
  given: (ha : 0 < a)
  statement: c <= b ⌊/⌋ a ↔ a • c <= b
  proof: (gc_floorDiv_smul ha _ _).symm

中文:
引理 le_floorDiv_iff_smul_le
  条件: (ha : 0 < a)
  结论: c <= b ⌊/⌋ a ↔ a • c <= b
  证明: (gc_floorDiv_smul ha _ _).symm
-/
@[simp] lemma le_floorDiv_iff_smul_le (ha : 0 < a) : c <= b ⌊/⌋ a ↔ a • c <= b :=
  (gc_floorDiv_smul ha _ _).symm

/--
lemma `floorDiv_of_nonpos` / 引理 `floorDiv_of_nonpos`

English:
lemma floorDiv_of_nonpos
  given: (ha : a <= 0) (b : β)
  statement: b ⌊/⌋ a = 0
  proof: FloorDiv.floorDiv_nonpos ha _

中文:
引理 floorDiv_of_nonpos
  条件: (ha : a <= 0) (b : β)
  结论: b ⌊/⌋ a = 0
  证明: FloorDiv.floorDiv_nonpos ha _
-/
@[simp] lemma floorDiv_of_nonpos (ha : a <= 0) (b : β) : b ⌊/⌋ a = 0 := FloorDiv.floorDiv_nonpos ha _
/--
lemma `floorDiv_zero` / 引理 `floorDiv_zero`

English:
lemma floorDiv_zero
  given: (b : β)
  statement: b ⌊/⌋ (0 : α) = 0
  proof: by simp

中文:
引理 floorDiv_zero
  条件: (b : β)
  结论: b ⌊/⌋ (0 : α) = 0
  证明: by simp

Depends on / 依赖: FloorDiv, FloorDiv.zero_floorDiv, zero_floorDiv
-/
lemma floorDiv_zero (b : β) : b ⌊/⌋ (0 : α) = 0 := by simp
/--
lemma `zero_floorDiv` / 引理 `zero_floorDiv`

English:
lemma zero_floorDiv
  given: (a : α)
  statement: (0 : β) ⌊/⌋ a = 0
  proof: FloorDiv.zero_floorDiv _

中文:
引理 zero_floorDiv
  条件: (a : α)
  结论: (0 : β) ⌊/⌋ a = 0
  证明: FloorDiv.zero_floorDiv _
-/
@[simp] lemma zero_floorDiv (a : α) : (0 : β) ⌊/⌋ a = 0 := FloorDiv.zero_floorDiv _

/--
lemma `smul_floorDiv_le` / 引理 `smul_floorDiv_le`

English:
lemma smul_floorDiv_le
  given: (ha : 0 < a)
  statement: a • (b ⌊/⌋ a) <= b
  proof: (le_floorDiv_iff_smul_le ha).1 le_rfl

中文:
引理 smul_floorDiv_le
  条件: (ha : 0 < a)
  结论: a • (b ⌊/⌋ a) <= b
  证明: (le_floorDiv_iff_smul_le ha).1 le_rfl

Depends on / 依赖: le_floorDiv_iff_smul_le, le_rfl
-/
lemma smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) <= b := (le_floorDiv_iff_smul_le ha).1 le_rfl

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α} {b c : β}

/--
lemma `gc_smul_ceilDiv` / 引理 `gc_smul_ceilDiv`

English:
lemma gc_smul_ceilDiv
  given: (ha : 0 < a)
  statement: GaloisConnection (· ⌈/⌉ a) (a • · : β -> β)
  proof: CeilDiv.ceilDiv_gc ha

@[simp]

中文:
引理 gc_smul_ceilDiv
  条件: (ha : 0 < a)
  结论: GaloisConnection (· ⌈/⌉ a) (a • · : β -> β)
  证明: CeilDiv.ceilDiv_gc ha

@[simp]

Depends on / 依赖: CeilDiv, CeilDiv.ceilDiv_gc, ceilDiv_gc
-/
lemma gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a • · : β -> β) :=
  CeilDiv.ceilDiv_gc ha

@[simp]
/--
lemma `ceilDiv_le_iff_le_smul` / 引理 `ceilDiv_le_iff_le_smul`

English:
lemma ceilDiv_le_iff_le_smul
  given: (ha : 0 < a)
  statement: b ⌈/⌉ a <= c ↔ b <= a • c
  proof: gc_smul_ceilDiv ha _ _

中文:
引理 ceilDiv_le_iff_le_smul
  条件: (ha : 0 < a)
  结论: b ⌈/⌉ a <= c ↔ b <= a • c
  证明: gc_smul_ceilDiv ha _ _

Depends on / 依赖: PosMulStrictMono, PosMulStrictMono.toPosMulReflectLE, gc_smul_ceilDiv, toPosMulReflectLE
-/
lemma ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a <= c ↔ b <= a • c := gc_smul_ceilDiv ha _ _

/--
lemma `ceilDiv_of_nonpos` / 引理 `ceilDiv_of_nonpos`

English:
lemma ceilDiv_of_nonpos
  given: (ha : a <= 0) (b : β)
  statement: b ⌈/⌉ a = 0
  proof: CeilDiv.ceilDiv_nonpos ha _

中文:
引理 ceilDiv_of_nonpos
  条件: (ha : a <= 0) (b : β)
  结论: b ⌈/⌉ a = 0
  证明: CeilDiv.ceilDiv_nonpos ha _

Depends on / 依赖: MulPosStrictMono, MulPosStrictMono.toMulPosReflectLE, toMulPosReflectLE
-/
@[simp] lemma ceilDiv_of_nonpos (ha : a <= 0) (b : β) : b ⌈/⌉ a = 0 := CeilDiv.ceilDiv_nonpos ha _
/--
lemma `ceilDiv_zero` / 引理 `ceilDiv_zero`

English:
lemma ceilDiv_zero
  given: (b : β)
  statement: b ⌈/⌉ (0 : α) = 0
  proof: by simp

中文:
引理 ceilDiv_zero
  条件: (b : β)
  结论: b ⌈/⌉ (0 : α) = 0
  证明: by simp

Depends on / 依赖: CeilDiv, CeilDiv.zero_ceilDiv, zero_ceilDiv
-/
lemma ceilDiv_zero (b : β) : b ⌈/⌉ (0 : α) = 0 := by simp
/--
lemma `zero_ceilDiv` / 引理 `zero_ceilDiv`

English:
lemma zero_ceilDiv
  given: (a : α)
  statement: (0 : β) ⌈/⌉ a = 0
  proof: CeilDiv.zero_ceilDiv _

中文:
引理 zero_ceilDiv
  条件: (a : α)
  结论: (0 : β) ⌈/⌉ a = 0
  证明: CeilDiv.zero_ceilDiv _
-/
@[simp] lemma zero_ceilDiv (a : α) : (0 : β) ⌈/⌉ a = 0 := CeilDiv.zero_ceilDiv _

/--
lemma `le_smul_ceilDiv` / 引理 `le_smul_ceilDiv`

English:
lemma le_smul_ceilDiv
  given: (ha : 0 < a)
  statement: b <= a • (b ⌈/⌉ a)
  proof: (ceilDiv_le_iff_le_smul ha).1 le_rfl

中文:
引理 le_smul_ceilDiv
  条件: (ha : 0 < a)
  结论: b <= a • (b ⌈/⌉ a)
  证明: (ceilDiv_le_iff_le_smul ha).1 le_rfl

Depends on / 依赖: ceilDiv_le_iff_le_smul, le_rfl
-/
lemma le_smul_ceilDiv (ha : 0 < a) : b <= a • (b ⌈/⌉ a) := (ceilDiv_le_iff_le_smul ha).1 le_rfl

end CeilDiv
end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid
variable [AddCommMonoid α] [LinearOrder α] [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]
  [PosSMulReflectLE α β] [FloorDiv α β] [CeilDiv α β] {a : α} {b : β}

/--
lemma `floorDiv_le_ceilDiv` / 引理 `floorDiv_le_ceilDiv`

English:
lemma floorDiv_le_ceilDiv
  statement: b ⌊/⌋ a <= b ⌈/⌉ a
  proof: by
  obtain ha | ha := le_or_gt a 0
  · simp [ha]
  · exact le_of_smul_le_smul_left ((smul_floorDiv_le ha).trans <| le_smul_ceilDiv ha) ha

中文:
引理 floorDiv_le_ceilDiv
  结论: b ⌊/⌋ a <= b ⌈/⌉ a
  证明: by
  obtain ha | ha := le_or_gt a 0
  · simp [ha]
  · exact le_of_smul_le_smul_left ((smul_floorDiv_le ha).trans <| le_smul_ceilDiv ha) ha

Depends on / 依赖: le_of_smul_le_smul_left, le_or_gt, le_smul_ceilDiv, smul_floorDiv_le
-/
lemma floorDiv_le_ceilDiv : b ⌊/⌋ a <= b ⌈/⌉ a := by
  obtain ha | ha := le_or_gt a 0
  · simp [ha]
  · exact le_of_smul_le_smul_left ((smul_floorDiv_le ha).trans <| le_smul_ceilDiv ha) ha

end LinearOrderedAddCommMonoid

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

section FloorDiv
variable [FloorDiv α β] {a : α}

/--
lemma `floorDiv_one` / 引理 `floorDiv_one`

English:
lemma floorDiv_one
  given: [IsOrderedRing α] [Nontrivial α] (b : β)
  statement: b ⌊/⌋ (1 : α) = b
  proof: eq_of_forall_le_iff fun c => by simp [zero_lt_one' α]

中文:
引理 floorDiv_one
  条件: [IsOrderedRing α] [Nontrivial α] (b : β)
  结论: b ⌊/⌋ (1 : α) = b
  证明: eq_of_forall_le_iff fun c => by simp [zero_lt_one' α]
-/
@[simp] lemma floorDiv_one [IsOrderedRing α] [Nontrivial α] (b : β) : b ⌊/⌋ (1 : α) = b :=
eq_of_forall_le_iff fun c => by simp [zero_lt_one' α]

/--
lemma `smul_floorDiv` / 引理 `smul_floorDiv`

English:
lemma smul_floorDiv
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β)
  proof: eq_of_forall_le_iff by simp [smul_le_smul_iff_of_pos_left, ha]

中文:
引理 smul_floorDiv
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β)
  证明: eq_of_forall_le_iff by simp [smul_le_smul_iff_of_pos_left, ha]
-/
@[simp] lemma smul_floorDiv [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β) :
    a • b ⌊/⌋ a = b :=
eq_of_forall_le_iff by simp [smul_le_smul_iff_of_pos_left, ha]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α}

/--
lemma `ceilDiv_one` / 引理 `ceilDiv_one`

English:
lemma ceilDiv_one
  given: [IsOrderedRing α] [Nontrivial α] (b : β)
  statement: b ⌈/⌉ (1 : α) = b
  proof: eq_of_forall_ge_iff fun c => by simp [zero_lt_one' α]

中文:
引理 ceilDiv_one
  条件: [IsOrderedRing α] [Nontrivial α] (b : β)
  结论: b ⌈/⌉ (1 : α) = b
  证明: eq_of_forall_ge_iff fun c => by simp [zero_lt_one' α]
-/
@[simp] lemma ceilDiv_one [IsOrderedRing α] [Nontrivial α] (b : β) : b ⌈/⌉ (1 : α) = b :=
eq_of_forall_ge_iff fun c => by simp [zero_lt_one' α]

/--
lemma `smul_ceilDiv` / 引理 `smul_ceilDiv`

English:
lemma smul_ceilDiv
  given: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β)
  proof: eq_of_forall_ge_iff by simp [smul_le_smul_iff_of_pos_left, ha]

中文:
引理 smul_ceilDiv
  条件: [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β)
  证明: eq_of_forall_ge_iff by simp [smul_le_smul_iff_of_pos_left, ha]
-/
@[simp] lemma smul_ceilDiv [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β) :
    a • b ⌈/⌉ a = b :=
eq_of_forall_ge_iff by simp [smul_le_smul_iff_of_pos_left, ha]

end CeilDiv

section FloorDiv
variable [FloorDiv α α] {a b c : α}

/--
lemma `gc_floorDiv_mul` / 引理 `gc_floorDiv_mul`

English:
lemma gc_floorDiv_mul
  given: (ha : 0 < a)
  statement: GaloisConnection (a * ·) (· ⌊/⌋ a)
  proof: gc_floorDiv_smul ha

中文:
引理 gc_floorDiv_mul
  条件: (ha : 0 < a)
  结论: GaloisConnection (a * ·) (· ⌊/⌋ a)
  证明: gc_floorDiv_smul ha

Depends on / 依赖: gc_floorDiv_smul
-/
lemma gc_floorDiv_mul (ha : 0 < a) : GaloisConnection (a * ·) (· ⌊/⌋ a) := gc_floorDiv_smul ha
/--
lemma `le_floorDiv_iff_mul_le` / 引理 `le_floorDiv_iff_mul_le`

English:
lemma le_floorDiv_iff_mul_le
  given: (ha : 0 < a)
  statement: c <= b ⌊/⌋ a ↔ a • c <= b
  proof: le_floorDiv_iff_smul_le ha

中文:
引理 le_floorDiv_iff_mul_le
  条件: (ha : 0 < a)
  结论: c <= b ⌊/⌋ a ↔ a • c <= b
  证明: le_floorDiv_iff_smul_le ha

Depends on / 依赖: le_floorDiv_iff_smul_le
-/
lemma le_floorDiv_iff_mul_le (ha : 0 < a) : c <= b ⌊/⌋ a ↔ a • c <= b := le_floorDiv_iff_smul_le ha

end FloorDiv

section CeilDiv
variable [CeilDiv α α] {a b c : α}

/--
lemma `gc_mul_ceilDiv` / 引理 `gc_mul_ceilDiv`

English:
lemma gc_mul_ceilDiv
  given: (ha : 0 < a)
  statement: GaloisConnection (· ⌈/⌉ a) (a * ·)
  proof: gc_smul_ceilDiv ha

中文:
引理 gc_mul_ceilDiv
  条件: (ha : 0 < a)
  结论: GaloisConnection (· ⌈/⌉ a) (a * ·)
  证明: gc_smul_ceilDiv ha

Depends on / 依赖: gc_smul_ceilDiv
-/
lemma gc_mul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a * ·) := gc_smul_ceilDiv ha
/--
lemma `ceilDiv_le_iff_le_mul` / 引理 `ceilDiv_le_iff_le_mul`

English:
lemma ceilDiv_le_iff_le_mul
  given: (ha : 0 < a)
  statement: b ⌈/⌉ a <= c ↔ b <= a * c
  proof: ceilDiv_le_iff_le_smul ha

中文:
引理 ceilDiv_le_iff_le_mul
  条件: (ha : 0 < a)
  结论: b ⌈/⌉ a <= c ↔ b <= a * c
  证明: ceilDiv_le_iff_le_smul ha

Depends on / 依赖: ceilDiv_le_iff_le_smul
-/
lemma ceilDiv_le_iff_le_mul (ha : 0 < a) : b ⌈/⌉ a <= c ↔ b <= a * c := ceilDiv_le_iff_le_smul ha

end CeilDiv
end OrderedSemiring

namespace Nat

/--
Instance `instFloorDiv` / 实例 `instFloorDiv`

English:
instance instFloorDiv
  signature: : FloorDiv Nat Nat where
  body: HDiv.hDiv
  floorDiv_gc a ha := by simpa [mul_comm] using Nat.galoisConnection_mul_div ha
  floorDiv_nonpos a ha b := by rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_floorDiv := Nat.zero_div

中文:
实例 instFloorDiv
  签名: : FloorDiv 自然数 自然数 where
  定义体: HDiv.hDiv
  floorDiv_gc a ha := by simpa [mul_comm] using Nat.galoisConnection_mul_div ha
  floorDiv_nonpos a ha b := by rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_floorDiv := Nat.zero_div

Depends on / 依赖: HDiv.hDiv, le_sup, mul_le_mul
-/
instance instFloorDiv : FloorDiv Nat Nat where
  floorDiv := HDiv.hDiv
  floorDiv_gc a ha := by simpa [mul_comm] using Nat.galoisConnection_mul_div ha
  floorDiv_nonpos a ha b := by rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_floorDiv := Nat.zero_div

/--
Instance `instCeilDiv` / 实例 `instCeilDiv`

English:
instance instCeilDiv
  signature: : CeilDiv Nat Nat where
  body: (a + b - 1) / b
  ceilDiv_gc a ha b c := by
    simp [div_le_iff_le_mul_add_pred ha, add_assoc, tsub_add_cancel_of_le <| succ_le_iff.2 ha]
  ceilDiv_nonpos a ha b := by simp_rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_ceilDiv a := by cases a <;> simp [Nat.div_eq_zero_iff]

中文:
实例 instCeilDiv
  签名: : CeilDiv 自然数 自然数 where
  定义体: (a + b - 1) / b
  ceilDiv_gc a ha b c := by
    simp [div_le_iff_le_mul_add_pred ha, add_assoc, tsub_add_cancel_of_le <| succ_le_iff.2 ha]
  ceilDiv_nonpos a ha b := by simp_rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_ceilDiv a := by cases a <;> simp [Nat.div_eq_zero_iff]

Depends on / 依赖: le_inf, mul_le_mul
-/
instance instCeilDiv : CeilDiv Nat Nat where
  ceilDiv a b := (a + b - 1) / b
  ceilDiv_gc a ha b c := by
    simp [div_le_iff_le_mul_add_pred ha, add_assoc, tsub_add_cancel_of_le <| succ_le_iff.2 ha]
  ceilDiv_nonpos a ha b := by simp_rw [ha.antisymm <| zero_le _, Nat.div_zero]
  zero_ceilDiv a := by cases a <;> simp [Nat.div_eq_zero_iff]

/--
lemma `floorDiv_eq_div` / 引理 `floorDiv_eq_div`

English:
lemma floorDiv_eq_div
  given: (a b : Nat)
  statement: a ⌊/⌋ b = a / b
  proof: rfl

中文:
引理 floorDiv_eq_div
  条件: (a b : 自然数)
  结论: a ⌊/⌋ b = a / b
  证明: rfl

Depends on / 依赖: OrderIso, OrderIso.mulRight, lt_of_le_of_ne, map_finset_sup
-/
@[simp] lemma floorDiv_eq_div (a b : Nat) : a ⌊/⌋ b = a / b := rfl
/--
lemma `ceilDiv_eq_add_pred_div` / 引理 `ceilDiv_eq_add_pred_div`

English:
lemma ceilDiv_eq_add_pred_div
  given: (a b : Nat)
  statement: a ⌈/⌉ b = (a + b - 1) / b
  proof: rfl

中文:
引理 ceilDiv_eq_add_pred_div
  条件: (a b : 自然数)
  结论: a ⌈/⌉ b = (a + b - 1) / b
  证明: rfl
-/
lemma ceilDiv_eq_add_pred_div (a b : Nat) : a ⌈/⌉ b = (a + b - 1) / b := rfl

end Nat

namespace Pi
variable {π : ι -> Type*} [AddCommMonoid α] [PartialOrder α]
  [forall i, AddCommMonoid (π i)] [forall i, PartialOrder (π i)]
  [forall i, SMulZeroClass α (π i)]

section FloorDiv
variable [forall i, FloorDiv α (π i)]

/--
Instance `instFloorDiv` / 实例 `instFloorDiv`

English:
instance instFloorDiv
  signature: : FloorDiv α (forall i, π i) where
  body: f i ⌊/⌋ a
  floorDiv_gc _a ha _f _g := forall_congr' fun _i => gc_floorDiv_smul ha _ _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext i; exact zero_floorDiv a

@[push ←]

中文:
实例 instFloorDiv
  签名: : FloorDiv α (对任意 i, π i) where
  定义体: f i ⌊/⌋ a
  floorDiv_gc _a ha _f _g := forall_congr' fun _i => gc_floorDiv_smul ha _ _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext i; exact zero_floorDiv a

@[push ←]

Depends on / 依赖: OrderIso, OrderIso.divRight, lt_of_le_of_ne, map_finset_sup
-/
instance instFloorDiv : FloorDiv α (forall i, π i) where
  floorDiv f a i := f i ⌊/⌋ a
  floorDiv_gc _a ha _f _g := forall_congr' fun _i => gc_floorDiv_smul ha _ _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext i; exact zero_floorDiv a

@[push ←]
/--
lemma `floorDiv_def` / 引理 `floorDiv_def`

English:
lemma floorDiv_def
  given: (f : forall i, π i) (a : α)
  statement: f ⌊/⌋ a = fun i => f i ⌊/⌋ a
  proof: rfl

中文:
引理 floorDiv_def
  条件: (f : 对任意 i, π i) (a : α)
  结论: f ⌊/⌋ a = fun i => f i ⌊/⌋ a
  证明: rfl
-/
lemma floorDiv_def (f : forall i, π i) (a : α) : f ⌊/⌋ a = fun i => f i ⌊/⌋ a := rfl
/--
lemma `floorDiv_apply` / 引理 `floorDiv_apply`

English:
lemma floorDiv_apply
  given: (f : forall i, π i) (a : α) (i : ι)
  statement: (f ⌊/⌋ a) i = f i ⌊/⌋ a
  proof: rfl

中文:
引理 floorDiv_apply
  条件: (f : 对任意 i, π i) (a : α) (i : ι)
  结论: (f ⌊/⌋ a) i = f i ⌊/⌋ a
  证明: rfl
-/
@[simp] lemma floorDiv_apply (f : forall i, π i) (a : α) (i : ι) : (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

end FloorDiv

section CeilDiv
variable [forall i, CeilDiv α (π i)]

/--
Instance `instCeilDiv` / 实例 `instCeilDiv`

English:
instance instCeilDiv
  signature: : CeilDiv α (forall i, π i) where
  body: f i ⌈/⌉ a
  ceilDiv_gc _a ha _f _g := forall_congr' fun _i => gc_smul_ceilDiv ha _ _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

中文:
实例 instCeilDiv
  签名: : CeilDiv α (对任意 i, π i) where
  定义体: f i ⌈/⌉ a
  ceilDiv_gc _a ha _f _g := forall_congr' fun _i => gc_smul_ceilDiv ha _ _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _
-/
instance instCeilDiv : CeilDiv α (forall i, π i) where
  ceilDiv f a i := f i ⌈/⌉ a
  ceilDiv_gc _a ha _f _g := forall_congr' fun _i => gc_smul_ceilDiv ha _ _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

/--
lemma `ceilDiv_def` / 引理 `ceilDiv_def`

English:
lemma ceilDiv_def
  given: (f : forall i, π i) (a : α)
  statement: f ⌈/⌉ a = fun i => f i ⌈/⌉ a
  proof: rfl

中文:
引理 ceilDiv_def
  条件: (f : 对任意 i, π i) (a : α)
  结论: f ⌈/⌉ a = fun i => f i ⌈/⌉ a
  证明: rfl
-/
lemma ceilDiv_def (f : forall i, π i) (a : α) : f ⌈/⌉ a = fun i => f i ⌈/⌉ a := rfl
/--
lemma `ceilDiv_apply` / 引理 `ceilDiv_apply`

English:
lemma ceilDiv_apply
  given: (f : forall i, π i) (a : α) (i : ι)
  statement: (f ⌈/⌉ a) i = f i ⌈/⌉ a
  proof: rfl

中文:
引理 ceilDiv_apply
  条件: (f : 对任意 i, π i) (a : α) (i : ι)
  结论: (f ⌈/⌉ a) i = f i ⌈/⌉ a
  证明: rfl
-/
@[simp] lemma ceilDiv_apply (f : forall i, π i) (a : α) (i : ι) : (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

end CeilDiv
end Pi

namespace Finsupp
variable [AddCommMonoid α] [PartialOrder α]
  [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]

section FloorDiv
variable [FloorDiv α β] {f : ι ->₀ β} {a : α}

/--
Instance `instFloorDiv` / 实例 `instFloorDiv`

English:
instance instFloorDiv
  signature: : FloorDiv α (ι ->₀ β) where
  body: f.mapRange (· ⌊/⌋ a) zero_floorDiv _
  floorDiv_gc _a ha f _g := forall_congr' fun i => by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_floorDiv_smul ha (f i) _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext; exact zero_floorDiv _

中文:
实例 instFloorDiv
  签名: : FloorDiv α (ι ->₀ β) where
  定义体: f.mapRange (· ⌊/⌋ a) zero_floorDiv _
  floorDiv_gc _a ha f _g := forall_congr' fun i => by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_floorDiv_smul ha (f i) _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext; exact zero_floorDiv _

Depends on / 依赖: f.mapRange, mapRange, zero_floorDiv
-/
noncomputable instance instFloorDiv : FloorDiv α (ι ->₀ β) where
floorDiv f a := f.mapRange (· ⌊/⌋ a) zero_floorDiv _
  floorDiv_gc _a ha f _g := forall_congr' fun i => by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_floorDiv_smul ha (f i) _
  floorDiv_nonpos a ha f := by ext i; exact floorDiv_of_nonpos ha _
  zero_floorDiv a := by ext; exact zero_floorDiv _

/--
lemma `floorDiv_def` / 引理 `floorDiv_def`

English:
lemma floorDiv_def
  given: (f : ι ->₀ β) (a : α)
  statement: f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_floorDiv _)
  proof: rfl

中文:
引理 floorDiv_def
  条件: (f : ι ->₀ β) (a : α)
  结论: f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_floorDiv _)
  证明: rfl
-/
lemma floorDiv_def (f : ι ->₀ β) (a : α) : f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_floorDiv _) := rfl
set_option warning.simp.otherHead false in
/--
lemma `coe_floorDiv` / 引理 `coe_floorDiv`

English:
lemma coe_floorDiv
  given: (f : ι ->₀ β) (a : α)
  statement: f ⌊/⌋ a = fun i => f i ⌊/⌋ a
  proof: rfl

中文:
引理 coe_floorDiv
  条件: (f : ι ->₀ β) (a : α)
  结论: f ⌊/⌋ a = fun i => f i ⌊/⌋ a
  证明: rfl
-/
@[norm_cast] lemma coe_floorDiv (f : ι ->₀ β) (a : α) : f ⌊/⌋ a = fun i => f i ⌊/⌋ a := rfl
/--
lemma `floorDiv_apply` / 引理 `floorDiv_apply`

English:
lemma floorDiv_apply
  given: (f : ι ->₀ β) (a : α) (i : ι)
  statement: (f ⌊/⌋ a) i = f i ⌊/⌋ a
  proof: rfl

中文:
引理 floorDiv_apply
  条件: (f : ι ->₀ β) (a : α) (i : ι)
  结论: (f ⌊/⌋ a) i = f i ⌊/⌋ a
  证明: rfl
-/
@[simp] lemma floorDiv_apply (f : ι ->₀ β) (a : α) (i : ι) : (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

/--
lemma `support_floorDiv_subset` / 引理 `support_floorDiv_subset`

English:
lemma support_floorDiv_subset
  statement: (f ⌊/⌋ a).support subseteq f.support
  proof: by
  simp +contextual [Finset.subset_iff, not_imp_not]

中文:
引理 support_floorDiv_subset
  结论: (f ⌊/⌋ a).support subseteq f.support
  证明: by
  simp +contextual [Finset.subset_iff, not_imp_not]

Depends on / 依赖: Finset, Finset.subset_iff, contextual, not_imp_not, subset_iff
-/
lemma support_floorDiv_subset : (f ⌊/⌋ a).support subseteq f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {f : ι ->₀ β} {a : α}

/--
Instance `instCeilDiv` / 实例 `instCeilDiv`

English:
instance instCeilDiv
  signature: : CeilDiv α (ι ->₀ β) where
  body: f.mapRange (· ⌈/⌉ a) zero_ceilDiv _
  ceilDiv_gc _a ha f _g := forall_congr' fun i => by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_smul_ceilDiv ha (f i) _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

中文:
实例 instCeilDiv
  签名: : CeilDiv α (ι ->₀ β) where
  定义体: f.mapRange (· ⌈/⌉ a) zero_ceilDiv _
  ceilDiv_gc _a ha f _g := forall_congr' fun i => by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_smul_ceilDiv ha (f i) _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

Depends on / 依赖: f.mapRange, mapRange, zero_ceilDiv
-/
noncomputable instance instCeilDiv : CeilDiv α (ι ->₀ β) where
ceilDiv f a := f.mapRange (· ⌈/⌉ a) zero_ceilDiv _
  ceilDiv_gc _a ha f _g := forall_congr' fun i => by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_smul_ceilDiv ha (f i) _
  ceilDiv_nonpos a ha f := by ext i; exact ceilDiv_of_nonpos ha _
  zero_ceilDiv a := by ext; exact zero_ceilDiv _

/--
lemma `ceilDiv_def` / 引理 `ceilDiv_def`

English:
lemma ceilDiv_def
  given: (f : ι ->₀ β) (a : α)
  statement: f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_ceilDiv _)
  proof: rfl

中文:
引理 ceilDiv_def
  条件: (f : ι ->₀ β) (a : α)
  结论: f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_ceilDiv _)
  证明: rfl
-/
lemma ceilDiv_def (f : ι ->₀ β) (a : α) : f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_ceilDiv _) := rfl
set_option warning.simp.otherHead false in
/--
lemma `coe_ceilDiv_def` / 引理 `coe_ceilDiv_def`

English:
lemma coe_ceilDiv_def
  given: (f : ι ->₀ β) (a : α)
  statement: f ⌈/⌉ a = fun i => f i ⌈/⌉ a
  proof: rfl

中文:
引理 coe_ceilDiv_def
  条件: (f : ι ->₀ β) (a : α)
  结论: f ⌈/⌉ a = fun i => f i ⌈/⌉ a
  证明: rfl
-/
@[norm_cast] lemma coe_ceilDiv_def (f : ι ->₀ β) (a : α) : f ⌈/⌉ a = fun i => f i ⌈/⌉ a := rfl
/--
lemma `ceilDiv_apply` / 引理 `ceilDiv_apply`

English:
lemma ceilDiv_apply
  given: (f : ι ->₀ β) (a : α) (i : ι)
  statement: (f ⌈/⌉ a) i = f i ⌈/⌉ a
  proof: rfl

中文:
引理 ceilDiv_apply
  条件: (f : ι ->₀ β) (a : α) (i : ι)
  结论: (f ⌈/⌉ a) i = f i ⌈/⌉ a
  证明: rfl
-/
@[simp] lemma ceilDiv_apply (f : ι ->₀ β) (a : α) (i : ι) : (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

/--
lemma `support_ceilDiv_subset` / 引理 `support_ceilDiv_subset`

English:
lemma support_ceilDiv_subset
  statement: (f ⌈/⌉ a).support subseteq f.support
  proof: by
  simp +contextual [Finset.subset_iff, not_imp_not]

中文:
引理 support_ceilDiv_subset
  结论: (f ⌈/⌉ a).support subseteq f.support
  证明: by
  simp +contextual [Finset.subset_iff, not_imp_not]

Depends on / 依赖: Finset, Finset.subset_iff, contextual, not_imp_not, subset_iff
-/
lemma support_ceilDiv_subset : (f ⌈/⌉ a).support subseteq f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

end CeilDiv
end Finsupp

/-- This is the motivating example. -/
noncomputable example : FloorDiv Nat (Nat ->₀ Nat) := inferInstance
