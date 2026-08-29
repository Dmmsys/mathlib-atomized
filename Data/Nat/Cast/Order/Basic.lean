/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.NeZero
public import Mathlib.Order.Hom.Basic

/-!
# Cast of natural numbers: lemmas about order

-/

@[expose] public section

assert_not_exists IsOrderedMonoid

variable {α : Type*}

namespace Nat
variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]

@[gcongr, mono]
/--
theorem `mono_cast` / 定理 `mono_cast`

English:
theorem mono_cast
  statement: Monotone (Nat.cast : Nat -> α)
  proof: monotone_nat_of_le_succ fun n => by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

中文:
定理 mono_cast
  结论: Monotone (自然数.cast : 自然数 -> α)
  证明: monotone_nat_of_le_succ fun n => by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

Depends on / 依赖: Nat.cast_succ, cast_succ, le_add_of_nonneg_right, monotone_nat_of_le_succ, zero_le_one
-/
theorem mono_cast : Monotone (Nat.cast : Nat -> α) :=
  monotone_nat_of_le_succ fun n => by
    rw [Nat.cast_succ]; exact le_add_of_nonneg_right zero_le_one

/-- See also `Nat.cast_nonneg`, specialised to `IsOrderedRing`. -/
@[simp low]
/--
theorem `cast_nonneg'` / 定理 `cast_nonneg'`

English:
theorem cast_nonneg'
  given: (n : Nat)
  statement: 0 <= (n : α)
  proof: @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

中文:
定理 cast_nonneg'
  条件: (n : 自然数)
  结论: 0 <= (n : α)
  证明: @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

Depends on / 依赖: Nat.cast_zero, Nat.zero_le, cast_zero, mono_cast, zero_le
-/
theorem cast_nonneg' (n : Nat) : 0 <= (n : α) :=
  @Nat.cast_zero α _ ▸ mono_cast (Nat.zero_le n)

/-- See also `Nat.ofNat_nonneg`, specialised to `IsOrderedRing`. -/
@[simp low]
/--
theorem `ofNat_nonneg'` / 定理 `ofNat_nonneg'`

English:
theorem ofNat_nonneg'
  given: (n : Nat) [n.AtLeastTwo]
  statement: 0 <= (ofNat(n) : α)
  proof: cast_nonneg' n

中文:
定理 ofNat_nonneg'
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: 0 <= (of自然数(n) : α)
  证明: cast_nonneg' n

Depends on / 依赖: cast_nonneg
-/
theorem ofNat_nonneg' (n : Nat) [n.AtLeastTwo] : 0 <= (ofNat(n) : α) := cast_nonneg' n

section Nontrivial

variable [NeZero (1 : α)]

/--
theorem `cast_add_one_pos` / 定理 `cast_add_one_pos`

English:
theorem cast_add_one_pos
  given: (n : Nat)
  statement: 0 < (n : α) + 1
  proof: by
  apply zero_lt_one.trans_le
  convert! (@mono_cast α _).imp (?_ : 1 <= n + 1)
  <;> simp

中文:
定理 cast_add_one_pos
  条件: (n : 自然数)
  结论: 0 < (n : α) + 1
  证明: by
  apply zero_lt_one.trans_le
  convert! (@mono_cast α _).imp (?_ : 1 <= n + 1)
  <;> simp

Depends on / 依赖: convert, mono_cast, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem cast_add_one_pos (n : Nat) : 0 < (n : α) + 1 := by
  apply zero_lt_one.trans_le
  convert! (@mono_cast α _).imp (?_ : 1 <= n + 1)
  <;> simp

/-- See also `Nat.cast_pos`, specialised to `IsOrderedRing`. -/
@[simp low]
/--
theorem `cast_pos'` / 定理 `cast_pos'`

English:
theorem cast_pos'
  given: {n : Nat}
  statement: (0 : α) < n ↔ 0 < n
  proof: by cases n <;> simp [cast_add_one_pos]

中文:
定理 cast_pos'
  条件: {n : 自然数}
  结论: (0 : α) < n ↔ 0 < n
  证明: by cases n <;> simp [cast_add_one_pos]

Depends on / 依赖: cast_add_one_pos
-/
theorem cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n := by cases n <;> simp [cast_add_one_pos]

end Nontrivial

variable [CharZero α] {m n : Nat}

@[gcongr]
/--
theorem `strictMono_cast` / 定理 `strictMono_cast`

English:
theorem strictMono_cast
  statement: StrictMono (Nat.cast : Nat -> α)
  proof: mono_cast.strictMono_of_injective cast_injective

中文:
定理 strictMono_cast
  结论: StrictMono (自然数.cast : 自然数 -> α)
  证明: mono_cast.strictMono_of_injective cast_injective

Depends on / 依赖: cast_injective, mono_cast, mono_cast.strictMono_of_injective, strictMono_of_injective
-/
theorem strictMono_cast : StrictMono (Nat.cast : Nat -> α) :=
  mono_cast.strictMono_of_injective cast_injective

/-- `Nat.cast : ℕ → α` as an `OrderEmbedding` -/
@[simps! -fullyApplied]
/--
Definition of `castOrderEmbedding` / `castOrderEmbedding` 的定义

English:
definition castOrderEmbedding
  signature: : Nat ↪o α
  body: OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast

@[simp, norm_cast]

中文:
定义 castOrderEmbedding
  签名: : 自然数 ↪o α
  定义体: OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast

@[simp, norm_cast]

Depends on / 依赖: Nat.cast, Nat.strictMono_cast, OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, strictMono_cast
-/
def castOrderEmbedding : Nat ↪o α :=
  OrderEmbedding.ofStrictMono Nat.cast Nat.strictMono_cast

@[simp, norm_cast]
/--
theorem `cast_le` / 定理 `cast_le`

English:
theorem cast_le
  statement: (m : α) <= n ↔ m <= n
  proof: strictMono_cast.le_iff_le

@[simp, norm_cast, mono]

中文:
定理 cast_le
  结论: (m : α) <= n ↔ m <= n
  证明: strictMono_cast.le_iff_le

@[simp, norm_cast, mono]

Depends on / 依赖: le_iff_le, strictMono_cast, strictMono_cast.le_iff_le
-/
theorem cast_le : (m : α) <= n ↔ m <= n :=
  strictMono_cast.le_iff_le

@[simp, norm_cast, mono]
/--
theorem `cast_lt` / 定理 `cast_lt`

English:
theorem cast_lt
  statement: (m : α) < n ↔ m < n
  proof: strictMono_cast.lt_iff_lt

@[simp, norm_cast]

中文:
定理 cast_lt
  结论: (m : α) < n ↔ m < n
  证明: strictMono_cast.lt_iff_lt

@[simp, norm_cast]

Depends on / 依赖: lt_iff_lt, strictMono_cast, strictMono_cast.lt_iff_lt
-/
theorem cast_lt : (m : α) < n ↔ m < n :=
  strictMono_cast.lt_iff_lt

@[simp, norm_cast]
/--
theorem `one_lt_cast` / 定理 `one_lt_cast`

English:
theorem one_lt_cast
  statement: 1 < (n : α) ↔ 1 < n
  proof: by rw [← cast_one, cast_lt]

@[simp, norm_cast]

中文:
定理 one_lt_cast
  结论: 1 < (n : α) ↔ 1 < n
  证明: by rw [← cast_one, cast_lt]

@[simp, norm_cast]

Depends on / 依赖: cast_lt, cast_one
-/
theorem one_lt_cast : 1 < (n : α) ↔ 1 < n := by rw [← cast_one, cast_lt]

@[simp, norm_cast]
/--
theorem `one_le_cast` / 定理 `one_le_cast`

English:
theorem one_le_cast
  statement: 1 <= (n : α) ↔ 1 <= n
  proof: by rw [← cast_one, cast_le]

中文:
定理 one_le_cast
  结论: 1 <= (n : α) ↔ 1 <= n
  证明: by rw [← cast_one, cast_le]

Depends on / 依赖: cast_le, cast_one
-/
theorem one_le_cast : 1 <= (n : α) ↔ 1 <= n := by rw [← cast_one, cast_le]

/--
theorem `one_le_cast_iff_ne_zero` / 定理 `one_le_cast_iff_ne_zero`

English:
theorem one_le_cast_iff_ne_zero
  statement: 1 <= (n : α) ↔ n != 0
  proof: one_le_cast.trans one_le_iff_ne_zero

@[simp, norm_cast]

中文:
定理 one_le_cast_iff_ne_zero
  结论: 1 <= (n : α) ↔ n != 0
  证明: one_le_cast.trans one_le_iff_ne_zero

@[simp, norm_cast]

Depends on / 依赖: one_le_cast, one_le_cast.trans, one_le_iff_ne_zero
-/
theorem one_le_cast_iff_ne_zero : 1 <= (n : α) ↔ n != 0 :=
  one_le_cast.trans one_le_iff_ne_zero

@[simp, norm_cast]
/--
theorem `cast_lt_one` / 定理 `cast_lt_one`

English:
theorem cast_lt_one
  statement: (n : α) < 1 ↔ n = 0
  proof: by
  rw [← cast_one]; rw [cast_lt]; rw [Nat.lt_succ_iff]; rw [le_zero]

@[simp, norm_cast]

中文:
定理 cast_lt_one
  结论: (n : α) < 1 ↔ n = 0
  证明: by
  rw [← cast_one]; rw [cast_lt]; rw [Nat.lt_succ_iff]; rw [le_zero]

@[simp, norm_cast]

Depends on / 依赖: Nat.lt_succ_iff, cast_lt, cast_one, le_zero, lt_succ_iff
-/
theorem cast_lt_one : (n : α) < 1 ↔ n = 0 := by
  rw [← cast_one]; rw [cast_lt]; rw [Nat.lt_succ_iff]; rw [le_zero]

@[simp, norm_cast]
/--
theorem `cast_le_one` / 定理 `cast_le_one`

English:
theorem cast_le_one
  statement: (n : α) <= 1 ↔ n <= 1
  proof: by rw [← cast_one, cast_le]

中文:
定理 cast_le_one
  结论: (n : α) <= 1 ↔ n <= 1
  证明: by rw [← cast_one, cast_le]

Depends on / 依赖: cast_le, cast_one
-/
theorem cast_le_one : (n : α) <= 1 ↔ n <= 1 := by rw [← cast_one, cast_le]

/--
lemma `cast_nonpos` / 引理 `cast_nonpos`

English:
lemma cast_nonpos
  statement: (n : α) <= 0 ↔ n = 0
  proof: by norm_cast; lia

中文:
引理 cast_nonpos
  结论: (n : α) <= 0 ↔ n = 0
  证明: by norm_cast; lia
-/
@[simp] lemma cast_nonpos : (n : α) <= 0 ↔ n = 0 := by norm_cast; lia

section
variable [m.AtLeastTwo]

@[simp]
/--
theorem `ofNat_le_cast` / 定理 `ofNat_le_cast`

English:
theorem ofNat_le_cast
  statement: (ofNat(m) : α) <= n ↔ (OfNat.ofNat m : Nat) <= n
  proof: cast_le

@[simp]

中文:
定理 ofNat_le_cast
  结论: (of自然数(m) : α) <= n ↔ (Of自然数.of自然数 m : 自然数) <= n
  证明: cast_le

@[simp]

Depends on / 依赖: cast_le
-/
theorem ofNat_le_cast : (ofNat(m) : α) <= n ↔ (OfNat.ofNat m : Nat) <= n :=
  cast_le

@[simp]
/--
theorem `ofNat_lt_cast` / 定理 `ofNat_lt_cast`

English:
theorem ofNat_lt_cast
  statement: (ofNat(m) : α) < n ↔ (OfNat.ofNat m : Nat) < n
  proof: cast_lt

中文:
定理 ofNat_lt_cast
  结论: (of自然数(m) : α) < n ↔ (Of自然数.of自然数 m : 自然数) < n
  证明: cast_lt

Depends on / 依赖: cast_lt
-/
theorem ofNat_lt_cast : (ofNat(m) : α) < n ↔ (OfNat.ofNat m : Nat) < n :=
  cast_lt

end

variable [n.AtLeastTwo]

@[simp]
/--
theorem `cast_le_ofNat` / 定理 `cast_le_ofNat`

English:
theorem cast_le_ofNat
  statement: (m : α) <= (ofNat(n) : α) ↔ m <= OfNat.ofNat n
  proof: cast_le

@[simp]

中文:
定理 cast_le_ofNat
  结论: (m : α) <= (of自然数(n) : α) ↔ m <= Of自然数.of自然数 n
  证明: cast_le

@[simp]

Depends on / 依赖: cast_le
-/
theorem cast_le_ofNat : (m : α) <= (ofNat(n) : α) ↔ m <= OfNat.ofNat n :=
  cast_le

@[simp]
/--
theorem `cast_lt_ofNat` / 定理 `cast_lt_ofNat`

English:
theorem cast_lt_ofNat
  statement: (m : α) < (ofNat(n) : α) ↔ m < OfNat.ofNat n
  proof: cast_lt

@[simp]

中文:
定理 cast_lt_ofNat
  结论: (m : α) < (of自然数(n) : α) ↔ m < Of自然数.of自然数 n
  证明: cast_lt

@[simp]

Depends on / 依赖: cast_lt
-/
theorem cast_lt_ofNat : (m : α) < (ofNat(n) : α) ↔ m < OfNat.ofNat n :=
  cast_lt

@[simp]
/--
theorem `one_lt_ofNat` / 定理 `one_lt_ofNat`

English:
theorem one_lt_ofNat
  statement: 1 < (ofNat(n) : α)
  proof: one_lt_cast.mpr AtLeastTwo.one_lt

@[simp]

中文:
定理 one_lt_ofNat
  结论: 1 < (of自然数(n) : α)
  证明: one_lt_cast.mpr AtLeastTwo.one_lt

@[simp]

Depends on / 依赖: AtLeastTwo, AtLeastTwo.one_lt, one_lt, one_lt_cast, one_lt_cast.mpr
-/
theorem one_lt_ofNat : 1 < (ofNat(n) : α) :=
  one_lt_cast.mpr AtLeastTwo.one_lt

@[simp]
/--
theorem `one_le_ofNat` / 定理 `one_le_ofNat`

English:
theorem one_le_ofNat
  statement: 1 <= (ofNat(n) : α)
  proof: one_le_cast.mpr NeZero.one_le

@[simp]

中文:
定理 one_le_ofNat
  结论: 1 <= (of自然数(n) : α)
  证明: one_le_cast.mpr NeZero.one_le

@[simp]

Depends on / 依赖: NeZero, NeZero.one_le, one_le, one_le_cast, one_le_cast.mpr
-/
theorem one_le_ofNat : 1 <= (ofNat(n) : α) :=
  one_le_cast.mpr NeZero.one_le

@[simp]
/--
theorem `not_ofNat_le_one` / 定理 `not_ofNat_le_one`

English:
theorem not_ofNat_le_one
  statement: ¬(ofNat(n) : α) <= 1
  proof: (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt

@[simp]

中文:
定理 not_ofNat_le_one
  结论: ¬(of自然数(n) : α) <= 1
  证明: (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt

@[simp]

Depends on / 依赖: AtLeastTwo, AtLeastTwo.one_lt, cast_le_one, cast_le_one.not.trans, not_le, one_lt
-/
theorem not_ofNat_le_one : ¬(ofNat(n) : α) <= 1 :=
  (cast_le_one.not.trans not_le).mpr AtLeastTwo.one_lt

@[simp]
/--
theorem `not_ofNat_lt_one` / 定理 `not_ofNat_lt_one`

English:
theorem not_ofNat_lt_one
  statement: ¬(ofNat(n) : α) < 1
  proof: mt le_of_lt not_ofNat_le_one

中文:
定理 not_ofNat_lt_one
  结论: ¬(of自然数(n) : α) < 1
  证明: mt le_of_lt not_ofNat_le_one

Depends on / 依赖: le_of_lt, not_ofNat_le_one
-/
theorem not_ofNat_lt_one : ¬(ofNat(n) : α) < 1 :=
  mt le_of_lt not_ofNat_le_one

variable [m.AtLeastTwo]

-- TODO: These lemmas need to be `@[simp]` for confluence in the presence of `cast_lt`, `cast_le`,
-- and `Nat.cast_ofNat`, but their LHSs match literally every inequality, so they're too expensive.
-- If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, these can be made `@[simp]`.

-- @[simp]
/--
theorem `ofNat_le` / 定理 `ofNat_le`

English:
theorem ofNat_le
  proof: cast_le

中文:
定理 ofNat_le
  证明: cast_le

Depends on / 依赖: cast_le
-/
theorem ofNat_le :
    (ofNat(m) : α) <= (ofNat(n) : α) ↔ (OfNat.ofNat m : Nat) <= OfNat.ofNat n :=
  cast_le

-- @[simp]
/--
theorem `ofNat_lt` / 定理 `ofNat_lt`

English:
theorem ofNat_lt
  proof: cast_lt

中文:
定理 ofNat_lt
  证明: cast_lt

Depends on / 依赖: cast_lt
-/
theorem ofNat_lt :
    (ofNat(m) : α) < (ofNat(n) : α) ↔ (OfNat.ofNat m : Nat) < OfNat.ofNat n :=
  cast_lt

end Nat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoidWithOne
  signature: α] [CharZero α] : Nontrivial α where exists_pair_ne
  body: ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

中文:
实例 [AddMonoidWithOne
  签名: α] [CharZero α] : Nontrivial α where 存在_pair_ne
  定义体: ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

Depends on / 依赖: Nat.cast_ne_zero, Nat.cast_one, cast_ne_zero, cast_one
-/
instance [AddMonoidWithOne α] [CharZero α] : Nontrivial α where exists_pair_ne :=
  ⟨1, 0, (Nat.cast_one (R := α) ▸ Nat.cast_ne_zero.2 (by decide))⟩

section RingHomClass

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [FunLike F R S]

/--
theorem `NeZero.nat_of_injective` / 定理 `NeZero.nat_of_injective`

English:
theorem NeZero.nat_of_injective
  statement: {n : Nat} [NeZero (n : R)] [RingHomClass F R S] {f : F}
  proof: ⟨fun h => NeZero.natCast_ne n R hf by simpa only [map_natCast, map_zero f]⟩

中文:
定理 NeZero.nat_of_injective
  结论: {n : 自然数} [NeZero (n : R)] [RingHomClass F R S] {f : F}
  证明: ⟨fun h => NeZero.natCast_ne n R hf by simpa only [map_natCast, map_zero f]⟩

Depends on / 依赖: NeZero, NeZero.natCast_ne, map_natCast, map_zero, natCast_ne
-/
theorem NeZero.nat_of_injective {n : Nat} [NeZero (n : R)] [RingHomClass F R S] {f : F}
    (hf : Function.Injective f) : NeZero (n : S) :=
⟨fun h => NeZero.natCast_ne n R hf by simpa only [map_natCast, map_zero f]⟩

end RingHomClass
