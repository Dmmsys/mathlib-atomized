/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.GaloisConnection.Defs

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `Rat` and provides its basic algebraic
order structure.

Note that `NNRat` is not declared as a `Semifield` here. See `Mathlib/Algebra/Field/Rat.lean` for
that instance.

We also define an instance `CanLift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `NNRat` in scope `NNRat`.

## Huge warning

Whenever you state a lemma about the coercion `ℚ≥0 → ℚ`, check that Lean inserts `NNRat.cast`, not
`Subtype.val`. Else your lemma will never apply.
-/

@[expose] public section

assert_not_exists CompleteLattice IsOrderedMonoid

library_note «specialised high priority simp lemma» /--
It sometimes happens that a `@[simp]` lemma declared early in the library can be proved by `simp`
using later, more general simp lemmas. In that case, the following reasons might be arguments for
the early lemma to be tagged `@[simp high]` (rather than `@[simp, nolint simpNF]` or
un-`@[simp]`ed):
1. There is a significant portion of the library which needs the early lemma to be available via
  `simp` and which doesn't have access to the more general lemmas.
2. The more general lemmas have more complicated typeclass assumptions, causing rewrites with them
  to be slower.
-/

open Function

/--
Instance `Rat.instPosMulMono` / 实例 `Rat.instPosMulMono`

English:
instance Rat.instPosMulMono
  signature: : PosMulMono Rat where
  body: by
    simpa [mul_sub, sub_nonneg] using Rat.mul_nonneg hr (sub_nonneg.2 hpq)

deriving instance CommSemiring for NNRat

deriving instance AddCancelCommMonoid for NNRat

deriving instance LinearOrder for NNRat

deriving instance Sub for NNRat

deriving instance Inhabited for NNRat

中文:
实例 Rat.instPosMulMono
  签名: : PosMulMono Rat where
  定义体: by
    simpa [mul_sub, sub_nonneg] using Rat.mul_nonneg hr (sub_nonneg.2 hpq)

deriving instance CommSemiring for NNRat

deriving instance AddCancelCommMonoid for NNRat

deriving instance LinearOrder for NNRat

deriving instance Sub for NNRat

deriving instance Inhabited for NNRat

Depends on / 依赖: Rat.mul_nonneg, mul_nonneg, mul_sub, sub_nonneg
-/
instance Rat.instPosMulMono : PosMulMono Rat where
  mul_le_mul_of_nonneg_left r hr p q hpq := by
    simpa [mul_sub, sub_nonneg] using Rat.mul_nonneg hr (sub_nonneg.2 hpq)

deriving instance CommSemiring for NNRat

deriving instance AddCancelCommMonoid for NNRat

deriving instance LinearOrder for NNRat

deriving instance Sub for NNRat

deriving instance Inhabited for NNRat

namespace NNRat

variable {p q : Rat>=0}

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial Rat>=0 where exists_pair_ne
  body: ⟨1, 0, by decide⟩

中文:
实例 instNontrivial
  签名: : Nontrivial Rat>=0 where 存在_pair_ne
  定义体: ⟨1, 0, by decide⟩
-/
instance instNontrivial : Nontrivial Rat>=0 where exists_pair_ne := ⟨1, 0, by decide⟩
/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot Rat>=0 where
  body: 0
  bot_le q := q.2

中文:
实例 instOrderBot
  签名: : OrderBot Rat>=0 where
  定义体: 0
  bot_le q := q.2
-/
instance instOrderBot : OrderBot Rat>=0 where
  bot := 0
  bot_le q := q.2

/--
lemma `val_eq_cast` / 引理 `val_eq_cast`

English:
lemma val_eq_cast
  given: (q : Rat>=0)
  statement: q.1 = q
  proof: rfl

中文:
引理 val_eq_cast
  条件: (q : Rat>=0)
  结论: q.1 = q
  证明: rfl
-/
@[simp] lemma val_eq_cast (q : Rat>=0) : q.1 = q := rfl

/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: : CharZero Rat>=0 where
  body: by simpa using! congr_arg num hab

中文:
实例 instCharZero
  签名: : CharZero Rat>=0 where
  定义体: by simpa using! congr_arg num hab

Depends on / 依赖: congr_arg
-/
instance instCharZero : CharZero Rat>=0 where
  cast_injective a b hab := by simpa using! congr_arg num hab

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Rat Rat>=0 (↑) fun q => 0 <= q where
  body: ⟨⟨q, hq⟩, rfl⟩

@[ext]

中文:
实例 canLift
  签名: : CanLift Rat Rat>=0 (↑) fun q => 0 <= q where
  定义体: ⟨⟨q, hq⟩, rfl⟩

@[ext]
-/
instance canLift : CanLift Rat Rat>=0 (↑) fun q => 0 <= q where
  prf q hq := ⟨⟨q, hq⟩, rfl⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (p : Rat) = (q : Rat) -> p = q
  proof: Subtype.ext

中文:
定理 ext
  结论: (p : Rat) = (q : Rat) -> p = q
  证明: Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem ext : (p : Rat) = (q : Rat) -> p = q :=
  Subtype.ext

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Injective ((↑) : Rat>=0 -> Rat)
  proof: Subtype.coe_injective

中文:
定理 coe_injective
  结论: Injective ((↑) : Rat>=0 -> Rat)
  证明: Subtype.coe_injective
-/
protected theorem coe_injective : Injective ((↑) : Rat>=0 -> Rat) :=
  Subtype.coe_injective

-- See note [specialised high priority simp lemma]
@[simp high, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (p : Rat) = q ↔ p = q
  proof: Subtype.coe_inj

中文:
定理 coe_inj
  结论: (p : Rat) = q ↔ p = q
  证明: Subtype.coe_inj

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj
-/
theorem coe_inj : (p : Rat) = q ↔ p = q :=
  Subtype.coe_inj

/--
theorem `ne_iff` / 定理 `ne_iff`

English:
theorem ne_iff
  given: {x y : Rat>=0}
  statement: (x : Rat) != (y : Rat) ↔ x != y
  proof: NNRat.coe_inj.not

中文:
定理 ne_iff
  条件: {x y : Rat>=0}
  结论: (x : Rat) != (y : Rat) ↔ x != y
  证明: NNRat.coe_inj.not

Depends on / 依赖: NNRat.coe_inj.not, coe_inj
-/
theorem ne_iff {x y : Rat>=0} : (x : Rat) != (y : Rat) ↔ x != y :=
  NNRat.coe_inj.not

-- TODO: We have to write `NNRat.cast` explicitly, else the statement picks up `Subtype.val` instead
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (q : Rat) (hq)
  statement: NNRat.cast ⟨q, hq⟩ = q
  proof: rfl

中文:
引理 coe_mk
  条件: (q : Rat) (hq)
  结论: NNRat.cast ⟨q, hq⟩ = q
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mk (q : Rat) (hq) : NNRat.cast ⟨q, hq⟩ = q := rfl

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : Rat>=0 -> Prop}
  statement: (forall q, p q) ↔ forall q hq, p ⟨q, hq⟩
  proof: Subtype.forall

中文:
引理 «forall»
  条件: {p : Rat>=0 -> 命题}
  结论: (对任意 q, p q) ↔ 对任意 q hq, p ⟨q, hq⟩
  证明: Subtype.forall
-/
lemma «forall» {p : Rat>=0 -> Prop} : (forall q, p q) ↔ forall q hq, p ⟨q, hq⟩ := Subtype.forall
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : Rat>=0 -> Prop}
  statement: (exists q, p q) ↔ exists q hq, p ⟨q, hq⟩
  proof: Subtype.exists

中文:
引理 «exists»
  条件: {p : Rat>=0 -> 命题}
  结论: (存在 q, p q) ↔ 存在 q hq, p ⟨q, hq⟩
  证明: Subtype.exists
-/
lemma «exists» {p : Rat>=0 -> Prop} : (exists q, p q) ↔ exists q hq, p ⟨q, hq⟩ := Subtype.exists

/--
Definition of `_root_.Rat.toNNRat` / `_root_.Rat.toNNRat` 的定义

English:
definition _root_.Rat.toNNRat
  signature: (q : Rat)
  body: ⟨max q 0, le_max_right _ _⟩

中文:
定义 _root_.Rat.toNNRat
  签名: (q : Rat)
  定义体: ⟨max q 0, le_max_right _ _⟩

Depends on / 依赖: le_max_right
-/
def _root_.Rat.toNNRat (q : Rat) : Rat>=0 :=
  ⟨max q 0, le_max_right _ _⟩

/--
theorem `_root_.Rat.coe_toNNRat` / 定理 `_root_.Rat.coe_toNNRat`

English:
theorem _root_.Rat.coe_toNNRat
  given: (q : Rat) (hq : 0 <= q)
  statement: (q.toNNRat : Rat) = q
  proof: max_eq_left hq

中文:
定理 _root_.Rat.coe_toNNRat
  条件: (q : Rat) (hq : 0 <= q)
  结论: (q.toNNRat : Rat) = q
  证明: max_eq_left hq

Depends on / 依赖: max_eq_left
-/
theorem _root_.Rat.coe_toNNRat (q : Rat) (hq : 0 <= q) : (q.toNNRat : Rat) = q :=
  max_eq_left hq

/--
theorem `_root_.Rat.le_coe_toNNRat` / 定理 `_root_.Rat.le_coe_toNNRat`

English:
theorem _root_.Rat.le_coe_toNNRat
  given: (q : Rat)
  statement: q <= q.toNNRat
  proof: le_max_left _ _

中文:
定理 _root_.Rat.le_coe_toNNRat
  条件: (q : Rat)
  结论: q <= q.toNNRat
  证明: le_max_left _ _

Depends on / 依赖: le_max_left
-/
theorem _root_.Rat.le_coe_toNNRat (q : Rat) : q <= q.toNNRat :=
  le_max_left _ _

open Rat (toNNRat)

@[simp]
/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: (q : Rat>=0)
  statement: (0 : Rat) <= q
  proof: q.2

中文:
定理 coe_nonneg
  条件: (q : Rat>=0)
  结论: (0 : Rat) <= q
  证明: q.2
-/
theorem coe_nonneg (q : Rat>=0) : (0 : Rat) <= q :=
  q.2

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ((0 : Rat>=0) : Rat) = 0
  proof: rfl

中文:
引理 coe_zero
  结论: ((0 : Rat>=0) : Rat) = 0
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zero : ((0 : Rat>=0) : Rat) = 0 := rfl
/--
lemma `num_zero` / 引理 `num_zero`

English:
lemma num_zero
  statement: num 0 = 0
  proof: rfl

中文:
引理 num_zero
  结论: num 0 = 0
  证明: rfl
-/
@[simp] lemma num_zero : num 0 = 0 := rfl
/--
lemma `den_zero` / 引理 `den_zero`

English:
lemma den_zero
  statement: den 0 = 1
  proof: rfl

中文:
引理 den_zero
  结论: den 0 = 1
  证明: rfl
-/
@[simp] lemma den_zero : den 0 = 1 := rfl

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : Rat>=0) : Rat) = 1
  proof: rfl

中文:
引理 coe_one
  结论: ((1 : Rat>=0) : Rat) = 1
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ((1 : Rat>=0) : Rat) = 1 := rfl
/--
lemma `num_one` / 引理 `num_one`

English:
lemma num_one
  statement: num 1 = 1
  proof: rfl

中文:
引理 num_one
  结论: num 1 = 1
  证明: rfl

Depends on / 依赖: tower_top
-/
@[simp] lemma num_one : num 1 = 1 := rfl
/--
lemma `den_one` / 引理 `den_one`

English:
lemma den_one
  statement: den 1 = 1
  proof: rfl

@[simp, norm_cast]

中文:
引理 den_one
  结论: den 1 = 1
  证明: rfl

@[simp, norm_cast]
-/
@[simp] lemma den_one : den 1 = 1 := rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (p q : Rat>=0)
  statement: ((p + q : Rat>=0) : Rat) = p + q
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (p q : Rat>=0)
  结论: ((p + q : Rat>=0) : Rat) = p + q
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (p q : Rat>=0) : ((p + q : Rat>=0) : Rat) = p + q :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (p q : Rat>=0)
  statement: ((p * q : Rat>=0) : Rat) = p * q
  proof: rfl

中文:
定理 coe_mul
  条件: (p q : Rat>=0)
  结论: ((p * q : Rat>=0) : Rat) = p * q
  证明: rfl
-/
theorem coe_mul (p q : Rat>=0) : ((p * q : Rat>=0) : Rat) = p * q :=
  rfl

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (q : Rat>=0) (n : Nat)
  statement: (↑(q ^ n) : Rat) = (q : Rat) ^ n
  proof: rfl

中文:
引理 coe_pow
  条件: (q : Rat>=0) (n : 自然数)
  结论: (↑(q ^ n) : Rat) = (q : Rat) ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pow (q : Rat>=0) (n : Nat) : (↑(q ^ n) : Rat) = (q : Rat) ^ n :=
  rfl

/--
lemma `num_pow` / 引理 `num_pow`

English:
lemma num_pow
  given: (q : Rat>=0) (n : Nat)
  statement: (q ^ n).num = q.num ^ n
  proof: by simp [num, Int.natAbs_pow]

中文:
引理 num_pow
  条件: (q : Rat>=0) (n : 自然数)
  结论: (q ^ n).num = q.num ^ n
  证明: by simp [num, Int.natAbs_pow]
-/
@[simp] lemma num_pow (q : Rat>=0) (n : Nat) : (q ^ n).num = q.num ^ n := by simp [num, Int.natAbs_pow]
/--
lemma `den_pow` / 引理 `den_pow`

English:
lemma den_pow
  given: (q : Rat>=0) (n : Nat)
  statement: (q ^ n).den = q.den ^ n
  proof: rfl

@[simp, norm_cast]

中文:
引理 den_pow
  条件: (q : Rat>=0) (n : 自然数)
  结论: (q ^ n).den = q.den ^ n
  证明: rfl

@[simp, norm_cast]
-/
@[simp] lemma den_pow (q : Rat>=0) (n : Nat) : (q ^ n).den = q.den ^ n := rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (h : q <= p)
  statement: ((p - q : Rat>=0) : Rat) = p - q
  proof: max_eq_left le_sub_comm.2 by rwa [sub_zero]

中文:
定理 coe_sub
  条件: (h : q <= p)
  结论: ((p - q : Rat>=0) : Rat) = p - q
  证明: max_eq_left le_sub_comm.2 by rwa [sub_zero]

Depends on / 依赖: le_sub_comm, max_eq_left, sub_zero
-/
theorem coe_sub (h : q <= p) : ((p - q : Rat>=0) : Rat) = p - q :=
max_eq_left le_sub_comm.2 by rwa [sub_zero]

-- See note [specialised high priority simp lemma]
@[simp high]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  statement: (q : Rat) = 0 ↔ q = 0
  proof: by norm_cast

中文:
定理 coe_eq_zero
  结论: (q : Rat) = 0 ↔ q = 0
  证明: by norm_cast
-/
theorem coe_eq_zero : (q : Rat) = 0 ↔ q = 0 := by norm_cast

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  statement: (q : Rat) != 0 ↔ q != 0
  proof: coe_eq_zero.not

@[simp]

中文:
定理 coe_ne_zero
  结论: (q : Rat) != 0 ↔ q != 0
  证明: coe_eq_zero.not

@[simp]

Depends on / 依赖: coe_eq_zero, coe_eq_zero.not
-/
theorem coe_ne_zero : (q : Rat) != 0 ↔ q != 0 :=
  coe_eq_zero.not

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: (⟨0, le_rfl⟩ : Rat>=0) = 0
  proof: rfl

@[norm_cast]

中文:
定理 mk_zero
  结论: (⟨0, le_rfl⟩ : Rat>=0) = 0
  证明: rfl

@[norm_cast]
-/
theorem mk_zero : (⟨0, le_rfl⟩ : Rat>=0) = 0 := rfl

@[norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (p : Rat) <= q ↔ p <= q
  proof: Iff.rfl

@[norm_cast]

中文:
定理 coe_le_coe
  结论: (p : Rat) <= q ↔ p <= q
  证明: Iff.rfl

@[norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe : (p : Rat) <= q ↔ p <= q :=
  Iff.rfl

@[norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (p : Rat) < q ↔ p < q
  proof: Iff.rfl

@[norm_cast]

中文:
定理 coe_lt_coe
  结论: (p : Rat) < q ↔ p < q
  证明: Iff.rfl

@[norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe : (p : Rat) < q ↔ p < q :=
  Iff.rfl

@[norm_cast]
/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  statement: (0 : Rat) < q ↔ 0 < q
  proof: Iff.rfl

中文:
定理 coe_pos
  结论: (0 : Rat) < q ↔ 0 < q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, IntermediateField, IsGalois, IsGalois.tower_top_intermediateField, tower_top_intermediateField
-/
theorem coe_pos : (0 : Rat) < q ↔ 0 < q :=
  Iff.rfl

/--
theorem `coe_mono` / 定理 `coe_mono`

English:
theorem coe_mono
  statement: Monotone ((↑) : Rat>=0 -> Rat)
  proof: fun _ _ => coe_le_coe.2

中文:
定理 coe_mono
  结论: Monotone ((↑) : Rat>=0 -> Rat)
  证明: fun _ _ => coe_le_coe.2

Depends on / 依赖: coe_le_coe
-/
theorem coe_mono : Monotone ((↑) : Rat>=0 -> Rat) :=
  fun _ _ => coe_le_coe.2

/--
theorem `toNNRat_mono` / 定理 `toNNRat_mono`

English:
theorem toNNRat_mono
  statement: Monotone toNNRat
  proof: fun _ _ h => max_le_max h le_rfl

@[simp]

中文:
定理 toNNRat_mono
  结论: Monotone toNNRat
  证明: fun _ _ h => max_le_max h le_rfl

@[simp]

Depends on / 依赖: le_rfl, max_le_max
-/
theorem toNNRat_mono : Monotone toNNRat :=
  fun _ _ h => max_le_max h le_rfl

@[simp]
/--
theorem `toNNRat_coe` / 定理 `toNNRat_coe`

English:
theorem toNNRat_coe
  given: (q : Rat>=0)
  statement: toNNRat q = q
  proof: ext max_eq_left q.2

@[simp]

中文:
定理 toNNRat_coe
  条件: (q : Rat>=0)
  结论: toNNRat q = q
  证明: ext max_eq_left q.2

@[simp]

Depends on / 依赖: max_eq_left
-/
theorem toNNRat_coe (q : Rat>=0) : toNNRat q = q :=
ext max_eq_left q.2

@[simp]
/--
theorem `toNNRat_coe_nat` / 定理 `toNNRat_coe_nat`

English:
theorem toNNRat_coe_nat
  given: (n : Nat)
  statement: toNNRat n = n
  proof: ext by simp only [Nat.cast_nonneg', Rat.coe_toNNRat]; rfl

中文:
定理 toNNRat_coe_nat
  条件: (n : 自然数)
  结论: toNNRat n = n
  证明: ext by simp only [Nat.cast_nonneg', Rat.coe_toNNRat]; rfl

Depends on / 依赖: Nat.cast_nonneg, Rat.coe_toNNRat, cast_nonneg, coe_toNNRat
-/
theorem toNNRat_coe_nat (n : Nat) : toNNRat n = n :=
ext by simp only [Nat.cast_nonneg', Rat.coe_toNNRat]; rfl

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion toNNRat (↑)
  body: GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe

中文:
定义 gi
  签名: : GaloisInsertion toNNRat (↑)
  定义体: GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe
-/
protected def gi : GaloisInsertion toNNRat (↑) :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe

/--
Definition of `coeHom` / `coeHom` 的定义

English:
definition coeHom
  signature: : Rat>=0 ->+* Rat where
  body: (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add

中文:
定义 coeHom
  签名: : Rat>=0 ->+* Rat where
  定义体: (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add
-/
def coeHom : Rat>=0 ->+* Rat where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add

/--
lemma `coe_natCast` / 引理 `coe_natCast`

English:
lemma coe_natCast
  given: (n : Nat)
  statement: (↑(↑n : Rat>=0) : Rat) = n
  proof: rfl

@[simp]

中文:
引理 coe_natCast
  条件: (n : 自然数)
  结论: (↑(↑n : Rat>=0) : Rat) = n
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_natCast (n : Nat) : (↑(↑n : Rat>=0) : Rat) = n := rfl

@[simp]
/--
theorem `mk_natCast` / 定理 `mk_natCast`

English:
theorem mk_natCast
  given: (n : Nat)
  statement: @Eq Rat>=0 (⟨(n : Rat), Nat.cast_nonneg' n⟩ : Rat>=0) n
  proof: rfl

@[simp]

中文:
定理 mk_natCast
  条件: (n : 自然数)
  结论: @Eq Rat>=0 (⟨(n : Rat), 自然数.cast_nonneg' n⟩ : Rat>=0) n
  证明: rfl

@[simp]
-/
theorem mk_natCast (n : Nat) : @Eq Rat>=0 (⟨(n : Rat), Nat.cast_nonneg' n⟩ : Rat>=0) n :=
  rfl

@[simp]
/--
theorem `coe_coeHom` / 定理 `coe_coeHom`

English:
theorem coe_coeHom
  statement: ⇑coeHom = ((↑) : Rat>=0 -> Rat)
  proof: rfl

@[norm_cast]

中文:
定理 coe_coeHom
  结论: ⇑coeHom = ((↑) : Rat>=0 -> Rat)
  证明: rfl

@[norm_cast]
-/
theorem coe_coeHom : ⇑coeHom = ((↑) : Rat>=0 -> Rat) :=
  rfl

@[norm_cast]
/--
theorem `nsmul_coe` / 定理 `nsmul_coe`

English:
theorem nsmul_coe
  given: (q : Rat>=0) (n : Nat)
  statement: ↑(n • q) = n • (q : Rat)
  proof: coeHom.toAddMonoidHom.map_nsmul _ _

中文:
定理 nsmul_coe
  条件: (q : Rat>=0) (n : 自然数)
  结论: ↑(n • q) = n • (q : Rat)
  证明: coeHom.toAddMonoidHom.map_nsmul _ _

Depends on / 依赖: coeHom, coeHom.toAddMonoidHom.map_nsmul, map_nsmul, toAddMonoidHom
-/
theorem nsmul_coe (q : Rat>=0) (n : Nat) : ↑(n • q) = n • (q : Rat) :=
  coeHom.toAddMonoidHom.map_nsmul _ _

/--
theorem `bddAbove_coe` / 定理 `bddAbove_coe`

English:
theorem bddAbove_coe
  given: {s : Set Rat>=0}
  statement: BddAbove ((↑) '' s : Set Rat) ↔ BddAbove s
  proof: ⟨fun ⟨b, hb⟩ =>
    ⟨toNNRat b, fun ⟨y, _⟩ hys =>
show y <= max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans le_max_left _ _⟩,
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, Eq⟩ => Eq ▸ hb hx⟩⟩

中文:
定理 bddAbove_coe
  条件: {s : Set Rat>=0}
  结论: BddAbove ((↑) '' s : Set Rat) ↔ BddAbove s
  证明: ⟨fun ⟨b, hb⟩ =>
    ⟨toNNRat b, fun ⟨y, _⟩ hys =>
show y <= max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans le_max_left _ _⟩,
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, Eq⟩ => Eq ▸ hb hx⟩⟩

Depends on / 依赖: Set.mem_image_of_mem, le_max_left, mem_image_of_mem, toNNRat
-/
theorem bddAbove_coe {s : Set Rat>=0} : BddAbove ((↑) '' s : Set Rat) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ =>
    ⟨toNNRat b, fun ⟨y, _⟩ hys =>
show y <= max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans le_max_left _ _⟩,
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, Eq⟩ => Eq ▸ hb hx⟩⟩

/--
theorem `bddBelow_coe` / 定理 `bddBelow_coe`

English:
theorem bddBelow_coe
  given: (s : Set Rat>=0)
  statement: BddBelow (((↑) : Rat>=0 -> Rat) '' s)
  proof: ⟨0, fun _ ⟨q, _, h⟩ => h ▸ q.2⟩

@[norm_cast]

中文:
定理 bddBelow_coe
  条件: (s : Set Rat>=0)
  结论: BddBelow (((↑) : Rat>=0 -> Rat) '' s)
  证明: ⟨0, fun _ ⟨q, _, h⟩ => h ▸ q.2⟩

@[norm_cast]
-/
theorem bddBelow_coe (s : Set Rat>=0) : BddBelow (((↑) : Rat>=0 -> Rat) '' s) :=
  ⟨0, fun _ ⟨q, _, h⟩ => h ▸ q.2⟩

@[norm_cast]
/--
theorem `coe_max` / 定理 `coe_max`

English:
theorem coe_max
  given: (x y : Rat>=0)
  statement: ((max x y : Rat>=0) : Rat) = max (x : Rat) (y : Rat)
  proof: coe_mono.map_max

@[norm_cast]

中文:
定理 coe_max
  条件: (x y : Rat>=0)
  结论: ((max x y : Rat>=0) : Rat) = max (x : Rat) (y : Rat)
  证明: coe_mono.map_max

@[norm_cast]

Depends on / 依赖: coe_mono, coe_mono.map_max, map_max
-/
theorem coe_max (x y : Rat>=0) : ((max x y : Rat>=0) : Rat) = max (x : Rat) (y : Rat) :=
  coe_mono.map_max

@[norm_cast]
/--
theorem `coe_min` / 定理 `coe_min`

English:
theorem coe_min
  given: (x y : Rat>=0)
  statement: ((min x y : Rat>=0) : Rat) = min (x : Rat) (y : Rat)
  proof: coe_mono.map_min

中文:
定理 coe_min
  条件: (x y : Rat>=0)
  结论: ((min x y : Rat>=0) : Rat) = min (x : Rat) (y : Rat)
  证明: coe_mono.map_min

Depends on / 依赖: coe_mono, coe_mono.map_min, map_min
-/
theorem coe_min (x y : Rat>=0) : ((min x y : Rat>=0) : Rat) = min (x : Rat) (y : Rat) :=
  coe_mono.map_min

/--
theorem `sub_def` / 定理 `sub_def`

English:
theorem sub_def
  given: (p q : Rat>=0)
  statement: p - q = toNNRat (p - q)
  proof: rfl

@[simp]

中文:
定理 sub_def
  条件: (p q : Rat>=0)
  结论: p - q = toNNRat (p - q)
  证明: rfl

@[simp]
-/
theorem sub_def (p q : Rat>=0) : p - q = toNNRat (p - q) :=
  rfl

@[simp]
/--
theorem `abs_coe` / 定理 `abs_coe`

English:
theorem abs_coe
  given: (q : Rat>=0)
  statement: |(q : Rat)| = q
  proof: abs_of_nonneg q.2

中文:
定理 abs_coe
  条件: (q : Rat>=0)
  结论: |(q : Rat)| = q
  证明: abs_of_nonneg q.2

Depends on / 依赖: abs_of_nonneg
-/
theorem abs_coe (q : Rat>=0) : |(q : Rat)| = q :=
  abs_of_nonneg q.2

-- See note [specialised high priority simp lemma]
@[simp high]
/--
theorem `nonpos_iff_eq_zero` / 定理 `nonpos_iff_eq_zero`

English:
theorem nonpos_iff_eq_zero
  given: (q : Rat>=0)
  statement: q <= 0 ↔ q = 0
  proof: ⟨fun h => le_antisymm h q.2, fun h => h.symm ▸ q.2⟩

中文:
定理 nonpos_iff_eq_zero
  条件: (q : Rat>=0)
  结论: q <= 0 ↔ q = 0
  证明: ⟨fun h => le_antisymm h q.2, fun h => h.symm ▸ q.2⟩

Depends on / 依赖: h.symm, le_antisymm
-/
theorem nonpos_iff_eq_zero (q : Rat>=0) : q <= 0 ↔ q = 0 :=
  ⟨fun h => le_antisymm h q.2, fun h => h.symm ▸ q.2⟩

end NNRat

open NNRat

namespace Rat

variable {p q : Rat}

@[simp]
/--
theorem `toNNRat_zero` / 定理 `toNNRat_zero`

English:
theorem toNNRat_zero
  statement: toNNRat 0 = 0
  proof: rfl

@[simp]

中文:
定理 toNNRat_zero
  结论: toNNRat 0 = 0
  证明: rfl

@[simp]
-/
theorem toNNRat_zero : toNNRat 0 = 0 := rfl

@[simp]
/--
theorem `toNNRat_one` / 定理 `toNNRat_one`

English:
theorem toNNRat_one
  statement: toNNRat 1 = 1
  proof: rfl

中文:
定理 toNNRat_one
  结论: toNNRat 1 = 1
  证明: rfl
-/
theorem toNNRat_one : toNNRat 1 = 1 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toNNRat_pos` / 定理 `toNNRat_pos`

English:
theorem toNNRat_pos
  statement: 0 < toNNRat q ↔ 0 < q
  proof: by simp [toNNRat, ← coe_lt_coe]

@[simp]

中文:
定理 toNNRat_pos
  结论: 0 < toNNRat q ↔ 0 < q
  证明: by simp [toNNRat, ← coe_lt_coe]

@[simp]

Depends on / 依赖: coe_lt_coe, toNNRat
-/
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [toNNRat, ← coe_lt_coe]

@[simp]
/--
theorem `toNNRat_eq_zero` / 定理 `toNNRat_eq_zero`

English:
theorem toNNRat_eq_zero
  statement: toNNRat q = 0 ↔ q <= 0
  proof: by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero

中文:
定理 toNNRat_eq_zero
  结论: toNNRat q = 0 ↔ q <= 0
  证明: by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero

Depends on / 依赖: toNNRat_pos
-/
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q <= 0 := by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toNNRat_le_toNNRat_iff` / 定理 `toNNRat_le_toNNRat_iff`

English:
theorem toNNRat_le_toNNRat_iff
  given: (hp : 0 <= p)
  statement: toNNRat q <= toNNRat p ↔ q <= p
  proof: by
  simp [← coe_le_coe, toNNRat, hp]

中文:
定理 toNNRat_le_toNNRat_iff
  条件: (hp : 0 <= p)
  结论: toNNRat q <= toNNRat p ↔ q <= p
  证明: by
  simp [← coe_le_coe, toNNRat, hp]

Depends on / 依赖: coe_le_coe, toNNRat
-/
theorem toNNRat_le_toNNRat_iff (hp : 0 <= p) : toNNRat q <= toNNRat p ↔ q <= p := by
  simp [← coe_le_coe, toNNRat, hp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toNNRat_lt_toNNRat_iff'` / 定理 `toNNRat_lt_toNNRat_iff'`

English:
theorem toNNRat_lt_toNNRat_iff'
  statement: toNNRat q < toNNRat p ↔ q < p ∧ 0 < p
  proof: by
  simp [← coe_lt_coe, toNNRat]

中文:
定理 toNNRat_lt_toNNRat_iff'
  结论: toNNRat q < toNNRat p ↔ q < p ∧ 0 < p
  证明: by
  simp [← coe_lt_coe, toNNRat]

Depends on / 依赖: coe_lt_coe, toNNRat
-/
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, toNNRat]

/--
theorem `toNNRat_lt_toNNRat_iff` / 定理 `toNNRat_lt_toNNRat_iff`

English:
theorem toNNRat_lt_toNNRat_iff
  given: (h : 0 < p)
  statement: toNNRat q < toNNRat p ↔ q < p
  proof: toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)

中文:
定理 toNNRat_lt_toNNRat_iff
  条件: (h : 0 < p)
  结论: toNNRat q < toNNRat p ↔ q < p
  证明: toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)

Depends on / 依赖: and_iff_left, toNNRat_lt_toNNRat_iff
-/
theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)

/--
theorem `toNNRat_lt_toNNRat_iff_of_nonneg` / 定理 `toNNRat_lt_toNNRat_iff_of_nonneg`

English:
theorem toNNRat_lt_toNNRat_iff_of_nonneg
  given: (hq : 0 <= q)
  statement: toNNRat q < toNNRat p ↔ q < p
  proof: toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h => ⟨h, hq.trans_lt h⟩⟩

中文:
定理 toNNRat_lt_toNNRat_iff_of_nonneg
  条件: (hq : 0 <= q)
  结论: toNNRat q < toNNRat p ↔ q < p
  证明: toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h => ⟨h, hq.trans_lt h⟩⟩

Depends on / 依赖: And.left, hq.trans_lt, toNNRat_lt_toNNRat_iff, trans_lt
-/
theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 <= q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h => ⟨h, hq.trans_lt h⟩⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toNNRat_add` / 定理 `toNNRat_add`

English:
theorem toNNRat_add
  given: (hq : 0 <= q) (hp : 0 <= p)
  statement: toNNRat (q + p) = toNNRat q + toNNRat p
  proof: NNRat.ext by simp [toNNRat, hq, hp, add_nonneg]

中文:
定理 toNNRat_add
  条件: (hq : 0 <= q) (hp : 0 <= p)
  结论: toNNRat (q + p) = toNNRat q + toNNRat p
  证明: NNRat.ext by simp [toNNRat, hq, hp, add_nonneg]

Depends on / 依赖: NNRat.ext, add_nonneg, toNNRat
-/
theorem toNNRat_add (hq : 0 <= q) (hp : 0 <= p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
NNRat.ext by simp [toNNRat, hq, hp, add_nonneg]

/--
theorem `toNNRat_add_le` / 定理 `toNNRat_add_le`

English:
theorem toNNRat_add_le
  statement: toNNRat (q + p) <= toNNRat q + toNNRat p
  proof: coe_le_coe.1 max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) coe_nonneg _

中文:
定理 toNNRat_add_le
  结论: toNNRat (q + p) <= toNNRat q + toNNRat p
  证明: coe_le_coe.1 max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) coe_nonneg _

Depends on / 依赖: add_le_add, coe_le_coe, coe_nonneg, le_max_left, max_le
-/
theorem toNNRat_add_le : toNNRat (q + p) <= toNNRat q + toNNRat p :=
coe_le_coe.1 max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) coe_nonneg _

/--
theorem `toNNRat_le_iff_le_coe` / 定理 `toNNRat_le_iff_le_coe`

English:
theorem toNNRat_le_iff_le_coe
  given: {p : Rat>=0}
  statement: toNNRat q <= p ↔ q <= ↑p
  proof: NNRat.gi.gc q p

中文:
定理 toNNRat_le_iff_le_coe
  条件: {p : Rat>=0}
  结论: toNNRat q <= p ↔ q <= ↑p
  证明: NNRat.gi.gc q p

Depends on / 依赖: NNRat.gi.gc
-/
theorem toNNRat_le_iff_le_coe {p : Rat>=0} : toNNRat q <= p ↔ q <= ↑p :=
  NNRat.gi.gc q p

/--
theorem `le_toNNRat_iff_coe_le` / 定理 `le_toNNRat_iff_coe_le`

English:
theorem le_toNNRat_iff_coe_le
  given: {q : Rat>=0} (hp : 0 <= p)
  statement: q <= toNNRat p ↔ ↑q <= p
  proof: by
  rw [← coe_le_coe]; rw [Rat.coe_toNNRat p hp]

中文:
定理 le_toNNRat_iff_coe_le
  条件: {q : Rat>=0} (hp : 0 <= p)
  结论: q <= toNNRat p ↔ ↑q <= p
  证明: by
  rw [← coe_le_coe]; rw [Rat.coe_toNNRat p hp]

Depends on / 依赖: Rat.coe_toNNRat, coe_le_coe, coe_toNNRat
-/
theorem le_toNNRat_iff_coe_le {q : Rat>=0} (hp : 0 <= p) : q <= toNNRat p ↔ ↑q <= p := by
  rw [← coe_le_coe]; rw [Rat.coe_toNNRat p hp]

/--
theorem `le_toNNRat_iff_coe_le'` / 定理 `le_toNNRat_iff_coe_le'`

English:
theorem le_toNNRat_iff_coe_le'
  given: {q : Rat>=0} (hq : 0 < q)
  statement: q <= toNNRat p ↔ ↑q <= p
  proof: (le_or_gt 0 p).elim le_toNNRat_iff_coe_le fun hp => by
    simp only [(hp.trans_le q.coe_nonneg).not_ge, toNNRat_eq_zero.2 hp.le, hq.not_ge]

中文:
定理 le_toNNRat_iff_coe_le'
  条件: {q : Rat>=0} (hq : 0 < q)
  结论: q <= toNNRat p ↔ ↑q <= p
  证明: (le_or_gt 0 p).elim le_toNNRat_iff_coe_le fun hp => by
    simp only [(hp.trans_le q.coe_nonneg).not_ge, toNNRat_eq_zero.2 hp.le, hq.not_ge]

Depends on / 依赖: coe_nonneg, hp.le, hp.trans_le, hq.not_ge, le_or_gt, le_toNNRat_iff_coe_le, not_ge, q.coe_nonneg, toNNRat_eq_zero, trans_le
-/
theorem le_toNNRat_iff_coe_le' {q : Rat>=0} (hq : 0 < q) : q <= toNNRat p ↔ ↑q <= p :=
  (le_or_gt 0 p).elim le_toNNRat_iff_coe_le fun hp => by
    simp only [(hp.trans_le q.coe_nonneg).not_ge, toNNRat_eq_zero.2 hp.le, hq.not_ge]

/--
theorem `toNNRat_lt_iff_lt_coe` / 定理 `toNNRat_lt_iff_lt_coe`

English:
theorem toNNRat_lt_iff_lt_coe
  given: {p : Rat>=0} (hq : 0 <= q)
  statement: toNNRat q < p ↔ q < ↑p
  proof: by
  rw [← coe_lt_coe]; rw [Rat.coe_toNNRat q hq]

中文:
定理 toNNRat_lt_iff_lt_coe
  条件: {p : Rat>=0} (hq : 0 <= q)
  结论: toNNRat q < p ↔ q < ↑p
  证明: by
  rw [← coe_lt_coe]; rw [Rat.coe_toNNRat q hq]

Depends on / 依赖: Rat.coe_toNNRat, coe_lt_coe, coe_toNNRat
-/
theorem toNNRat_lt_iff_lt_coe {p : Rat>=0} (hq : 0 <= q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe]; rw [Rat.coe_toNNRat q hq]

/--
theorem `lt_toNNRat_iff_coe_lt` / 定理 `lt_toNNRat_iff_coe_lt`

English:
theorem lt_toNNRat_iff_coe_lt
  given: {q : Rat>=0}
  statement: q < toNNRat p ↔ ↑q < p
  proof: NNRat.gi.gc.lt_iff_lt

中文:
定理 lt_toNNRat_iff_coe_lt
  条件: {q : Rat>=0}
  结论: q < toNNRat p ↔ ↑q < p
  证明: NNRat.gi.gc.lt_iff_lt

Depends on / 依赖: NNRat.gi.gc.lt_iff_lt, lt_iff_lt
-/
theorem lt_toNNRat_iff_coe_lt {q : Rat>=0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toNNRat_mul` / 定理 `toNNRat_mul`

English:
theorem toNNRat_mul
  given: (hp : 0 <= p)
  statement: toNNRat (p * q) = toNNRat p * toNNRat q
  proof: by
  rcases le_total 0 q with hq | hq
  · ext; simp [toNNRat, hp, hq, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq]; rw [toNNRat_eq_zero.2 hpq]; rw [mul_zero]

中文:
定理 toNNRat_mul
  条件: (hp : 0 <= p)
  结论: toNNRat (p * q) = toNNRat p * toNNRat q
  证明: by
  rcases le_total 0 q with hq | hq
  · ext; simp [toNNRat, hp, hq, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq]; rw [toNNRat_eq_zero.2 hpq]; rw [mul_zero]

Depends on / 依赖: le_total, mul_nonneg, mul_nonpos_of_nonneg_of_nonpos, mul_zero, toNNRat, toNNRat_eq_zero
-/
theorem toNNRat_mul (hp : 0 <= p) : toNNRat (p * q) = toNNRat p * toNNRat q := by
  rcases le_total 0 q with hq | hq
  · ext; simp [toNNRat, hp, hq, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq]; rw [toNNRat_eq_zero.2 hpq]; rw [mul_zero]

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot]
/--
Definition of `Rat.nnabs` / `Rat.nnabs` 的定义

English:
definition Rat.nnabs
  signature: (x : Rat)
  body: ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]

中文:
定义 Rat.nnabs
  签名: (x : Rat)
  定义体: ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]

Depends on / 依赖: abs_nonneg
-/
def Rat.nnabs (x : Rat) : Rat>=0 :=
  ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]
/--
theorem `Rat.coe_nnabs` / 定理 `Rat.coe_nnabs`

English:
theorem Rat.coe_nnabs
  given: (x : Rat)
  statement: (Rat.nnabs x : Rat) = abs x
  proof: rfl

中文:
定理 Rat.coe_nnabs
  条件: (x : Rat)
  结论: (Rat.nnabs x : Rat) = abs x
  证明: rfl
-/
theorem Rat.coe_nnabs (x : Rat) : (Rat.nnabs x : Rat) = abs x := rfl

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : Rat>=0}

/--
lemma `num_coe` / 引理 `num_coe`

English:
lemma num_coe
  given: (q : Rat>=0)
  statement: (q : Rat).num = q.num
  proof: by
  simp only [num, Int.natCast_natAbs, Rat.num_nonneg, coe_nonneg, abs_of_nonneg]

中文:
引理 num_coe
  条件: (q : Rat>=0)
  结论: (q : Rat).num = q.num
  证明: by
  simp only [num, Int.natCast_natAbs, Rat.num_nonneg, coe_nonneg, abs_of_nonneg]
-/
@[norm_cast] lemma num_coe (q : Rat>=0) : (q : Rat).num = q.num := by
  simp only [num, Int.natCast_natAbs, Rat.num_nonneg, coe_nonneg, abs_of_nonneg]

/--
theorem `natAbs_num_coe` / 定理 `natAbs_num_coe`

English:
theorem natAbs_num_coe
  statement: (q : Rat).num.natAbs = q.num
  proof: rfl

中文:
定理 natAbs_num_coe
  结论: (q : Rat).num.natAbs = q.num
  证明: rfl
-/
theorem natAbs_num_coe : (q : Rat).num.natAbs = q.num := rfl

/--
lemma `den_coe` / 引理 `den_coe`

English:
lemma den_coe
  statement: (q : Rat).den = q.den
  proof: rfl

中文:
引理 den_coe
  结论: (q : Rat).den = q.den
  证明: rfl
-/
@[norm_cast] lemma den_coe : (q : Rat).den = q.den := rfl

/--
lemma `num_ne_zero` / 引理 `num_ne_zero`

English:
lemma num_ne_zero
  statement: q.num != 0 ↔ q != 0
  proof: by simp [num]

中文:
引理 num_ne_zero
  结论: q.num != 0 ↔ q != 0
  证明: by simp [num]
-/
@[simp] lemma num_ne_zero : q.num != 0 ↔ q != 0 := by simp [num]
/--
lemma `num_pos` / 引理 `num_pos`

English:
lemma num_pos
  statement: 0 < q.num ↔ 0 < q
  proof: by
.not.symm simpa [num, -nonpos_iff_eq_zero] using nonpos_iff_eq_zero _

中文:
引理 num_pos
  结论: 0 < q.num ↔ 0 < q
  证明: by
.not.symm simpa [num, -nonpos_iff_eq_zero] using nonpos_iff_eq_zero _
-/
@[simp] lemma num_pos : 0 < q.num ↔ 0 < q := by
.not.symm simpa [num, -nonpos_iff_eq_zero] using nonpos_iff_eq_zero _
/--
lemma `den_pos` / 引理 `den_pos`

English:
lemma den_pos
  given: (q : Rat>=0)
  statement: 0 < q.den
  proof: Rat.den_pos _

中文:
引理 den_pos
  条件: (q : Rat>=0)
  结论: 0 < q.den
  证明: Rat.den_pos _
-/
@[simp] lemma den_pos (q : Rat>=0) : 0 < q.den := Rat.den_pos _
/--
lemma `den_ne_zero` / 引理 `den_ne_zero`

English:
lemma den_ne_zero
  given: (q : Rat>=0)
  statement: q.den != 0
  proof: Rat.den_ne_zero _

中文:
引理 den_ne_zero
  条件: (q : Rat>=0)
  结论: q.den != 0
  证明: Rat.den_ne_zero _
-/
@[simp] lemma den_ne_zero (q : Rat>=0) : q.den != 0 := Rat.den_ne_zero _

/--
lemma `coprime_num_den` / 引理 `coprime_num_den`

English:
lemma coprime_num_den
  given: (q : Rat>=0)
  statement: q.num.Coprime q.den
  proof: by simpa [num, den] using Rat.reduced _

中文:
引理 coprime_num_den
  条件: (q : Rat>=0)
  结论: q.num.Coprime q.den
  证明: by simpa [num, den] using Rat.reduced _

Depends on / 依赖: Rat.reduced, reduced
-/
lemma coprime_num_den (q : Rat>=0) : q.num.Coprime q.den := by simpa [num, den] using Rat.reduced _

-- TODO: Rename `Rat.coe_nat_num`, `Rat.intCast_den`, `Rat.ofNat_num`, `Rat.ofNat_den`
/--
lemma `num_natCast` / 引理 `num_natCast`

English:
lemma num_natCast
  given: (n : Nat)
  statement: num n = n
  proof: rfl

中文:
引理 num_natCast
  条件: (n : 自然数)
  结论: num n = n
  证明: rfl
-/
@[simp, norm_cast] lemma num_natCast (n : Nat) : num n = n := rfl
/--
lemma `den_natCast` / 引理 `den_natCast`

English:
lemma den_natCast
  given: (n : Nat)
  statement: den n = 1
  proof: rfl

中文:
引理 den_natCast
  条件: (n : 自然数)
  结论: den n = 1
  证明: rfl
-/
@[simp, norm_cast] lemma den_natCast (n : Nat) : den n = 1 := rfl

/--
lemma `num_ofNat` / 引理 `num_ofNat`

English:
lemma num_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: num ofNat(n) = OfNat.ofNat n
  proof: rfl

中文:
引理 num_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: num of自然数(n) = Of自然数.of自然数 n
  证明: rfl

Depends on / 依赖: Algebra, IsAlgClosure, IsAlgClosure.isGalois, isGalois
-/
@[simp] lemma num_ofNat (n : Nat) [n.AtLeastTwo] : num ofNat(n) = OfNat.ofNat n :=
  rfl
/--
lemma `den_ofNat` / 引理 `den_ofNat`

English:
lemma den_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: den ofNat(n) = 1
  proof: rfl

中文:
引理 den_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: den of自然数(n) = 1
  证明: rfl
-/
@[simp] lemma den_ofNat (n : Nat) [n.AtLeastTwo] : den ofNat(n) = 1 := rfl

/--
theorem `ext_num_den` / 定理 `ext_num_den`

English:
theorem ext_num_den
  given: (hn : p.num = q.num) (hd : p.den = q.den)
  statement: p = q
  proof: by
refine ext Rat.ext ?_ hd
  simpa [num_coe]

中文:
定理 ext_num_den
  条件: (hn : p.num = q.num) (hd : p.den = q.den)
  结论: p = q
  证明: by
refine ext Rat.ext ?_ hd
  simpa [num_coe]

Depends on / 依赖: Rat.ext, num_coe
-/
theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q := by
refine ext Rat.ext ?_ hd
  simpa [num_coe]

/--
theorem `ext_num_den_iff` / 定理 `ext_num_den_iff`

English:
theorem ext_num_den_iff
  statement: p = q ↔ p.num = q.num ∧ p.den = q.den
  proof: ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h => ext_num_den h.1 h.2⟩

中文:
定理 ext_num_den_iff
  结论: p = q ↔ p.num = q.num ∧ p.den = q.den
  证明: ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h => ext_num_den h.1 h.2⟩

Depends on / 依赖: ext_num_den
-/
theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h => ext_num_den h.1 h.2⟩

/--
Definition of `divNat` / `divNat` 的定义

English:
definition divNat
  signature: (n d : Nat)
  body: ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d)⟩

中文:
定义 divNat
  签名: (n d : 自然数)
  定义体: ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d)⟩

Depends on / 依赖: Int.natCast_nonneg, Rat.divInt_nonneg, divInt, divInt_nonneg, natCast_nonneg
-/
def divNat (n d : Nat) : Rat>=0 :=
  ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d)⟩

variable {n₁ n₂ d₁ d₂ : Nat}

/--
lemma `coe_divNat` / 引理 `coe_divNat`

English:
lemma coe_divNat
  given: (n d : Nat)
  statement: (divNat n d : Rat) = .divInt n d
  proof: rfl

中文:
引理 coe_divNat
  条件: (n d : 自然数)
  结论: (div自然数 n d : Rat) = .div整数 n d
  证明: rfl
-/
@[simp, norm_cast] lemma coe_divNat (n d : Nat) : (divNat n d : Rat) = .divInt n d := rfl

/--
lemma `mk_divInt` / 引理 `mk_divInt`

English:
lemma mk_divInt
  given: (n d : Nat)
  proof: rfl

中文:
引理 mk_divInt
  条件: (n d : 自然数)
  证明: rfl
-/
lemma mk_divInt (n d : Nat) :
    ⟨.divInt n d, Rat.divInt_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg d)⟩ =
      divNat n d := rfl

/--
lemma `divNat_inj` / 引理 `divNat_inj`

English:
lemma divNat_inj
  given: (h₁ : d₁ != 0) (h₂ : d₂ != 0)
  statement: divNat n₁ d₁ = divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁
  proof: by
  rw [← coe_inj]; simp [Rat.mkRat_eq_iff, h₁, h₂]; norm_cast

中文:
引理 divNat_inj
  条件: (h₁ : d₁ != 0) (h₂ : d₂ != 0)
  结论: div自然数 n₁ d₁ = div自然数 n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁
  证明: by
  rw [← coe_inj]; simp [Rat.mkRat_eq_iff, h₁, h₂]; norm_cast

Depends on / 依赖: Rat.mkRat_eq_iff, coe_inj, mkRat_eq_iff
-/
lemma divNat_inj (h₁ : d₁ != 0) (h₂ : d₂ != 0) : divNat n₁ d₁ = divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← coe_inj]; simp [Rat.mkRat_eq_iff, h₁, h₂]; norm_cast

set_option backward.isDefEq.respectTransparency false in
/--
lemma `divNat_zero` / 引理 `divNat_zero`

English:
lemma divNat_zero
  given: (n : Nat)
  statement: divNat n 0 = 0
  proof: by simp [divNat]

中文:
引理 divNat_zero
  条件: (n : 自然数)
  结论: div自然数 n 0 = 0
  证明: by simp [divNat]
-/
@[simp] lemma divNat_zero (n : Nat) : divNat n 0 = 0 := by simp [divNat]

/--
lemma `num_divNat_den` / 引理 `num_divNat_den`

English:
lemma num_divNat_den
  given: (q : Rat>=0)
  statement: divNat q.num q.den = q
  proof: ext by rw [← (q : Rat).mkRat_num_den']; simp [num_coe, den_coe]

中文:
引理 num_divNat_den
  条件: (q : Rat>=0)
  结论: div自然数 q.num q.den = q
  证明: ext by rw [← (q : Rat).mkRat_num_den']; simp [num_coe, den_coe]
-/
@[simp] lemma num_divNat_den (q : Rat>=0) : divNat q.num q.den = q :=
ext by rw [← (q : Rat).mkRat_num_den']; simp [num_coe, den_coe]

/--
lemma `natCast_eq_divNat` / 引理 `natCast_eq_divNat`

English:
lemma natCast_eq_divNat
  given: (n : Nat)
  statement: (n : Rat>=0) = divNat n 1
  proof: (num_divNat_den _).symm

中文:
引理 natCast_eq_divNat
  条件: (n : 自然数)
  结论: (n : Rat>=0) = div自然数 n 1
  证明: (num_divNat_den _).symm

Depends on / 依赖: num_divNat_den
-/
lemma natCast_eq_divNat (n : Nat) : (n : Rat>=0) = divNat n 1 := (num_divNat_den _).symm

/--
lemma `divNat_mul_divNat` / 引理 `divNat_mul_divNat`

English:
lemma divNat_mul_divNat
  given: (n₁ n₂ : Nat) {d₁ d₂}
  proof: by
  ext; push_cast; exact Rat.divInt_mul_divInt _ _

中文:
引理 divNat_mul_divNat
  条件: (n₁ n₂ : 自然数) {d₁ d₂}
  证明: by
  ext; push_cast; exact Rat.divInt_mul_divInt _ _

Depends on / 依赖: Rat.divInt_mul_divInt, divInt_mul_divInt
-/
lemma divNat_mul_divNat (n₁ n₂ : Nat) {d₁ d₂} :
    divNat n₁ d₁ * divNat n₂ d₂ = divNat (n₁ * n₂) (d₁ * d₂) := by
  ext; push_cast; exact Rat.divInt_mul_divInt _ _

/--
lemma `divNat_mul_left` / 引理 `divNat_mul_left`

English:
lemma divNat_mul_left
  given: {a : Nat} (ha : a != 0) (n d : Nat)
  statement: divNat (a * n) (a * d) = divNat n d
  proof: by
  ext; push_cast; exact Rat.divInt_mul_left (mod_cast ha)

中文:
引理 divNat_mul_left
  条件: {a : 自然数} (ha : a != 0) (n d : 自然数)
  结论: div自然数 (a * n) (a * d) = div自然数 n d
  证明: by
  ext; push_cast; exact Rat.divInt_mul_left (mod_cast ha)

Depends on / 依赖: L.finiteDimensional, Rat.divInt_mul_left, divInt_mul_left, finiteDimensional, mod_cast
-/
lemma divNat_mul_left {a : Nat} (ha : a != 0) (n d : Nat) : divNat (a * n) (a * d) = divNat n d := by
  ext; push_cast; exact Rat.divInt_mul_left (mod_cast ha)

/--
lemma `divNat_mul_right` / 引理 `divNat_mul_right`

English:
lemma divNat_mul_right
  given: {a : Nat} (ha : a != 0) (n d : Nat)
  statement: divNat (n * a) (d * a) = divNat n d
  proof: by
  ext; push_cast; exact Rat.divInt_mul_right (mod_cast ha)

中文:
引理 divNat_mul_right
  条件: {a : 自然数} (ha : a != 0) (n d : 自然数)
  结论: div自然数 (n * a) (d * a) = div自然数 n d
  证明: by
  ext; push_cast; exact Rat.divInt_mul_right (mod_cast ha)

Depends on / 依赖: L.isGalois, Rat.divInt_mul_right, divInt_mul_right, isGalois, mod_cast
-/
lemma divNat_mul_right {a : Nat} (ha : a != 0) (n d : Nat) : divNat (n * a) (d * a) = divNat n d := by
  ext; push_cast; exact Rat.divInt_mul_right (mod_cast ha)

/--
lemma `mul_den_eq_num` / 引理 `mul_den_eq_num`

English:
lemma mul_den_eq_num
  given: (q : Rat>=0)
  statement: q * q.den = q.num
  proof: by
  ext
  push_cast
  rw [← Int.cast_natCast]; rw [← den_coe]; rw [← Int.cast_natCast q.num]; rw [← num_coe]
  exact Rat.mul_den_eq_num _

中文:
引理 mul_den_eq_num
  条件: (q : Rat>=0)
  结论: q * q.den = q.num
  证明: by
  ext
  push_cast
  rw [← Int.cast_natCast]; rw [← den_coe]; rw [← Int.cast_natCast q.num]; rw [← num_coe]
  exact Rat.mul_den_eq_num _
-/
@[simp] lemma mul_den_eq_num (q : Rat>=0) : q * q.den = q.num := by
  ext
  push_cast
  rw [← Int.cast_natCast]; rw [← den_coe]; rw [← Int.cast_natCast q.num]; rw [← num_coe]
  exact Rat.mul_den_eq_num _

/--
lemma `den_mul_eq_num` / 引理 `den_mul_eq_num`

English:
lemma den_mul_eq_num
  given: (q : Rat>=0)
  statement: q.den * q = q.num
  proof: by rw [mul_comm, mul_den_eq_num]

中文:
引理 den_mul_eq_num
  条件: (q : Rat>=0)
  结论: q.den * q = q.num
  证明: by rw [mul_comm, mul_den_eq_num]

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, inclusion, inf_le_left, injective, of_injective, toLinearMap, toRingHom, toRingHom.injective
-/
@[simp] lemma den_mul_eq_num (q : Rat>=0) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with nonnegative rational
numbers of the form `n / d` with `d ≠ 0` and `n`, `d` coprime. -/
@[elab_as_elim]
/--
Definition of `numDenCasesOn.` / `numDenCasesOn.` 的定义

English:
definition numDenCasesOn.{u}
  signature: {C : Rat>=0 -> Sort u} (q) (H : forall n d, d != 0 -> n.Coprime d -> C (divNat n d))
  body: by rw [← q.num_divNat_den]; exact H _ _ q.den_ne_zero q.coprime_num_den

中文:
定义 numDenCasesOn.{u}
  签名: {C : Rat>=0 -> Sort u} (q) (H : 对任意 n d, d != 0 -> n.Coprime d -> C (div自然数 n d))
  定义体: by rw [← q.num_divNat_den]; exact H _ _ q.den_ne_zero q.coprime_num_den

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, coprime_num_den, den_ne_zero, inclusion, inf_le_right, injective, num_divNat_den, of_injective, q.coprime_num_den, q.den_ne_zero, q.num_divNat_den, toLinearMap
-/
def numDenCasesOn.{u} {C : Rat>=0 -> Sort u} (q) (H : forall n d, d != 0 -> n.Coprime d -> C (divNat n d)) :
    C q := by rw [← q.num_divNat_den]; exact H _ _ q.den_ne_zero q.coprime_num_den

/--
lemma `add_def` / 引理 `add_def`

English:
lemma add_def
  given: (q r : Rat>=0)
  statement: q + r = divNat (q.num * r.den + r.num * q.den) (q.den * r.den)
  proof: by
  ext; simp [Rat.add_def', Rat.mkRat_eq_divInt, num_coe, den_coe]

中文:
引理 add_def
  条件: (q r : Rat>=0)
  结论: q + r = div自然数 (q.num * r.den + r.num * q.den) (q.den * r.den)
  证明: by
  ext; simp [Rat.add_def', Rat.mkRat_eq_divInt, num_coe, den_coe]

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, Rat.add_def, Rat.mkRat_eq_divInt, add_def, den_coe, inclusion, inf_le_left, mkRat_eq_divInt, num_coe, of_algHom
-/
lemma add_def (q r : Rat>=0) : q + r = divNat (q.num * r.den + r.num * q.den) (q.den * r.den) := by
  ext; simp [Rat.add_def', Rat.mkRat_eq_divInt, num_coe, den_coe]

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (q r : Rat>=0)
  statement: q * r = divNat (q.num * r.num) (q.den * r.den)
  proof: by
  ext; simp [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, num_coe, den_coe]

中文:
引理 mul_def
  条件: (q r : Rat>=0)
  结论: q * r = div自然数 (q.num * r.num) (q.den * r.den)
  证明: by
  ext; simp [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, num_coe, den_coe]

Depends on / 依赖: IntermediateField, IntermediateField.inclusion, Rat.mkRat_eq_divInt, Rat.mul_eq_mkRat, den_coe, inclusion, inf_le_right, mkRat_eq_divInt, mul_eq_mkRat, num_coe, of_algHom
-/
lemma mul_def (q r : Rat>=0) : q * r = divNat (q.num * r.num) (q.den * r.den) := by
  ext; simp [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, num_coe, den_coe]

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {p q : Rat>=0}
  statement: p < q ↔ p.num * q.den < q.num * p.den
  proof: by
  rw [← NNRat.coe_lt_coe]; rw [Rat.lt_iff]; norm_cast

中文:
定理 lt_def
  条件: {p q : Rat>=0}
  结论: p < q ↔ p.num * q.den < q.num * p.den
  证明: by
  rw [← NNRat.coe_lt_coe]; rw [Rat.lt_iff]; norm_cast

Depends on / 依赖: NNRat.coe_lt_coe, Rat.lt_iff, coe_lt_coe, lt_iff
-/
theorem lt_def {p q : Rat>=0} : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [← NNRat.coe_lt_coe]; rw [Rat.lt_iff]; norm_cast

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {p q : Rat>=0}
  statement: p <= q ↔ p.num * q.den <= q.num * p.den
  proof: by
  rw [← NNRat.coe_le_coe]; rw [Rat.le_iff]; norm_cast

中文:
定理 le_def
  条件: {p q : Rat>=0}
  结论: p <= q ↔ p.num * q.den <= q.num * p.den
  证明: by
  rw [← NNRat.coe_le_coe]; rw [Rat.le_iff]; norm_cast

Depends on / 依赖: NNRat.coe_le_coe, Rat.le_iff, coe_le_coe, le_iff
-/
theorem le_def {p q : Rat>=0} : p <= q ↔ p.num * q.den <= q.num * p.den := by
  rw [← NNRat.coe_le_coe]; rw [Rat.le_iff]; norm_cast

end NNRat

namespace Mathlib.Tactic.Qify

/--
lemma `nnratCast_eq` / 引理 `nnratCast_eq`

English:
lemma nnratCast_eq
  given: (a b : Rat>=0)
  statement: a = b ↔ (a : Rat) = (b : Rat)
  proof: NNRat.coe_inj.symm

中文:
引理 nnratCast_eq
  条件: (a b : Rat>=0)
  结论: a = b ↔ (a : Rat) = (b : Rat)
  证明: NNRat.coe_inj.symm
-/
@[qify_simps] lemma nnratCast_eq (a b : Rat>=0) : a = b ↔ (a : Rat) = (b : Rat) := NNRat.coe_inj.symm
/--
lemma `nnratCast_le` / 引理 `nnratCast_le`

English:
lemma nnratCast_le
  given: (a b : Rat>=0)
  statement: a <= b ↔ (a : Rat) <= (b : Rat)
  proof: NNRat.coe_le_coe.symm

中文:
引理 nnratCast_le
  条件: (a b : Rat>=0)
  结论: a <= b ↔ (a : Rat) <= (b : Rat)
  证明: NNRat.coe_le_coe.symm
-/
@[qify_simps] lemma nnratCast_le (a b : Rat>=0) : a <= b ↔ (a : Rat) <= (b : Rat) := NNRat.coe_le_coe.symm
/--
lemma `nnratCast_lt` / 引理 `nnratCast_lt`

English:
lemma nnratCast_lt
  given: (a b : Rat>=0)
  statement: a < b ↔ (a : Rat) < (b : Rat)
  proof: NNRat.coe_lt_coe.symm

中文:
引理 nnratCast_lt
  条件: (a b : Rat>=0)
  结论: a < b ↔ (a : Rat) < (b : Rat)
  证明: NNRat.coe_lt_coe.symm
-/
@[qify_simps] lemma nnratCast_lt (a b : Rat>=0) : a < b ↔ (a : Rat) < (b : Rat) := NNRat.coe_lt_coe.symm
/--
lemma `nnratCast_ne` / 引理 `nnratCast_ne`

English:
lemma nnratCast_ne
  given: (a b : Rat>=0)
  statement: a != b ↔ (a : Rat) != (b : Rat)
  proof: NNRat.ne_iff.symm

中文:
引理 nnratCast_ne
  条件: (a b : Rat>=0)
  结论: a != b ↔ (a : Rat) != (b : Rat)
  证明: NNRat.ne_iff.symm
-/
@[qify_simps] lemma nnratCast_ne (a b : Rat>=0) : a != b ↔ (a : Rat) != (b : Rat) := NNRat.ne_iff.symm

end Mathlib.Tactic.Qify
