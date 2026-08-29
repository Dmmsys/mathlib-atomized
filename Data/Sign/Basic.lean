/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Sign.Defs

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/

@[expose] public section

universe u
variable {α : Type u}

namespace SignType

/-- Casting `SignType → ℤ → α` is the same as casting directly `SignType → α`. -/
@[simp, norm_cast]
/--
lemma `intCast_cast` / 引理 `intCast_cast`

English:
lemma intCast_cast
  given: {α : Type*} [AddGroupWithOne α] (s : SignType)
  statement: ((s : Int) : α) = s
  proof: map_cast' _ Int.cast_one Int.cast_zero (@Int.cast_one α _ ▸ Int.cast_neg 1) _

中文:
引理 intCast_cast
  条件: {α : 类型} [加法带幺群 α] (s : SignType)
  结论: ((s : 整数) : α) = s
  证明: map_cast' _ Int.cast_one Int.cast_zero (@Int.cast_one α _ ▸ Int.cast_neg 1) _

Depends on / 依赖: Int.cast_neg, Int.cast_one, Int.cast_zero, cast_neg, cast_one, cast_zero, map_cast
-/
lemma intCast_cast {α : Type*} [AddGroupWithOne α] (s : SignType) : ((s : Int) : α) = s :=
  map_cast' _ Int.cast_one Int.cast_zero (@Int.cast_one α _ ▸ Int.cast_neg 1) _

/--
theorem `pow_odd` / 定理 `pow_odd`

English:
theorem pow_odd
  given: (s : SignType) {n : Nat} (hn : Odd n)
  statement: s ^ n = s
  proof: by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add]; rw [pow_one]; rw [pow_mul]; rw [sq]
  cases s <;> simp

中文:
定理 pow_odd
  条件: (s : SignType) {n : 自然数} (hn : Odd n)
  结论: s ^ n = s
  证明: by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add]; rw [pow_one]; rw [pow_mul]; rw [sq]
  cases s <;> simp

Depends on / 依赖: pow_add, pow_mul, pow_one
-/
theorem pow_odd (s : SignType) {n : Nat} (hn : Odd n) : s ^ n = s := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add]; rw [pow_one]; rw [pow_mul]; rw [sq]
  cases s <;> simp

/--
theorem `zpow_odd` / 定理 `zpow_odd`

English:
theorem zpow_odd
  given: (s : SignType) {z : Int} (hz : Odd z)
  statement: s ^ z = s
  proof: by
  obtain rfl | hs := eq_or_ne s 0
  · rw [zero_zpow]
    rintro rfl
    simp at hz
  obtain ⟨k, rfl⟩ := hz
  rw [zpow_add₀ hs]; rw [zpow_one]; rw [zpow_mul]; rw [zpow_two]
  cases s <;> simp

中文:
定理 zpow_odd
  条件: (s : SignType) {z : 整数} (hz : Odd z)
  结论: s ^ z = s
  证明: by
  obtain rfl | hs := eq_or_ne s 0
  · rw [zero_zpow]
    rintro rfl
    simp at hz
  obtain ⟨k, rfl⟩ := hz
  rw [zpow_add₀ hs]; rw [zpow_one]; rw [zpow_mul]; rw [zpow_two]
  cases s <;> simp

Depends on / 依赖: eq_or_ne, zero_zpow, zpow_mul, zpow_one, zpow_two
-/
theorem zpow_odd (s : SignType) {z : Int} (hz : Odd z) : s ^ z = s := by
  obtain rfl | hs := eq_or_ne s 0
  · rw [zero_zpow]
    rintro rfl
    simp at hz
  obtain ⟨k, rfl⟩ := hz
  rw [zpow_add₀ hs]; rw [zpow_one]; rw [zpow_mul]; rw [zpow_two]
  cases s <;> simp

/--
lemma `pow_even` / 引理 `pow_even`

English:
lemma pow_even
  given: (s : SignType) {n : Nat} (hn : Even n) (hs : s != 0)
  proof: by
  cases s <;> simp_all

中文:
引理 pow_even
  条件: (s : SignType) {n : 自然数} (hn : Even n) (hs : s != 0)
  证明: by
  cases s <;> simp_all
-/
lemma pow_even (s : SignType) {n : Nat} (hn : Even n) (hs : s != 0) :
    s ^ n = 1 := by
  cases s <;> simp_all

/--
lemma `zpow_even` / 引理 `zpow_even`

English:
lemma zpow_even
  given: (s : SignType) {z : Int} (hz : Even z) (hs : s != 0)
  proof: by
  cases s <;> simp_all [Even.neg_one_zpow]

中文:
引理 zpow_even
  条件: (s : SignType) {z : 整数} (hz : Even z) (hs : s != 0)
  证明: by
  cases s <;> simp_all [Even.neg_one_zpow]

Depends on / 依赖: Even.neg_one_zpow, neg_one_zpow
-/
lemma zpow_even (s : SignType) {z : Int} (hz : Even z) (hs : s != 0) :
    s ^ z = 1 := by
  cases s <;> simp_all [Even.neg_one_zpow]

/-- `SignType.cast` as a `MulWithZeroHom`. -/
@[simps]
/--
Definition of `castHom` / `castHom` 的定义

English:
definition castHom
  signature: {α} [MulZeroOneClass α] [HasDistribNeg α]
  body: cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> simp [zero_eq_zero, pos_eq_one, neg_eq_neg_one]

中文:
定义 castHom
  签名: {α} [乘零幺类 α] [有DistribNeg α]
  定义体: cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> simp [zero_eq_zero, pos_eq_one, neg_eq_neg_one]
-/
def castHom {α} [MulZeroOneClass α] [HasDistribNeg α] : SignType ->*₀ α where
  toFun := cast
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> simp [zero_eq_zero, pos_eq_one, neg_eq_neg_one]

/--
theorem `univ_eq` / 定理 `univ_eq`

English:
theorem univ_eq
  statement: (Finset.univ : Finset SignType) = {0, -1, 1}
  proof: by
  decide

中文:
定理 univ_eq
  结论: (有限集.univ : 有限集 SignType) = {0, -1, 1}
  证明: by
  decide
-/
theorem univ_eq : (Finset.univ : Finset SignType) = {0, -1, 1} := by
  decide

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: {α} (f : SignType -> α)
  statement: Set.range f = {f zero, f neg, f pos}
  proof: by
  classical rw [← Fintype.coe_image_univ, univ_eq]
  simp [Finset.coe_insert]

中文:
定理 range_eq
  条件: {α} (f : SignType -> α)
  结论: 集合.range f = {f zero, f neg, f pos}
  证明: by
  classical rw [← Fintype.coe_image_univ, univ_eq]
  simp [Finset.coe_insert]

Depends on / 依赖: Finset, Finset.coe_insert, Fintype, Fintype.coe_image_univ, classical, coe_image_univ, coe_insert, univ_eq
-/
theorem range_eq {α} (f : SignType -> α) : Set.range f = {f zero, f neg, f pos} := by
  classical rw [← Fintype.coe_image_univ, univ_eq]
  simp [Finset.coe_insert]

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: {α} [MulZeroOneClass α] [HasDistribNeg α] (a b : SignType)
  proof: map_mul SignType.castHom _ _

中文:
引理 coe_mul
  条件: {α} [乘零幺类 α] [有DistribNeg α] (a b : SignType)
  证明: map_mul SignType.castHom _ _
-/
@[simp, norm_cast] lemma coe_mul {α} [MulZeroOneClass α] [HasDistribNeg α] (a b : SignType) :
    ↑(a * b) = (a : α) * b :=
  map_mul SignType.castHom _ _

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: {α} [MonoidWithZero α] [HasDistribNeg α] (a : SignType) (k : Nat)
  proof: map_pow SignType.castHom _ _

中文:
引理 coe_pow
  条件: {α} [带零幺半群 α] [有DistribNeg α] (a : SignType) (k : 自然数)
  证明: map_pow SignType.castHom _ _
-/
@[simp, norm_cast] lemma coe_pow {α} [MonoidWithZero α] [HasDistribNeg α] (a : SignType) (k : Nat) :
    ↑(a ^ k) = (a : α) ^ k :=
  map_pow SignType.castHom _ _

/--
lemma `coe_zpow` / 引理 `coe_zpow`

English:
lemma coe_zpow
  given: {α} [GroupWithZero α] [HasDistribNeg α] (a : SignType) (k : Int)
  proof: map_zpow₀ SignType.castHom _ _

中文:
引理 coe_zpow
  条件: {α} [带零群 α] [有DistribNeg α] (a : SignType) (k : 整数)
  证明: map_zpow₀ SignType.castHom _ _
-/
@[simp, norm_cast] lemma coe_zpow {α} [GroupWithZero α] [HasDistribNeg α] (a : SignType) (k : Int) :
    ↑(a ^ k) = (a : α) ^ k :=
  map_zpow₀ SignType.castHom _ _

end SignType

open SignType

section OrderedRing

@[simp]
/--
lemma `sign_intCast` / 引理 `sign_intCast`

English:
lemma sign_intCast
  statement: {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
  proof: by
  simp only [sign_apply, Int.cast_pos, Int.cast_lt_zero]

中文:
引理 sign_intCast
  结论: {α : 类型} [环 α] [偏序 α] [是Ordered环 α]
  证明: by
  simp only [sign_apply, Int.cast_pos, Int.cast_lt_zero]

Depends on / 依赖: Int.cast_lt_zero, Int.cast_pos, cast_lt_zero, cast_pos, sign_apply
-/
lemma sign_intCast {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
    [Nontrivial α] [DecidableLT α] (n : Int) :
    sign (n : α) = sign n := by
  simp only [sign_apply, Int.cast_pos, Int.cast_lt_zero]

end OrderedRing

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

/--
theorem `sign_mul` / 定理 `sign_mul`

English:
theorem sign_mul
  given: (x y : α)
  statement: sign (x * y) = sign x * sign y
  proof: by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp [hx, hy, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]

中文:
定理 sign_mul
  条件: (x y : α)
  结论: sign (x * y) = sign x * sign y
  证明: by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp [hx, hy, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]

Depends on / 依赖: lt_trichotomy, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg, mul_pos_of_neg_of_neg
-/
theorem sign_mul (x y : α) : sign (x * y) = sign x * sign y := by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp [hx, hy, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]

/--
theorem `sign_mul_abs` / 定理 `sign_mul_abs`

English:
theorem sign_mul_abs
  given: (x : α)
  statement: (sign x * |x| : α) = x
  proof: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

中文:
定理 sign_mul_abs
  条件: (x : α)
  结论: (sign x * |x| : α) = x
  证明: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]
-/
@[simp] theorem sign_mul_abs (x : α) : (sign x * |x| : α) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

/--
theorem `abs_mul_sign` / 定理 `abs_mul_sign`

English:
theorem abs_mul_sign
  given: (x : α)
  statement: (|x| * sign x : α) = x
  proof: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]

中文:
定理 abs_mul_sign
  条件: (x : α)
  结论: (|x| * sign x : α) = x
  证明: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
-/
@[simp] theorem abs_mul_sign (x : α) : (|x| * sign x : α) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
/--
theorem `sign_mul_self` / 定理 `sign_mul_self`

English:
theorem sign_mul_self
  given: (x : α)
  statement: sign x * x = |x|
  proof: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]

中文:
定理 sign_mul_self
  条件: (x : α)
  结论: sign x * x = |x|
  证明: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]

Depends on / 依赖: abs_of_neg, abs_of_pos, lt_trichotomy
-/
theorem sign_mul_self (x : α) : sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

@[simp]
/--
theorem `self_mul_sign` / 定理 `self_mul_sign`

English:
theorem self_mul_sign
  given: (x : α)
  statement: x * sign x = |x|
  proof: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

中文:
定理 self_mul_sign
  条件: (x : α)
  结论: x * sign x = |x|
  证明: by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

Depends on / 依赖: abs_of_neg, abs_of_pos, lt_trichotomy
-/
theorem self_mul_sign (x : α) : x * sign x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> simp [*, abs_of_pos, abs_of_neg]

/-- `SignType.sign` as a `MonoidWithZeroHom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + I` and `1 - I` are incomparable to zero, and thus we have:
`0 * 0 = SignType.sign (1 + I) * SignType.sign (1 - I) ≠ SignType.sign 2 = 1`.
(`Complex.orderedCommRing`) -/
@[simps -fullyApplied]
/--
Definition of `signHom` / `signHom` 的定义

English:
definition signHom
  signature: : α ->*₀ SignType where
  body: sign
  map_zero' := sign_zero
  map_one' := sign_one
  map_mul' := sign_mul

中文:
定义 signHom
  签名: : α ->*₀ SignType where
  定义体: sign
  map_zero' := sign_zero
  map_one' := sign_one
  map_mul' := sign_mul
-/
def signHom : α ->*₀ SignType where
  toFun := sign
  map_zero' := sign_zero
  map_one' := sign_one
  map_mul' := sign_mul

/--
theorem `sign_pow` / 定理 `sign_pow`

English:
theorem sign_pow
  given: (x : α) (n : Nat)
  statement: sign (x ^ n) = sign x ^ n
  proof: map_pow signHom x n

中文:
定理 sign_pow
  条件: (x : α) (n : 自然数)
  结论: sign (x ^ n) = sign x ^ n
  证明: map_pow signHom x n

Depends on / 依赖: map_pow, signHom
-/
theorem sign_pow (x : α) (n : Nat) : sign (x ^ n) = sign x ^ n := map_pow signHom x n

end LinearOrderedRing

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/--
theorem `sign_sum` / 定理 `sign_sum`

English:
theorem sign_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> α} (hs : s.Nonempty) (t : SignType)
  proof: by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h ⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h ⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h ⊢
    exact Finset.sum_pos h hs

中文:
定理 sign_sum
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> α} (hs : s.非空) (t : SignType)
  证明: by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h ⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h ⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h ⊢
    exact Finset.sum_pos h hs

Depends on / 依赖: Finset, Finset.sum_eq_zero, Finset.sum_neg, Finset.sum_pos, neg_eq_neg_one, pos_eq_one, sign_eq_neg_one_iff, sign_eq_one_iff, sign_eq_zero_iff, simp_rw, sum_eq_zero, sum_neg, sum_pos, zero_eq_zero
-/
theorem sign_sum {ι : Type*} {s : Finset ι} {f : ι -> α} (hs : s.Nonempty) (t : SignType)
    (h : forall i in s, sign (f i) = t) : sign (∑ i in s, f i) = t := by
  cases t
  · simp_rw [zero_eq_zero, sign_eq_zero_iff] at h ⊢
    exact Finset.sum_eq_zero h
  · simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at h ⊢
    exact Finset.sum_neg h hs
  · simp_rw [pos_eq_one, sign_eq_one_iff] at h ⊢
    exact Finset.sum_pos h hs

end LinearOrderedAddCommGroup

open Finset Nat

section exists_signed_sum


/--
theorem `exists_signed_sum_aux` / 定理 `exists_signed_sum_aux`

English:
theorem exists_signed_sum_aux
  given: [DecidableEq α] (s : Finset α) (f : α -> Int)
  proof: by
  refine
    ⟨(Σ _ : { x // x in s }, Nat), Finset.univ.sigma fun a => range (f a).natAbs,
      fun a => sign (f a.1), fun a => a.1, fun a => a.1.2, ?_, ?_⟩
  · simp [sum_attach (f := fun a => (f a).natAbs)]
  · intro x hx
    simp [sum_sigma, hx, ← Int.sign_eq_sign, Int.sign_mul_abs, mul_comm |

中文:
定理 存在_signed_sum_aux
  条件: [DecidableEq α] (s : 有限集 α) (f : α -> 整数)
  证明: by
  refine
    ⟨(Σ _ : { x // x in s }, Nat), Finset.univ.sigma fun a => range (f a).natAbs,
      fun a => sign (f a.1), fun a => a.1, fun a => a.1.2, ?_, ?_⟩
  · simp [sum_attach (f := fun a => (f a).natAbs)]
  · intro x hx
    simp [sum_sigma, hx, ← Int.sign_eq_sign, Int.sign_mul_abs, mul_comm |
-/
private theorem exists_signed_sum_aux [DecidableEq α] (s : Finset α) (f : α -> Int) :
    exists (β : Type u) (t : Finset β) (sgn : β -> SignType) (g : β -> α),
      (forall b, g b in s) ∧
        (#t = ∑ a in s, (f a).natAbs) ∧
          forall a in s, (∑ b in t, if g b = a then (sgn b : Int) else 0) = f a := by
  refine
    ⟨(Σ _ : { x // x in s }, Nat), Finset.univ.sigma fun a => range (f a).natAbs,
      fun a => sign (f a.1), fun a => a.1, fun a => a.1.2, ?_, ?_⟩
  · simp [sum_attach (f := fun a => (f a).natAbs)]
  · intro x hx
    simp [sum_sigma, hx, ← Int.sign_eq_sign, Int.sign_mul_abs, mul_comm |f _|,
      sum_attach (s := s) (f := fun y => if y = x then f y else 0)]

/--
theorem `exists_signed_sum` / 定理 `exists_signed_sum`

English:
theorem exists_signed_sum
  given: [DecidableEq α] (s : Finset α) (f : α -> Int)
  proof: let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f
  ⟨t, inferInstance, fun b => sgn b, fun b => g b, fun b => hg b, by simp [ht], fun a ha =>
(sum_attach t fun b => ite (g b = a) (sgn b : Int) 0).trans hf _ ha⟩

中文:
定理 存在_signed_sum
  条件: [DecidableEq α] (s : 有限集 α) (f : α -> 整数)
  证明: let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f
  ⟨t, inferInstance, fun b => sgn b, fun b => g b, fun b => hg b, by simp [ht], fun a ha =>
(sum_attach t fun b => ite (g b = a) (sgn b : Int) 0).trans hf _ ha⟩

Depends on / 依赖: exists_signed_sum_aux, sum_attach
-/
theorem exists_signed_sum [DecidableEq α] (s : Finset α) (f : α -> Int) :
    exists (β : Type u) (_ : Fintype β) (sgn : β -> SignType) (g : β -> α),
      (forall b, g b in s) ∧
        (Fintype.card β = ∑ a in s, (f a).natAbs) ∧
          forall a in s, (∑ b, if g b = a then (sgn b : Int) else 0) = f a :=
  let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f
  ⟨t, inferInstance, fun b => sgn b, fun b => g b, fun b => hg b, by simp [ht], fun a ha =>
(sum_attach t fun b => ite (g b = a) (sgn b : Int) 0).trans hf _ ha⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_signed_sum'` / 定理 `exists_signed_sum'`

English:
theorem exists_signed_sum'
  statement: [Nonempty α] [DecidableEq α] (s : Finset α) (f : α -> Int)
  proof: by
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f
  refine
    ⟨β oplus (Fin (n - ∑ i in s, (f i).natAbs)), inferInstance, Sum.elim sgn 0,
      Sum.elim g (Classical.arbitrary (Fin (n - Finset.sum s fun i => Int.natAbs (f i)) -> α)),
        ?_, by simp [hβ, h], fun a ha => by simp [h

中文:
定理 存在_signed_sum'
  结论: [非空 α] [DecidableEq α] (s : 有限集 α) (f : α -> 整数)
  证明: by
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f
  refine
    ⟨β oplus (Fin (n - ∑ i in s, (f i).natAbs)), inferInstance, Sum.elim sgn 0,
      Sum.elim g (Classical.arbitrary (Fin (n - Finset.sum s fun i => Int.natAbs (f i)) -> α)),
        ?_, by simp [hβ, h], fun a ha => by simp [h

Depends on / 依赖: Classical, Classical.arbitrary, Finset, Finset.sum, Int.natAbs, Sum.elim, arbitrary, exists_signed_sum, natAbs
-/
theorem exists_signed_sum' [Nonempty α] [DecidableEq α] (s : Finset α) (f : α -> Int)
    (n : Nat) (h : (∑ i in s, (f i).natAbs) <= n) :
    exists (β : Type u) (_ : Fintype β) (sgn : β -> SignType) (g : β -> α),
      (forall b, g b ∉ s -> sgn b = 0) ∧
        Fintype.card β = n ∧ forall a in s, (∑ i, if g i = a then (sgn i : Int) else 0) = f a := by
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f
  refine
    ⟨β oplus (Fin (n - ∑ i in s, (f i).natAbs)), inferInstance, Sum.elim sgn 0,
      Sum.elim g (Classical.arbitrary (Fin (n - Finset.sum s fun i => Int.natAbs (f i)) -> α)),
        ?_, by simp [hβ, h], fun a ha => by simp [hf _ ha]⟩
  rintro (b | b) hb
  · cases hb (hg _)
  · rfl

end exists_signed_sum
