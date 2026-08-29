/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Data.ENat.Basic
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Conversion between `Cardinal` and `ℕ∞`

In this file we define a coercion `Cardinal.ofENat : ℕ∞ → Cardinal`
and a projection `Cardinal.toENat : Cardinal →+*o ℕ∞`.
We also prove basic theorems about these definitions.

## Implementation notes

We define `Cardinal.ofENat` as a function instead of a bundled homomorphism
so that we can use it as a coercion and delaborate its application to `↑n`.

We define `Cardinal.toENat` as a bundled homomorphism
so that we can use all the theorems about homomorphisms without specializing them to this function.
Since it is not registered as a coercion, the argument about delaboration does not apply.

## Keywords

set theory, cardinals, extended natural numbers
-/

@[expose] public section

assert_not_exists Field

open Function Set
universe u v

namespace Cardinal

/--
Definition of `ofENat` / `ofENat` 的定义

English:
definition ofENat
  signature: : Nat∞ -> Cardinal

中文:
定义 ofENat
  签名: : 自然数∞ -> Cardinal
-/
@[coe] def ofENat : Nat∞ -> Cardinal
  | (n : Nat) => n
  | ⊤ => ℵ₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe ENat Cardinal
  body: ⟨Cardinal.ofENat⟩

中文:
实例 :
  签名: Coe E自然数 Cardinal
  定义体: ⟨Cardinal.ofENat⟩

Depends on / 依赖: Cardinal, Cardinal.ofENat, ofENat
-/
instance : Coe ENat Cardinal := ⟨Cardinal.ofENat⟩

/--
lemma `ofENat_top` / 引理 `ofENat_top`

English:
lemma ofENat_top
  statement: ofENat ⊤ = ℵ₀
  proof: rfl

中文:
引理 ofENat_top
  结论: ofE自然数 ⊤ = ℵ₀
  证明: rfl
-/
@[simp, norm_cast] lemma ofENat_top : ofENat ⊤ = ℵ₀ := rfl
/--
lemma `ofENat_nat` / 引理 `ofENat_nat`

English:
lemma ofENat_nat
  given: (n : Nat)
  statement: ofENat n = n
  proof: rfl

中文:
引理 ofENat_nat
  条件: (n : 自然数)
  结论: ofE自然数 n = n
  证明: rfl
-/
@[simp, norm_cast] lemma ofENat_nat (n : Nat) : ofENat n = n := rfl
/--
lemma `ofENat_zero` / 引理 `ofENat_zero`

English:
lemma ofENat_zero
  statement: ofENat 0 = 0
  proof: rfl

中文:
引理 ofENat_zero
  结论: ofE自然数 0 = 0
  证明: rfl
-/
@[simp, norm_cast] lemma ofENat_zero : ofENat 0 = 0 := rfl
/--
lemma `ofENat_one` / 引理 `ofENat_one`

English:
lemma ofENat_one
  statement: ofENat 1 = 1
  proof: rfl

中文:
引理 ofENat_one
  结论: ofE自然数 1 = 1
  证明: rfl
-/
@[simp, norm_cast] lemma ofENat_one : ofENat 1 = 1 := rfl

/--
lemma `ofENat_ofNat` / 引理 `ofENat_ofNat`

English:
lemma ofENat_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
引理 ofENat_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
@[simp, norm_cast] lemma ofENat_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : Nat∞) : Cardinal) = OfNat.ofNat n :=
  rfl

/--
lemma `ofENat_strictMono` / 引理 `ofENat_strictMono`

English:
lemma ofENat_strictMono
  statement: StrictMono ofENat
  proof: WithTop.strictMono_iff.2 ⟨Nat.strictMono_cast, fun _ => natCast_lt_aleph0⟩

@[simp, norm_cast]

中文:
引理 ofENat_strictMono
  结论: StrictMono ofE自然数
  证明: WithTop.strictMono_iff.2 ⟨Nat.strictMono_cast, fun _ => natCast_lt_aleph0⟩

@[simp, norm_cast]

Depends on / 依赖: Nat.strictMono_cast, WithTop, WithTop.strictMono_iff, natCast_lt_aleph0, strictMono_cast, strictMono_iff
-/
lemma ofENat_strictMono : StrictMono ofENat :=
  WithTop.strictMono_iff.2 ⟨Nat.strictMono_cast, fun _ => natCast_lt_aleph0⟩

@[simp, norm_cast]
/--
lemma `ofENat_lt_ofENat` / 引理 `ofENat_lt_ofENat`

English:
lemma ofENat_lt_ofENat
  given: {m n : Nat∞}
  statement: (m : Cardinal) < n ↔ m < n
  proof: ofENat_strictMono.lt_iff_lt

@[gcongr, mono] alias ⟨_, ofENat_lt_ofENat_of_lt⟩ := ofENat_lt_ofENat

@[simp, norm_cast]

中文:
引理 ofENat_lt_ofENat
  条件: {m n : 自然数∞}
  结论: (m : Cardinal) < n ↔ m < n
  证明: ofENat_strictMono.lt_iff_lt

@[gcongr, mono] alias ⟨_, ofENat_lt_ofENat_of_lt⟩ := ofENat_lt_ofENat

@[simp, norm_cast]

Depends on / 依赖: lt_iff_lt, ofENat_strictMono, ofENat_strictMono.lt_iff_lt
-/
lemma ofENat_lt_ofENat {m n : Nat∞} : (m : Cardinal) < n ↔ m < n :=
  ofENat_strictMono.lt_iff_lt

@[gcongr, mono] alias ⟨_, ofENat_lt_ofENat_of_lt⟩ := ofENat_lt_ofENat

@[simp, norm_cast]
/--
lemma `ofENat_lt_aleph0` / 引理 `ofENat_lt_aleph0`

English:
lemma ofENat_lt_aleph0
  given: {m : Nat∞}
  statement: (m : Cardinal) < ℵ₀ ↔ m < ⊤
  proof: ofENat_lt_ofENat (n := ⊤)

中文:
引理 ofENat_lt_aleph0
  条件: {m : 自然数∞}
  结论: (m : Cardinal) < ℵ₀ ↔ m < ⊤
  证明: ofENat_lt_ofENat (n := ⊤)

Depends on / 依赖: ofENat_lt_ofENat
-/
lemma ofENat_lt_aleph0 {m : Nat∞} : (m : Cardinal) < ℵ₀ ↔ m < ⊤ :=
  ofENat_lt_ofENat (n := ⊤)

/--
lemma `ofENat_lt_nat` / 引理 `ofENat_lt_nat`

English:
lemma ofENat_lt_nat
  given: {m : Nat∞} {n : Nat}
  statement: ofENat m < n ↔ m < n
  proof: by norm_cast

中文:
引理 ofENat_lt_nat
  条件: {m : 自然数∞} {n : 自然数}
  结论: ofE自然数 m < n ↔ m < n
  证明: by norm_cast
-/
@[simp] lemma ofENat_lt_nat {m : Nat∞} {n : Nat} : ofENat m < n ↔ m < n := by norm_cast

/--
lemma `ofENat_lt_ofNat` / 引理 `ofENat_lt_ofNat`

English:
lemma ofENat_lt_ofNat
  given: {m : Nat∞} {n : Nat} [n.AtLeastTwo]
  proof: ofENat_lt_nat

中文:
引理 ofENat_lt_ofNat
  条件: {m : 自然数∞} {n : 自然数} [n.AtLeastTwo]
  证明: ofENat_lt_nat
-/
@[simp] lemma ofENat_lt_ofNat {m : Nat∞} {n : Nat} [n.AtLeastTwo] :
    ofENat m < ofNat(n) ↔ m < OfNat.ofNat n := ofENat_lt_nat

/--
lemma `nat_lt_ofENat` / 引理 `nat_lt_ofENat`

English:
lemma nat_lt_ofENat
  given: {m : Nat} {n : Nat∞}
  statement: (m : Cardinal) < n ↔ m < n
  proof: by norm_cast

中文:
引理 nat_lt_ofENat
  条件: {m : 自然数} {n : 自然数∞}
  结论: (m : Cardinal) < n ↔ m < n
  证明: by norm_cast
-/
@[simp] lemma nat_lt_ofENat {m : Nat} {n : Nat∞} : (m : Cardinal) < n ↔ m < n := by norm_cast
/--
lemma `ofENat_pos` / 引理 `ofENat_pos`

English:
lemma ofENat_pos
  given: {m : Nat∞}
  statement: 0 < (m : Cardinal) ↔ 0 < m
  proof: by norm_cast

中文:
引理 ofENat_pos
  条件: {m : 自然数∞}
  结论: 0 < (m : Cardinal) ↔ 0 < m
  证明: by norm_cast
-/
@[simp] lemma ofENat_pos {m : Nat∞} : 0 < (m : Cardinal) ↔ 0 < m := by norm_cast
/--
lemma `one_lt_ofENat` / 引理 `one_lt_ofENat`

English:
lemma one_lt_ofENat
  given: {m : Nat∞}
  statement: 1 < (m : Cardinal) ↔ 1 < m
  proof: by norm_cast

中文:
引理 one_lt_ofENat
  条件: {m : 自然数∞}
  结论: 1 < (m : Cardinal) ↔ 1 < m
  证明: by norm_cast
-/
@[simp] lemma one_lt_ofENat {m : Nat∞} : 1 < (m : Cardinal) ↔ 1 < m := by norm_cast

/--
lemma `ofNat_lt_ofENat` / 引理 `ofNat_lt_ofENat`

English:
lemma ofNat_lt_ofENat
  given: {m : Nat} [m.AtLeastTwo] {n : Nat∞}
  proof: nat_lt_ofENat

中文:
引理 ofNat_lt_ofENat
  条件: {m : 自然数} [m.AtLeastTwo] {n : 自然数∞}
  证明: nat_lt_ofENat
-/
@[simp, norm_cast] lemma ofNat_lt_ofENat {m : Nat} [m.AtLeastTwo] {n : Nat∞} :
    (ofNat(m) : Cardinal) < n ↔ OfNat.ofNat m < n := nat_lt_ofENat

/--
lemma `ofENat_mono` / 引理 `ofENat_mono`

English:
lemma ofENat_mono
  statement: Monotone ofENat
  proof: ofENat_strictMono.monotone

@[simp, norm_cast]

中文:
引理 ofENat_mono
  结论: Monotone ofE自然数
  证明: ofENat_strictMono.monotone

@[simp, norm_cast]

Depends on / 依赖: monotone, ofENat_strictMono, ofENat_strictMono.monotone
-/
lemma ofENat_mono : Monotone ofENat := ofENat_strictMono.monotone

@[simp, norm_cast]
/--
lemma `ofENat_le_ofENat` / 引理 `ofENat_le_ofENat`

English:
lemma ofENat_le_ofENat
  given: {m n : Nat∞}
  statement: (m : Cardinal) <= n ↔ m <= n
  proof: ofENat_strictMono.le_iff_le

@[gcongr, mono] alias ⟨_, ofENat_le_ofENat_of_le⟩ := ofENat_le_ofENat

中文:
引理 ofENat_le_ofENat
  条件: {m n : 自然数∞}
  结论: (m : Cardinal) <= n ↔ m <= n
  证明: ofENat_strictMono.le_iff_le

@[gcongr, mono] alias ⟨_, ofENat_le_ofENat_of_le⟩ := ofENat_le_ofENat

Depends on / 依赖: le_iff_le, ofENat_strictMono, ofENat_strictMono.le_iff_le
-/
lemma ofENat_le_ofENat {m n : Nat∞} : (m : Cardinal) <= n ↔ m <= n := ofENat_strictMono.le_iff_le

@[gcongr, mono] alias ⟨_, ofENat_le_ofENat_of_le⟩ := ofENat_le_ofENat

/--
lemma `ofENat_le_aleph0` / 引理 `ofENat_le_aleph0`

English:
lemma ofENat_le_aleph0
  given: (n : Nat∞)
  statement: ↑n <= ℵ₀
  proof: ofENat_le_ofENat.2 le_top

中文:
引理 ofENat_le_aleph0
  条件: (n : 自然数∞)
  结论: ↑n <= ℵ₀
  证明: ofENat_le_ofENat.2 le_top
-/
@[simp] lemma ofENat_le_aleph0 (n : Nat∞) : ↑n <= ℵ₀ := ofENat_le_ofENat.2 le_top
/--
lemma `ofENat_le_nat` / 引理 `ofENat_le_nat`

English:
lemma ofENat_le_nat
  given: {m : Nat∞} {n : Nat}
  statement: ofENat m <= n ↔ m <= n
  proof: by norm_cast

中文:
引理 ofENat_le_nat
  条件: {m : 自然数∞} {n : 自然数}
  结论: ofE自然数 m <= n ↔ m <= n
  证明: by norm_cast
-/
@[simp] lemma ofENat_le_nat {m : Nat∞} {n : Nat} : ofENat m <= n ↔ m <= n := by norm_cast
/--
lemma `ofENat_le_one` / 引理 `ofENat_le_one`

English:
lemma ofENat_le_one
  given: {m : Nat∞}
  statement: ofENat m <= 1 ↔ m <= 1
  proof: by norm_cast

中文:
引理 ofENat_le_one
  条件: {m : 自然数∞}
  结论: ofE自然数 m <= 1 ↔ m <= 1
  证明: by norm_cast
-/
@[simp] lemma ofENat_le_one {m : Nat∞} : ofENat m <= 1 ↔ m <= 1 := by norm_cast

/--
lemma `ofENat_le_ofNat` / 引理 `ofENat_le_ofNat`

English:
lemma ofENat_le_ofNat
  given: {m : Nat∞} {n : Nat} [n.AtLeastTwo]
  proof: ofENat_le_nat

中文:
引理 ofENat_le_ofNat
  条件: {m : 自然数∞} {n : 自然数} [n.AtLeastTwo]
  证明: ofENat_le_nat
-/
@[simp] lemma ofENat_le_ofNat {m : Nat∞} {n : Nat} [n.AtLeastTwo] :
    ofENat m <= ofNat(n) ↔ m <= OfNat.ofNat n := ofENat_le_nat

/--
lemma `nat_le_ofENat` / 引理 `nat_le_ofENat`

English:
lemma nat_le_ofENat
  given: {m : Nat} {n : Nat∞}
  statement: (m : Cardinal) <= n ↔ m <= n
  proof: by norm_cast

中文:
引理 nat_le_ofENat
  条件: {m : 自然数} {n : 自然数∞}
  结论: (m : Cardinal) <= n ↔ m <= n
  证明: by norm_cast
-/
@[simp] lemma nat_le_ofENat {m : Nat} {n : Nat∞} : (m : Cardinal) <= n ↔ m <= n := by norm_cast
/--
lemma `one_le_ofENat` / 引理 `one_le_ofENat`

English:
lemma one_le_ofENat
  given: {n : Nat∞}
  statement: 1 <= (n : Cardinal) ↔ 1 <= n
  proof: by norm_cast

@[simp]

中文:
引理 one_le_ofENat
  条件: {n : 自然数∞}
  结论: 1 <= (n : Cardinal) ↔ 1 <= n
  证明: by norm_cast

@[simp]
-/
@[simp] lemma one_le_ofENat {n : Nat∞} : 1 <= (n : Cardinal) ↔ 1 <= n := by norm_cast

@[simp]
/--
lemma `ofNat_le_ofENat` / 引理 `ofNat_le_ofENat`

English:
lemma ofNat_le_ofENat
  given: {m : Nat} [m.AtLeastTwo] {n : Nat∞}
  proof: nat_le_ofENat

中文:
引理 ofNat_le_ofENat
  条件: {m : 自然数} [m.AtLeastTwo] {n : 自然数∞}
  证明: nat_le_ofENat

Depends on / 依赖: nat_le_ofENat
-/
lemma ofNat_le_ofENat {m : Nat} [m.AtLeastTwo] {n : Nat∞} :
    (ofNat(m) : Cardinal) <= n ↔ OfNat.ofNat m <= n := nat_le_ofENat

/--
lemma `ofENat_injective` / 引理 `ofENat_injective`

English:
lemma ofENat_injective
  statement: Injective ofENat
  proof: ofENat_strictMono.injective

@[simp, norm_cast]

中文:
引理 ofENat_injective
  结论: Injective ofE自然数
  证明: ofENat_strictMono.injective

@[simp, norm_cast]

Depends on / 依赖: injective, ofENat_strictMono, ofENat_strictMono.injective
-/
lemma ofENat_injective : Injective ofENat := ofENat_strictMono.injective

@[simp, norm_cast]
/--
lemma `ofENat_inj` / 引理 `ofENat_inj`

English:
lemma ofENat_inj
  given: {m n : Nat∞}
  statement: (m : Cardinal) = n ↔ m = n
  proof: ofENat_injective.eq_iff

中文:
引理 ofENat_inj
  条件: {m n : 自然数∞}
  结论: (m : Cardinal) = n ↔ m = n
  证明: ofENat_injective.eq_iff

Depends on / 依赖: eq_iff, ofENat_injective, ofENat_injective.eq_iff
-/
lemma ofENat_inj {m n : Nat∞} : (m : Cardinal) = n ↔ m = n := ofENat_injective.eq_iff

/--
lemma `ofENat_eq_nat` / 引理 `ofENat_eq_nat`

English:
lemma ofENat_eq_nat
  given: {m : Nat∞} {n : Nat}
  statement: (m : Cardinal) = n ↔ m = n
  proof: by norm_cast

中文:
引理 ofENat_eq_nat
  条件: {m : 自然数∞} {n : 自然数}
  结论: (m : Cardinal) = n ↔ m = n
  证明: by norm_cast
-/
@[simp] lemma ofENat_eq_nat {m : Nat∞} {n : Nat} : (m : Cardinal) = n ↔ m = n := by norm_cast
/--
lemma `nat_eq_ofENat` / 引理 `nat_eq_ofENat`

English:
lemma nat_eq_ofENat
  given: {m : Nat} {n : Nat∞}
  statement: (m : Cardinal) = n ↔ m = n
  proof: by norm_cast

中文:
引理 nat_eq_ofENat
  条件: {m : 自然数} {n : 自然数∞}
  结论: (m : Cardinal) = n ↔ m = n
  证明: by norm_cast
-/
@[simp] lemma nat_eq_ofENat {m : Nat} {n : Nat∞} : (m : Cardinal) = n ↔ m = n := by norm_cast

/--
lemma `ofENat_eq_zero` / 引理 `ofENat_eq_zero`

English:
lemma ofENat_eq_zero
  given: {m : Nat∞}
  statement: (m : Cardinal) = 0 ↔ m = 0
  proof: by norm_cast

中文:
引理 ofENat_eq_zero
  条件: {m : 自然数∞}
  结论: (m : Cardinal) = 0 ↔ m = 0
  证明: by norm_cast
-/
@[simp] lemma ofENat_eq_zero {m : Nat∞} : (m : Cardinal) = 0 ↔ m = 0 := by norm_cast
/--
lemma `zero_eq_ofENat` / 引理 `zero_eq_ofENat`

English:
lemma zero_eq_ofENat
  given: {m : Nat∞}
  statement: 0 = (m : Cardinal) ↔ m = 0
  proof: by norm_cast; apply eq_comm

中文:
引理 zero_eq_ofENat
  条件: {m : 自然数∞}
  结论: 0 = (m : Cardinal) ↔ m = 0
  证明: by norm_cast; apply eq_comm
-/
@[simp] lemma zero_eq_ofENat {m : Nat∞} : 0 = (m : Cardinal) ↔ m = 0 := by norm_cast; apply eq_comm

/--
lemma `ofENat_eq_one` / 引理 `ofENat_eq_one`

English:
lemma ofENat_eq_one
  given: {m : Nat∞}
  statement: (m : Cardinal) = 1 ↔ m = 1
  proof: by norm_cast

中文:
引理 ofENat_eq_one
  条件: {m : 自然数∞}
  结论: (m : Cardinal) = 1 ↔ m = 1
  证明: by norm_cast
-/
@[simp] lemma ofENat_eq_one {m : Nat∞} : (m : Cardinal) = 1 ↔ m = 1 := by norm_cast
/--
lemma `one_eq_ofENat` / 引理 `one_eq_ofENat`

English:
lemma one_eq_ofENat
  given: {m : Nat∞}
  statement: 1 = (m : Cardinal) ↔ m = 1
  proof: by norm_cast; apply eq_comm

中文:
引理 one_eq_ofENat
  条件: {m : 自然数∞}
  结论: 1 = (m : Cardinal) ↔ m = 1
  证明: by norm_cast; apply eq_comm
-/
@[simp] lemma one_eq_ofENat {m : Nat∞} : 1 = (m : Cardinal) ↔ m = 1 := by norm_cast; apply eq_comm

/--
lemma `ofENat_eq_ofNat` / 引理 `ofENat_eq_ofNat`

English:
lemma ofENat_eq_ofNat
  given: {m : Nat∞} {n : Nat} [n.AtLeastTwo]
  proof: ofENat_eq_nat

中文:
引理 ofENat_eq_ofNat
  条件: {m : 自然数∞} {n : 自然数} [n.AtLeastTwo]
  证明: ofENat_eq_nat
-/
@[simp] lemma ofENat_eq_ofNat {m : Nat∞} {n : Nat} [n.AtLeastTwo] :
    (m : Cardinal) = ofNat(n) ↔ m = OfNat.ofNat n := ofENat_eq_nat

/--
lemma `ofNat_eq_ofENat` / 引理 `ofNat_eq_ofENat`

English:
lemma ofNat_eq_ofENat
  given: {m : Nat} {n : Nat∞} [m.AtLeastTwo]
  proof: nat_eq_ofENat

中文:
引理 ofNat_eq_ofENat
  条件: {m : 自然数} {n : 自然数∞} [m.AtLeastTwo]
  证明: nat_eq_ofENat
-/
@[simp] lemma ofNat_eq_ofENat {m : Nat} {n : Nat∞} [m.AtLeastTwo] :
    ofNat(m) = (n : Cardinal) ↔ OfNat.ofNat m = n := nat_eq_ofENat

/--
lemma `lift_ofENat` / 引理 `lift_ofENat`

English:
lemma lift_ofENat
  statement: forall m : Nat∞, lift.{u, v} m = m

中文:
引理 lift_ofENat
  结论: 对任意 m : 自然数∞, lift.{u, v} m = m
-/
@[simp, norm_cast] lemma lift_ofENat : forall m : Nat∞, lift.{u, v} m = m
  | (m : Nat) => lift_natCast m
  | ⊤ => lift_aleph0

/--
lemma `lift_lt_ofENat` / 引理 `lift_lt_ofENat`

English:
lemma lift_lt_ofENat
  given: {x : Cardinal.{v}} {m : Nat∞}
  statement: lift.{u} x < m ↔ x < m
  proof: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_lt]

中文:
引理 lift_lt_ofENat
  条件: {x : Cardinal.{v}} {m : 自然数∞}
  结论: lift.{u} x < m ↔ x < m
  证明: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_lt]
-/
@[simp] lemma lift_lt_ofENat {x : Cardinal.{v}} {m : Nat∞} : lift.{u} x < m ↔ x < m := by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_lt]

/--
lemma `lift_le_ofENat` / 引理 `lift_le_ofENat`

English:
lemma lift_le_ofENat
  given: {x : Cardinal.{v}} {m : Nat∞}
  statement: lift.{u} x <= m ↔ x <= m
  proof: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_le]

中文:
引理 lift_le_ofENat
  条件: {x : Cardinal.{v}} {m : 自然数∞}
  结论: lift.{u} x <= m ↔ x <= m
  证明: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_le]
-/
@[simp] lemma lift_le_ofENat {x : Cardinal.{v}} {m : Nat∞} : lift.{u} x <= m ↔ x <= m := by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_le]

/--
lemma `lift_eq_ofENat` / 引理 `lift_eq_ofENat`

English:
lemma lift_eq_ofENat
  given: {x : Cardinal.{v}} {m : Nat∞}
  statement: lift.{u} x = m ↔ x = m
  proof: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_inj]

中文:
引理 lift_eq_ofENat
  条件: {x : Cardinal.{v}} {m : 自然数∞}
  结论: lift.{u} x = m ↔ x = m
  证明: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_inj]
-/
@[simp] lemma lift_eq_ofENat {x : Cardinal.{v}} {m : Nat∞} : lift.{u} x = m ↔ x = m := by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_inj]

/--
lemma `ofENat_lt_lift` / 引理 `ofENat_lt_lift`

English:
lemma ofENat_lt_lift
  given: {x : Cardinal.{v}} {m : Nat∞}
  statement: m < lift.{u} x ↔ m < x
  proof: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_lt]

中文:
引理 ofENat_lt_lift
  条件: {x : Cardinal.{v}} {m : 自然数∞}
  结论: m < lift.{u} x ↔ m < x
  证明: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_lt]
-/
@[simp] lemma ofENat_lt_lift {x : Cardinal.{v}} {m : Nat∞} : m < lift.{u} x ↔ m < x := by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_lt]

/--
lemma `ofENat_le_lift` / 引理 `ofENat_le_lift`

English:
lemma ofENat_le_lift
  given: {x : Cardinal.{v}} {m : Nat∞}
  statement: m <= lift.{u} x ↔ m <= x
  proof: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_le]

中文:
引理 ofENat_le_lift
  条件: {x : Cardinal.{v}} {m : 自然数∞}
  结论: m <= lift.{u} x ↔ m <= x
  证明: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_le]
-/
@[simp] lemma ofENat_le_lift {x : Cardinal.{v}} {m : Nat∞} : m <= lift.{u} x ↔ m <= x := by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_le]

/--
lemma `ofENat_eq_lift` / 引理 `ofENat_eq_lift`

English:
lemma ofENat_eq_lift
  given: {x : Cardinal.{v}} {m : Nat∞}
  statement: m = lift.{u} x ↔ m = x
  proof: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_inj]

@[simp]

中文:
引理 ofENat_eq_lift
  条件: {x : Cardinal.{v}} {m : 自然数∞}
  结论: m = lift.{u} x ↔ m = x
  证明: by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_inj]

@[simp]
-/
@[simp] lemma ofENat_eq_lift {x : Cardinal.{v}} {m : Nat∞} : m = lift.{u} x ↔ m = x := by
  rw [← lift_ofENat.{u]; rw [v}]; rw [lift_inj]

@[simp]
/--
lemma `range_ofENat` / 引理 `range_ofENat`

English:
lemma range_ofENat
  statement: range ofENat = Iic ℵ₀
  proof: by
  refine (range_subset_iff.2 ofENat_le_aleph0).antisymm fun x (hx : x <= ℵ₀) => ?_
  rcases hx.lt_or_eq with hlt | rfl
  · lift x to Nat using hlt
    exact mem_range_self (x : Nat∞)
  · exact mem_range_self (⊤ : Nat∞)

中文:
引理 range_ofENat
  结论: range ofE自然数 = Iic ℵ₀
  证明: by
  refine (range_subset_iff.2 ofENat_le_aleph0).antisymm fun x (hx : x <= ℵ₀) => ?_
  rcases hx.lt_or_eq with hlt | rfl
  · lift x to Nat using hlt
    exact mem_range_self (x : Nat∞)
  · exact mem_range_self (⊤ : Nat∞)

Depends on / 依赖: antisymm, hx.lt_or_eq, lt_or_eq, mem_range_self, ofENat_le_aleph0, range_subset_iff
-/
lemma range_ofENat : range ofENat = Iic ℵ₀ := by
  refine (range_subset_iff.2 ofENat_le_aleph0).antisymm fun x (hx : x <= ℵ₀) => ?_
  rcases hx.lt_or_eq with hlt | rfl
  · lift x to Nat using hlt
    exact mem_range_self (x : Nat∞)
  · exact mem_range_self (⊤ : Nat∞)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift Cardinal Nat∞ (↑) (· <= ℵ₀)
  body: (Set.ext_iff.1 range_ofENat x).2

中文:
实例 :
  签名: CanLift Cardinal 自然数∞ (↑) (· <= ℵ₀)
  定义体: (Set.ext_iff.1 range_ofENat x).2

Depends on / 依赖: Set.ext_iff, ext_iff, range_ofENat
-/
instance : CanLift Cardinal Nat∞ (↑) (· <= ℵ₀) where
  prf x := (Set.ext_iff.1 range_ofENat x).2

/--
Definition of `toENatAux` / `toENatAux` 的定义

English:
definition toENatAux
  signature: : Cardinal.{u} -> Nat∞
  body: extend Nat.cast Nat.cast fun _ => ⊤

中文:
定义 toENatAux
  签名: : Cardinal.{u} -> 自然数∞
  定义体: extend Nat.cast Nat.cast fun _ => ⊤

Depends on / 依赖: Nat.cast, extend
-/
noncomputable def toENatAux : Cardinal.{u} -> Nat∞ := extend Nat.cast Nat.cast fun _ => ⊤

/--
lemma `toENatAux_nat` / 引理 `toENatAux_nat`

English:
lemma toENatAux_nat
  given: (n : Nat)
  statement: toENatAux n = n
  proof: Nat.cast_injective.extend_apply ..

中文:
引理 toENatAux_nat
  条件: (n : 自然数)
  结论: toE自然数Aux n = n
  证明: Nat.cast_injective.extend_apply ..

Depends on / 依赖: Nat.cast_injective.extend_apply, cast_injective, extend_apply
-/
lemma toENatAux_nat (n : Nat) : toENatAux n = n := Nat.cast_injective.extend_apply ..
/--
lemma `toENatAux_zero` / 引理 `toENatAux_zero`

English:
lemma toENatAux_zero
  statement: toENatAux 0 = 0
  proof: toENatAux_nat 0

中文:
引理 toENatAux_zero
  结论: toE自然数Aux 0 = 0
  证明: toENatAux_nat 0

Depends on / 依赖: toENatAux_nat
-/
lemma toENatAux_zero : toENatAux 0 = 0 := toENatAux_nat 0

/--
lemma `toENatAux_eq_top` / 引理 `toENatAux_eq_top`

English:
lemma toENatAux_eq_top
  given: {a : Cardinal} (ha : ℵ₀ <= a)
  statement: toENatAux a = ⊤
  proof: extend_apply' _ _ _ fun ⟨_n, hn⟩ => ha.not_gt hn ▸ natCast_lt_aleph0

中文:
引理 toENatAux_eq_top
  条件: {a : Cardinal} (ha : ℵ₀ <= a)
  结论: toE自然数Aux a = ⊤
  证明: extend_apply' _ _ _ fun ⟨_n, hn⟩ => ha.not_gt hn ▸ natCast_lt_aleph0

Depends on / 依赖: extend_apply, ha.not_gt, natCast_lt_aleph0, not_gt
-/
lemma toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ <= a) : toENatAux a = ⊤ :=
extend_apply' _ _ _ fun ⟨_n, hn⟩ => ha.not_gt hn ▸ natCast_lt_aleph0

/--
lemma `toENatAux_ofENat` / 引理 `toENatAux_ofENat`

English:
lemma toENatAux_ofENat
  statement: forall n : Nat∞, toENatAux n = n

中文:
引理 toENatAux_ofENat
  结论: 对任意 n : 自然数∞, toE自然数Aux n = n
-/
lemma toENatAux_ofENat : forall n : Nat∞, toENatAux n = n
  | (n : Nat) => toENatAux_nat n
  | ⊤ => toENatAux_eq_top le_rfl

attribute [local simp] toENatAux_nat toENatAux_zero toENatAux_ofENat

/--
lemma `toENatAux_gc` / 引理 `toENatAux_gc`

English:
lemma toENatAux_gc
  statement: GaloisConnection (↑) toENatAux
  proof: fun n x => by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to Nat using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (ofENat_le_aleph0 n).trans hx]

中文:
引理 toENatAux_gc
  结论: GaloisConnection (↑) toE自然数Aux
  证明: fun n x => by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to Nat using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (ofENat_le_aleph0 n).trans hx]

Depends on / 依赖: lt_or_ge, ofENat_le_aleph0, toENatAux_eq_top
-/
lemma toENatAux_gc : GaloisConnection (↑) toENatAux := fun n x => by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to Nat using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (ofENat_le_aleph0 n).trans hx]

/--
theorem `toENatAux_le_nat` / 定理 `toENatAux_le_nat`

English:
theorem toENatAux_le_nat
  given: {x : Cardinal} {n : Nat}
  statement: toENatAux x <= n ↔ x <= n
  proof: by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to Nat using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, natCast_lt_aleph0.trans_le hx]

中文:
定理 toENatAux_le_nat
  条件: {x : Cardinal} {n : 自然数}
  结论: toE自然数Aux x <= n ↔ x <= n
  证明: by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to Nat using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, natCast_lt_aleph0.trans_le hx]

Depends on / 依赖: lt_or_ge, natCast_lt_aleph0, natCast_lt_aleph0.trans_le, toENatAux_eq_top, trans_le
-/
theorem toENatAux_le_nat {x : Cardinal} {n : Nat} : toENatAux x <= n ↔ x <= n := by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to Nat using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, natCast_lt_aleph0.trans_le hx]

/--
lemma `toENatAux_eq_nat` / 引理 `toENatAux_eq_nat`

English:
lemma toENatAux_eq_nat
  given: {x : Cardinal} {n : Nat}
  statement: toENatAux x = n ↔ x = n
  proof: by
  simp only [le_antisymm_iff, toENatAux_le_nat, ← toENatAux_gc _, ofENat_nat]

中文:
引理 toENatAux_eq_nat
  条件: {x : Cardinal} {n : 自然数}
  结论: toE自然数Aux x = n ↔ x = n
  证明: by
  simp only [le_antisymm_iff, toENatAux_le_nat, ← toENatAux_gc _, ofENat_nat]

Depends on / 依赖: le_antisymm_iff, ofENat_nat, toENatAux_gc, toENatAux_le_nat
-/
lemma toENatAux_eq_nat {x : Cardinal} {n : Nat} : toENatAux x = n ↔ x = n := by
  simp only [le_antisymm_iff, toENatAux_le_nat, ← toENatAux_gc _, ofENat_nat]

/--
lemma `toENatAux_eq_zero` / 引理 `toENatAux_eq_zero`

English:
lemma toENatAux_eq_zero
  given: {x : Cardinal}
  statement: toENatAux x = 0 ↔ x = 0
  proof: toENatAux_eq_nat

中文:
引理 toENatAux_eq_zero
  条件: {x : Cardinal}
  结论: toE自然数Aux x = 0 ↔ x = 0
  证明: toENatAux_eq_nat

Depends on / 依赖: toENatAux_eq_nat
-/
lemma toENatAux_eq_zero {x : Cardinal} : toENatAux x = 0 ↔ x = 0 := toENatAux_eq_nat

/--
Definition of `toENat` / `toENat` 的定义

English:
definition toENat
  signature: : Cardinal.{u} ->+*o Nat∞ where
  body: toENatAux
  map_one' := toENatAux_nat 1
  map_mul' x y := by
    wlog hle : x <= y; · rw [mul_comm, this y x (le_of_not_ge hle), mul_comm]
    cases lt_or_ge y ℵ₀ with
    | inl hy =>
      lift x to Nat using hle.trans_lt hy; lift y to Nat using hy
      simp only [← Nat.cast_mul, toENatAux_nat]
  

中文:
定义 toENat
  签名: : Cardinal.{u} ->+*o 自然数∞ where
  定义体: toENatAux
  map_one' := toENatAux_nat 1
  map_mul' x y := by
    wlog hle : x <= y; · rw [mul_comm, this y x (le_of_not_ge hle), mul_comm]
    cases lt_or_ge y ℵ₀ with
    | inl hy =>
      lift x to Nat using hle.trans_lt hy; lift y to Nat using hy
      simp only [← Nat.cast_mul, toENatAux_nat]
  

Depends on / 依赖: toENatAux
-/
noncomputable def toENat : Cardinal.{u} ->+*o Nat∞ where
  toFun := toENatAux
  map_one' := toENatAux_nat 1
  map_mul' x y := by
    wlog hle : x <= y; · rw [mul_comm, this y x (le_of_not_ge hle), mul_comm]
    cases lt_or_ge y ℵ₀ with
    | inl hy =>
      lift x to Nat using hle.trans_lt hy; lift y to Nat using hy
      simp only [← Nat.cast_mul, toENatAux_nat]
    | inr hy =>
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · simp only [toENatAux_eq_top hy]
        rw [toENatAux_eq_top]; rw [ENat.mul_top]
        · rwa [Ne, toENatAux_eq_zero]
        · exact le_mul_of_one_le_of_le (Cardinal.one_le_iff_ne_zero.2 hx) hy
  map_add' x y := by
    wlog hle : x <= y; · rw [add_comm, this y x (le_of_not_ge hle), add_comm]
    cases lt_or_ge y ℵ₀ with
    | inl hy =>
      lift x to Nat using hle.trans_lt hy; lift y to Nat using hy
      simp only [← Nat.cast_add, toENatAux_nat]
    | inr hy =>
      simp only [toENatAux_eq_top hy, add_top]
exact toENatAux_eq_top le_add_left hy
  map_zero' := toENatAux_zero
  monotone' := toENatAux_gc.monotone_u

/--
lemma `enat_gc` / 引理 `enat_gc`

English:
lemma enat_gc
  statement: GaloisConnection (↑) toENat
  proof: toENatAux_gc

中文:
引理 enat_gc
  结论: GaloisConnection (↑) toE自然数
  证明: toENatAux_gc

Depends on / 依赖: toENatAux_gc
-/
lemma enat_gc : GaloisConnection (↑) toENat := toENatAux_gc

/--
lemma `toENat_ofENat` / 引理 `toENat_ofENat`

English:
lemma toENat_ofENat
  given: (n : Nat∞)
  statement: toENat n = n
  proof: toENatAux_ofENat n

中文:
引理 toENat_ofENat
  条件: (n : 自然数∞)
  结论: toE自然数 n = n
  证明: toENatAux_ofENat n
-/
@[simp] lemma toENat_ofENat (n : Nat∞) : toENat n = n := toENatAux_ofENat n
/--
lemma `toENat_comp_ofENat` / 引理 `toENat_comp_ofENat`

English:
lemma toENat_comp_ofENat
  statement: toENat ∘ (↑) = id
  proof: funext toENat_ofENat

中文:
引理 toENat_comp_ofENat
  结论: toE自然数 ∘ (↑) = id
  证明: funext toENat_ofENat
-/
@[simp] lemma toENat_comp_ofENat : toENat ∘ (↑) = id := funext toENat_ofENat

/--
Definition of `gciENat` / `gciENat` 的定义

English:
definition gciENat
  signature: : GaloisCoinsertion (↑) toENat
  body: enat_gc.toGaloisCoinsertion fun n => (toENat_ofENat n).le

中文:
定义 gciENat
  签名: : GaloisCoinsertion (↑) toE自然数
  定义体: enat_gc.toGaloisCoinsertion fun n => (toENat_ofENat n).le

Depends on / 依赖: enat_gc, enat_gc.toGaloisCoinsertion, toENat_ofENat, toGaloisCoinsertion
-/
noncomputable def gciENat : GaloisCoinsertion (↑) toENat :=
  enat_gc.toGaloisCoinsertion fun n => (toENat_ofENat n).le

/--
lemma `toENat_strictMonoOn` / 引理 `toENat_strictMonoOn`

English:
lemma toENat_strictMonoOn
  statement: StrictMonoOn toENat (Iic ℵ₀)
  proof: by
  simp only [← range_ofENat, StrictMonoOn, forall_mem_range, toENat_ofENat, ofENat_lt_ofENat]
  exact fun _ _ => id

中文:
引理 toENat_strictMonoOn
  结论: StrictMonoOn toE自然数 (Iic ℵ₀)
  证明: by
  simp only [← range_ofENat, StrictMonoOn, forall_mem_range, toENat_ofENat, ofENat_lt_ofENat]
  exact fun _ _ => id

Depends on / 依赖: StrictMonoOn, forall_mem_range, ofENat_lt_ofENat, range_ofENat, toENat_ofENat
-/
lemma toENat_strictMonoOn : StrictMonoOn toENat (Iic ℵ₀) := by
  simp only [← range_ofENat, StrictMonoOn, forall_mem_range, toENat_ofENat, ofENat_lt_ofENat]
  exact fun _ _ => id

/--
lemma `toENat_injOn` / 引理 `toENat_injOn`

English:
lemma toENat_injOn
  statement: InjOn toENat (Iic ℵ₀)
  proof: toENat_strictMonoOn.injOn

中文:
引理 toENat_injOn
  结论: InjOn toE自然数 (Iic ℵ₀)
  证明: toENat_strictMonoOn.injOn

Depends on / 依赖: toENat_strictMonoOn, toENat_strictMonoOn.injOn
-/
lemma toENat_injOn : InjOn toENat (Iic ℵ₀) := toENat_strictMonoOn.injOn

/--
lemma `ofENat_toENat_le` / 引理 `ofENat_toENat_le`

English:
lemma ofENat_toENat_le
  given: (a : Cardinal)
  statement: ↑(toENat a) <= a
  proof: enat_gc.l_u_le _

@[simp]

中文:
引理 ofENat_toENat_le
  条件: (a : Cardinal)
  结论: ↑(toE自然数 a) <= a
  证明: enat_gc.l_u_le _

@[simp]

Depends on / 依赖: enat_gc, enat_gc.l_u_le, l_u_le
-/
lemma ofENat_toENat_le (a : Cardinal) : ↑(toENat a) <= a := enat_gc.l_u_le _

@[simp]
/--
lemma `ofENat_toENat_eq_self` / 引理 `ofENat_toENat_eq_self`

English:
lemma ofENat_toENat_eq_self
  given: {a : Cardinal}
  statement: toENat a = a ↔ a <= ℵ₀
  proof: by
  rw [eq_comm]; rw [← enat_gc.exists_eq_l]
  simpa only [mem_range, eq_comm] using! Set.ext_iff.1 range_ofENat a

@[simp] alias ⟨_, ofENat_toENat⟩ := ofENat_toENat_eq_self

中文:
引理 ofENat_toENat_eq_self
  条件: {a : Cardinal}
  结论: toE自然数 a = a ↔ a <= ℵ₀
  证明: by
  rw [eq_comm]; rw [← enat_gc.exists_eq_l]
  simpa only [mem_range, eq_comm] using! Set.ext_iff.1 range_ofENat a

@[simp] alias ⟨_, ofENat_toENat⟩ := ofENat_toENat_eq_self

Depends on / 依赖: Set.ext_iff, enat_gc, enat_gc.exists_eq_l, eq_comm, exists_eq_l, ext_iff, mem_range, range_ofENat
-/
lemma ofENat_toENat_eq_self {a : Cardinal} : toENat a = a ↔ a <= ℵ₀ := by
  rw [eq_comm]; rw [← enat_gc.exists_eq_l]
  simpa only [mem_range, eq_comm] using! Set.ext_iff.1 range_ofENat a

@[simp] alias ⟨_, ofENat_toENat⟩ := ofENat_toENat_eq_self

/--
lemma `toENat_nat` / 引理 `toENat_nat`

English:
lemma toENat_nat
  given: (n : Nat)
  statement: toENat n = n
  proof: map_natCast _ n

中文:
引理 toENat_nat
  条件: (n : 自然数)
  结论: toE自然数 n = n
  证明: map_natCast _ n

Depends on / 依赖: map_natCast
-/
lemma toENat_nat (n : Nat) : toENat n = n := map_natCast _ n

/--
lemma `toENat_ofNat` / 引理 `toENat_ofNat`

English:
lemma toENat_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: toENat ofNat(n) = ofNat(n)
  proof: toENat_nat _

中文:
引理 toENat_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: toE自然数 of自然数(n) = of自然数(n)
  证明: toENat_nat _
-/
@[simp] lemma toENat_ofNat (n : Nat) [n.AtLeastTwo] : toENat ofNat(n) = ofNat(n) := toENat_nat _

variable {c c' : Cardinal.{u}} {n : Nat}

/--
lemma `toENat_le_natCast` / 引理 `toENat_le_natCast`

English:
lemma toENat_le_natCast
  statement: toENat c <= n ↔ c <= n
  proof: toENatAux_le_nat

中文:
引理 toENat_le_natCast
  结论: toE自然数 c <= n ↔ c <= n
  证明: toENatAux_le_nat
-/
@[simp] lemma toENat_le_natCast : toENat c <= n ↔ c <= n := toENatAux_le_nat
/--
lemma `toENat_le_one` / 引理 `toENat_le_one`

English:
lemma toENat_le_one
  statement: toENat c <= 1 ↔ c <= 1
  proof: toENat_le_natCast

中文:
引理 toENat_le_one
  结论: toE自然数 c <= 1 ↔ c <= 1
  证明: toENat_le_natCast
-/
@[simp] lemma toENat_le_one : toENat c <= 1 ↔ c <= 1 := toENat_le_natCast
/--
lemma `toENat_le_ofNat` / 引理 `toENat_le_ofNat`

English:
lemma toENat_le_ofNat
  given: [n.AtLeastTwo]
  statement: toENat c <= ofNat(n) ↔ c <= ofNat(n)
  proof: toENat_le_natCast

@[deprecated (since := "2026-01-13")] alias toENat_le_nat := toENat_le_natCast

中文:
引理 toENat_le_ofNat
  条件: [n.AtLeastTwo]
  结论: toE自然数 c <= of自然数(n) ↔ c <= of自然数(n)
  证明: toENat_le_natCast

@[deprecated (since := "2026-01-13")] alias toENat_le_nat := toENat_le_natCast
-/
@[simp] lemma toENat_le_ofNat [n.AtLeastTwo] : toENat c <= ofNat(n) ↔ c <= ofNat(n) :=
  toENat_le_natCast

@[deprecated (since := "2026-01-13")] alias toENat_le_nat := toENat_le_natCast

/--
lemma `toENat_le_iff_of_le_aleph0` / 引理 `toENat_le_iff_of_le_aleph0`

English:
lemma toENat_le_iff_of_le_aleph0
  given: (hc : c <= ℵ₀)
  statement: toENat c <= toENat c' ↔ c <= c'
  proof: by
  lift c to Nat∞ using hc; simp_rw [toENat_ofENat, enat_gc _]

中文:
引理 toENat_le_iff_of_le_aleph0
  条件: (hc : c <= ℵ₀)
  结论: toE自然数 c <= toE自然数 c' ↔ c <= c'
  证明: by
  lift c to Nat∞ using hc; simp_rw [toENat_ofENat, enat_gc _]

Depends on / 依赖: enat_gc, simp_rw, toENat_ofENat
-/
lemma toENat_le_iff_of_le_aleph0 (hc : c <= ℵ₀) : toENat c <= toENat c' ↔ c <= c' := by
  lift c to Nat∞ using hc; simp_rw [toENat_ofENat, enat_gc _]

/--
lemma `toENat_le_iff_of_lt_aleph0` / 引理 `toENat_le_iff_of_lt_aleph0`

English:
lemma toENat_le_iff_of_lt_aleph0
  given: (hc' : c' < ℵ₀)
  statement: toENat c <= toENat c' ↔ c <= c'
  proof: by
  lift c' to Nat using hc'; simp_rw [toENat_nat, ← toENat_le_natCast]

中文:
引理 toENat_le_iff_of_lt_aleph0
  条件: (hc' : c' < ℵ₀)
  结论: toE自然数 c <= toE自然数 c' ↔ c <= c'
  证明: by
  lift c' to Nat using hc'; simp_rw [toENat_nat, ← toENat_le_natCast]

Depends on / 依赖: simp_rw, toENat_le_natCast, toENat_nat
-/
lemma toENat_le_iff_of_lt_aleph0 (hc' : c' < ℵ₀) : toENat c <= toENat c' ↔ c <= c' := by
  lift c' to Nat using hc'; simp_rw [toENat_nat, ← toENat_le_natCast]

/--
lemma `toENat_eq_iff_of_le_aleph0` / 引理 `toENat_eq_iff_of_le_aleph0`

English:
lemma toENat_eq_iff_of_le_aleph0
  given: (hc : c <= ℵ₀) (hc' : c' <= ℵ₀)
  statement: toENat c = toENat c' ↔ c = c'
  proof: toENat_strictMonoOn.injOn.eq_iff hc hc'

中文:
引理 toENat_eq_iff_of_le_aleph0
  条件: (hc : c <= ℵ₀) (hc' : c' <= ℵ₀)
  结论: toE自然数 c = toE自然数 c' ↔ c = c'
  证明: toENat_strictMonoOn.injOn.eq_iff hc hc'

Depends on / 依赖: eq_iff, toENat_strictMonoOn, toENat_strictMonoOn.injOn.eq_iff
-/
lemma toENat_eq_iff_of_le_aleph0 (hc : c <= ℵ₀) (hc' : c' <= ℵ₀) : toENat c = toENat c' ↔ c = c' :=
  toENat_strictMonoOn.injOn.eq_iff hc hc'

/--
lemma `natCast_le_toENat` / 引理 `natCast_le_toENat`

English:
lemma natCast_le_toENat
  statement: n <= toENat c ↔ n <= c
  proof: by
  rw [← toENat_nat n]; rw [toENat_le_iff_of_le_aleph0 natCast_le_aleph0]

中文:
引理 natCast_le_toENat
  结论: n <= toE自然数 c ↔ n <= c
  证明: by
  rw [← toENat_nat n]; rw [toENat_le_iff_of_le_aleph0 natCast_le_aleph0]
-/
@[simp] lemma natCast_le_toENat : n <= toENat c ↔ n <= c := by
  rw [← toENat_nat n]; rw [toENat_le_iff_of_le_aleph0 natCast_le_aleph0]

/--
lemma `one_le_toENat` / 引理 `one_le_toENat`

English:
lemma one_le_toENat
  statement: 1 <= toENat c ↔ 1 <= c
  proof: natCast_le_toENat

中文:
引理 one_le_toENat
  结论: 1 <= toE自然数 c ↔ 1 <= c
  证明: natCast_le_toENat
-/
@[simp] lemma one_le_toENat : 1 <= toENat c ↔ 1 <= c := natCast_le_toENat
/--
lemma `ofNat_le_toENat` / 引理 `ofNat_le_toENat`

English:
lemma ofNat_le_toENat
  given: [n.AtLeastTwo]
  statement: ofNat(n) <= toENat c ↔ ofNat(n) <= c
  proof: natCast_le_toENat

中文:
引理 ofNat_le_toENat
  条件: [n.AtLeastTwo]
  结论: of自然数(n) <= toE自然数 c ↔ of自然数(n) <= c
  证明: natCast_le_toENat
-/
@[simp] lemma ofNat_le_toENat [n.AtLeastTwo] : ofNat(n) <= toENat c ↔ ofNat(n) <= c :=
  natCast_le_toENat

/--
lemma `toENat_lt_natCast` / 引理 `toENat_lt_natCast`

English:
lemma toENat_lt_natCast
  statement: toENat c < n ↔ c < n
  proof: by simp [← not_le]

中文:
引理 toENat_lt_natCast
  结论: toE自然数 c < n ↔ c < n
  证明: by simp [← not_le]
-/
@[simp] lemma toENat_lt_natCast : toENat c < n ↔ c < n := by simp [← not_le]
/--
lemma `toENat_lt_ofNat` / 引理 `toENat_lt_ofNat`

English:
lemma toENat_lt_ofNat
  given: [n.AtLeastTwo]
  statement: toENat c < ofNat(n) ↔ c < ofNat(n)
  proof: toENat_lt_natCast

中文:
引理 toENat_lt_ofNat
  条件: [n.AtLeastTwo]
  结论: toE自然数 c < of自然数(n) ↔ c < of自然数(n)
  证明: toENat_lt_natCast
-/
@[simp] lemma toENat_lt_ofNat [n.AtLeastTwo] : toENat c < ofNat(n) ↔ c < ofNat(n) :=
  toENat_lt_natCast

/--
lemma `natCast_lt_toENat` / 引理 `natCast_lt_toENat`

English:
lemma natCast_lt_toENat
  statement: n < toENat c ↔ n < c
  proof: by simp [← not_le]

中文:
引理 natCast_lt_toENat
  结论: n < toE自然数 c ↔ n < c
  证明: by simp [← not_le]
-/
@[simp] lemma natCast_lt_toENat : n < toENat c ↔ n < c := by simp [← not_le]
/--
lemma `one_lt_toENat` / 引理 `one_lt_toENat`

English:
lemma one_lt_toENat
  statement: 1 < toENat c ↔ 1 < c
  proof: natCast_lt_toENat

中文:
引理 one_lt_toENat
  结论: 1 < toE自然数 c ↔ 1 < c
  证明: natCast_lt_toENat
-/
@[simp] lemma one_lt_toENat : 1 < toENat c ↔ 1 < c := natCast_lt_toENat
/--
lemma `ofNat_lt_toENat` / 引理 `ofNat_lt_toENat`

English:
lemma ofNat_lt_toENat
  given: [n.AtLeastTwo]
  statement: ofNat(n) < toENat c ↔ ofNat(n) < c
  proof: natCast_lt_toENat

中文:
引理 ofNat_lt_toENat
  条件: [n.AtLeastTwo]
  结论: of自然数(n) < toE自然数 c ↔ of自然数(n) < c
  证明: natCast_lt_toENat
-/
@[simp] lemma ofNat_lt_toENat [n.AtLeastTwo] : ofNat(n) < toENat c ↔ ofNat(n) < c :=
  natCast_lt_toENat

/--
lemma `toENat_eq_natCast` / 引理 `toENat_eq_natCast`

English:
lemma toENat_eq_natCast
  statement: toENat c = n ↔ c = n
  proof: toENatAux_eq_nat

中文:
引理 toENat_eq_natCast
  结论: toE自然数 c = n ↔ c = n
  证明: toENatAux_eq_nat
-/
@[simp] lemma toENat_eq_natCast : toENat c = n ↔ c = n := toENatAux_eq_nat
/--
lemma `toENat_eq_zero` / 引理 `toENat_eq_zero`

English:
lemma toENat_eq_zero
  statement: toENat c = 0 ↔ c = 0
  proof: toENat_eq_natCast

中文:
引理 toENat_eq_zero
  结论: toE自然数 c = 0 ↔ c = 0
  证明: toENat_eq_natCast
-/
@[simp] lemma toENat_eq_zero : toENat c = 0 ↔ c = 0 := toENat_eq_natCast
/--
lemma `toENat_eq_one` / 引理 `toENat_eq_one`

English:
lemma toENat_eq_one
  statement: toENat c = 1 ↔ c = 1
  proof: toENat_eq_natCast

中文:
引理 toENat_eq_one
  结论: toE自然数 c = 1 ↔ c = 1
  证明: toENat_eq_natCast
-/
@[simp] lemma toENat_eq_one : toENat c = 1 ↔ c = 1 := toENat_eq_natCast
/--
lemma `toENat_eq_ofNat` / 引理 `toENat_eq_ofNat`

English:
lemma toENat_eq_ofNat
  given: [n.AtLeastTwo]
  statement: toENat c = ofNat(n) ↔ c = ofNat(n)
  proof: toENat_eq_natCast

@[deprecated toENat_eq_zero (since := "2026-05-25")]

中文:
引理 toENat_eq_ofNat
  条件: [n.AtLeastTwo]
  结论: toE自然数 c = of自然数(n) ↔ c = of自然数(n)
  证明: toENat_eq_natCast

@[deprecated toENat_eq_zero (since := "2026-05-25")]
-/
@[simp] lemma toENat_eq_ofNat [n.AtLeastTwo] : toENat c = ofNat(n) ↔ c = ofNat(n) :=
  toENat_eq_natCast

@[deprecated toENat_eq_zero (since := "2026-05-25")]
/--
lemma `toENat_lt_one` / 引理 `toENat_lt_one`

English:
lemma toENat_lt_one
  statement: toENat c < 1 ↔ c < 1
  proof: by simp

@[deprecated (since := "2026-01-13")] alias toENat_eq_nat := toENat_eq_natCast

中文:
引理 toENat_lt_one
  结论: toE自然数 c < 1 ↔ c < 1
  证明: by simp

@[deprecated (since := "2026-01-13")] alias toENat_eq_nat := toENat_eq_natCast
-/
lemma toENat_lt_one : toENat c < 1 ↔ c < 1 := by simp

@[deprecated (since := "2026-01-13")] alias toENat_eq_nat := toENat_eq_natCast

/--
lemma `natCast_eq_toENat` / 引理 `natCast_eq_toENat`

English:
lemma natCast_eq_toENat
  statement: n = toENat c ↔ n = c
  proof: by simp [eq_comm (a := Nat.cast _)]

中文:
引理 natCast_eq_toENat
  结论: n = toE自然数 c ↔ n = c
  证明: by simp [eq_comm (a := Nat.cast _)]
-/
@[simp] lemma natCast_eq_toENat : n = toENat c ↔ n = c := by simp [eq_comm (a := Nat.cast _)]
/--
lemma `ofNat_eq_toENat` / 引理 `ofNat_eq_toENat`

English:
lemma ofNat_eq_toENat
  given: [n.AtLeastTwo]
  statement: ofNat(n) = toENat c ↔ ofNat(n) = c
  proof: natCast_eq_toENat

中文:
引理 ofNat_eq_toENat
  条件: [n.AtLeastTwo]
  结论: of自然数(n) = toE自然数 c ↔ of自然数(n) = c
  证明: natCast_eq_toENat
-/
@[simp] lemma ofNat_eq_toENat [n.AtLeastTwo] : ofNat(n) = toENat c ↔ ofNat(n) = c :=
  natCast_eq_toENat

/--
lemma `toENat_eq_top` / 引理 `toENat_eq_top`

English:
lemma toENat_eq_top
  statement: toENat c = ⊤ ↔ ℵ₀ <= c
  proof: enat_gc.u_eq_top

中文:
引理 toENat_eq_top
  结论: toE自然数 c = ⊤ ↔ ℵ₀ <= c
  证明: enat_gc.u_eq_top
-/
@[simp] lemma toENat_eq_top : toENat c = ⊤ ↔ ℵ₀ <= c := enat_gc.u_eq_top

/--
lemma `toENat_ne_top` / 引理 `toENat_ne_top`

English:
lemma toENat_ne_top
  statement: toENat c != ⊤ ↔ c < ℵ₀
  proof: by simp

中文:
引理 toENat_ne_top
  结论: toE自然数 c != ⊤ ↔ c < ℵ₀
  证明: by simp
-/
lemma toENat_ne_top : toENat c != ⊤ ↔ c < ℵ₀ := by simp

/--
lemma `toENat_lt_top` / 引理 `toENat_lt_top`

English:
lemma toENat_lt_top
  statement: toENat c < ⊤ ↔ c < ℵ₀
  proof: by simp [lt_top_iff_ne_top]

@[simp]

中文:
引理 toENat_lt_top
  结论: toE自然数 c < ⊤ ↔ c < ℵ₀
  证明: by simp [lt_top_iff_ne_top]

@[simp]
-/
@[simp] lemma toENat_lt_top : toENat c < ⊤ ↔ c < ℵ₀ := by simp [lt_top_iff_ne_top]

@[simp]
/--
theorem `toENat_lift` / 定理 `toENat_lift`

English:
theorem toENat_lift
  statement: toENat (lift.{v} c) = toENat c
  proof: by
  cases le_total c ℵ₀ with
  | inl ha => lift c to Nat∞ using ha; simp
  | inr ha => simp [toENat_eq_top.2, ha]

中文:
定理 toENat_lift
  结论: toE自然数 (lift.{v} c) = toE自然数 c
  证明: by
  cases le_total c ℵ₀ with
  | inl ha => lift c to Nat∞ using ha; simp
  | inr ha => simp [toENat_eq_top.2, ha]

Depends on / 依赖: le_total, toENat_eq_top
-/
theorem toENat_lift : toENat (lift.{v} c) = toENat c := by
  cases le_total c ℵ₀ with
  | inl ha => lift c to Nat∞ using ha; simp
  | inr ha => simp [toENat_eq_top.2, ha]

/--
theorem `toENat_congr` / 定理 `toENat_congr`

English:
theorem toENat_congr
  given: {α : Type u} {β : Type v} (e : α ≃ β)
  statement: toENat #α = toENat #β
  proof: by
  rw [← toENat_lift]; rw [lift_mk_eq.{_]; rw [_]; rw [v}.mpr ⟨e⟩]; rw [toENat_lift]

@[simp, norm_cast]

中文:
定理 toENat_congr
  条件: {α : 类型u} {β : 类型v} (e : α ≃ β)
  结论: toE自然数 #α = toE自然数 #β
  证明: by
  rw [← toENat_lift]; rw [lift_mk_eq.{_]; rw [_]; rw [v}.mpr ⟨e⟩]; rw [toENat_lift]

@[simp, norm_cast]

Depends on / 依赖: lift_mk_eq, toENat_lift
-/
theorem toENat_congr {α : Type u} {β : Type v} (e : α ≃ β) : toENat #α = toENat #β := by
  rw [← toENat_lift]; rw [lift_mk_eq.{_]; rw [_]; rw [v}.mpr ⟨e⟩]; rw [toENat_lift]

@[simp, norm_cast]
/--
lemma `ofENat_add` / 引理 `ofENat_add`

English:
lemma ofENat_add
  given: (m n : Nat∞)
  statement: ofENat (m + n) = m + n
  proof: by apply toENat_injOn <;> simp

中文:
引理 ofENat_add
  条件: (m n : 自然数∞)
  结论: ofE自然数 (m + n) = m + n
  证明: by apply toENat_injOn <;> simp

Depends on / 依赖: toENat_injOn
-/
lemma ofENat_add (m n : Nat∞) : ofENat (m + n) = m + n := by apply toENat_injOn <;> simp

/--
lemma `aleph0_add_ofENat` / 引理 `aleph0_add_ofENat`

English:
lemma aleph0_add_ofENat
  given: (m : Nat∞)
  statement: ℵ₀ + m = ℵ₀
  proof: (ofENat_add ⊤ m).symm

中文:
引理 aleph0_add_ofENat
  条件: (m : 自然数∞)
  结论: ℵ₀ + m = ℵ₀
  证明: (ofENat_add ⊤ m).symm
-/
@[simp] lemma aleph0_add_ofENat (m : Nat∞) : ℵ₀ + m = ℵ₀ := (ofENat_add ⊤ m).symm

/--
lemma `ofENat_add_aleph0` / 引理 `ofENat_add_aleph0`

English:
lemma ofENat_add_aleph0
  given: (m : Nat∞)
  statement: m + ℵ₀ = ℵ₀
  proof: by rw [add_comm, aleph0_add_ofENat]

中文:
引理 ofENat_add_aleph0
  条件: (m : 自然数∞)
  结论: m + ℵ₀ = ℵ₀
  证明: by rw [add_comm, aleph0_add_ofENat]
-/
@[simp] lemma ofENat_add_aleph0 (m : Nat∞) : m + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_ofENat]

/--
lemma `ofENat_mul_aleph0` / 引理 `ofENat_mul_aleph0`

English:
lemma ofENat_mul_aleph0
  given: {m : Nat∞} (hm : m != 0)
  statement: ↑m * ℵ₀ = ℵ₀
  proof: by
  induction m with
  | top => exact aleph0_mul_aleph0
  | coe m => rw [ofENat_nat, nat_mul_aleph0 (mod_cast hm)]

中文:
引理 ofENat_mul_aleph0
  条件: {m : 自然数∞} (hm : m != 0)
  结论: ↑m * ℵ₀ = ℵ₀
  证明: by
  induction m with
  | top => exact aleph0_mul_aleph0
  | coe m => rw [ofENat_nat, nat_mul_aleph0 (mod_cast hm)]
-/
@[simp] lemma ofENat_mul_aleph0 {m : Nat∞} (hm : m != 0) : ↑m * ℵ₀ = ℵ₀ := by
  induction m with
  | top => exact aleph0_mul_aleph0
  | coe m => rw [ofENat_nat, nat_mul_aleph0 (mod_cast hm)]

/--
lemma `aleph0_mul_ofENat` / 引理 `aleph0_mul_ofENat`

English:
lemma aleph0_mul_ofENat
  given: {m : Nat∞} (hm : m != 0)
  statement: ℵ₀ * m = ℵ₀
  proof: by
  rw [mul_comm]; rw [ofENat_mul_aleph0 hm]

中文:
引理 aleph0_mul_ofENat
  条件: {m : 自然数∞} (hm : m != 0)
  结论: ℵ₀ * m = ℵ₀
  证明: by
  rw [mul_comm]; rw [ofENat_mul_aleph0 hm]
-/
@[simp] lemma aleph0_mul_ofENat {m : Nat∞} (hm : m != 0) : ℵ₀ * m = ℵ₀ := by
  rw [mul_comm]; rw [ofENat_mul_aleph0 hm]

/--
lemma `ofENat_mul` / 引理 `ofENat_mul`

English:
lemma ofENat_mul
  given: (m n : Nat∞)
  statement: ofENat (m * n) = m * n
  proof: toENat_injOn (by simp)
    (aleph0_mul_aleph0 ▸ mul_le_mul' (ofENat_le_aleph0 _) (ofENat_le_aleph0 _)) (by simp)

中文:
引理 ofENat_mul
  条件: (m n : 自然数∞)
  结论: ofE自然数 (m * n) = m * n
  证明: toENat_injOn (by simp)
    (aleph0_mul_aleph0 ▸ mul_le_mul' (ofENat_le_aleph0 _) (ofENat_le_aleph0 _)) (by simp)
-/
@[simp] lemma ofENat_mul (m n : Nat∞) : ofENat (m * n) = m * n :=
  toENat_injOn (by simp)
    (aleph0_mul_aleph0 ▸ mul_le_mul' (ofENat_le_aleph0 _) (ofENat_le_aleph0 _)) (by simp)

/--
Definition of `ofENatHom` / `ofENatHom` 的定义

English:
definition ofENatHom
  signature: : Nat∞ ->+*o Cardinal where
  body: (↑)
  map_one' := ofENat_one
  map_mul' := ofENat_mul
  map_zero' := ofENat_zero
  map_add' := ofENat_add
  monotone' := ofENat_mono

中文:
定义 ofENatHom
  签名: : 自然数∞ ->+*o Cardinal where
  定义体: (↑)
  map_one' := ofENat_one
  map_mul' := ofENat_mul
  map_zero' := ofENat_zero
  map_add' := ofENat_add
  monotone' := ofENat_mono
-/
def ofENatHom : Nat∞ ->+*o Cardinal where
  toFun := (↑)
  map_one' := ofENat_one
  map_mul' := ofENat_mul
  map_zero' := ofENat_zero
  map_add' := ofENat_add
  monotone' := ofENat_mono

end Cardinal
