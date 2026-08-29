/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENNReal.Basic

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/

@[expose] public section

assert_not_exists Finset

open NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : Nat∞}

/--
Definition of `toENNReal` / `toENNReal` 的定义

English:
definition toENNReal
  signature: : Nat∞ -> Real>=0∞
  body: ENat.map Nat.cast

中文:
定义 toENNReal
  签名: : 自然数∞ -> 实数>=0∞
  定义体: ENat.map Nat.cast
-/
@[coe] def toENNReal : Nat∞ -> Real>=0∞ := ENat.map Nat.cast

/--
Instance `hasCoeENNReal` / 实例 `hasCoeENNReal`

English:
instance hasCoeENNReal
  signature: : CoeTC Nat∞ Real>=0∞
  body: ⟨toENNReal⟩

@[simp]

中文:
实例 hasCoeENNReal
  签名: : CoeTC 自然数∞ 实数>=0∞
  定义体: ⟨toENNReal⟩

@[simp]

Depends on / 依赖: toENNReal
-/
instance hasCoeENNReal : CoeTC Nat∞ Real>=0∞ := ⟨toENNReal⟩

@[simp]
/--
theorem `map_coe_nnreal` / 定理 `map_coe_nnreal`

English:
theorem map_coe_nnreal
  statement: ENat.map ((↑) : Nat -> Real>=0) = ((↑) : Nat∞ -> Real>=0∞)
  proof: rfl

中文:
定理 map_coe_nnreal
  结论: E自然数.map ((↑) : 自然数 -> 实数>=0) = ((↑) : 自然数∞ -> 实数>=0∞)
  证明: rfl
-/
theorem map_coe_nnreal : ENat.map ((↑) : Nat -> Real>=0) = ((↑) : Nat∞ -> Real>=0∞) :=
  rfl

/-- Coercion `ℕ∞ → ℝ≥0∞` as an `OrderEmbedding`. -/
@[simps! -fullyApplied]
/--
Definition of `toENNRealOrderEmbedding` / `toENNRealOrderEmbedding` 的定义

English:
definition toENNRealOrderEmbedding
  signature: : Nat∞ ↪o Real>=0∞
  body: Nat.castOrderEmbedding.withTopMap

中文:
定义 toENNRealOrderEmbedding
  签名: : 自然数∞ ↪o 实数>=0∞
  定义体: Nat.castOrderEmbedding.withTopMap

Depends on / 依赖: Nat.castOrderEmbedding.withTopMap, castOrderEmbedding, withTopMap
-/
def toENNRealOrderEmbedding : Nat∞ ↪o Real>=0∞ :=
  Nat.castOrderEmbedding.withTopMap

/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps! -fullyApplied]
/--
Definition of `toENNRealRingHom` / `toENNRealRingHom` 的定义

English:
definition toENNRealRingHom
  signature: : Nat∞ ->+* Real>=0∞
  body: .ENatMap (Nat.castRingHom Real>=0) Nat.cast_injective

@[simp, norm_cast]

中文:
定义 toENNRealRingHom
  签名: : 自然数∞ ->+* 实数>=0∞
  定义体: .ENatMap (Nat.castRingHom Real>=0) Nat.cast_injective

@[simp, norm_cast]

Depends on / 依赖: ENatMap, Nat.castRingHom, Nat.cast_injective, castRingHom, cast_injective
-/
def toENNRealRingHom : Nat∞ ->+* Real>=0∞ :=
  .ENatMap (Nat.castRingHom Real>=0) Nat.cast_injective

@[simp, norm_cast]
/--
theorem `toENNReal_top` / 定理 `toENNReal_top`

English:
theorem toENNReal_top
  statement: ((⊤ : Nat∞) : Real>=0∞) = ⊤
  proof: rfl

@[simp, norm_cast]

中文:
定理 toENNReal_top
  结论: ((⊤ : 自然数∞) : 实数>=0∞) = ⊤
  证明: rfl

@[simp, norm_cast]
-/
theorem toENNReal_top : ((⊤ : Nat∞) : Real>=0∞) = ⊤ :=
  rfl

@[simp, norm_cast]
/--
theorem `toENNReal_coe` / 定理 `toENNReal_coe`

English:
theorem toENNReal_coe
  given: (n : Nat)
  statement: ((n : Nat∞) : Real>=0∞) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 toENNReal_coe
  条件: (n : 自然数)
  结论: ((n : 自然数∞) : 实数>=0∞) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem toENNReal_coe (n : Nat) : ((n : Nat∞) : Real>=0∞) = n :=
  rfl

@[simp, norm_cast]
/--
theorem `toENNReal_ofNat` / 定理 `toENNReal_ofNat`

English:
theorem toENNReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ((ofNat(n) : Nat∞) : Real>=0∞) = ofNat(n)
  proof: rfl

@[simp, norm_cast]

中文:
定理 toENNReal_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ((of自然数(n) : 自然数∞) : 实数>=0∞) = of自然数(n)
  证明: rfl

@[simp, norm_cast]
-/
theorem toENNReal_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Nat∞) : Real>=0∞) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/--
theorem `toENNReal_inj` / 定理 `toENNReal_inj`

English:
theorem toENNReal_inj
  statement: (m : Real>=0∞) = (n : Real>=0∞) ↔ m = n
  proof: toENNRealOrderEmbedding.eq_iff_eq

中文:
定理 toENNReal_inj
  结论: (m : 实数>=0∞) = (n : 实数>=0∞) ↔ m = n
  证明: toENNRealOrderEmbedding.eq_iff_eq

Depends on / 依赖: eq_iff_eq, toENNRealOrderEmbedding, toENNRealOrderEmbedding.eq_iff_eq
-/
theorem toENNReal_inj : (m : Real>=0∞) = (n : Real>=0∞) ↔ m = n :=
  toENNRealOrderEmbedding.eq_iff_eq

/--
lemma `toENNReal_eq_top` / 引理 `toENNReal_eq_top`

English:
lemma toENNReal_eq_top
  statement: (n : Real>=0∞) = ∞ ↔ n = ⊤
  proof: by simp [← toENNReal_inj]

中文:
引理 toENNReal_eq_top
  结论: (n : 实数>=0∞) = ∞ ↔ n = ⊤
  证明: by simp [← toENNReal_inj]
-/
@[simp, norm_cast] lemma toENNReal_eq_top : (n : Real>=0∞) = ∞ ↔ n = ⊤ := by simp [← toENNReal_inj]
/--
lemma `toENNReal_ne_top` / 引理 `toENNReal_ne_top`

English:
lemma toENNReal_ne_top
  statement: (n : Real>=0∞) != ∞ ↔ n != ⊤
  proof: by simp

@[simp, norm_cast, gcongr]

中文:
引理 toENNReal_ne_top
  结论: (n : 实数>=0∞) != ∞ ↔ n != ⊤
  证明: by simp

@[simp, norm_cast, gcongr]
-/
@[norm_cast] lemma toENNReal_ne_top : (n : Real>=0∞) != ∞ ↔ n != ⊤ := by simp

@[simp, norm_cast, gcongr]
/--
theorem `toENNReal_le` / 定理 `toENNReal_le`

English:
theorem toENNReal_le
  statement: (m : Real>=0∞) <= n ↔ m <= n
  proof: toENNRealOrderEmbedding.le_iff_le

@[simp, norm_cast, gcongr]

中文:
定理 toENNReal_le
  结论: (m : 实数>=0∞) <= n ↔ m <= n
  证明: toENNRealOrderEmbedding.le_iff_le

@[simp, norm_cast, gcongr]

Depends on / 依赖: le_iff_le, toENNRealOrderEmbedding, toENNRealOrderEmbedding.le_iff_le
-/
theorem toENNReal_le : (m : Real>=0∞) <= n ↔ m <= n :=
  toENNRealOrderEmbedding.le_iff_le

@[simp, norm_cast, gcongr]
/--
theorem `toENNReal_lt` / 定理 `toENNReal_lt`

English:
theorem toENNReal_lt
  statement: (m : Real>=0∞) < n ↔ m < n
  proof: toENNRealOrderEmbedding.lt_iff_lt

@[simp, norm_cast]

中文:
定理 toENNReal_lt
  结论: (m : 实数>=0∞) < n ↔ m < n
  证明: toENNRealOrderEmbedding.lt_iff_lt

@[simp, norm_cast]

Depends on / 依赖: lt_iff_lt, toENNRealOrderEmbedding, toENNRealOrderEmbedding.lt_iff_lt
-/
theorem toENNReal_lt : (m : Real>=0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt

@[simp, norm_cast]
/--
lemma `toENNReal_lt_top` / 引理 `toENNReal_lt_top`

English:
lemma toENNReal_lt_top
  statement: (n : Real>=0∞) < ∞ ↔ n < ⊤
  proof: by simp [← toENNReal_lt]

@[gcongr, mono]

中文:
引理 toENNReal_lt_top
  结论: (n : 实数>=0∞) < ∞ ↔ n < ⊤
  证明: by simp [← toENNReal_lt]

@[gcongr, mono]

Depends on / 依赖: toENNReal_lt
-/
lemma toENNReal_lt_top : (n : Real>=0∞) < ∞ ↔ n < ⊤ := by simp [← toENNReal_lt]

@[gcongr, mono]
/--
theorem `toENNReal_mono` / 定理 `toENNReal_mono`

English:
theorem toENNReal_mono
  statement: Monotone ((↑) : Nat∞ -> Real>=0∞)
  proof: toENNRealOrderEmbedding.monotone

@[gcongr, mono]

中文:
定理 toENNReal_mono
  结论: Monotone ((↑) : 自然数∞ -> 实数>=0∞)
  证明: toENNRealOrderEmbedding.monotone

@[gcongr, mono]

Depends on / 依赖: monotone, toENNRealOrderEmbedding, toENNRealOrderEmbedding.monotone
-/
theorem toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞) :=
  toENNRealOrderEmbedding.monotone

@[gcongr, mono]
/--
theorem `toENNReal_strictMono` / 定理 `toENNReal_strictMono`

English:
theorem toENNReal_strictMono
  statement: StrictMono ((↑) : Nat∞ -> Real>=0∞)
  proof: toENNRealOrderEmbedding.strictMono

@[simp, norm_cast]

中文:
定理 toENNReal_strictMono
  结论: StrictMono ((↑) : 自然数∞ -> 实数>=0∞)
  证明: toENNRealOrderEmbedding.strictMono

@[simp, norm_cast]

Depends on / 依赖: strictMono, toENNRealOrderEmbedding, toENNRealOrderEmbedding.strictMono
-/
theorem toENNReal_strictMono : StrictMono ((↑) : Nat∞ -> Real>=0∞) :=
  toENNRealOrderEmbedding.strictMono

@[simp, norm_cast]
/--
theorem `toENNReal_zero` / 定理 `toENNReal_zero`

English:
theorem toENNReal_zero
  statement: ((0 : Nat∞) : Real>=0∞) = 0
  proof: map_zero toENNRealRingHom

中文:
定理 toENNReal_zero
  结论: ((0 : 自然数∞) : 实数>=0∞) = 0
  证明: map_zero toENNRealRingHom

Depends on / 依赖: map_zero, toENNRealRingHom
-/
theorem toENNReal_zero : ((0 : Nat∞) : Real>=0∞) = 0 :=
  map_zero toENNRealRingHom

/--
lemma `toENNReal_eq_zero` / 引理 `toENNReal_eq_zero`

English:
lemma toENNReal_eq_zero
  statement: toENNReal n = 0 ↔ n = 0
  proof: by rw [← toENNReal_zero, toENNReal_inj]

@[simp, norm_cast]

中文:
引理 toENNReal_eq_zero
  结论: toENN实数 n = 0 ↔ n = 0
  证明: by rw [← toENNReal_zero, toENNReal_inj]

@[simp, norm_cast]
-/
@[simp] lemma toENNReal_eq_zero : toENNReal n = 0 ↔ n = 0 := by rw [← toENNReal_zero, toENNReal_inj]

@[simp, norm_cast]
/--
theorem `toENNReal_add` / 定理 `toENNReal_add`

English:
theorem toENNReal_add
  given: (m n : Nat∞)
  statement: ↑(m + n) = (m + n : Real>=0∞)
  proof: map_add toENNRealRingHom m n

@[simp, norm_cast]

中文:
定理 toENNReal_add
  条件: (m n : 自然数∞)
  结论: ↑(m + n) = (m + n : 实数>=0∞)
  证明: map_add toENNRealRingHom m n

@[simp, norm_cast]

Depends on / 依赖: map_add, toENNRealRingHom
-/
theorem toENNReal_add (m n : Nat∞) : ↑(m + n) = (m + n : Real>=0∞) :=
  map_add toENNRealRingHom m n

@[simp, norm_cast]
/--
theorem `toENNReal_one` / 定理 `toENNReal_one`

English:
theorem toENNReal_one
  statement: ((1 : Nat∞) : Real>=0∞) = 1
  proof: map_one toENNRealRingHom

@[simp, norm_cast]

中文:
定理 toENNReal_one
  结论: ((1 : 自然数∞) : 实数>=0∞) = 1
  证明: map_one toENNRealRingHom

@[simp, norm_cast]

Depends on / 依赖: map_one, toENNRealRingHom
-/
theorem toENNReal_one : ((1 : Nat∞) : Real>=0∞) = 1 :=
  map_one toENNRealRingHom

@[simp, norm_cast]
/--
theorem `toENNReal_mul` / 定理 `toENNReal_mul`

English:
theorem toENNReal_mul
  given: (m n : Nat∞)
  statement: ↑(m * n) = (m * n : Real>=0∞)
  proof: map_mul toENNRealRingHom m n

@[simp, norm_cast]

中文:
定理 toENNReal_mul
  条件: (m n : 自然数∞)
  结论: ↑(m * n) = (m * n : 实数>=0∞)
  证明: map_mul toENNRealRingHom m n

@[simp, norm_cast]

Depends on / 依赖: map_mul, toENNRealRingHom
-/
theorem toENNReal_mul (m n : Nat∞) : ↑(m * n) = (m * n : Real>=0∞) :=
  map_mul toENNRealRingHom m n

@[simp, norm_cast]
/--
theorem `toENNReal_pow` / 定理 `toENNReal_pow`

English:
theorem toENNReal_pow
  given: (x : Nat∞) (n : Nat)
  statement: (x ^ n : Nat∞) = (x : Real>=0∞) ^ n
  proof: map_pow toENNRealRingHom x n

@[simp, norm_cast]

中文:
定理 toENNReal_pow
  条件: (x : 自然数∞) (n : 自然数)
  结论: (x ^ n : 自然数∞) = (x : 实数>=0∞) ^ n
  证明: map_pow toENNRealRingHom x n

@[simp, norm_cast]

Depends on / 依赖: map_pow, toENNRealRingHom
-/
theorem toENNReal_pow (x : Nat∞) (n : Nat) : (x ^ n : Nat∞) = (x : Real>=0∞) ^ n :=
  map_pow toENNRealRingHom x n

@[simp, norm_cast]
/--
theorem `toENNReal_min` / 定理 `toENNReal_min`

English:
theorem toENNReal_min
  given: (m n : Nat∞)
  statement: ↑(min m n) = (min m n : Real>=0∞)
  proof: toENNReal_mono.map_min

@[simp, norm_cast]

中文:
定理 toENNReal_min
  条件: (m n : 自然数∞)
  结论: ↑(min m n) = (min m n : 实数>=0∞)
  证明: toENNReal_mono.map_min

@[simp, norm_cast]

Depends on / 依赖: map_min, toENNReal_mono, toENNReal_mono.map_min
-/
theorem toENNReal_min (m n : Nat∞) : ↑(min m n) = (min m n : Real>=0∞) :=
  toENNReal_mono.map_min

@[simp, norm_cast]
/--
theorem `toENNReal_max` / 定理 `toENNReal_max`

English:
theorem toENNReal_max
  given: (m n : Nat∞)
  statement: ↑(max m n) = (max m n : Real>=0∞)
  proof: toENNReal_mono.map_max

@[simp, norm_cast]

中文:
定理 toENNReal_max
  条件: (m n : 自然数∞)
  结论: ↑(max m n) = (max m n : 实数>=0∞)
  证明: toENNReal_mono.map_max

@[simp, norm_cast]

Depends on / 依赖: map_max, toENNReal_mono, toENNReal_mono.map_max
-/
theorem toENNReal_max (m n : Nat∞) : ↑(max m n) = (max m n : Real>=0∞) :=
  toENNReal_mono.map_max

@[simp, norm_cast]
/--
theorem `toENNReal_sub` / 定理 `toENNReal_sub`

English:
theorem toENNReal_sub
  given: (m n : Nat∞)
  statement: ↑(m - n) = (m - n : Real>=0∞)
  proof: WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

中文:
定理 toENNReal_sub
  条件: (m n : 自然数∞)
  结论: ↑(m - n) = (m - n : 实数>=0∞)
  证明: WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

Depends on / 依赖: Nat.cast_tsub, Nat.cast_zero, WithTop, WithTop.map_sub, cast_tsub, cast_zero, map_sub
-/
theorem toENNReal_sub (m n : Nat∞) : ↑(m - n) = (m - n : Real>=0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n

end ENat
