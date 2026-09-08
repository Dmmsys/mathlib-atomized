/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Models of elliptic curves with prescribed j-invariant

This file defines the Weierstrass equation over a field with prescribed j-invariant,
proved that it is an elliptic curve, and that its j-invariant is equal to the given value.
It is a modification of [silverman2009], Chapter III, Proposition 1.4 (c).

## Main definitions

* `WeierstrassCurve.ofJ0`: an elliptic curve whose j-invariant is 0.
* `WeierstrassCurve.ofJ1728`: an elliptic curve whose j-invariant is 1728.
* `WeierstrassCurve.ofJNe0Or1728`: an elliptic curve whose j-invariant is neither 0 nor 1728.
* `WeierstrassCurve.ofJ`: an elliptic curve whose j-invariant equal to j.

## Main statements

* `WeierstrassCurve.ofJ_j`: the j-invariant of `WeierstrassCurve.ofJ` is equal to j.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

@[expose] public section

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] (W : WeierstrassCurve R)

/-- The Weierstrass curve `Y² + Y = X³`. It is of j-invariant 0 if it is an elliptic curve. -/
/-
**WeierstrassCurve.ofJ0** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJ0 : WeierstrassCurve R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve `Y² + Y = X³`. It is of j-invariant 0 if it is an elliptic
 curve.
-/
def ofJ0 : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, 0⟩
/-
**WeierstrassCurve.ofJ0_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofJ0_c₄ : (ofJ0 R).c₄ = 0 := by
  rw [ofJ0, c₄, b₂, b₄]
  norm_num1
/-
**WeierstrassCurve.ofJ0_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofJ0_Δ : (ofJ0 R).Δ = -27 := by
  rw [ofJ0, Δ, b₂, b₄, b₆, b₈]
  norm_num1

/-- The Weierstrass curve `Y² = X³ + X`. It is of j-invariant 1728 if it is an elliptic curve. -/
/-
**WeierstrassCurve.ofJ1728** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJ1728 : WeierstrassCurve R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve `Y² = X³ + X`. It is of j-invariant 1728 if it is an ellip
tic curve.
-/
def ofJ1728 : WeierstrassCurve R :=
  ⟨0, 0, 0, 1, 0⟩
/-
**WeierstrassCurve.ofJ1728_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofJ1728_c₄ : (ofJ1728 R).c₄ = -48 := by
  rw [ofJ1728, c₄, b₂, b₄]
  norm_num1
/-
**WeierstrassCurve.ofJ1728_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofJ1728_Δ : (ofJ1728 R).Δ = -64 := by
  rw [ofJ1728, Δ, b₂, b₄, b₆, b₈]
  norm_num1

variable {R} (j : R)

/-- The Weierstrass curve `Y² + (j - 1728)XY = X³ - 36(j - 1728)³X - (j - 1728)⁵`.
It is a modification of the curve in [silverman2009], Chapter III, Proposition 1.4 (c) to avoid
denominators. It is of j-invariant j if it is an elliptic curve. -/
/-
**WeierstrassCurve.ofJNe0Or1728** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJNe0Or1728 : WeierstrassCurve R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Weierstrass curve `Y² + (j - 1728)XY = X³ - 36(j - 1728)³X - (j - 1728)⁵`.
It is a modification of the curve in [silverman2009], Chapter III, Proposition 1
.4 (c) to avoid
denominators. It is of j-invariant j if it is an elliptic curve.
-/
def ofJNe0Or1728 : WeierstrassCurve R :=
  ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩
/-
**WeierstrassCurve.ofJNe0Or1728_c** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofJNe0Or1728_c₄ : (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3 := by
  simp only [ofJNe0Or1728, c₄, b₂, b₄]
  ring1
/-
**WeierstrassCurve.ofJNe0Or1728_** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofJNe0Or1728_Δ : (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp only [ofJNe0Or1728, Δ, b₂, b₄, b₆, b₈]
  ring1

variable (R) [W.IsElliptic]

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-- When 3 is a unit, `Y² + Y = X³` is an elliptic curve.
It is of j-invariant 0 (see `WeierstrassCurve.ofJ0_j`). -/
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When 3 is a unit, `Y² + Y = X³` is an elliptic curve.
It is of j-invariant 0 (see `WeierstrassCurve.ofJ0_j`).
-/
instance [hu : Fact (IsUnit (3 : R))] : (ofJ0 R).IsElliptic := by
  rw [isElliptic_iff, ofJ0_Δ]
  convert! (hu.out.pow 3).neg
  norm_num1

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-
**WeierstrassCurve.ofJ0_j** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJ0_j [Fact (IsUnit (3 : R))] : (ofJ0 R).j = 0
参数：IsUnit (3 : R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WeierstrassCurve.instIsEllipticOfJ0OfFactIsUnitOfNat`：∀ (R : Type u_1) [
inst : CommRing R] [hu : Fact (IsUnit 3)], (WeierstrassCurve.ofJ0 R).IsElliptic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用引理 `WeierstrassCurve.ofJ0_c₄`：ofJ0_c₄ : (ofJ0 R).c₄ = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_pow`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {b : ℕ}, 0 < b → 0 ^ b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.const_pos`：∀ (n : ℕ), Nat.ble 1 n = true → 0 
< n.rawCast
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
-/
lemma ofJ0_j [Fact (IsUnit (3 : R))] : (ofJ0 R).j = 0 := by
  rw [j, ofJ0_c₄]
  ring1

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-- When 2 is a unit, `Y² = X³ + X` is an elliptic curve.
It is of j-invariant 1728 (see `WeierstrassCurve.ofJ1728_j`). -/
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When 2 is a unit, `Y² = X³ + X` is an elliptic curve.
It is of j-invariant 1728 (see `WeierstrassCurve.ofJ1728_j`).
-/
instance [hu : Fact (IsUnit (2 : R))] : (ofJ1728 R).IsElliptic := by
  rw [isElliptic_iff, ofJ1728_Δ]
  convert! (hu.out.pow 6).neg
  norm_num1

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-
**WeierstrassCurve.ofJ1728_j** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJ1728_j [Fact (IsUnit (2 : R))] : (ofJ1728 R).j = 1728
参数：IsUnit (2 : R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WeierstrassCurve.instIsEllipticOfJ1728OfFactIsUnitOfNat`：∀ (R : Type u_1
) [inst : CommRing R] [hu : Fact (IsUnit 2)], (WeierstrassCurve.ofJ1728 R).IsEll
iptic
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
· 使用引理 `WeierstrassCurve.ofJ1728_c₄`：ofJ1728_c₄ : (ofJ1728 R).c₄ = -48
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用引理 `WeierstrassCurve.ofJ1728_Δ`：ofJ1728_Δ : (ofJ1728 R).Δ = -64
· 使用定理 `Mathlib.Meta.NormNum.isInt_eq_true`：∀ {α : Type u} [inst : Ring α] {a b 
: α} {z : ℤ},   Mathlib.Meta.NormNum.IsInt a z → Mathlib.Meta.NormNum.IsInt b z 
→ a = b
· 使用定理 `Mathlib.Meta.NormNum.isInt_pow`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ ℕ → α} {a : α} {b : ℕ} {a' : ℤ} {b' : ℕ} {c : ℤ},   f = HPow.hPow →     Mathli
b.Meta.NormNum.IsInt…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.intPow_negOfNat_bit1`：intPow_negOfNat_bit1 {b' c' :
 Nat} (h1 : Nat.pow a b' = c') (hb : nat_lit 2 * b' + nat_lit 1 = b) (hc : c' * 
(c' * a) = c) : Int.pow (Int.ne…
· 使用定理 `Mathlib.Meta.NormNum.natPow_one`：natPow_one : Nat.pow a (nat_lit 1) = a
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
-/
lemma ofJ1728_j [Fact (IsUnit (2 : R))] : (ofJ1728 R).j = 1728 := by
  rw [j, Units.inv_mul_eq_iff_eq_mul, ofJ1728_c₄, coe_Δ', ofJ1728_Δ]
  norm_num1

variable {R}

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-- When j and j - 1728 are both units,
`Y² + (j - 1728)XY = X³ - 36(j - 1728)³X - (j - 1728)⁵` is an elliptic curve.
It is of j-invariant j (see `WeierstrassCurve.ofJNe0Or1728_j`). -/
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When j and j - 1728 are both units,
`Y² + (j - 1728)XY = X³ - 36(j - 1728)³X - (j - 1728)⁵` is an elliptic curve.
It is of j-invariant j (see `WeierstrassCurve.ofJNe0Or1728_j`).
-/
instance (j : R) [h1 : Fact (IsUnit j)] [h2 : Fact (IsUnit (j - 1728))] :
    (ofJNe0Or1728 j).IsElliptic := by
  rw [isElliptic_iff, ofJNe0Or1728_Δ]
  exact (h1.out.pow 2).mul (h2.out.pow 9)

-- TODO: change to `[IsUnit ...]` once https://github.com/leanprover-community/mathlib4/issues/17458 is merged
/-
**WeierstrassCurve.ofJNe0Or1728_j** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJNe0Or1728_j (j : R) [Fact (IsUnit j)] [Fact (IsUnit (j - 1728))] : (ofJ
Ne0Or1728 j).j = j
参数：j : R；IsUnit j；IsUnit (j - 1728)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `WeierstrassCurve.instIsEllipticOfJNe0Or1728OfFactIsUnitHSubOfNat`：∀ {R :
 Type u_1} [inst : CommRing R] (j : R) [h1 : Fact (IsUnit j)] [h2 : Fact (IsUnit
 (j - 1728))],   (WeierstrassCurve.ofJNe0Or1728 j).IsE…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
· 使用引理 `WeierstrassCurve.ofJNe0Or1728_c₄`：ofJNe0Or1728_c₄ : (ofJNe0Or1728 j).c₄ 
= j * (j - 1728) ^ 3
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用引理 `WeierstrassCurve.ofJNe0Or1728_Δ`：ofJNe0Or1728_Δ : (ofJNe0Or1728 j).Δ = j
 ^ 2 * (j - 1728) ^ 9
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
（共 56 条，此处仅展示前 30 条）
-/
lemma ofJNe0Or1728_j (j : R) [Fact (IsUnit j)] [Fact (IsUnit (j - 1728))] :
    (ofJNe0Or1728 j).j = j := by
  rw [WeierstrassCurve.j, Units.inv_mul_eq_iff_eq_mul, ofJNe0Or1728_c₄, coe_Δ', ofJNe0Or1728_Δ]
  ring1

variable {F : Type*} [Field F] (j : F) [DecidableEq F]

/-- For any element j of a field `F`, there exists an elliptic curve over `F`
with j-invariant equal to j (see `WeierstrassCurve.ofJ_j`).
Its coefficients are given explicitly (see `WeierstrassCurve.ofJ0`, `WeierstrassCurve.ofJ1728`
and `WeierstrassCurve.ofJNe0Or1728`). -/
/-
**WeierstrassCurve.ofJ** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJ : WeierstrassCurve F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any element j of a field `F`, there exists an elliptic curve over `F`
with j-invariant equal to j (see `WeierstrassCurve.ofJ_j`).
Its coefficients are given explicitly (see `WeierstrassCurve.ofJ0`, `Weierstrass
Curve.ofJ1728`
and `WeierstrassCurve.ofJNe0Or1728`).
-/
def ofJ : WeierstrassCurve F :=
  if j = 0 then if (3 : F) = 0 then ofJ1728 F else ofJ0 F
  else if j = 1728 then ofJ1728 F else ofJNe0Or1728 j
/-
**WeierstrassCurve.ofJ_0_of_three_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve`。
形式化陈述：ofJ_0_of_three_ne_zero (h3 : (3 : F) != 0) : ofJ 0 = ofJ0 F
参数：h3 : (3 : F) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma ofJ_0_of_three_ne_zero (h3 : (3 : F) ≠ 0) : ofJ 0 = ofJ0 F := by
  rw [ofJ, if_pos rfl, if_neg h3]
/-
**WeierstrassCurve.ofJ_0_of_three_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve`。
形式化陈述：ofJ_0_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 0 = ofJ1728 F
参数：h3 : (3 : F) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma ofJ_0_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 0 = ofJ1728 F := by
  rw [ofJ, if_pos rfl, if_pos h3]
/-
**WeierstrassCurve.ofJ_0_of_two_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCu
rve`。
形式化陈述：ofJ_0_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 0 = ofJ0 F
参数：h2 : (2 : F) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 37 条，此处仅展示前 30 条）
-/
lemma ofJ_0_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 0 = ofJ0 F := by
  rw [ofJ, if_pos rfl, if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]
/-
**WeierstrassCurve.ofJ_1728_of_three_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstr
assCurve`。
形式化陈述：ofJ_1728_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 1728 = ofJ1728 F
参数：h3 : (3 : F) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 37 条，此处仅展示前 30 条）
-/
lemma ofJ_1728_of_three_eq_zero (h3 : (3 : F) = 0) : ofJ 1728 = ofJ1728 F := by
  rw [ofJ, if_pos (by linear_combination 576 * h3), if_pos h3]
/-
**WeierstrassCurve.ofJ_1728_of_two_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve`。
形式化陈述：ofJ_1728_of_two_ne_zero (h2 : (2 : F) != 0) : ofJ 1728 = ofJ1728 F
参数：h2 : (2 : F) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `WeierstrassCurve.ofJ_1728_of_three_eq_zero`：ofJ_1728_of_three_eq_zero (h
3 : (3 : F) = 0) : ofJ 1728 = ofJ1728 F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.trans`：∀ {a b c : ℕ} {p : Prop} {b' c' : 
ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a b c →     Mathlib.Meta.NormNum.IsNatPow
T (a.pow b = c) a b' c' → …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit1`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b + 1) (c.mul (c.mul a))
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma ofJ_1728_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ofJ 1728 = ofJ1728 F := by
  by_cases h3 : (3 : F) = 0
  · exact ofJ_1728_of_three_eq_zero h3
  · rw [ofJ, show (1728 : F) = 2 ^ 6 * 3 ^ 3 by norm_num1,
      if_neg (mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3)), if_pos rfl]
/-
**WeierstrassCurve.ofJ_1728_of_two_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Weierstras
sCurve`。
形式化陈述：ofJ_1728_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 1728 = ofJ0 F
参数：h2 : (2 : F) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 44 条，此处仅展示前 30 条）
-/
lemma ofJ_1728_of_two_eq_zero (h2 : (2 : F) = 0) : ofJ 1728 = ofJ0 F := by
  rw [ofJ, if_pos (by linear_combination 864 * h2),
    if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]
/-
**WeierstrassCurve.ofJ_ne_0_ne_1728** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`
。
形式化陈述：ofJ_ne_0_ne_1728 (h0 : j != 0) (h1728 : j != 1728) : ofJ j = ofJNe0Or1728 
j
参数：h0 : j != 0；h1728 : j != 1728。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.ofJ.eq_1`：∀ {F : Type u_2} [inst : Field F] (j : F) [in
st_1 : DecidableEq F],   WeierstrassCurve.ofJ j =     if j = 0 then if 3 = 0 the
n WeierstrassCu…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma ofJ_ne_0_ne_1728 (h0 : j ≠ 0) (h1728 : j ≠ 1728) : ofJ j = ofJNe0Or1728 j := by
  rw [ofJ, if_neg h0, if_neg h1728]
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ofJ j).IsElliptic := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
    · have : Fact <| IsUnit (2 : F) := ⟨.of_mul_eq_one 2 <| by linear_combination h3⟩
      rw [h0, ofJ_0_of_three_eq_zero h3]
      infer_instance
    · have := Fact.mk (Ne.isUnit h3)
      rw [h0, ofJ_0_of_three_ne_zero h3]
      infer_instance
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) ≠ 0 := fun h ↦ h0 (by linear_combination h1728 + 864 * h)
      have := Fact.mk h2.isUnit
      rw [h1728, ofJ_1728_of_two_ne_zero h2]
      infer_instance
    · have := Fact.mk (Ne.isUnit h0)
      have := Fact.mk (sub_ne_zero.2 h1728).isUnit
      rw [ofJ_ne_0_ne_1728 j h0 h1728]
      infer_instance
/-
**WeierstrassCurve.ofJ_j** 是 Mathlib 中的一个引理，位于命名空间 `WeierstrassCurve`。
形式化陈述：ofJ_j : (ofJ j).j = j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.instIsEllipticOfJ`：∀ {F : Type u_2} [inst : Field F] (j
 : F) [inst_1 : DecidableEq F], (WeierstrassCurve.ofJ j).IsElliptic
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 64 条，此处仅展示前 30 条）
-/
lemma ofJ_j : (ofJ j).j = j := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
    · have : Fact <| IsUnit (2 : F) := ⟨.of_mul_eq_one 2 <| by linear_combination h3⟩
      simp_rw [h0, ofJ_0_of_three_eq_zero h3, ofJ1728_j]
      linear_combination 576 * h3
    · have := Fact.mk (Ne.isUnit h3)
      simp_rw [h0, ofJ_0_of_three_ne_zero h3, ofJ0_j]
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) ≠ 0 := fun h ↦ h0 (by linear_combination h1728 + 864 * h)
      have := Fact.mk h2.isUnit
      simp_rw [h1728, ofJ_1728_of_two_ne_zero h2, ofJ1728_j]
    · have := Fact.mk (Ne.isUnit h0)
      have := Fact.mk (sub_ne_zero.2 h1728).isUnit
      simp_rw [ofJ_ne_0_ne_1728 j h0 h1728, ofJNe0Or1728_j]
/-
**WeierstrassCurve.** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited { W : WeierstrassCurve F // W.IsElliptic } :=
  ⟨⟨ofJ 37, inferInstance⟩⟩

end WeierstrassCurve

