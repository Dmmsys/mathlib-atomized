/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Algebra.GroupWithZero.Nat

/-!
# ℕ and ℤ are normalized GCD monoids.

## Main statements

* ℕ is a `GCDMonoid`
* ℕ is a `StrongNormalizedGCDMonoid`
* ℤ is a `StrongNormalizationMonoid`
* ℤ is a `GCDMonoid`
* ℤ is a `StrongNormalizedGCDMonoid`

## Tags
natural numbers, integers, normalization monoid, gcd monoid, greatest common divisor
-/

@[expose] public section

assert_not_exists IsOrderedMonoid

/-- `ℕ` is a `GCDMonoid`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℕ` is a `GCDMonoid`.
-/
instance : GCDMonoid ℕ where
  gcd := Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd := Nat.dvd_gcd
  gcd_mul_lcm a b := by rw [Nat.gcd_mul_lcm]; rfl
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right
/-
**gcd_eq_nat_gcd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gcd_eq_nat_gcd (m n : Nat) : gcd m n = Nat.gcd m n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_eq_nat_gcd (m n : ℕ) : gcd m n = Nat.gcd m n :=
  rfl
/-
**lcm_eq_nat_lcm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lcm_eq_nat_lcm (m n : Nat) : lcm m n = Nat.lcm m n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_eq_nat_lcm (m n : ℕ) : lcm m n = Nat.lcm m n :=
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StrongNormalizedGCDMonoid ℕ :=
  { (inferInstance : GCDMonoid ℕ),
    (inferInstance : StrongNormalizationMonoid ℕ) with
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

namespace Int

section NormalizationMonoid

/-
**Int.strongNormalizationMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：strongNormalizationMonoid : StrongNormalizationMonoid Int where normUnit a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance strongNormalizationMonoid : StrongNormalizationMonoid ℤ where
  normUnit a := if 0 ≤ a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul {a b} hna hnb := by
    rcases hna.lt_or_gt with ha | ha <;> rcases hnb.lt_or_gt with hb | hb <;>
      simp [Int.mul_nonneg_iff, ha.le, ha.not_ge, hb.le, hb.not_ge]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => eq.symm ▸ if_pos Int.one_nonneg) fun eq =>
      eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : ℤ) < 0 by decide)

@[deprecated (since := "2026-07-08")]
alias normalizationMonoid := strongNormalizationMonoid
/-
**Int.normUnit_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：normUnit_eq (z : Int) : normUnit z = if 0 <= z then 1 else -1
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem normUnit_eq (z : ℤ) : normUnit z = if 0 ≤ z then 1 else -1 := rfl
/-
**Int.normalize_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：normalize_of_nonneg {z : Int} (h : 0 <= z) : normalize z = z
参数：h : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `Int.normUnit_eq`：normUnit_eq (z : Int) : normUnit z = if 0 <= z then 1 e
lse -1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z := by
  rw [normalize_apply, normUnit_eq, if_pos h, Units.val_one, mul_one]
/-
**Int.normalize_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：normalize_of_nonpos {z : Int} (h : z <= 0) : normalize z = -z
参数：h : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `Int.normUnit_eq`：normUnit_eq (z : Int) : normUnit z = if 0 <= z then 1 e
lse -1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Units.val_neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg 
α] (u : αˣ), ↑(-u) = -↑u
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
-/
theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]
/-
**Int.normalize_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：normalize_coe_nat (n : Nat) : normalize (n : Int) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.normalize_of_nonneg`：normalize_of_nonneg {z : Int} (h : 0 <= z) : no
rmalize z = z
· 使用定理 `Int.ofNat_le_ofNat_of_le`：∀ {m n : ℕ}, m ≤ n → ↑m ≤ ↑n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
  normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)
/-
**Int.abs_eq_normalize** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_eq_normalize (z : Int) : |z| = normalize z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Int.normalize_of_nonneg`：normalize_of_nonneg {z : Int} (h : 0 <= z) : no
rmalize z = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `Int.normalize_of_nonpos`：normalize_of_nonpos {z : Int} (h : z <= 0) : no
rmalize z = -z
-/
theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  cases le_total 0 z <;>
  simp [abs_of_nonneg, abs_of_nonpos, normalize_of_nonneg, normalize_of_nonpos, *]
/-
**Int.nonneg_of_normalize_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：nonneg_of_normalize_eq_self {z : Int} (hz : normalize z = z) : 0 <= z
参数：hz : normalize z = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.normalize_of_nonpos`：normalize_of_nonpos {z : Int} (h : z <= 0) : no
rmalize z = -z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z := by
  by_cases! h : 0 ≤ z
  · exact h
  · rw [normalize_of_nonpos h.le] at hz
    lia
/-
**Int.nonneg_iff_normalize_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：nonneg_iff_normalize_eq_self (z : Int) : normalize z = z ↔ 0 <= z
参数：z : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.nonneg_of_normalize_eq_self`：nonneg_of_normalize_eq_self {z : Int} (
hz : normalize z = z) : 0 <= z
· 使用定理 `Int.normalize_of_nonneg`：normalize_of_nonneg {z : Int} (h : 0 <= z) : no
rmalize z = z
-/
theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z :=
  ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩
/-
**Int.eq_of_associated_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：eq_of_associated_of_nonneg {a b : Int} (h : Associated a b) (ha : 0 <= a) 
(hb : 0 <= b) : a = b
参数：h : Associated a b；ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm_of_normalize_eq`：dvd_antisymm_of_normalize_eq {a b : α} (ha
 : normalize a = a) (hb : normalize b = b) (hab : a ∣ b) (hba : b ∣ a) : a = b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Int.normalize_of_nonneg`：normalize_of_nonneg {z : Int} (h : 0 <= z) : no
rmalize z = z
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
-/
theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b :=
  dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd

end NormalizationMonoid

section GCDMonoid

/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GCDMonoid ℤ where
  gcd a b := Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left := Int.gcd_dvd_left
  gcd_dvd_right := Int.gcd_dvd_right
  dvd_gcd := dvd_coe_gcd
  gcd_mul_lcm a b := by
    rw [← Int.natCast_mul, gcd_mul_lcm, ← natAbs_mul, natCast_natAbs, abs_eq_normalize]
    exact normalize_associated (a * b)
  lcm_zero_left _ := natCast_eq_zero.2 <| Nat.lcm_zero_left _
  lcm_zero_right _ := natCast_eq_zero.2 <| Nat.lcm_zero_right _
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StrongNormalizedGCDMonoid ℤ :=
  { Int.strongNormalizationMonoid,
    (inferInstance : GCDMonoid ℤ) with
    normalize_gcd := fun _ _ => normalize_coe_nat _
    normalize_lcm := fun _ _ => normalize_coe_nat _ }
/-
**Int.coe_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：coe_gcd (i j : Int) : ↑(Int.gcd i j) = GCDMonoid.gcd i j
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_gcd (i j : ℤ) : ↑(Int.gcd i j) = GCDMonoid.gcd i j :=
  rfl
/-
**Int.coe_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：coe_lcm (i j : Int) : ↑(Int.lcm i j) = GCDMonoid.lcm i j
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lcm (i j : ℤ) : ↑(Int.lcm i j) = GCDMonoid.lcm i j :=
  rfl
/-
**Int.natAbs_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_gcd (i j : Int) : natAbs (GCDMonoid.gcd i j) = Int.gcd i j
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natAbs_gcd (i j : ℤ) : natAbs (GCDMonoid.gcd i j) = Int.gcd i j :=
  rfl
/-
**Int.natAbs_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_lcm (i j : Int) : natAbs (GCDMonoid.lcm i j) = Int.lcm i j
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natAbs_lcm (i j : ℤ) : natAbs (GCDMonoid.lcm i j) = Int.lcm i j :=
  rfl
/-
**Int.gcd_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：gcd_nonneg (i j : Int) : 0 <= GCDMonoid.gcd i j
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma gcd_nonneg (i j : ℤ) : 0 ≤ GCDMonoid.gcd i j := by simp [← coe_gcd]
/-
**Int.lcm_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：lcm_nonneg (i j : Int) : 0 <= GCDMonoid.lcm i j
参数：i j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma lcm_nonneg (i j : ℤ) : 0 ≤ GCDMonoid.lcm i j := by simp [← coe_lcm]

end GCDMonoid

/-
**Int.exists_unit_of_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_unit_of_abs (a : Int) : exists (u : Int) (_ : IsUnit u), (Int.natAb
s a : Int) = u * a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ) (_ : IsUnit u), (Int.natAbs a : ℤ) = u * a := by
  rcases natAbs_eq a with h | h
  · use 1, isUnit_one
    rw [← h, one_mul]
  · use -1, isUnit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]
/-
**Int.gcd_eq_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_eq_natAbs {a b : Int} : Int.gcd a b = Nat.gcd a.natAbs b.natAbs
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_eq_natAbs {a b : ℤ} : Int.gcd a b = Nat.gcd a.natAbs b.natAbs :=
  rfl
end Int

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
/-
**associatesIntEquivNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：associatesIntEquivNat : Associates Int ≃ Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps an associate class of integers consisting of `-n, n` to `n : ℕ`
-/
def associatesIntEquivNat : Associates ℤ ≃ ℕ := by
  refine ⟨(·.out.natAbs), (Associates.mk ·), ?_, fun n ↦ ?_⟩
  · refine Associates.forall_associated.2 fun a ↦ ?_
    refine Associates.mk_eq_mk_iff_associated.2 <| Associated.symm <| ⟨normUnit a, ?_⟩
    simp [Int.natCast_natAbs, Int.abs_eq_normalize, normalize_apply]
  · dsimp only [Associates.out_mk]
    rw [← Int.abs_eq_normalize, Int.natAbs_abs, Int.natAbs_natCast]
/-
**Int.associated_natAbs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.associated_natAbs (k : Int) : Associated k k.natAbs
参数：k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.dvd_natCast`：dvd_natCast {n : Nat} : m ∣ (n : Int) ↔ m.natAbs ∣ n
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Int.natAbs_dvd`：∀ {a b : ℤ}, ↑a.natAbs ∣ b ↔ a ∣ b
-/
theorem Int.associated_natAbs (k : ℤ) : Associated k k.natAbs :=
  associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)
/-
**Int.associated_iff_natAbs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.associated_iff_natAbs {a b : Int} : Associated a b ↔ a.natAbs = b.natA
bs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_dvd_iff_associated`：dvd_dvd_iff_associated [MonoidWithZero M] [IsLef
tCancelMulZero M] {a b : M} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Int.natAbs_dvd_natAbs`：∀ {a b : ℤ}, a.natAbs ∣ b.natAbs ↔ a ∣ b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem Int.associated_iff_natAbs {a b : ℤ} : Associated a b ↔ a.natAbs = b.natAbs := by
  rw [← dvd_dvd_iff_associated, ← Int.natAbs_dvd_natAbs, ← Int.natAbs_dvd_natAbs,
    dvd_dvd_iff_associated]
  exact associated_iff_eq
/-
**Int.associated_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.associated_iff {a b : Int} : Associated a b ↔ a = b ∨ a = -b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.associated_iff_natAbs`：Int.associated_iff_natAbs {a b : Int} : Assoc
iated a b ↔ a.natAbs = b.natAbs
· 使用定理 `Int.natAbs_eq_natAbs_iff`：∀ {a b : ℤ}, a.natAbs = b.natAbs ↔ a = b ∨ a =
 -b
-/
theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b := by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff
