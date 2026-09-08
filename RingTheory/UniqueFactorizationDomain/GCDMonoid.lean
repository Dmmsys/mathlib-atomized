/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Building GCD out of unique factorization

## Main results
* `UniqueFactorizationMonoid.toGCDMonoid`: choose a GCD monoid structure given unique factorization.
-/

@[expose] public section

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section

open Associates UniqueFactorizationMonoid

/-- `toGCDMonoid` constructs a GCD monoid out of a unique factorization domain. -/
@[instance_reducible]
/-
**UniqueFactorizationMonoid.toGCDMonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniqueFactorizationMonoid.toGCDMonoid (α : Type*) [CommMonoidWithZero α] [
UniqueFactorizationMonoid α] : GCDMonoid α where gcd a b
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α

--- 原说明 ---
`toGCDMonoid` constructs a GCD monoid out of a unique factorization domain.
-/
noncomputable def UniqueFactorizationMonoid.toGCDMonoid (α : Type*) [CommMonoidWithZero α]
    [UniqueFactorizationMonoid α] : GCDMonoid α where
  gcd a b := Quot.out (Associates.mk a ⊓ Associates.mk b : Associates α)
  lcm a b := Quot.out (Associates.mk a ⊔ Associates.mk b : Associates α)
  gcd_dvd_left a b := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_left
  gcd_dvd_right a b := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le]
    exact inf_le_right
  dvd_gcd {a b c} hac hab := by
    rw [← mk_dvd_mk, Associates.quot_out, congr_fun₂ dvd_eq_le, le_inf_iff,
      mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
    exact ⟨hac, hab⟩
  lcm_zero_left a := by simp
  lcm_zero_right a := by simp
  gcd_mul_lcm a b := by
    rw [← mk_eq_mk_iff_associated, ← Associates.mk_mul_mk, ← associated_iff_eq, Associates.quot_out,
      Associates.quot_out, mul_comm, sup_mul_inf, Associates.mk_mul_mk]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (α) [CommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    IsGCDMonoid α := ⟨toGCDMonoid α⟩

/-- `toNormalizedGCDMonoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
@[instance_reducible]
/-
**UniqueFactorizationMonoid.toNormalizedGCDMonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*) [CommMonoidWit
hZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] : NormalizedGCDMo
noid α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : Co
mmMonoidWithZero α} [self : UniqueFactorizationMonoid α], IsCancelMulZero α

--- 原说明 ---
`toNormalizedGCDMonoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain.
-/
noncomputable def UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*)
    [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] :
    NormalizedGCDMonoid α :=
  { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_left
    gcd_dvd_right := fun a b =>
      (out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
    gcd_mul_lcm := fun a b => (out_mul' ..).symm.trans <| by
      rw [mul_comm, sup_mul_inf, mk_mul_mk, out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }

/-- `toStrongNormalizedGCDMonoid` constructs a GCD monoid out of a strong normalization on a
  unique factorization domain. -/
/-
**UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid** 是 Mathlib 中的一个缩写定义，位于命
名空间 ``。
形式化陈述：UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid (α : Type*) [CommMon
oidWithZero α] [UniqueFactorizationMonoid α] [StrongNormalizationMonoid α] : Str
ongNormalizedGCDMonoid α where __
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StrongNormalizationMonoid.normUnit_mul`：∀ {α : Type u_2} {inst : CommMon
oidWithZero α} [self : StrongNormalizationMonoid α] {a b : α},   a ≠ 0 → b ≠ 0 →
 normUnit (a * b) = normUnit…
· 使用定理 `StrongNormalizationMonoid.normUnit_coe_units`：∀ {α : Type u_2} {inst : C
ommMonoidWithZero α} [self : StrongNormalizationMonoid α] (u : αˣ), normUnit ↑u 
= u⁻¹
· 使用定理 `NormalizedGCDMonoid.normalize_gcd`：∀ {α : Type u_2} {inst : CommMonoidWi
thZero α} [self : NormalizedGCDMonoid α] (a b : α), normalize (gcd a b) = gcd a 
b
· 使用定理 `NormalizedGCDMonoid.normalize_lcm`：∀ {α : Type u_2} {inst : CommMonoidWi
thZero α} [self : NormalizedGCDMonoid α] (a b : α), normalize (lcm a b) = lcm a 
b

--- 原说明 ---
`toStrongNormalizedGCDMonoid` constructs a GCD monoid out of a strong normalizat
ion on a
  unique factorization domain.
-/
noncomputable abbrev UniqueFactorizationMonoid.toStrongNormalizedGCDMonoid (α : Type*)
    [CommMonoidWithZero α] [UniqueFactorizationMonoid α] [StrongNormalizationMonoid α] :
    StrongNormalizedGCDMonoid α where
  __ := toNormalizedGCDMonoid α
  __ := ‹StrongNormalizationMonoid α›

end

