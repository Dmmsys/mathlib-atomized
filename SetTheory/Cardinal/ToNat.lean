/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Projection from cardinal numbers to natural numbers

In this file we define `Cardinal.toNat` to be the natural projection `Cardinal → ℕ`,
sending all infinite cardinals to zero.
We also prove basic lemmas about this definition.
-/

@[expose] public section

assert_not_exists Field

universe u v
open Function Set

namespace Cardinal

variable {α : Type u} {c d : Cardinal.{u}}

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
/-
**Cardinal.toNat** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：toNat : Cardinal ->*₀ Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This function sends finite cardinals to the corresponding natural, and infinite 
cardinals
  to 0.
-/
noncomputable def toNat : Cardinal →*₀ ℕ :=
  ENat.toNatHom.comp (.ofClass toENat)
/-
**Cardinal.toNat_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (a : Cardinal.{u_1}), (Cardinal.toENat a).toNat = Cardinal.toNat a
参数：a : Cardinal.{u_1}；Cardinal.toENat a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toNat_toENat (a : Cardinal) : ENat.toNat (toENat a) = toNat a := rfl

@[simp]
/-
**Cardinal.toNat_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_ofENat (n : Nat∞) : toNat n = ENat.toNat n
参数：n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
-/
theorem toNat_ofENat (n : ℕ∞) : toNat n = ENat.toNat n :=
  congr_arg ENat.toNat <| toENat_ofENat n
/-
**Cardinal.toNat_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ), Cardinal.toNat ↑n = n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_ofENat`：toNat_ofENat (n : Nat∞) : toNat n = ENat.toNat n
-/
@[simp, norm_cast] theorem toNat_natCast (n : ℕ) : toNat n = n := toNat_ofENat n

@[simp]
/-
**Cardinal.toNat_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_toENat`：∀ (a : Cardinal.{u_1}), (Cardinal.toENat a).toNat
 = Cardinal.toNat a
· 使用定理 `ENat.toNat_eq_zero`：∀ {n : ℕ∞}, n.toNat = 0 ↔ n = 0 ∨ n = ⊤
· 使用定理 `Cardinal.toENat_eq_zero`：∀ {c : Cardinal.{u}}, Cardinal.toENat c = 0 ↔ c
 = 0
· 使用定理 `Cardinal.toENat_eq_top`：∀ {c : Cardinal.{u}}, Cardinal.toENat c = ⊤ ↔ Ca
rdinal.aleph0 ≤ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c := by
  rw [← toNat_toENat, ENat.toNat_eq_zero, toENat_eq_zero, toENat_eq_top]
/-
**Cardinal.toNat_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toNat_ne_zero : toNat c != 0 ↔ c != 0 ∧ c < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toNat_ne_zero : toNat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀ := by simp [not_or]
/-
**Cardinal.toNat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, 0 < Cardinal.toNat c ↔ c ≠ 0 ∧ c < Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Cardinal.toNat_ne_zero`：toNat_ne_zero : toNat c != 0 ↔ c != 0 ∧ c < ℵ₀
-/
@[simp] lemma toNat_pos : 0 < toNat c ↔ c ≠ 0 ∧ c < ℵ₀ := pos_iff_ne_zero.trans toNat_ne_zero
/-
**Cardinal.cast_toNat_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑(toNat c) = c
参数：h : c < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
-/
theorem cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑(toNat c) = c := by
  lift c to ℕ using h
  rw [toNat_natCast]
/-
**Cardinal.toNat_apply_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_apply_of_lt_aleph0 {c : Cardinal.{u}} (h : c < ℵ₀) : toNat c = Class
ical.choose (lt_aleph0.1 h)
参数：h : c < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem toNat_apply_of_lt_aleph0 {c : Cardinal.{u}} (h : c < ℵ₀) :
    toNat c = Classical.choose (lt_aleph0.1 h) :=
  Nat.cast_injective (R := Cardinal.{u}) <| by
    rw [cast_toNat_of_lt_aleph0 h, ← Classical.choose_spec (lt_aleph0.1 h)]
/-
**Cardinal.toNat_apply_of_aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ <= c) : toNat c = 0
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : toNat c = 0 := by simp [h]
/-
**Cardinal.cast_toNat_of_aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ <= c) : ↑(toNat c) = (0 : C
ardinal)
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : ↑(toNat c) = (0 : Cardinal) := by
  rw [toNat_apply_of_aleph0_le h, Nat.cast_zero]
/-
**Cardinal.cast_toNat_eq_iff_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cast_toNat_eq_iff_lt_aleph0 {c : Cardinal} : toNat c = c ↔ c < ℵ₀ where mp
 h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
-/
theorem cast_toNat_eq_iff_lt_aleph0 {c : Cardinal} : toNat c = c ↔ c < ℵ₀ where
  mp h := by rw [← h]; simp
  mpr := cast_toNat_of_lt_aleph0
/-
**Cardinal.toNat_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_strictMonoOn : StrictMonoOn toNat (Iio ℵ₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
-/
theorem toNat_strictMonoOn : StrictMonoOn toNat (Iio ℵ₀) := by
  simp only [← range_natCast, StrictMonoOn, forall_mem_range, toNat_natCast, Nat.cast_lt]
  exact fun _ _ ↦ id
/-
**Cardinal.toNat_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_monotoneOn : MonotoneOn toNat (Iio ℵ₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictMonoOn f s → Monoton
eOn f s
· 使用定理 `Cardinal.toNat_strictMonoOn`：toNat_strictMonoOn : StrictMonoOn toNat (Ii
o ℵ₀)
-/
theorem toNat_monotoneOn : MonotoneOn toNat (Iio ℵ₀) := toNat_strictMonoOn.monotoneOn
/-
**Cardinal.toNat_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_injOn : InjOn toNat (Iio ℵ₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Cardinal.toNat_strictMonoOn`：toNat_strictMonoOn : StrictMonoOn toNat (Ii
o ℵ₀)
-/
theorem toNat_injOn : InjOn toNat (Iio ℵ₀) := toNat_strictMonoOn.injOn

/-- Two finite cardinals are equal
iff they are equal their `Cardinal.toNat` projections are equal. -/
/-
**Cardinal.toNat_inj_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_inj_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat c = toNat d ↔ c
 = d
参数：hc : c < ℵ₀；hd : d < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Cardinal.toNat_injOn`：toNat_injOn : InjOn toNat (Iio ℵ₀)

--- 原说明 ---
Two finite cardinals are equal
iff they are equal their `Cardinal.toNat` projections are equal.
-/
theorem toNat_inj_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c = toNat d ↔ c = d :=
  toNat_injOn.eq_iff hc hd
/-
**Cardinal.toNat_le_iff_le_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_le_iff_le_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat c <= toNa
t d ↔ c <= d
参数：hc : c < ℵ₀；hd : d < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Cardinal.toNat_strictMonoOn`：toNat_strictMonoOn : StrictMonoOn toNat (Ii
o ℵ₀)
-/
theorem toNat_le_iff_le_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c ≤ toNat d ↔ c ≤ d :=
  toNat_strictMonoOn.le_iff_le hc hd
/-
**Cardinal.toNat_lt_iff_lt_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_lt_iff_lt_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat c < toNat
 d ↔ c < d
参数：hc : c < ℵ₀；hd : d < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `Cardinal.toNat_strictMonoOn`：toNat_strictMonoOn : StrictMonoOn toNat (Ii
o ℵ₀)
-/
theorem toNat_lt_iff_lt_of_lt_aleph0 (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c < toNat d ↔ c < d :=
  toNat_strictMonoOn.lt_iff_lt hc hd

@[gcongr]
/-
**Cardinal.toNat_le_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : toNat c <= toNat d
参数：hcd : c <= d；hd : d < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_monotoneOn`：toNat_monotoneOn : MonotoneOn toNat (Iio ℵ₀)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem toNat_le_toNat (hcd : c ≤ d) (hd : d < ℵ₀) : toNat c ≤ toNat d :=
  toNat_monotoneOn (hcd.trans_lt hd) hd hcd
/-
**Cardinal.toNat_lt_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_lt_toNat (hcd : c < d) (hd : d < ℵ₀) : toNat c < toNat d
参数：hcd : c < d；hd : d < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_strictMonoOn`：toNat_strictMonoOn : StrictMonoOn toNat (Ii
o ℵ₀)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem toNat_lt_toNat (hcd : c < d) (hd : d < ℵ₀) : toNat c < toNat d :=
  toNat_strictMonoOn (hcd.trans hd) hd hcd

@[simp]
/-
**Cardinal.toNat_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_ofNat (n : Nat) [n.AtLeastTwo] : Cardinal.toNat ofNat(n) = OfNat.ofN
at n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
-/
theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] :
    Cardinal.toNat ofNat(n) = OfNat.ofNat n :=
  toNat_natCast n

/-- `toNat` has a right-inverse: coercion. -/
/-
**Cardinal.toNat_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_rightInverse : Function.RightInverse ((↑) : Nat -> Cardinal) toNat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n

--- 原说明 ---
`toNat` has a right-inverse: coercion.
-/
theorem toNat_rightInverse : Function.RightInverse ((↑) : ℕ → Cardinal) toNat :=
  toNat_natCast
/-
**Cardinal.toNat_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_surjective : Surjective toNat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `Cardinal.toNat_rightInverse`：toNat_rightInverse : Function.RightInverse 
((↑) : Nat -> Cardinal) toNat
-/
theorem toNat_surjective : Surjective toNat :=
  toNat_rightInverse.surjective

@[simp]
/-
**Cardinal.mk_toNat_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_toNat_of_infinite [h : Infinite α] : toNat #α = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem mk_toNat_of_infinite [h : Infinite α] : toNat #α = 0 := by simp

@[simp]
/-
**Cardinal.aleph0_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_toNat : toNat ℵ₀ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem aleph0_toNat : toNat ℵ₀ = 0 :=
  toNat_apply_of_aleph0_le le_rfl
/-
**Cardinal.mk_toNat_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_toNat_eq_card [Fintype α] : toNat #α = Fintype.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_toNat_eq_card [Fintype α] : toNat #α = Fintype.card α := by simp

@[simp]
/-
**Cardinal.zero_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：zero_toNat : toNat 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem zero_toNat : toNat 0 = 0 := map_zero _
/-
**Cardinal.one_toNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_toNat : toNat 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem one_toNat : toNat 1 = 1 := map_one _
/-
**Cardinal.toNat_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_iff {n : Nat} (hn : n != 0) : toNat c = n ↔ c = n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_toENat`：∀ (a : Cardinal.{u_1}), (Cardinal.toENat a).toNat
 = Cardinal.toNat a
· 使用定理 `ENat.toNat_eq_iff`：toNat_eq_iff {m : Nat∞} {n : Nat} (hn : n != 0) : toN
at m = n ↔ m = n
· 使用定理 `Cardinal.toENat_eq_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c = ↑n ↔ c = ↑n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNat_eq_iff {n : ℕ} (hn : n ≠ 0) : toNat c = n ↔ c = n := by
  rw [← toNat_toENat, ENat.toNat_eq_iff hn, toENat_eq_natCast]

/-- A version of `toNat_eq_iff` for literals -/
/-
**Cardinal.toNat_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_ofNat {n : Nat} [Nat.AtLeastTwo n] : toNat c = OfNat.ofNat n ↔ c 
= OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_eq_iff`：toNat_eq_iff {n : Nat} (hn : n != 0) : toNat c = 
n ↔ c = n
· 使用定理 `OfNat.ofNat_ne_zero`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZ
ero R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 0

--- 原说明 ---
A version of `toNat_eq_iff` for literals
-/
theorem toNat_eq_ofNat {n : ℕ} [Nat.AtLeastTwo n] :
    toNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n :=
  toNat_eq_iff <| OfNat.ofNat_ne_zero n

@[simp]
/-
**Cardinal.toNat_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_one : toNat c = 1 ↔ c = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_eq_iff`：toNat_eq_iff {n : Nat} (hn : n != 0) : toNat c = 
n ↔ c = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toNat_eq_one : toNat c = 1 ↔ c = 1 := by
  rw [toNat_eq_iff one_ne_zero, Nat.cast_one]
/-
**Cardinal.toNat_eq_one_iff_unique** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_one_iff_unique : toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Cardinal.toNat_eq_one`：toNat_eq_one : toNat c = 1 ↔ c = 1
· 使用定理 `Cardinal.eq_one_iff_unique`：eq_one_iff_unique {α : Type*} : #α = 1 ↔ Sub
singleton α ∧ Nonempty α
-/
theorem toNat_eq_one_iff_unique : toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  toNat_eq_one.trans eq_one_iff_unique

@[simp]
/-
**Cardinal.toNat_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} c) = toNat c
参数：c : Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} c) = toNat c := by
  simp only [← toNat_toENat, toENat_lift]
/-
**Cardinal.toNat_congr** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = toNat #β
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
-/
theorem toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = toNat #β := by
  -- Porting note: Inserted universe hint below
  rw [← toNat_lift, (lift_mk_eq.{_, _, v}).mpr ⟨e⟩, toNat_lift]
/-
**Cardinal.toNat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x * toNat y
参数：x y : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x * toNat y := map_mul toNat x y

@[simp]
/-
**Cardinal.toNat_add** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d) = toNat c + toNat d
参数：hc : c < ℵ₀；hd : d < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
-/
theorem toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d) = toNat c + toNat d := by
  lift c to ℕ using hc
  lift d to ℕ using hd
  norm_cast
/-
**Cardinal.toNat_lift_add_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_lift_add_lift {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (h
b : b < ℵ₀) : toNat (lift.{v} a + lift.{u} b) = toNat a + toNat b
参数：ha : a < ℵ₀；hb : b < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_add`：toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d
) = toNat c + toNat d
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNat_lift_add_lift {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    toNat (lift.{v} a + lift.{u} b) = toNat a + toNat b := by
  simp [*]

@[simp]
/-
**Cardinal.natCast_toNat_le** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：natCast_toNat_le (a : Cardinal) : (toNat a : Cardinal) <= a
参数：a : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
lemma natCast_toNat_le (a : Cardinal) : (toNat a : Cardinal) ≤ a := by
  obtain h | h := lt_or_ge a ℵ₀
  · simp [cast_toNat_of_lt_aleph0 h]
  · simp [Cardinal.toNat_apply_of_aleph0_le h]
/-
**Cardinal.toNat_le_iff_of_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toNat_le_iff_of_lt_aleph0 {a : Cardinal.{u}} (n : Nat) (lt : a < Cardinal.
aleph0) : a.toNat <= n ↔ a <= n
参数：n : Nat；lt : a < Cardinal.aleph0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `Cardinal.toNat_le_iff_le_of_lt_aleph0`：toNat_le_iff_le_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c <= toNat d ↔ c <= d
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toNat_le_iff_of_lt_aleph0 {a : Cardinal.{u}} (n : ℕ) (lt : a < Cardinal.aleph0) :
    a.toNat ≤ n ↔ a ≤ n := by
  nth_rw 1 [← Cardinal.toNat_natCast.{u} n,
    Cardinal.toNat_le_iff_le_of_lt_aleph0 lt (Cardinal.natCast_lt_aleph0)]
/-
**Cardinal.toNat_eq_iff_of_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_iff_of_lt_aleph0 {a : Cardinal.{u}} (n : Nat) (lt : a < Cardinal.
aleph0) : a.toNat = n ↔ a = n
参数：n : Nat；lt : a < Cardinal.aleph0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
-/
lemma toNat_eq_iff_of_lt_aleph0 {a : Cardinal.{u}} (n : ℕ) (lt : a < Cardinal.aleph0) :
    a.toNat = n ↔ a = n := by
  nth_rw 2 [← Cardinal.cast_toNat_of_lt_aleph0 lt]
  exact Nat.cast_inj.symm

/-- A `Cardinal.toNat` version of `eq_of_forall_le_iff`.
This is useful for proving equality of `Module.finrank`. -/
/-
**Cardinal.toNat_eq_of_forall_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toNat_eq_of_forall_le_iff {c : Cardinal.{u}} {d : Cardinal.{v}} (h : foral
l n : Nat, n <= c ↔ n <= d) : c.toNat = d.toNat
参数：h : forall n : Nat, n <= c ↔ n <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_iff_and_or_not_and_not`：iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b
 ∨ ¬a ∧ ¬b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.aleph0_le`：aleph0_le {c : Cardinal} : ℵ₀ <= c ↔ forall n : Nat,
 ↑n <= c where mp h _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_apply_of_aleph0_le`：toNat_apply_of_aleph0_le {c : Cardina
l} (h : ℵ₀ <= c) : toNat c = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a

--- 原说明 ---
A `Cardinal.toNat` version of `eq_of_forall_le_iff`.
This is useful for proving equality of `Module.finrank`.
-/
theorem toNat_eq_of_forall_le_iff {c : Cardinal.{u}} {d : Cardinal.{v}}
    (h : ∀ n : ℕ, n ≤ c ↔ n ≤ d) : c.toNat = d.toNat := by
  have h' := forall_congr' h
  rw [← Cardinal.aleph0_le, ← Cardinal.aleph0_le] at h'
  rcases iff_iff_and_or_not_and_not.mp h' with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · simp [Cardinal.toNat_apply_of_aleph0_le, hc, hd]
  · apply eq_of_forall_le_iff
    rw [← cast_toNat_of_lt_aleph0 (not_le.mp hc), ← cast_toNat_of_lt_aleph0 (not_le.mp hd)] at h
    simpa using h

end Cardinal

