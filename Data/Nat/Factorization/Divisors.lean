/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors

/-!
# Results about divisors and factorizations
-/

public section

open Finsupp

namespace Nat

/-
**Nat.coe_divisors_eq_prod_pow_le_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coe_divisors_eq_prod_pow_le_factorization {n : Nat} (hn : n != 0) : n.divi
sors = { f.prod (· ^ ·) | f <= n.factorization }
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.dvd_of_mem_divisors`：dvd_of_mem_divisors {m : Nat} (h : n in divisor
s m) : n ∣ m
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_dvd_prod_of_subset_of_dvd`：prod_dvd_prod_of_subset_of_dvd [
Zero M] [CommMonoid N] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N} (h1 : f1.support 
subseteq f2.support) (h2 : f…
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
· 使用定理 `Nat.pow_dvd_pow`：∀ {m n : ℕ} (a : ℕ), m ≤ n → a ^ m ∣ a ^ n
-/
theorem coe_divisors_eq_prod_pow_le_factorization {n : ℕ} (hn : n ≠ 0) :
    n.divisors = { f.prod (· ^ ·) | f ≤ n.factorization } := by
  refine Set.ext fun k ↦ ⟨fun h ↦ ?_, fun ⟨f, hle, h⟩ ↦ mem_divisors.mpr ⟨?_, hn⟩⟩
  · have hdvd := dvd_of_mem_divisors h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    exact ⟨_, factorization_le_iff_dvd hk hn |>.mpr hdvd, prod_factorization_pow_eq_self hk⟩
  · rw [← h, ← prod_factorization_pow_eq_self hn]
    exact prod_dvd_prod_of_subset_of_dvd (support_mono hle) fun p _ ↦ Nat.pow_dvd_pow p <| hle p
/-
**Nat.divisors_eq_image_Iic_factorization_prod_pow** 是 Mathlib 中的一个定理，位于命名空间 `Na
t`。
形式化陈述：divisors_eq_image_Iic_factorization_prod_pow {n : Nat} (hn : n != 0) : n.d
ivisors = (Finset.Iic n.factorization).image (·.prod (· ^ ·))
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
-/
theorem divisors_eq_image_Iic_factorization_prod_pow {n : ℕ} (hn : n ≠ 0) :
    n.divisors = (Finset.Iic n.factorization).image (·.prod (· ^ ·)) := by
  apply Finset.coe_inj.mp
  grind [coe_divisors_eq_prod_pow_le_factorization]
/-
**Nat.Iic_factorization_prod_pow_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Iic_factorization_prod_pow_injective (n : Nat) : (·.val.prod (· ^ ·) : Fin
set.Iic n.factorization -> _).Injective
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_factorization_prod_pow_injective (n : ℕ) :
    (·.val.prod (· ^ ·) : Finset.Iic n.factorization → _).Injective := by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]
/-
**Nat.divisors_eq_map_attach_Iic_factorization_prod_pow** 是 Mathlib 中的一个定理，位于命名空
间 `Nat`。
形式化陈述：divisors_eq_map_attach_Iic_factorization_prod_pow {n : Nat} (hn : n != 0) 
: n.divisors = (Finset.Iic n.factorization).attach.map ⟨(·.val.prod (· ^ ·)), Ii
c_factorization_prod_pow_injective n⟩
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Iic_factorization_prod_pow_injective`：Iic_factorization_prod_pow_inj
ective (n : Nat) : (·.val.prod (· ^ ·) : Finset.Iic n.factorization -> _).Inject
ive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `Finset.attach_image_val`：attach_image_val [DecidableEq α] {s : Finset α}
 : s.attach.image Subtype.val = s
· 使用定理 `Nat.divisors_eq_image_Iic_factorization_prod_pow`：divisors_eq_image_Iic_
factorization_prod_pow {n : Nat} (hn : n != 0) : n.divisors = (Finset.Iic n.fact
orization).image (·.prod (· ^ ·))
-/
theorem divisors_eq_map_attach_Iic_factorization_prod_pow {n : ℕ} (hn : n ≠ 0) :
    n.divisors = (Finset.Iic n.factorization).attach.map
      ⟨(·.val.prod (· ^ ·)), Iic_factorization_prod_pow_injective n⟩ := by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iic n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image, Finset.attach_image_val]
  exact divisors_eq_image_Iic_factorization_prod_pow hn
/-
**Nat.coe_properDivisors_eq_prod_pow_lt_factorization** 是 Mathlib 中的一个定理，位于命名空间 
`Nat`。
形式化陈述：coe_properDivisors_eq_prod_pow_lt_factorization {n : Nat} : n.properDiviso
rs = { f.prod (· ^ ·) | f < n.factorization }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.properDivisors_zero`：properDivisors_zero : properDivisors 0 = ∅
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.eq_of_factorization_eq'`：eq_of_factorization_eq' {a b : Nat} (ha : a
 != 0) (hb : b != 0) (h : a.factorization = b.factorization) : a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_dvd_prod_of_subset_of_dvd`：prod_dvd_prod_of_subset_of_dvd [
Zero M] [CommMonoid N] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N} (h1 : f1.support 
subseteq f2.support) (h2 : f…
· 使用引理 `Finsupp.support_mono`：support_mono (hfg : f <= g) : f.support subseteq g
.support
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.pow_dvd_pow`：∀ {m n : ℕ} (a : ℕ), m ≤ n → a ^ m ∣ a ^ n
（共 33 条，此处仅展示前 30 条）
-/
theorem coe_properDivisors_eq_prod_pow_lt_factorization {n : ℕ} :
    n.properDivisors = { f.prod (· ^ ·) | f < n.factorization } := by
  by_cases hn : n = 0
  · simp [hn]
  refine Set.ext fun k ↦ ⟨fun h ↦ ?_, fun ⟨f, hlt, h⟩ ↦ ?_⟩
  · have ⟨hdvd, hlt⟩ := mem_properDivisors.mp h
    have hk := ne_zero_of_dvd_ne_zero hn hdvd
    refine ⟨_, ?_, prod_factorization_pow_eq_self hk⟩
    apply lt_of_le_of_ne <| factorization_le_iff_dvd hk hn |>.mpr hdvd
    exact mt (Nat.eq_of_factorization_eq' hk hn) hlt.ne
  · have : k ∣ n := by
      rw [← h, ← prod_factorization_pow_eq_self hn]
      apply prod_dvd_prod_of_subset_of_dvd <| support_mono hlt.le
      exact fun p _ ↦ Nat.pow_dvd_pow p <| hlt.le p
    refine mem_properDivisors.mpr ⟨this, lt_of_le_of_ne (le_of_dvd (Nat.pos_of_ne_zero hn) this) ?_⟩
    suffices k.factorization = f from (this ▸ hlt.ne <| congrArg _ ·)
    exact h ▸ factorization_prod_pow_eq_self_of_le_factorization hlt.le
/-
**Nat.properDivisors_eq_image_Iio_factorization_prod_pow** 是 Mathlib 中的一个定理，位于命名
空间 `Nat`。
形式化陈述：properDivisors_eq_image_Iio_factorization_prod_pow {n : Nat} : n.properDiv
isors = (Finset.Iio n.factorization).image (·.prod (· ^ ·))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
-/
theorem properDivisors_eq_image_Iio_factorization_prod_pow {n : ℕ} :
    n.properDivisors = (Finset.Iio n.factorization).image (·.prod (· ^ ·)) := by
  apply Finset.coe_inj.mp
  grind [coe_properDivisors_eq_prod_pow_lt_factorization]
/-
**Nat.Iio_factorization_prod_pow_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Iio_factorization_prod_pow_injective (n : Nat) : (·.val.prod (· ^ ·) : Fin
set.Iio n.factorization -> _).Injective
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_factorization_prod_pow_injective (n : ℕ) :
    (·.val.prod (· ^ ·) : Finset.Iio n.factorization → _).Injective := by
  grind [Function.Injective, factorization_prod_pow_eq_self_of_le_factorization]
/-
**Nat.properDivisors_eq_map_attach_Iio_factorization_prod_pow** 是 Mathlib 中的一个定理
，位于命名空间 `Nat`。
形式化陈述：properDivisors_eq_map_attach_Iio_factorization_prod_pow {n : Nat} : n.prop
erDivisors = (Finset.Iio n.factorization).attach.map ⟨(·.val.prod (· ^ ·)), Iio_
factorization_prod_pow_injective n⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Iio_factorization_prod_pow_injective`：Iio_factorization_prod_pow_inj
ective (n : Nat) : (·.val.prod (· ^ ·) : Finset.Iio n.factorization -> _).Inject
ive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `Finset.attach_image_val`：attach_image_val [DecidableEq α] {s : Finset α}
 : s.attach.image Subtype.val = s
· 使用定理 `Nat.properDivisors_eq_image_Iio_factorization_prod_pow`：properDivisors_e
q_image_Iio_factorization_prod_pow {n : Nat} : n.properDivisors = (Finset.Iio n.
factorization).image (·.prod (· ^ ·))
-/
theorem properDivisors_eq_map_attach_Iio_factorization_prod_pow {n : ℕ} :
    n.properDivisors = (Finset.Iio n.factorization).attach.map
      ⟨(·.val.prod (· ^ ·)), Iio_factorization_prod_pow_injective n⟩ := by
  rw [Finset.map_eq_image]
  change _ = (Finset.Iio n.factorization).attach.image ((·.prod (· ^ ·)) ∘ Subtype.val)
  rw [← Finset.image_image, Finset.attach_image_val]
  exact properDivisors_eq_image_Iio_factorization_prod_pow

end Nat

