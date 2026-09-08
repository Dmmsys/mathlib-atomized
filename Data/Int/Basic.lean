/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.OfNat

/-!
# Basic operations on the integers

This file builds on `Data.Int.Init` by adding basic lemmas on integers.
depending on Mathlib definitions.
-/

public section

open Nat

namespace Int
variable {a b c d m n : ℤ}

attribute [gcongr] ofNat_le

/-
**Int.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instNontrivial : Nontrivial Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.zero_ne_one`：0 ≠ 1
-/
instance instNontrivial : Nontrivial ℤ := ⟨⟨0, 1, Int.zero_ne_one⟩⟩
/-
**Int.ofNat_injective** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Function.Injective Int.ofNat
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ofNat.inj`：∀ {a a_1 : ℕ}, Int.ofNat a = Int.ofNat a_1 → a = a_1
-/
@[simp] lemma ofNat_injective : Function.Injective ofNat := @Int.ofNat.inj

section strongRec

variable {P : ℤ → Sort*} {lt : ∀ n < m, P n} {ge : ∀ n ≥ m, (∀ k < n, P k) → P n}

/-
**Int.strongRec_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：strongRec_of_ge : forall hn : m <= n, m.strongRec lt ge n = ge n hn fun k 
_ => m.strongRec lt ge k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.not_lt`：∀ {a b : ℤ}, ¬a < b ↔ b ≤ a
· 使用引理 `Int.inductionOn'`：inductionOn'_self : b.inductionOn' b zero succ pred = 
zero
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.strongRec.eq_1`：∀ {m : ℤ} {motive : ℤ → Sort u_1} (lt : (n : ℤ) → n 
< m → motive n)   (ge : (n : ℤ) → n ≥ m → ((k : ℤ) → k < n → motive k) → motive 
n) (n : …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.inductionOn'_self`：∀ {motive : ℤ → Sort u_1} {b : ℤ} {zero : motive 
b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) → k ≤ 
b → motive …
· 使用引理 `Int.strongRec_of_lt`：strongRec_of_lt (hn : n < m) : m.strongRec lt ge n 
= lt n hn
· 使用定理 `Int.inductionOn'_add_one`：∀ {motive : ℤ → Sort u_1} {z b : ℤ} {zero : mo
tive b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) →
 k ≤ b → motiv…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Int.lt_trans`：∀ {a b c : ℤ}, a < b → b < c → a < c
· 使用定理 `Int.lt_succ`：∀ (a : ℤ), a < a + 1
· 使用定理 `Int.inductionOn'_sub_one`：∀ {motive : ℤ → Sort u_1} {z b : ℤ} {zero : mo
tive b} {succ : (k : ℤ) → b ≤ k → motive k → motive (k + 1)}   {pred : (k : ℤ) →
 k ≤ b → motiv…
· 使用定理 `Int.lt_of_le_of_lt`：∀ {a b c : ℤ}, a ≤ b → b < c → a < c
-/
lemma strongRec_of_ge :
    ∀ hn : m ≤ n, m.strongRec lt ge n = ge n hn fun k _ ↦ m.strongRec lt ge k := by
  refine m.strongRec (fun n hnm hmn ↦ (Int.not_lt.mpr hmn hnm).elim) (fun n _ ih hn ↦ ?_) n
  rw [Int.strongRec, dif_neg (Int.not_lt.mpr hn)]
  congr; revert ih
  refine n.inductionOn' m (fun _ ↦ ?_) (fun k hmk ih' ih ↦ ?_) (fun k hkm ih' _ ↦ ?_) <;> ext l hl
  · rw [inductionOn'_self, strongRec_of_lt hl]
  · rw [inductionOn'_add_one hmk]; split_ifs with hlm
    · rw [strongRec_of_lt hlm]
    · rw [ih' fun l hl ↦ ih l (Int.lt_trans hl k.lt_succ), ih _ hl]
  · rw [inductionOn'_sub_one hkm, ih']
    exact fun l hlk hml ↦ (Int.not_lt.mpr hkm <| Int.lt_of_le_of_lt hml hlk).elim

end strongRec

/-! ### nat abs -/

/-
**Int.natAbs_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natAbs_surjective : natAbs.Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n

--- 原说明 ---
### nat abs
-/
lemma natAbs_surjective : natAbs.Surjective := fun n => ⟨n, natAbs_natCast n⟩
/-
**Int.pow_right_injective** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：pow_right_injective (h : 1 < a.natAbs) : ((a ^ ·) : Nat -> Int).Injective
参数：h : 1 < a.natAbs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
-/
lemma pow_right_injective (h : 1 < a.natAbs) : ((a ^ ·) : ℕ → ℤ).Injective := by
  refine (?_ : (natAbs ∘ (a ^ · : ℕ → ℤ)).Injective).of_comp
  convert! Nat.pow_right_injective h using 2
  rw [Function.comp_apply, natAbs_pow]

/-! ### dvd -/

/-
**Int.ofNat_dvd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {x y : ℕ}, OfNat.ofNat x ∣ ↑y ↔ OfNat.ofNat x ∣ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n

--- 原说明 ---
### dvd
-/
@[norm_cast] theorem ofNat_dvd_natCast {x y : ℕ} : (ofNat(x) : ℤ) ∣ (y : ℤ) ↔ OfNat.ofNat x ∣ y :=
  natCast_dvd_natCast
/-
**Int.natCast_dvd_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {x y : ℕ}, ↑x ∣ OfNat.ofNat y ↔ x ∣ OfNat.ofNat y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
-/
@[norm_cast] theorem natCast_dvd_ofNat {x y : ℕ} : (x : ℤ) ∣ (ofNat(y) : ℤ) ↔ x ∣ OfNat.ofNat y :=
  natCast_dvd_natCast
/-
**Int.natCast_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
-/
lemma natCast_dvd {m : ℕ} : (m : ℤ) ∣ n ↔ m ∣ n.natAbs := by
  obtain hn | hn := natAbs_eq n <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]
/-
**Int.dvd_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：dvd_natCast {n : Nat} : m ∣ (n : Int) ↔ m.natAbs ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_eq`：∀ (a : ℤ), a = ↑a.natAbs ∨ a = -↑a.natAbs
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
-/
lemma dvd_natCast {n : ℕ} : m ∣ (n : ℤ) ↔ m.natAbs ∣ n := by
  obtain hn | hn := natAbs_eq m <;> rw [hn] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]
/-
**Int.eq_zero_of_dvd_of_nonneg_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：eq_zero_of_dvd_of_nonneg_of_lt (hm : 0 <= m) (hmn : m < n) (hnm : n ∣ m) :
 m = 0
参数：hm : 0 <= m；hmn : m < n；hnm : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`：∀ {d n : ℤ}, d ∣ n → n.natAbs < 
d.natAbs → n = 0
· 使用定理 `Int.natAbs_lt_natAbs_of_nonneg_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a.nat
Abs < b.natAbs
-/
lemma eq_zero_of_dvd_of_nonneg_of_lt (hm : 0 ≤ m) (hmn : m < n) (hnm : n ∣ m) : m = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs hnm (natAbs_lt_natAbs_of_nonneg_of_lt hm hmn)

/-- If two integers are congruent to a sufficiently large modulus, they are equal. -/
/-
**Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : Int} (h1 : a % b = c) (h2 : 
natAbs (a - c) < natAbs b) : a = c
参数：h1 : a % b = c；h2 : natAbs (a - c) < natAbs b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_of_sub_eq_zero`：∀ {a b : ℤ}, a - b = 0 → a = b
· 使用定理 `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`：∀ {d n : ℤ}, d ∣ n → n.natAbs < 
d.natAbs → n = 0
· 使用定理 `Int.dvd_self_sub_of_emod_eq`：∀ {a b c : ℤ}, a % b = c → b ∣ a - c

--- 原说明 ---
If two integers are congruent to a sufficiently large modulus, they are equal.
-/
lemma eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : ℤ} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  Int.eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_self_sub_of_emod_eq h1) h2)
/-
**Int.natAbs_le_of_dvd_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn : n != 0) : natAbs m <= natAbs 
n
参数：hmn : m ∣ n；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`：∀ {d n : ℤ}, d ∣ n → n.natAbs < 
d.natAbs → n = 0
-/
lemma natAbs_le_of_dvd_ne_zero (hmn : m ∣ n) (hn : n ≠ 0) : natAbs m ≤ natAbs n :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hmn) hn)
/-
**Int.gcd_emod** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_emod (m n : Int) : (m % n).gcd n = m.gcd n
参数：m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用定理 `Int.gcd_add_mul_left_left`：∀ (m n k : ℤ), (n + m * k).gcd m = n.gcd m
-/
theorem gcd_emod (m n : ℤ) : (m % n).gcd n = m.gcd n := by
  conv_rhs => rw [← m.emod_add_mul_ediv n, gcd_add_mul_left_left]

end Int

