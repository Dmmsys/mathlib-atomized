/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Cast.Lemmas

/-!

# Congruences modulo an integer

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`Data.Nat.ModEq` defines them for the natural numbers. The notation is short for `n.ModEq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/

@[expose] public section


/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
@[wikidata Q3773677]
/-
**Int.ModEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Int.ModEq (n a b : Int)
参数：n a b : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a ≡ b [ZMOD n]` when `a % n = b % n`.
-/
def Int.ModEq (n a b : ℤ) :=
  a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

namespace AddCommGroup

@[simp]
/-
**AddCommGroup.modEq_iff_intModEq** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：modEq_iff_intModEq {a b z : Int} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_iff_intModEq {a b z : ℤ} : a ≡ b [PMOD z] ↔ a ≡ b [ZMOD z] := by
  rw [modEq_comm]
  simp [modEq_iff_zsmul', dvd_iff_exists_eq_mul_left, Int.ModEq,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

@[deprecated (since := "2026-01-13")]
alias modEq_iff_int_modEq := modEq_iff_intModEq

variable {G : Type*} [AddCommGroupWithOne G] [CharZero G]

@[simp, norm_cast]
/-
**AddCommGroup.intCast_modEq_intCast** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGroup`。
形式化陈述：intCast_modEq_intCast {a b z : Int} : a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z
]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGroup.map_modEq_iff`：map_modEq_iff {N F : Type*} [AddCommMonoid N
] [FunLike F M N] [AddMonoidHomClass F M N] (f : F) (hf : Function.Injective f) 
: f a ≡ f b [PMO…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
-/
theorem intCast_modEq_intCast {a b z : ℤ} : a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z] :=
  map_modEq_iff (Int.castAddHom G) Int.cast_injective

@[simp, norm_cast]
/-
**AddCommGroup.intCast_modEq_intCast'** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGroup`。
形式化陈述：intCast_modEq_intCast' {a b : Int} {n : Nat} : a ≡ b [PMOD (n : G)] ↔ a ≡ 
b [PMOD (n : Int)]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `AddCommGroup.intCast_modEq_intCast`：intCast_modEq_intCast {a b z : Int} 
: a ≡ b [PMOD (z : G)] ↔ a ≡ b [PMOD z]
-/
lemma intCast_modEq_intCast' {a b : ℤ} {n : ℕ} : a ≡ b [PMOD (n : G)] ↔ a ≡ b [PMOD (n : ℤ)] := by
  simpa using intCast_modEq_intCast (G := G) (z := n)

alias ⟨ModEq.of_intCast, ModEq.intCast⟩ := intCast_modEq_intCast

end AddCommGroup

namespace Int

variable {m n a b c d : ℤ}

/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Decidable (ModEq n a b) := decEq (a % n) (b % n)

namespace ModEq

@[refl, simp]
/-
**Int.ModEq.refl** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]
参数：a : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] :=
  @rfl _ _
/-
**Int.ModEq.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a : ℤ}, a ≡ a [ZMOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.refl`：∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]
-/
protected theorem rfl : a ≡ a [ZMOD n] :=
  ModEq.refl _
/-
**Int.ModEq.** 是 Mathlib 中的一个实例，位于命名空间 `Int.ModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
/-
**Int.ModEq.symm** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] :=
  Eq.symm

@[trans]
/-
**Int.ModEq.trans** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] :=
  Eq.trans
/-
**Int.ModEq.** 是 Mathlib 中的一个实例，位于命名空间 `Int.ModEq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans ℤ (ModEq n) where
  trans := @Int.ModEq.trans n
/-
**Int.ModEq.eq** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → a % n = b % n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem eq : a ≡ b [ZMOD n] → a % n = b % n := id

end ModEq

/-
**Int.modEq_comm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
-/
theorem modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n] := ⟨ModEq.symm, ModEq.symm⟩

@[simp, norm_cast]
/-
**Int.natCast_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem natCast_modEq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] := by
  unfold ModEq Nat.ModEq; rw [← Int.ofNat_inj]; simp
/-
**Int.modEq_zero_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ModEq.eq_1`：∀ (n a b : ℤ), (a ≡ b [ZMOD n]) = (a % n = b % n)
· 使用定理 `Int.zero_emod`：∀ (b : ℤ), 0 % b = 0
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a := by
  rw [ModEq, zero_emod, dvd_iff_emod_eq_zero]
/-
**Int._root_.Dvd.dvd.modEq_zero_int** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dvd.dvd.modEq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modEq_zero_iff_dvd.2 h
/-
**Int._root_.Dvd.dvd.zero_modEq_int** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Dvd.dvd.zero_modEq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] :=
  h.modEq_zero_int.symm
/-
**Int.modEq_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ModEq.eq_1`：∀ (n a b : ℤ), (a ≡ b [ZMOD n]) = (a % n = b % n)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [ModEq, eq_comm]
  simp [emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero]
/-
**Int.modEq_iff_add_fac** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_iff_add_fac {a b n : Int} : a ≡ b [ZMOD n] ↔ exists t, b = a + n * t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
-/
theorem modEq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t := by
  rw [modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd
/-
**Int.mod_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mod_modEq (a n) : a % n ≡ a [ZMOD n]
参数：a n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.emod_emod`：∀ (a b : ℤ), a % b % b = a % b
-/
theorem mod_modEq (a n) : a % n ≡ a [ZMOD n] :=
  emod_emod _ _

@[simp]
/-
**Int.neg_modEq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：neg_modEq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neg_modEq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp only [modEq_iff_dvd, (by lia : -b - -a = -(b - a)), Int.dvd_neg]

@[simp]
/-
**Int.modEq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n] := by simp [modEq_iff_dvd]

namespace ModEq

/-
**Int.ModEq.of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {m n a b : ℤ}, m ∣ n → a ≡ b [ZMOD n] → a ≡ b [ZMOD m]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
-/
protected theorem of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
  modEq_iff_dvd.2 <| d.trans h.dvd
/-
**Int.ModEq.mul_left'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → c * a ≡ c * b [ZMOD c * n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.neg_modEq_neg`：neg_modEq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n]
· 使用定理 `Int.modEq_neg`：modEq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n]
· 使用定理 `Int.neg_mul`：∀ (a b : ℤ), -a * b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.mul_emod_mul_of_pos`：∀ {a : ℤ} (b c : ℤ), 0 < a → a * b % (a * c) = 
a * (b % c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.ModEq.eq`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → a % n = b % n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.zero_mul`：∀ (a : ℤ), 0 * a = 0
-/
protected theorem mul_left' (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD c * n] := by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · rw [← neg_modEq_neg, ← modEq_neg, ← Int.neg_mul, ← Int.neg_mul, ← Int.neg_mul]
    simp only [ModEq, mul_emod_mul_of_pos _ _ (neg_pos.2 hc), h.eq]
  · simp only [Int.zero_mul, ModEq.rfl]
  · simp only [ModEq, mul_emod_mul_of_pos _ _ hc, h.eq]
/-
**Int.ModEq.mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → a * c ≡ b * c [ZMOD n * c]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Int.ModEq.mul_left'`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → c * a ≡ c * b [ZM
OD c * n]
-/
protected theorem mul_right' (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left'

@[gcongr]
/-
**Int.ModEq.add** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a + c ≡ b + d [ZMOD n
]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.dvd_add`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b + c
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
-/
protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
  modEq_iff_dvd.2 <| by convert! Int.dvd_add h₁.dvd h₂.dvd using 1; lia
/-
**Int.ModEq.add_left** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → c + a ≡ c + b [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.add`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a + 
c ≡ b + d [ZMOD n]
· 使用定理 `Int.ModEq.rfl`：∀ {n a : ℤ}, a ≡ a [ZMOD n]
-/
protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
  ModEq.rfl.add h
/-
**Int.ModEq.add_right** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → a + c ≡ b + c [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.add`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a + 
c ≡ b + d [ZMOD n]
· 使用定理 `Int.ModEq.rfl`：∀ {n a : ℤ}, a ≡ a [ZMOD n]
-/
protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
  h.add ModEq.rfl
/-
**Int.ModEq.add_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a + c ≡ b + d [ZMOD n] → c ≡ d [ZMOD n
]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dvd_sub`：∀ {a b c : ℤ}, a ∣ b → a ∣ c → a ∣ b - c
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
-/
protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    c ≡ d [ZMOD n] :=
  have : d - c = b + d - (a + c) - (b - a) := by lia
  modEq_iff_dvd.2 <| by
    rw [this]
    exact Int.dvd_sub h₂.dvd h₁.dvd
/-
**Int.ModEq.add_left_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), c + a ≡ c + b [ZMOD n] → a ≡ b [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.add_left_cancel`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a + c ≡ b
 + d [ZMOD n] → c ≡ d [ZMOD n]
· 使用定理 `Int.ModEq.rfl`：∀ {n a : ℤ}, a ≡ a [ZMOD n]
-/
protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_left_cancel h
/-
**Int.ModEq.add_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c d : ℤ}, c ≡ d [ZMOD n] → a + c ≡ b + d [ZMOD n] → a ≡ b [ZMOD n
]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.add_left_cancel`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a + c ≡ b
 + d [ZMOD n] → c ≡ d [ZMOD n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂
/-
**Int.ModEq.add_right_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a + c ≡ b + c [ZMOD n] → a ≡ b [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.add_right_cancel`：∀ {n a b c d : ℤ}, c ≡ d [ZMOD n] → a + c ≡ 
b + d [ZMOD n] → a ≡ b [ZMOD n]
· 使用定理 `Int.ModEq.rfl`：∀ {n a : ℤ}, a ≡ a [ZMOD n]
-/
protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_right_cancel h
/-
**Int.ModEq.neg** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → -a ≡ -b [ZMOD n]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.add_left_cancel`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a + c ≡ b
 + d [ZMOD n] → c ≡ d [ZMOD n]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
@[gcongr] protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
  h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self]; rfl)

@[gcongr]
/-
**Int.ModEq.sub** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a - c ≡ b - d [ZMOD n
]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Int.ModEq.add`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a + 
c ≡ b + d [ZMOD n]
· 使用定理 `Int.ModEq.neg`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → -a ≡ -b [ZMOD n]
-/
protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg
/-
**Int.ModEq.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → c - a ≡ c - b [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.sub`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a - 
c ≡ b - d [ZMOD n]
· 使用定理 `Int.ModEq.rfl`：∀ {n a : ℤ}, a ≡ a [ZMOD n]
-/
protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
  ModEq.rfl.sub h
/-
**Int.ModEq.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → a - c ≡ b - c [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.sub`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a - 
c ≡ b - d [ZMOD n]
· 使用定理 `Int.ModEq.rfl`：∀ {n a : ℤ}, a ≡ a [ZMOD n]
-/
protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
  h.sub ModEq.rfl
/-
**Int.ModEq.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → c * a ≡ c * b [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.of_dvd`：∀ {m n a b : ℤ}, m ∣ n → a ≡ b [ZMOD n] → a ≡ b [ZMOD 
m]
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Int.ModEq.mul_left'`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → c * a ≡ c * b [ZM
OD c * n]
-/
protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
  h.mul_left'.of_dvd <| dvd_mul_left _ _
/-
**Int.ModEq.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → a * c ≡ b * c [ZMOD n]
参数：c : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.of_dvd`：∀ {m n a b : ℤ}, m ∣ n → a ≡ b [ZMOD n] → a ≡ b [ZMOD 
m]
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Int.ModEq.mul_right'`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → a * c ≡ b * c [Z
MOD n * c]
-/
protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
  h.mul_right'.of_dvd <| dvd_mul_right _ _

@[gcongr]
/-
**Int.ModEq.mul** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a * c ≡ b * d [ZMOD n
]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.trans`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ 
c [ZMOD n]
· 使用定理 `Int.ModEq.mul_left`：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → c * a ≡ c * 
b [ZMOD n]
· 使用定理 `Int.ModEq.mul_right`：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → a * c ≡ b *
 c [ZMOD n]
-/
protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)
/-
**Int.ModEq.pow** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {n a b : ℤ} (m : ℕ), a ≡ b [ZMOD n] → a ^ m ≡ b ^ m [ZMOD n]
参数：m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Int.ModEq.mul`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a * 
c ≡ b * d [ZMOD n]
-/
@[gcongr] protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] := by
  induction m with
  | zero => simp
  | succ d hd => rw [pow_succ, pow_succ]; exact hd.mul h
/-
**Int.ModEq.of_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Int.ModEq`。
形式化陈述：of_mul_left (m : Int) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n]
参数：m : Int；h : a ≡ b [ZMOD m * n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
-/
lemma of_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] := by
  rw [modEq_iff_dvd] at *; exact (dvd_mul_left n m).trans h
/-
**Int.ModEq.of_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Int.ModEq`。
形式化陈述：of_mul_right (m : Int) : a ≡ b [ZMOD n * m] -> a ≡ b [ZMOD n]
参数：m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.ModEq.of_mul_left`：of_mul_left (m : Int) (h : a ≡ b [ZMOD m * n]) : 
a ≡ b [ZMOD n]
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma of_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
  mul_comm m n ▸ of_mul_left _

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c`. -/
/-
**Int.ModEq.cancel_right_div_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) : a ≡ b [ZM
OD m / gcd m c]
参数：hm : 0 < m；h : a * c ≡ b * c [ZMOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `Int.dvd_of_dvd_mul_right_of_gcd_one`：dvd_of_dvd_mul_right_of_gcd_one {a 
b c : Int} (habc : a ∣ b * c) (hab : gcd a b = 1) : a ∣ c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.mul_ediv_assoc`：∀ (a : ℤ) {b c : ℤ}, c ∣ b → a * b / c = a * (b / c)
· 使用定理 `Int.gcd_dvd_right`：∀ (a b : ℤ), ↑(a.gcd b) ∣ b
· 使用定理 `Int.sub_mul`：∀ (a b c : ℤ), (a - b) * c = a * c - b * c
· 使用定理 `Int.ediv_dvd_ediv`：∀ {a b c : ℤ}, a ∣ b → b ∣ c → b / a ∣ c / a
· 使用定理 `Int.gcd_dvd_left`：∀ (a b : ℤ), ↑(a.gcd b) ∣ a
· 使用定理 `Int.gcd_div`：∀ {a b c : ℤ}, c ∣ a → c ∣ b → (a / c).gcd (b / c) = a.gcd 
b / c.natAbs
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Int.gcd_pos_of_ne_zero_left`：∀ {a : ℤ} (b : ℤ), a ≠ 0 → 0 < a.gcd b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `
gcd m c`.
-/
theorem cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) :
    a ≡ b [ZMOD m / gcd m c] := by
  let d := gcd m c
  rw [modEq_iff_dvd] at h ⊢
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (gcd_dvd_right ..), Int.sub_mul]
    exact Int.ediv_dvd_ediv (gcd_dvd_left ..) h
  · rw [gcd_div (gcd_dvd_left ..) (gcd_dvd_right ..), natAbs_natCast,
      Nat.div_self (gcd_pos_of_ne_zero_left c hm.ne')]

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c`. -/
/-
**Int.ModEq.cancel_left_div_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMO
D m / gcd m c]
参数：hm : 0 < m；h : c * a ≡ c * b [ZMOD m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.cancel_right_div_gcd`：cancel_right_div_gcd (hm : 0 < m) (h : a
 * c ≡ b * c [ZMOD m]) : a ≡ b [ZMOD m / gcd m c]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `
gcd m c`.
-/
theorem cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
  cancel_right_div_gcd hm <| by simpa [mul_comm] using h
/-
**Int.ModEq.of_div** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：of_div (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c 
∣ m) : a ≡ b [ZMOD m]
参数：h : a / c ≡ b / c [ZMOD m / c]；ha : c ∣ a；ha : c ∣ b；ha : c ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.mul_ediv_cancel'`：∀ {a b : ℤ}, a ∣ b → a * (b / a) = b
· 使用定理 `Int.ModEq.mul_left'`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → c * a ≡ c * b [ZM
OD c * n]
-/
theorem of_div (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [ZMOD m] := by convert! h.mul_left' <;> rwa [Int.mul_ediv_cancel']

/-- Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Int.ModEq.of_mul_left`. -/
/-
**Int.ModEq.mul_left_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {m a b c : ℤ}, c ≠ 0 → c * a ≡ c * b [ZMOD c * m] → a ≡ b [ZMOD m]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dvd_of_mul_dvd_mul_left`：∀ {a m n : ℤ}, a ≠ 0 → a * m ∣ a * n → m ∣ 
n

--- 原说明 ---
Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Int.ModEq.of_mul_left`.
-/
protected theorem mul_left_cancel' (hc : c ≠ 0) :
    c * a ≡ c * b [ZMOD c * m] → a ≡ b [ZMOD m] := by
  simp only [modEq_iff_dvd, ← Int.mul_sub]
  exact Int.dvd_of_mul_dvd_mul_left hc
/-
**Int.ModEq.mul_left_cancel_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {m a b c : ℤ}, c ≠ 0 → (c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m])
参数：c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.mul_left_cancel'`：∀ {m a b c : ℤ}, c ≠ 0 → c * a ≡ c * b [ZMOD
 c * m] → a ≡ b [ZMOD m]
· 使用定理 `Int.ModEq.mul_left'`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → c * a ≡ c * b [ZM
OD c * n]
-/
protected theorem mul_left_cancel_iff' (hc : c ≠ 0) :
    c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m] :=
  ⟨ModEq.mul_left_cancel' hc, Int.ModEq.mul_left'⟩

/-- Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Int.ModEq.of_mul_right`. -/
/-
**Int.ModEq.mul_right_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {m a b c : ℤ}, c ≠ 0 → a * c ≡ b * c [ZMOD m * c] → a ≡ b [ZMOD m]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dvd_of_mul_dvd_mul_right`：∀ {a m n : ℤ}, a ≠ 0 → m * a ∣ n * a → m ∣
 n

--- 原说明 ---
Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Int.ModEq.of_mul_right`
.
-/
protected theorem mul_right_cancel' (hc : c ≠ 0) :
    a * c ≡ b * c [ZMOD m * c] → a ≡ b [ZMOD m] := by
  simp only [modEq_iff_dvd, ← Int.sub_mul]
  exact Int.dvd_of_mul_dvd_mul_right hc
/-
**Int.ModEq.mul_right_cancel_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：∀ {m a b c : ℤ}, c ≠ 0 → (a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m])
参数：a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.mul_right_cancel'`：∀ {m a b c : ℤ}, c ≠ 0 → a * c ≡ b * c [ZMO
D m * c] → a ≡ b [ZMOD m]
· 使用定理 `Int.ModEq.mul_right'`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → a * c ≡ b * c [Z
MOD n * c]
-/
protected theorem mul_right_cancel_iff' (hc : c ≠ 0) :
    a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right'⟩
/-
**Int.ModEq.dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int.ModEq`。
形式化陈述：dvd_iff (h : a ≡ b [ZMOD n]) : n ∣ a ↔ n ∣ b
参数：h : a ≡ b [ZMOD n]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ModEq.trans`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ 
c [ZMOD n]
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
-/
theorem dvd_iff (h : a ≡ b [ZMOD n]) : n ∣ a ↔ n ∣ b := by
  simp only [← modEq_zero_iff_dvd]
  exact ⟨fun ha ↦ h.symm.trans ha, h.trans⟩

end ModEq

@[simp]
/-
**Int.abs_modEq_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_modEq_two : |a| ≡ a [ZMOD 2]
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_modEq_two : |a| ≡ a [ZMOD 2] := by
  grind [Int.ModEq]

@[simp]
/-
**Int.modulus_modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modulus_modEq_zero : n ≡ 0 [ZMOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.emod_self`：∀ {a : ℤ}, a % a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem modulus_modEq_zero : n ≡ 0 [ZMOD n] := by simp [ModEq]

@[simp]
/-
**Int.modEq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_abs : a ≡ b [ZMOD |n|] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.emod_abs`：emod_abs (a b : Int) : a % |b| = a % b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_abs : a ≡ b [ZMOD |n|] ↔ a ≡ b [ZMOD n] := by simp [ModEq]
/-
**Int.modEq_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n] := by simp [natCast_natAbs]

@[simp]
/-
**Int.add_modEq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_modEq_left_iff : a + b ≡ a [ZMOD n] ↔ n ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modEq_left_iff : a + b ≡ a [ZMOD n] ↔ n ∣ b := by
  simp [modEq_iff_dvd]

@[simp]
/-
**Int.add_modEq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_modEq_right_iff : a + b ≡ b [ZMOD n] ↔ n ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.add_modEq_left_iff`：add_modEq_left_iff : a + b ≡ a [ZMOD n] ↔ n ∣ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_modEq_right_iff : a + b ≡ b [ZMOD n] ↔ n ∣ a := by
  rw [add_comm, add_modEq_left_iff]

@[simp]
/-
**Int.left_modEq_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：left_modEq_add_iff : a ≡ a + b [ZMOD n] ↔ n ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_comm`：modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]
· 使用定理 `Int.add_modEq_left_iff`：add_modEq_left_iff : a + b ≡ a [ZMOD n] ↔ n ∣ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem left_modEq_add_iff : a ≡ a + b [ZMOD n] ↔ n ∣ b := by
  rw [modEq_comm, add_modEq_left_iff]

@[simp]
/-
**Int.right_modEq_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：right_modEq_add_iff : b ≡ a + b [ZMOD n] ↔ n ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_comm`：modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n]
· 使用定理 `Int.add_modEq_right_iff`：add_modEq_right_iff : a + b ≡ b [ZMOD n] ↔ n ∣ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem right_modEq_add_iff : b ≡ a + b [ZMOD n] ↔ n ∣ a := by
  rw [modEq_comm, add_modEq_right_iff]

@[simp]
/-
**Int.add_modulus_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_modulus_modEq_iff : a + n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_emod_right`：∀ (a b : ℤ), (a + b) % b = a % b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modulus_modEq_iff : a + n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.modulus_add_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modulus_add_modEq_iff : n + a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.add_modulus_modEq_iff`：add_modulus_modEq_iff : a + n ≡ b [ZMOD n] ↔ 
a ≡ b [ZMOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modulus_add_modEq_iff : n + a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [add_comm, add_modulus_modEq_iff]

@[simp]
/-
**Int.modEq_add_modulus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_add_modulus_iff : a ≡ b + n [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_emod_right`：∀ (a b : ℤ), (a + b) % b = a % b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_add_modulus_iff : a ≡ b + n [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.modEq_modulus_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_modulus_add_iff : a ≡ n + b [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_emod_left`：∀ (a b : ℤ), (a + b) % a = b % a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_modulus_add_iff : a ≡ n + b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.add_mul_modulus_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_mul_modulus_modEq_iff : a + b * n ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_mul_emod_self_right`：∀ (a b c : ℤ), (a + b * c) % c = a % c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_mul_modulus_modEq_iff : a + b * n ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.mul_modulus_add_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mul_modulus_add_modEq_iff : b * n + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.add_mul_modulus_modEq_iff`：add_mul_modulus_modEq_iff : a + b * n ≡ c
 [ZMOD n] ↔ a ≡ c [ZMOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_modulus_add_modEq_iff : b * n + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm, add_mul_modulus_modEq_iff]

@[simp]
/-
**Int.modEq_add_mul_modulus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_add_mul_modulus_iff : a ≡ b + c * n [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_mul_emod_self_right`：∀ (a b c : ℤ), (a + b * c) % c = a % c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_add_mul_modulus_iff : a ≡ b + c * n [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.modEq_mul_modulus_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_mul_modulus_add_iff : a ≡ b * n + c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.modEq_add_mul_modulus_iff`：modEq_add_mul_modulus_iff : a ≡ b + c * n
 [ZMOD n] ↔ a ≡ b [ZMOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_mul_modulus_add_iff : a ≡ b * n + c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm, modEq_add_mul_modulus_iff]

@[simp]
/-
**Int.add_modulus_mul_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_modulus_mul_modEq_iff : a + n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_mul_emod_self_left`：∀ (a b c : ℤ), (a + b * c) % b = a % b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_modulus_mul_modEq_iff : a + n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.modulus_mul_add_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modulus_mul_add_modEq_iff : n * b + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.add_modulus_mul_modEq_iff`：add_modulus_mul_modEq_iff : a + n * b ≡ c
 [ZMOD n] ↔ a ≡ c [ZMOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modulus_mul_add_modEq_iff : n * b + a ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm, add_modulus_mul_modEq_iff]

@[simp]
/-
**Int.modEq_add_modulus_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_add_modulus_mul_iff : a ≡ b + n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_mul_emod_self_left`：∀ (a b c : ℤ), (a + b * c) % b = a % b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_add_modulus_mul_iff : a ≡ b + n * c [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp [ModEq]

@[simp]
/-
**Int.modEq_modulus_mul_add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_modulus_mul_add_iff : a ≡ n * b + c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.modEq_add_modulus_mul_iff`：modEq_add_modulus_mul_iff : a ≡ b + n * c
 [ZMOD n] ↔ a ≡ b [ZMOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_modulus_mul_add_iff : a ≡ n * b + c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [add_comm, modEq_add_modulus_mul_iff]

@[simp]
/-
**Int.sub_modulus_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sub_modulus_modEq_iff : a - n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.add_modulus_modEq_iff`：add_modulus_modEq_iff : a + n ≡ b [ZMOD n] ↔ 
a ≡ b [ZMOD n]
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_modulus_modEq_iff : a - n ≡ b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [← add_modulus_modEq_iff, sub_add_cancel]

@[simp]
/-
**Int.sub_modulus_mul_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sub_modulus_mul_modEq_iff : a - n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.add_modulus_mul_modEq_iff`：add_modulus_mul_modEq_iff : a + n * b ≡ c
 [ZMOD n] ↔ a ≡ c [ZMOD n]
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_modulus_mul_modEq_iff : a - n * b ≡ c [ZMOD n] ↔ a ≡ c [ZMOD n] := by
  rw [← add_modulus_mul_modEq_iff, sub_add_cancel]

@[simp]
/-
**Int.modEq_sub_modulus_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_sub_modulus_iff : a ≡ b - n [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.modEq_add_modulus_iff`：modEq_add_modulus_iff : a ≡ b + n [ZMOD n] ↔ 
a ≡ b [ZMOD n]
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_sub_modulus_iff : a ≡ b - n [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [← modEq_add_modulus_iff, sub_add_cancel]

@[simp]
/-
**Int.modEq_sub_modulus_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_sub_modulus_mul_iff : a ≡ b - n * c [ZMOD n] ↔ a ≡ b [ZMOD n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.modEq_add_modulus_mul_iff`：modEq_add_modulus_mul_iff : a ≡ b + n * c
 [ZMOD n] ↔ a ≡ b [ZMOD n]
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_sub_modulus_mul_iff : a ≡ b - n * c [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  rw [← modEq_add_modulus_mul_iff, sub_add_cancel]
/-
**Int.modEq_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_one : a ≡ b [ZMOD 1]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.modEq_of_dvd`：∀ {n a b : ℤ}, n ∣ b - a → a ≡ b [ZMOD n]
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem modEq_one : a ≡ b [ZMOD 1] :=
  modEq_of_dvd (one_dvd _)
/-
**Int.modEq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_sub (a b : Int) : a ≡ b [ZMOD a - b]
参数：a b : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Int.modEq_of_dvd`：∀ {n a b : ℤ}, n ∣ b - a → a ≡ b [ZMOD n]
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem modEq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
  (modEq_of_dvd dvd_rfl).symm

@[simp]
/-
**Int.modEq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ModEq.eq_1`：∀ (n a b : ℤ), (a ≡ b [ZMOD n]) = (a % n = b % n)
· 使用定理 `Int.emod_zero`：∀ (a : ℤ), a % 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem modEq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b := by rw [ModEq, emod_zero, emod_zero]
/-
**Int.add_modEq_left** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_modEq_left : n + a ≡ a [ZMOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem add_modEq_left : n + a ≡ a [ZMOD n] := by simp
/-
**Int.add_modEq_right** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：add_modEq_right : a + n ≡ a [ZMOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem add_modEq_right : a + n ≡ a [ZMOD n] := by simp
/-
**Int.modEq_and_modEq_iff_modEq_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_and_modEq_iff_modEq_lcm {a b m n : Int} : a ≡ b [ZMOD m] ∧ a ≡ b [ZM
OD n] ↔ a ≡ b [ZMOD m.lcm n]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_and_modEq_iff_modEq_lcm {a b m n : ℤ} :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m.lcm n] := by
  simp only [modEq_iff_dvd, coe_lcm_dvd_iff]
/-
**Int.modEq_and_modEq_iff_modEq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_and_modEq_iff_modEq_mul {a b m n : Int} (hmn : m.natAbs.Coprime n.na
tAbs) : a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n]
参数：hmn : m.natAbs.Coprime n.natAbs。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.lcm_eq_mul_iff`：∀ {m n : ℤ}, m.lcm n = m.natAbs * n.natAbs ↔ m = 0 ∨
 n = 0 ∨ m.gcd n = 1
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Int.modEq_natAbs`：modEq_natAbs : a ≡ b [ZMOD n.natAbs] ↔ a ≡ b [ZMOD n]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Int.modEq_and_modEq_iff_modEq_lcm`：modEq_and_modEq_iff_modEq_lcm {a b m 
n : Int} : a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m.lcm n]
-/
theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℤ} (hmn : m.natAbs.Coprime n.natAbs) :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] := by
  convert! ← modEq_and_modEq_iff_modEq_lcm using 1
  rw [lcm_eq_mul_iff.mpr (.inr <| .inr hmn), ← natAbs_mul, modEq_natAbs]
/-
**Int.gcd_a_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：gcd_a_modEq (a b : Nat) : (a : Int) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b]
参数：a b : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用定理 `Int.ModEq.add_left`：∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] → c + a ≡ c + 
b [ZMOD n]
· 使用定理 `Dvd.dvd.zero_modEq_int`：∀ {n a : ℤ}, n ∣ a → 0 ≡ a [ZMOD n]
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem gcd_a_modEq (a b : ℕ) : (a : ℤ) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b] := by
  rw [← add_zero ((a : ℤ) * _), Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modEq_int.add_left _
/-
**Int.modEq_add_fac_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_add_fac_self {a t n : Int} : a + n * t ≡ a [ZMOD n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem modEq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] := by simp
/-
**Int.mod_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mod_coprime {a b : Nat} (hab : Nat.Coprime a b) : exists y : Int, a * y ≡ 
1 [ZMOD b]
参数：hab : Nat.Coprime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Int.ModEq.instIsTrans`：∀ {n : ℤ}, IsTrans ℤ n.ModEq
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
-/
theorem mod_coprime {a b : ℕ} (hab : Nat.Coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] := by simp
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩
/-
**Int.existsUnique_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：existsUnique_equiv (a : Int) {b : Int} (hb : 0 < b) : exists z : Int, 0 <=
 z ∧ z < b ∧ z ≡ a [ZMOD b]
参数：a : Int；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.emod_lt_abs`：emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < 
|b|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem existsUnique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
  ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
      have : a % b < |b| := emod_lt_abs _ (ne_of_gt hb)
      rwa [abs_of_pos hb] at this, by simp [ModEq]⟩
/-
**Int.existsUnique_equiv_nat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：existsUnique_equiv_nat (a : Int) {b : Int} (hb : 0 < b) : exists z : Nat, 
↑z < b ∧ ↑z ≡ a [ZMOD b]
参数：a : Int；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.existsUnique_equiv`：existsUnique_equiv (a : Int) {b : Int} (hb : 0 <
 b) : exists z : Int, 0 <= z ∧ z < b ∧ z ≡ a [ZMOD b]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
-/
theorem existsUnique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
  let ⟨z, hz1, hz2, hz3⟩ := existsUnique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [natAbs_of_nonneg hz1] <;> assumption⟩
/-
**Int.mod_mul_right_mod** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mod_mul_right_mod (a b c : Int) : a % (b * c) % b = a % b
参数：a b c : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.ModEq.of_mul_right`：of_mul_right (m : Int) : a ≡ b [ZMOD n * m] -> a
 ≡ b [ZMOD n]
· 使用定理 `Int.mod_modEq`：mod_modEq (a n) : a % n ≡ a [ZMOD n]
-/
theorem mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
  (mod_modEq _ _).of_mul_right _
/-
**Int.mod_mul_left_mod** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mod_mul_left_mod (a b c : Int) : a % (b * c) % c = a % c
参数：a b c : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.ModEq.of_mul_left`：of_mul_left (m : Int) (h : a ≡ b [ZMOD m * n]) : 
a ≡ b [ZMOD n]
· 使用定理 `Int.mod_modEq`：mod_modEq (a n) : a % n ≡ a [ZMOD n]
-/
theorem mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
  (mod_modEq _ _).of_mul_left _
/-
**Int.ext_ediv_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ext_ediv_modEq {n a b : Int} (h0 : a / n = b / n) (h1 : a ≡ b [ZMOD n]) : 
a = b
参数：h0 : a / n = b / n；h1 : a ≡ b [ZMOD n]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ext_ediv_emod`：∀ {n a b : ℤ}, a / n = b / n → a % n = b % n → a = b
-/
theorem ext_ediv_modEq {n a b : ℤ} (h0 : a / n = b / n) (h1 : a ≡ b [ZMOD n]) : a = b :=
  ext_ediv_emod h0 h1
/-
**Int.ext_ediv_modEq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ext_ediv_modEq_iff (n a b : Int) : a = b ↔ a / n = b / n ∧ a ≡ b [ZMOD n]
参数：n a b : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ext_ediv_emod_iff`：∀ (n a b : ℤ), a = b ↔ a / n = b / n ∧ a % n = b 
% n
-/
theorem ext_ediv_modEq_iff (n a b : ℤ) : a = b ↔ a / n = b / n ∧ a ≡ b [ZMOD n] :=
  ext_ediv_emod_iff _ _ _
/-
**Int.modEq_iff_eq_of_div_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：modEq_iff_eq_of_div_eq {n a b : Int} (h : a / n = b / n) : a ≡ b [ZMOD n] 
↔ a = b
参数：h : a / n = b / n。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem modEq_iff_eq_of_div_eq {n a b : ℤ} (h : a / n = b / n) :
    a ≡ b [ZMOD n] ↔ a = b := by grind [ext_ediv_modEq_iff]

end Int

