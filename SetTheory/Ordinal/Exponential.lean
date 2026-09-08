/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Ordinal exponential

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `Ordinal.opow_le_iff_le_log : b ^ c ≤ x ↔ c ≤ log b x` for nontrivial inputs
`b`, `c`.
-/

public noncomputable section

open Function Set Equiv Order
open scoped Cardinal Ordinal

universe u v w

namespace Ordinal

/-- The ordinal exponential, defined by transfinite recursion.

We call this `opow` in theorems in order to disambiguate from other exponentials. -/
@[no_expose]
/-
**Ordinal.instPow** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
形式化陈述：instPow : Pow Ordinal Ordinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal exponential, defined by transfinite recursion.

We call this `opow` in theorems in order to disambiguate from other exponentials
.
-/
instance instPow : Pow Ordinal Ordinal :=
  ⟨fun a b ↦ if a = 0 then 1 - b else
    limitRecOn b 1 (fun _ x ↦ x * a) fun o _ f ↦ ⨆ x : Iio o, f x.1 x.2⟩
/-
**Ordinal.opow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem opow_of_ne_zero {a b : Ordinal} (h : a ≠ 0) : a ^ b =
    limitRecOn b 1 (fun _ x ↦ x * a) fun o _ f ↦ ⨆ x : Iio o, f x.1 x.2 :=
  if_neg h

/-- `0 ^ a = 1` if `a = 0` and `0 ^ a = 0` otherwise. -/
/-
**Ordinal.zero_opow'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_opow' (a : Ordinal) : 0 ^ a = 1 - a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t

--- 原说明 ---
`0 ^ a = 1` if `a = 0` and `0 ^ a = 0` otherwise.
-/
theorem zero_opow' (a : Ordinal) : 0 ^ a = 1 - a :=
  if_pos rfl
/-
**Ordinal.zero_opow_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_opow_le (a : Ordinal) : (0 : Ordinal) ^ a <= 1
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow'`：zero_opow' (a : Ordinal) : 0 ^ a = 1 - a
· 使用定理 `Ordinal.sub_le_self`：sub_le_self (a b : Ordinal) : a - b <= a
-/
theorem zero_opow_le (a : Ordinal) : (0 : Ordinal) ^ a ≤ 1 := by
  rw [zero_opow']
  exact sub_le_self 1 a

@[simp]
/-
**Ordinal.zero_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal) ^ a = 0
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow'`：zero_opow' (a : Ordinal) : 0 ^ a = 1 - a
· 使用定理 `Ordinal.sub_eq_zero_iff_le`：∀ {a b : Ordinal.{u_4}}, a - b = 0 ↔ a ≤ b
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem zero_opow {a : Ordinal} (a0 : a ≠ 0) : (0 : Ordinal) ^ a = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
/-
**Ordinal.opow_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow'`：zero_opow' (a : Ordinal) : 0 ^ a = 1 - a
· 使用定理 `Ordinal.sub_zero`：sub_zero (a : Ordinal) : a - 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Exponential.0.Ordinal.opow_of_ne_zero
`：∀ {a b : Ordinal.{u_1}}, a ≠ 0 → a ^ b = Ordinal.limitRecOn b 1 (fun x x_1 => 
x_1 * a) fun o x f => ⨆ x, f ↑x ⋯
· 使用定理 `Ordinal.limitRecOn_zero`：limitRecOn_zero {motive} (H₁ H₂ H₃) : @limitRec
On motive 0 H₁ H₂ H₃ = H₁
-/
theorem opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1 := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow', Ordinal.sub_zero]
  · rw [opow_of_ne_zero h, limitRecOn_zero]

@[simp]
/-
**Ordinal.opow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b * a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Exponential.0.Ordinal.opow_of_ne_zero
`：∀ {a b : Ordinal.{u_1}}, a ≠ 0 → a ^ b = Ordinal.limitRecOn b 1 (fun x x_1 => 
x_1 * a) fun o x f => ⨆ x, f ↑x ⋯
· 使用定理 `Ordinal.limitRecOn_add_one`：limitRecOn_add_one {motive} (o H₁ H₂ H₃) : @
limitRecOn motive (o + 1) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃)
-/
theorem opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b * a := by
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_opow (add_pos_of_right zero_lt_one b).ne', mul_zero]
  · rw [opow_of_ne_zero h, opow_of_ne_zero h]
    exact limitRecOn_add_one ..

-- TODO: deprecate
/-
**Ordinal.opow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
-/
theorem opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a :=
  opow_add_one a b
/-
**Ordinal.opow_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_limit {a b : Ordinal} (ha : a != 0) (hb : IsSuccLimit b) : a ^ b = ⨆ 
x : Iio b, a ^ x.1
参数：ha : a != 0；hb : IsSuccLimit b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Exponential.0.Ordinal.opow_of_ne_zero
`：∀ {a b : Ordinal.{u_1}}, a ≠ 0 → a ^ b = Ordinal.limitRecOn b 1 (fun x x_1 => 
x_1 * a) fun o x f => ⨆ x, f ↑x ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.limitRecOn_limit`：limitRecOn_limit {motive} (o H₁ H₂ H₃ h) : @li
mitRecOn motive o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn motive x H₁ H₂ H₃
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opow_limit {a b : Ordinal} (ha : a ≠ 0) (hb : IsSuccLimit b) :
    a ^ b = ⨆ x : Iio b, a ^ x.1 := by
  simp_rw [opow_of_ne_zero ha, limitRecOn_limit _ _ _ _ hb]
/-
**Ordinal.opow_le_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_of_isSuccLimit {a b c : Ordinal} (a0 : a != 0) (h : IsSuccLimit b)
 : a ^ b <= c ↔ forall b' < b, a ^ b' <= c
参数：a0 : a != 0；h : IsSuccLimit b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_limit`：opow_limit {a b : Ordinal} (ha : a != 0) (hb : IsSuc
cLimit b) : a ^ b = ⨆ x : Iio b, a ^ x.1
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem opow_le_of_isSuccLimit {a b c : Ordinal} (a0 : a ≠ 0) (h : IsSuccLimit b) :
    a ^ b ≤ c ↔ ∀ b' < b, a ^ b' ≤ c := by
  rw [opow_limit a0 h, Ordinal.iSup_le_iff, Subtype.forall]
  rfl
/-
**Ordinal.lt_opow_of_isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_opow_of_isSuccLimit {a b c : Ordinal} (b0 : b != 0) (h : IsSuccLimit c)
 : a < b ^ c ↔ exists c' < c, a < b ^ c'
参数：b0 : b != 0；h : IsSuccLimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ordinal.opow_le_of_isSuccLimit`：opow_le_of_isSuccLimit {a b c : Ordinal}
 (a0 : a != 0) (h : IsSuccLimit b) : a ^ b <= c ↔ forall b' < b, a ^ b' <= c
-/
theorem lt_opow_of_isSuccLimit {a b c : Ordinal} (b0 : b ≠ 0) (h : IsSuccLimit c) :
    a < b ^ c ↔ ∃ c' < c, a < b ^ c' := by
  simpa using (opow_le_of_isSuccLimit b0 h).not

@[simp]
/-
**Ordinal.opow_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
-/
theorem opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a := by
  simpa using opow_add_one a 0

@[simp]
/-
**Ordinal.one_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Ordinal.opow_le_of_isSuccLimit`：opow_le_of_isSuccLimit {a b c : Ordinal}
 (a0 : a != 0) (h : IsSuccLimit b) : a ^ b <= c ↔ forall b' < b, a ^ b' <= c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
-/
theorem one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1 := by
  induction a using limitRecOn with
  | zero => simp
  | add_one _ IH => simp [IH, mul_one]
  | limit b l IH =>
    refine eq_of_forall_ge_iff fun c => ?_
    rw [opow_le_of_isSuccLimit one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.bot_lt, fun H b' h => by rwa [IH _ h]⟩
/-
**Ordinal.opow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 < a ^ b
参数：b : Ordinal；a0 : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.lt_opow_of_isSuccLimit`：lt_opow_of_isSuccLimit {a b c : Ordinal}
 (b0 : b != 0) (h : IsSuccLimit c) : a < b ^ c ↔ exists c' < c, a < b ^ c'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Order.IsSuccLimit.pos`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [ins
t_1 : Zero α] [IsBotZeroClass α], Order.IsSuccLimit a → 0 < a
-/
theorem opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 < a ^ b := by
  have h0 : 0 < a ^ (0 : Ordinal) := by simp
  induction b using limitRecOn with
  | zero => exact h0
  | add_one b IH => simpa using mul_pos IH a0
  | limit b l _ => exact (lt_opow_of_isSuccLimit (pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩
/-
**Ordinal.opow_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a != 0) : a ^ b != 0
参数：b : Ordinal；a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a ≠ 0) : a ^ b ≠ 0 :=
  pos_iff_ne_zero.1 <| opow_pos b <| pos_iff_ne_zero.2 a0

@[simp]
/-
**Ordinal.opow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧ b ≠ 0 := by
  by_cases a = 0 <;> by_cases b = 0 <;> simp_all [opow_ne_zero]

@[simp, norm_cast]
/-
**Ordinal.opow_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Ordinal) = a ^ n
参数：a : Ordinal；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem opow_natCast (a : Ordinal) (n : ℕ) : a ^ (n : Ordinal) = a ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, opow_zero, pow_zero]
  | succ n IH => rw [Nat.cast_succ, ← succ_eq_add_one, opow_succ, pow_succ, IH]
/-
**Ordinal.isNormal_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNormal (a ^ · : Ordinal -> Ord
inal)
参数：h : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Order.IsNormal.of_succ_lt`：of_succ_lt (hs : forall a, f a < f (succ a)) 
(hl : forall {a}, IsSuccLimit a -> IsLUB (f '' Iio a) (f a)) : IsNormal f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_le_of_isSuccLimit`：opow_le_of_isSuccLimit {a b c : Ordinal}
 (a0 : a != 0) (h : IsSuccLimit b) : a ^ b <= c ↔ forall b' < b, a ^ b' <= c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isNormal_opow {a : Ordinal} (h : 1 < a) : IsNormal (a ^ · : Ordinal → Ordinal) := by
  have ha : 0 < a := zero_lt_one.trans h
  refine IsNormal.of_succ_lt ?_ fun hl ↦ ?_
  · simpa only [mul_one, opow_succ] using fun b ↦ mul_lt_mul_of_pos_left h (opow_pos b ha)
  · simp [IsLUB, IsLeast, upperBounds, lowerBounds, ← opow_le_of_isSuccLimit ha.ne' hl]

@[simp]
/-
**Ordinal.opow_lt_opow_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b 
< c
参数：a1 : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
-/
theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
  (isNormal_opow a1).strictMono.lt_iff_lt

@[simp]
/-
**Ordinal.opow_le_opow_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b <= a ^ c ↔ b
 <= c
参数：a1 : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
-/
theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
  (isNormal_opow a1).strictMono.le_iff_le

@[simp]
/-
**Ordinal.opow_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c
参数：a1 : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
-/
theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
  (isNormal_opow a1).strictMono.injective.eq_iff

@[simp]
/-
**Ordinal.one_lt_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_lt_opow {a b : Ordinal} : 1 < a ^ b ↔ 1 < a ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.zero_opow_le`：zero_opow_le (a : Ordinal) : (0 : Ordinal) ^ a <= 
1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
-/
theorem one_lt_opow {a b : Ordinal} : 1 < a ^ b ↔ 1 < a ∧ b ≠ 0 := by
  refine ⟨?_, fun ⟨ha, hb⟩ ↦ ?_⟩
  · contrapose! +distrib
    rw [le_one_iff]
    rintro ((rfl | rfl) | rfl)
    · exact zero_opow_le b
    · simp
    · simp
  · rwa [← opow_zero a, opow_lt_opow_iff_right ha, pos_iff_ne_zero]

@[simp]
/-
**Ordinal.one_lt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：one_lt_pow {a : Ordinal} {n : Nat} : 1 < a ^ n ↔ 1 < a ∧ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
· 使用定理 `Ordinal.one_lt_opow`：one_lt_opow {a b : Ordinal} : 1 < a ^ b ↔ 1 < a ∧ b
 != 0
-/
theorem one_lt_pow {a : Ordinal} {n : ℕ} : 1 < a ^ n ↔ 1 < a ∧ n ≠ 0 :=
  mod_cast one_lt_opow (b := n)

@[simp]
/-
**Ordinal.opow_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_eq_one_iff {a b : Ordinal} : a ^ b = 1 ↔ a = 1 ∨ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem opow_eq_one_iff {a b : Ordinal} : a ^ b = 1 ↔ a = 1 ∨ b = 0 := by
  refine ⟨fun h ↦ ?_, by simp +contextual [or_imp]⟩
  contrapose! h
  obtain ha | ha := le_or_gt a 1
  · simp_all [le_one_iff]
  · simpa using ((opow_lt_opow_iff_right ha).2 h.2.pos).ne'

@[simp]
/-
**Ordinal.pow_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：pow_eq_one_iff {a : Ordinal} {n : Nat} : a ^ n = 1 ↔ a = 1 ∨ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
· 使用定理 `Ordinal.opow_eq_one_iff`：opow_eq_one_iff {a b : Ordinal} : a ^ b = 1 ↔ a
 = 1 ∨ b = 0
-/
theorem pow_eq_one_iff {a : Ordinal} {n : ℕ} : a ^ n = 1 ↔ a = 1 ∨ n = 0 :=
  mod_cast opow_eq_one_iff (b := n)
/-
**Ordinal.isSuccLimit_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_opow {a b : Ordinal} (a1 : 1 < a) : IsSuccLimit b -> IsSuccLim
it (a ^ b)
参数：a1 : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.map_isSuccLimit`：map_isSuccLimit (hf : IsNormal f) (ha : 
IsSuccLimit a) : IsSuccLimit (f a)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
-/
theorem isSuccLimit_opow {a b : Ordinal} (a1 : 1 < a) : IsSuccLimit b → IsSuccLimit (a ^ b) :=
  (isNormal_opow a1).map_isSuccLimit
/-
**Ordinal.isSuccLimit_opow_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_opow_left {a b : Ordinal} (l : IsSuccLimit a) (hb : b != 0) : 
IsSuccLimit (a ^ b)
参数：l : IsSuccLimit a；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.zero_or_succ_or_isSuccLimit`：zero_or_succ_or_isSuccLimit (o : Or
dinal) : o = 0 ∨ o in range succ ∨ IsSuccLimit o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `Ordinal.isSuccLimit_mul_right`：isSuccLimit_mul_right {a b : Ordinal} (a0
 : 0 < a) (l : IsSuccLimit b) : IsSuccLimit (a * b)
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Order.IsSuccLimit.bot_lt`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [
inst_1 : OrderBot α], Order.IsSuccLimit a → ⊥ < a
· 使用定理 `Ordinal.isSuccLimit_opow`：isSuccLimit_opow {a b : Ordinal} (a1 : 1 < a) 
: IsSuccLimit b -> IsSuccLimit (a ^ b)
· 使用定理 `Ordinal.one_lt_of_isSuccLimit`：one_lt_of_isSuccLimit {o : Ordinal} (h : 
IsSuccLimit o) : 1 < o
-/
theorem isSuccLimit_opow_left {a b : Ordinal} (l : IsSuccLimit a) (hb : b ≠ 0) :
    IsSuccLimit (a ^ b) := by
  rcases zero_or_succ_or_isSuccLimit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
  · rw [opow_succ]
    exact isSuccLimit_mul_right (opow_pos _ l.bot_lt) l
  · exact isSuccLimit_opow (one_lt_of_isSuccLimit l) l'
/-
**Ordinal.opow_le_opow_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b <= c) : a ^ b <=
 a ^ c
参数：h₁ : 0 < a；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `Ordinal.opow_le_opow_iff_right`：opow_le_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b <= a ^ c ↔ b <= c
-/
theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c := by
  rcases (one_le_iff_pos.2 h₁).eq_or_lt' with h₁ | h₁
  · simp_all
  · exact (opow_le_opow_iff_right h₁).2 h₂

@[gcongr]
/-
**Ordinal.opow_le_opow_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_opow_left {a b : Ordinal} (c : Ordinal) (ab : a <= b) : a ^ c <= b
 ^ c
参数：c : Ordinal；ab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.opow_le_of_isSuccLimit`：opow_le_of_isSuccLimit {a b c : Ordinal}
 (a0 : a != 0) (h : IsSuccLimit b) : a ^ b <= c ↔ forall b' < b, a ^ b' <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.opow_le_opow_right`：opow_le_opow_right {a b c : Ordinal} (h₁ : 0
 < a) (h₂ : b <= c) : a ^ b <= a ^ c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem opow_le_opow_left {a b : Ordinal} (c : Ordinal) (ab : a ≤ b) : a ^ c ≤ b ^ c := by
  by_cases ha : a = 0
  · by_cases c = 0 <;> simp_all
  · induction c using limitRecOn with
    | zero => simp
    | add_one c IH => simpa using mul_le_mul' IH ab
    | limit c l IH =>
      exact (opow_le_of_isSuccLimit ha l).2 fun b' h ↦
        (IH _ h).trans (opow_le_opow_right ((pos_iff_ne_zero.2 ha).trans_le ab) h.le)

@[gcongr]
/-
**Ordinal.opow_le_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_opow {a b c d : Ordinal} (hac : a <= c) (hbd : b <= d) (hc : 0 < c
) : a ^ b <= c ^ d
参数：hac : a <= c；hbd : b <= d；hc : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.opow_le_opow_left`：opow_le_opow_left {a b : Ordinal} (c : Ordina
l) (ab : a <= b) : a ^ c <= b ^ c
· 使用定理 `Ordinal.opow_le_opow_right`：opow_le_opow_right {a b c : Ordinal} (h₁ : 0
 < a) (h₂ : b <= c) : a ^ b <= a ^ c
-/
theorem opow_le_opow {a b c d : Ordinal} (hac : a ≤ c) (hbd : b ≤ d) (hc : 0 < c) : a ^ b ≤ c ^ d :=
  (opow_le_opow_left b hac).trans (opow_le_opow_right hc hbd)
/-
**Ordinal.left_le_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a <= a ^ b
参数：a : Ordinal；b1 : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.opow_le_opow_iff_right`：opow_le_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b <= a ^ c ↔ b <= c
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
-/
theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a ≤ a ^ b := by
  nth_rw 1 [← opow_one a]
  rcases le_or_gt a 1 with a1 | a1
  · rcases lt_or_eq_of_le a1 with a0 | a1
    · rw [lt_one_iff] at a0
      rw [a0, zero_opow one_ne_zero]
      exact zero_le
    rw [a1, one_opow, one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]
/-
**Ordinal.left_lt_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 < b) : a < a ^ b
参数：ha : 1 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
-/
theorem left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 < b) : a < a ^ b := by
  conv_lhs => rw [← opow_one a]
  rwa [opow_lt_opow_iff_right ha]
/-
**Ordinal.right_le_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1 < a) : b <= a ^ b
参数：b : Ordinal；a1 : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
-/
theorem right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1 < a) : b ≤ a ^ b :=
  (isNormal_opow a1).strictMono.le_apply
/-
**Ordinal.opow_lt_opow_left_of_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : a ^ succ c < b 
^ succ c
参数：ab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `mul_lt_mul_of_le_of_lt_of_nonneg_of_pos`：mul_lt_mul_of_le_of_lt_of_nonne
g_of_pos [PosMulStrictMono α] [MulPosMono α] (h₁ : a <= b) (h₂ : c < d) (c0 : 0 
<= c) (b0 : 0 < b) : a * c < …
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `MulRightMono.toMulPosMono`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zer
o α] [inst_2 : Preorder α] [MulRightMono α], MulPosMono α
· 使用定理 `Ordinal.opow_le_opow_left`：opow_le_opow_left {a b : Ordinal} (c : Ordina
l) (ab : a <= b) : a ^ c <= b ^ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `LT.lt.bot_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
-/
theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : a ^ succ c < b ^ succ c := by
  rw [opow_succ, opow_succ]
  exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (by gcongr) ab zero_le (opow_pos _ ab.bot_lt)
/-
**Ordinal.opow_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^ c
参数：a b c : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Order.IsNormal.le_iff_forall_le`：le_iff_forall_le (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : f a <= b ↔ forall a' < a, f a' <= b
· 使用定理 `Order.IsNormal.comp`：comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal
 (g ∘ f)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 36 条，此处仅展示前 30 条）
-/
theorem opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^ c := by
  obtain rfl | ha := eq_zero_or_pos a
  · obtain rfl | hc := eq_zero_or_pos c; · simp
    have : b + c ≠ 0 := (hc.trans_le le_add_self).ne'
    rw [zero_opow hc.ne', zero_opow, mul_zero]
    exact (hc.trans_le le_add_self).ne'
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha.ne').eq_or_lt; · simp
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [← add_assoc, opow_add_one, IH, opow_add_one, mul_assoc]
  | limit c l IH =>
    refine eq_of_forall_ge_iff fun d ↦
      (((isNormal_opow ha').comp (isNormal_add_right b)).le_iff_forall_le l).trans ?_
    simpa +contextual [IH] using
      (((isNormal_mul_right <| opow_pos b (pos_iff_ne_zero.2 ha.ne')).comp
        (isNormal_opow ha')).le_iff_forall_le l).symm
/-
**Ordinal.opow_one_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a ^ b
参数：a b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
-/
theorem opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a ^ b := by rw [opow_add, opow_one]
/-
**Ordinal.opow_dvd_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : b <= c) : a ^ b ∣ a ^ c
参数：a : Ordinal；h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
-/
theorem opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : b ≤ c) : a ^ b ∣ a ^ c :=
  ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩
/-
**Ordinal.opow_dvd_opow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b <= c
参数：a1 : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.opow_lt_opow_iff_right`：opow_lt_opow_iff_right {a b c : Ordinal}
 (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c
· 使用定理 `Ordinal.le_of_dvd`：le_of_dvd {a b : Ordinal} (b0 : b != 0) (h : a ∣ b) :
 a <= b
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordinal.opow_dvd_opow`：opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : 
b <= c) : a ^ b ∣ a ^ c
-/
theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_gt fun hn =>
      not_le_of_gt ((opow_lt_opow_iff_right a1).2 hn) <|
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩
/-
**Ordinal.opow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c
参数：a b c : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
· 使用定理 `Ordinal.opow_add_one`：opow_add_one (a b : Ordinal) : a ^ (b + 1) = a ^ b
 * a
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Order.IsNormal.le_iff_forall_le`：le_iff_forall_le (hf : IsNormal f) (ha 
: IsSuccLimit a) {b : β} : f a <= b ↔ forall a' < a, f a' <= b
· 使用定理 `Order.IsNormal.comp`：comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal
 (g ∘ f)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
（共 36 条，此处仅展示前 30 条）
-/
theorem opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c := by
  obtain rfl | hb := eq_zero_or_pos b; · simp
  obtain rfl | ha := eq_or_ne a 0
  · have := hb.ne'
    by_cases c = 0 <;> simp_all
  obtain rfl | ha' := (one_le_iff_ne_zero.2 ha).eq_or_lt; · simp
  induction c using limitRecOn with
  | zero => simp
  | add_one c IH => rw [mul_add_one, opow_add, IH, opow_add_one]
  | limit c l IH =>
    refine eq_of_forall_ge_iff fun d ↦
      (((isNormal_opow ha').comp (isNormal_mul_right hb)).le_iff_forall_le l).trans ?_
    simpa +contextual [IH] using (opow_le_of_isSuccLimit (opow_ne_zero _ ha) l).symm
/-
**Ordinal.opow_mul_add_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_mul_add_pos {b v : Ordinal} (hb : b != 0) (u : Ordinal) (hv : v != 0)
 (w : Ordinal) : 0 < b ^ u * v + w
参数：hb : b != 0；u : Ordinal；hv : v != 0；w : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.le_mul_left`：le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b
) : a <= a * b
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
-/
theorem opow_mul_add_pos {b v : Ordinal} (hb : b ≠ 0) (u : Ordinal) (hv : v ≠ 0) (w : Ordinal) :
    0 < b ^ u * v + w :=
  (opow_pos u <| pos_iff_ne_zero.2 hb).trans_le <|
    (le_mul_left _ <| pos_iff_ne_zero.2 hv).trans le_self_add
/-
**Ordinal.opow_mul_add_lt_opow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_mul_add_lt_opow_mul {b u w x : Ordinal} {v : Ordinal} (hw : w < b ^ u
) (hv : v < x) : b ^ u * v + w < b ^ u * x
参数：hw : w < b ^ u；hv : v < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Order.add_one_le_of_lt`：add_one_le_of_lt (h : x < y) : x + 1 <= y
-/
theorem opow_mul_add_lt_opow_mul {b u w x : Ordinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x) :
    b ^ u * v + w < b ^ u * x := by
  apply lt_of_lt_of_le (b := b ^ u * (v + 1))
  · rwa [mul_add_one, add_lt_add_iff_left]
  · grw [add_one_le_of_lt hv]
/-
**Ordinal.opow_mul_add_lt_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_mul_add_lt_opow {b u v w x : Ordinal} (hv : v < b) (hw : w < b ^ u) (
hu : u < x) : b ^ u * v + w < b ^ x
参数：hv : v < b；hw : w < b ^ u；hu : u < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.opow_mul_add_lt_opow_mul`：opow_mul_add_lt_opow_mul {b u w x : Or
dinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x) : b ^ u * v + w < b ^ u * x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `Ordinal.opow_le_opow_right`：opow_le_opow_right {a b c : Ordinal} (h₁ : 0
 < a) (h₂ : b <= c) : a ^ b <= a ^ c
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
-/
theorem opow_mul_add_lt_opow {b u v w x : Ordinal} (hv : v < b) (hw : w < b ^ u) (hu : u < x) :
    b ^ u * v + w < b ^ x := by
  apply (opow_mul_add_lt_opow_mul hw hv).trans_le
  rw [← opow_succ]
  exact opow_le_opow_right hv.pos (succ_le_of_lt hu)
/-
**Ordinal.opow_mul_lt_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_mul_lt_opow {b u v x : Ordinal} (hv : v < b) (hu : u < x) : b ^ u * v
 < b ^ x
参数：hv : v < b；hu : u < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.opow_mul_add_lt_opow`：opow_mul_add_lt_opow {b u v w x : Ordinal}
 (hv : v < b) (hw : w < b ^ u) (hu : u < x) : b ^ u * v + w < b ^ x
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem opow_mul_lt_opow {b u v x : Ordinal} (hv : v < b) (hu : u < x) : b ^ u * v < b ^ x := by
  simpa using opow_mul_add_lt_opow hv (opow_pos _ hv.pos) hu

/-! ### Ordinal logarithm -/

/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
`w < b ^ u`.

We special case `log 0 x = log 1 x = 0`, as well as `log b 0 = 0`. -/
@[pp_nodot]
/-
**Ordinal.log** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：log (b x : Ordinal) : Ordinal
参数：b x : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` wh
ere `v < b` and
`w < b ^ u`.

We special case `log 0 x = log 1 x = 0`, as well as `log b 0 = 0`.
-/
def log (b x : Ordinal) : Ordinal :=
  sSup ((b ^ ·) ⁻¹' Iic x)

@[simp]
/-
**Ordinal.log_of_left_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_of_left_le_one {b : Ordinal} (h : b <= 1) (x : Ordinal) : log b x = 0
参数：h : b <= 1；x : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `not_bddAbove_Ici`：not_bddAbove_Ici : ¬BddAbove (Ici a)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `Set.preimage_const`：preimage_const (b : β) (s : Set β) [Decidable (b in 
s)] : (fun _ : α => b) ⁻¹' s = if b in s then univ else ∅
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem log_of_left_le_one {b : Ordinal} (h : b ≤ 1) (x : Ordinal) : log b x = 0 := by
  obtain rfl | rfl := le_one_iff.1 h
  · apply (csSup_of_not_bddAbove _).trans csSup_empty
    by_contra! hb
    refine not_bddAbove_Ici 1 (hb.mono fun a ↦ ?_)
    simp +contextual [one_le_iff_ne_zero]
  · simp_rw [log, one_opow, preimage_const]
    split_ifs <;> simp
/-
**Ordinal.log_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_zero_left (x : Ordinal) : log 0 x = 0
参数：x : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_zero_left (x : Ordinal) : log 0 x = 0 := by simp
/-
**Ordinal.log_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_one_left (x : Ordinal) : log 1 x = 0
参数：x : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem log_one_left (x : Ordinal) : log 1 x = 0 := by simp

@[simp]
/-
**Ordinal.log_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_zero_right (b : Ordinal) : log b 0 = 0
参数：b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Ordinal.log_zero_left`：log_zero_left (x : Ordinal) : log 0 x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.SetTheory.Ordinal.Exponential.0.Ordinal.log.eq_1`：∀ (b 
x : Ordinal.{u_1}), Ordinal.log b x = sSup ((fun x => b ^ x) ⁻¹' Set.Iic x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
-/
theorem log_zero_right (b : Ordinal) : log b 0 = 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · exact log_zero_left 0
  · rw [log]
    convert! csSup_empty
    aesop

/-- `opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. See also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implications under weaker
assumptions. -/
/-
**Ordinal.opow_le_iff_le_log** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x != 0) : b ^ c <=
 x ↔ c <= log b x
参数：hb : 1 < b；hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.le_iff_le_sSup'`：le_iff_le_sSup' [WellFoundedLT α] {f : α
 -> α} (hf : IsNormal f) {x y : α} (h : (f ⁻¹' Iic y).Nonempty) : f x <= y ↔ x <
= sSup (f ⁻¹' Iic y)
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
`opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. Se
e also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implication
s under weaker
assumptions.
-/
theorem opow_le_iff_le_log {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) :
    b ^ c ≤ x ↔ c ≤ log b x :=
  (isNormal_opow hb).le_iff_le_sSup' ⟨0, by simpa [one_le_iff_ne_zero]⟩

/-- `opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implications under weaker
assumptions. -/
/-
**Ordinal.opow_le_iff_le_log'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_iff_le_log' {b x c : Ordinal} (hb : 1 < b) (hc : c != 0) : b ^ c <
= x ↔ c <= log b x
参数：hb : 1 < b；hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x

--- 原说明 ---
`opow b` and `log b` (almost) form a Galois connection.

See `opow_le_iff_le_log` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See
 also
`le_log_of_opow_le` and `opow_le_of_le_log`, which are both separate implication
s under weaker
assumptions.
-/
theorem opow_le_iff_le_log' {b x c : Ordinal} (hb : 1 < b) (hc : c ≠ 0) :
    b ^ c ≤ x ↔ c ≤ log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa [hc] using hb.ne_bot
  · exact opow_le_iff_le_log hb hx
/-
**Ordinal.le_log_of_opow_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_log_of_opow_le {b x c : Ordinal} (hb : 1 < b) (h : b ^ c <= x) : c <= l
og b x
参数：hb : 1 < b；h : b ^ c <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.opow_eq_zero`：opow_eq_zero {a b : Ordinal} : a ^ b = 0 ↔ a = 0 ∧
 b != 0
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x
-/
theorem le_log_of_opow_le {b x c : Ordinal} (hb : 1 < b) (h : b ^ c ≤ x) : c ≤ log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [nonpos_iff_eq_zero, opow_eq_zero] at h
    exact (zero_lt_one.asymm <| h.1 ▸ hb).elim
  · exact (opow_le_iff_le_log hb hx).1 h
/-
**Ordinal.opow_le_of_le_log** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_le_of_le_log {b x c : Ordinal} (hc : c != 0) (h : c <= log b x) : b ^
 c <= x
参数：hc : c != 0；h : c <= log b x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_le_iff_le_log'`：opow_le_iff_le_log' {b x c : Ordinal} (hb :
 1 < b) (hc : c != 0) : b ^ c <= x ↔ c <= log b x
-/
theorem opow_le_of_le_log {b x c : Ordinal} (hc : c ≠ 0) (h : c ≤ log b x) : b ^ c ≤ x := by
  obtain hb | hb := le_or_gt b 1
  · rw [log_of_left_le_one hb] at h
    exact (h.not_gt (pos_iff_ne_zero.2 hc)).elim
  · rwa [opow_le_iff_le_log' hb hc]

/-- `opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. See also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implications under weaker
assumptions. -/
/-
**Ordinal.lt_opow_iff_log_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x != 0) : x < b ^ 
c ↔ log b x < c
参数：hb : 1 < b；hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x

--- 原说明 ---
`opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt'` for a variant assuming `c ≠ 0` rather than `x ≠ 0`. Se
e also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implication
s under weaker
assumptions.
-/
theorem lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1 < b) (hx : x ≠ 0) : x < b ^ c ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log hb hx)

/-- `opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implications under weaker
assumptions. -/
/-
**Ordinal.lt_opow_iff_log_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_opow_iff_log_lt' {b x c : Ordinal} (hb : 1 < b) (hc : c != 0) : x < b ^
 c ↔ log b x < c
参数：hb : 1 < b；hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Ordinal.opow_le_iff_le_log'`：opow_le_iff_le_log' {b x c : Ordinal} (hb :
 1 < b) (hc : c != 0) : b ^ c <= x ↔ c <= log b x

--- 原说明 ---
`opow b` and `log b` (almost) form a Galois connection.

See `lt_opow_iff_log_lt` for a variant assuming `x ≠ 0` rather than `c ≠ 0`. See
 also
`lt_opow_of_log_lt` and `lt_log_of_lt_opow`, which are both separate implication
s under weaker
assumptions.
-/
theorem lt_opow_iff_log_lt' {b x c : Ordinal} (hb : 1 < b) (hc : c ≠ 0) : x < b ^ c ↔ log b x < c :=
  lt_iff_lt_of_le_iff_le (opow_le_iff_le_log' hb hc)
/-
**Ordinal.lt_opow_of_log_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_opow_of_log_lt {b x c : Ordinal} (hb : 1 < b) : log b x < c -> x < b ^ 
c
参数：hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Ordinal.le_log_of_opow_le`：le_log_of_opow_le {b x c : Ordinal} (hb : 1 <
 b) (h : b ^ c <= x) : c <= log b x
-/
theorem lt_opow_of_log_lt {b x c : Ordinal} (hb : 1 < b) : log b x < c → x < b ^ c :=
  lt_imp_lt_of_le_imp_le <| le_log_of_opow_le hb
/-
**Ordinal.lt_log_of_lt_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_log_of_lt_opow {b x c : Ordinal} (hc : c != 0) : x < b ^ c -> log b x <
 c
参数：hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `Ordinal.opow_le_of_le_log`：opow_le_of_le_log {b x c : Ordinal} (hc : c !
= 0) (h : c <= log b x) : b ^ c <= x
-/
theorem lt_log_of_lt_opow {b x c : Ordinal} (hc : c ≠ 0) : x < b ^ c → log b x < c :=
  lt_imp_lt_of_le_imp_le <| opow_le_of_le_log hc
/-
**Ordinal.lt_opow_succ_log_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) : x < b ^ s
ucc (log b x)
参数：hb : 1 < b；x : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_opow_iff_log_lt`：lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : x < b ^ c ↔ log b x < c
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) :
    x < b ^ succ (log b x) := by
  obtain rfl | hx := eq_or_ne x 0
  · simpa using hb.pos
  · rw [lt_opow_iff_log_lt hb hx, lt_succ_iff]
/-
**Ordinal.opow_log_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：opow_log_le_self (b : Ordinal) {x : Ordinal} (hx : x != 0) : b ^ log b x <
= x
参数：b : Ordinal；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem opow_log_le_self (b : Ordinal) {x : Ordinal} (hx : x ≠ 0) : b ^ log b x ≤ x := by
  obtain hb | hb := le_or_gt b 1
  · rw [← one_le_iff_ne_zero] at hx
    obtain rfl | rfl := le_one_iff.1 hb <;> simpa
  · rw [opow_le_iff_le_log hb hx]
/-
**Ordinal.log_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_pos {b o : Ordinal} (hb : 1 < b) (ho : o != 0) (hbo : b <= o) : 0 < lo
g b o
参数：hb : 1 < b；ho : o != 0；hbo : b <= o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.add_one_le_iff`：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
-/
theorem log_pos {b o : Ordinal} (hb : 1 < b) (ho : o ≠ 0) (hbo : b ≤ o) : 0 < log b o := by
  rwa [← add_one_le_iff, zero_add, ← opow_le_iff_le_log hb ho, opow_one]
/-
**Ordinal.log_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0
参数：hbo : o < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.log_zero_left`：log_zero_left (x : Ordinal) : log 0 x = 0
· 使用定理 `Ordinal.log_one_left`：log_one_left (x : Ordinal) : log 1 x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ordinal.lt_opow_iff_log_lt`：lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : x < b ^ c ↔ log b x < c
· 使用定理 `Ordinal.opow_one`：opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a
-/
theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  rcases le_or_gt b 1 with hb | hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← nonpos_iff_eq_zero, ← lt_add_one_iff, zero_add, ← lt_opow_iff_log_lt hb ho, opow_one]

@[gcongr, mono]
/-
**Ordinal.log_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_mono_right (b : Ordinal) {x y : Ordinal} (xy : x <= y) : log b x <= lo
g b y
参数：b : Ordinal；xy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem log_mono_right (b : Ordinal) {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [log_zero_right, zero_le]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (opow_le_iff_le_log hb (hx.bot_lt.trans_le xy).ne').1 <|
        (opow_log_le_self _ hx).trans xy
    · rw [log_of_left_le_one hb, log_of_left_le_one hb]
/-
**Ordinal.log_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_le_self (b x : Ordinal) : log b x <= x
参数：b x : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.right_le_opow`：right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1
 < a) : b <= a ^ b
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem log_le_self (b x : Ordinal) : log b x ≤ x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero_right]
  · obtain hb | hb := lt_or_ge 1 b
    · exact (right_le_opow _ hb).trans (opow_log_le_self b hx)
    · simp_rw [log_of_left_le_one hb, zero_le]

@[simp]
/-
**Ordinal.log_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_one_right (b : Ordinal) : log b 1 = 0
参数：b : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Ordinal.log_eq_zero`：log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o
 = 0
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
-/
theorem log_one_right (b : Ordinal) : log b 1 = 0 := by
  obtain hb | hb := lt_or_ge 1 b
  · exact log_eq_zero hb
  · exact log_of_left_le_one hb 1
/-
**Ordinal.mod_opow_log_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o != 0) : o % (b ^ 
log b o) < o
参数：b : Ordinal；ho : o != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.mod_one`：mod_one (a : Ordinal) : a % 1 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.mod_lt`：mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
-/
theorem mod_opow_log_lt_self (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : o % (b ^ log b o) < o := by
  rcases eq_or_ne b 0 with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · exact (mod_lt _ <| opow_ne_zero _ hb).trans_le (opow_log_le_self _ ho)
/-
**Ordinal.log_mod_opow_log_lt_log_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (hbo : b <= o) :
 log b (o % (b ^ log b o)) < log b o
参数：hb : 1 < b；hbo : b <= o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `Ordinal.log_pos`：log_pos {b o : Ordinal} (hb : 1 < b) (ho : o != 0) (hbo
 : b <= o) : 0 < log b o
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_opow_iff_log_lt`：lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : x < b ^ c ↔ log b x < c
· 使用定理 `Ordinal.mod_lt`：mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
-/
theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (hbo : b ≤ o) :
    log b (o % (b ^ log b o)) < log b o := by
  rcases eq_or_ne (o % (b ^ log b o)) 0 with h | h
  · rw [h, log_zero_right]
    exact log_pos hb (one_le_iff_ne_zero.1 (hb.le.trans hbo)) hbo
  · rw [← lt_opow_iff_log_lt hb h]
    exact mod_lt _ (opow_pos _ hb.pos).ne'
/-
**Ordinal.log_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x != 0) (y : Ordinal) : log 
b x = y ↔ b ^ y <= x ∧ x < b ^ (y + 1)
参数：hb : 1 < b；hx : x != 0；y : Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `Ordinal.lt_opow_succ_log_self`：lt_opow_succ_log_self {b : Ordinal} (hb :
 1 < b) (x : Ordinal) : x < b ^ succ (log b x)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.lt_opow_iff_log_lt`：lt_opow_iff_log_lt {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : x < b ^ c ↔ log b x < c
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x
-/
theorem log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x ≠ 0) (y : Ordinal) :
    log b x = y ↔ b ^ y ≤ x ∧ x < b ^ (y + 1) := by
  constructor
  · rintro rfl
    use opow_log_le_self b hx, lt_opow_succ_log_self hb x
  · rintro ⟨hx₁, hx₂⟩
    apply le_antisymm
    · rwa [← lt_add_one_iff, ← lt_opow_iff_log_lt hb hx]
    · rwa [← opow_le_iff_le_log hb hx]
/-
**Ordinal.log_opow_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v != 0) (hw : w < 
b ^ u) : log b (b ^ u * v + w) = u + log b v
参数：hb : 1 < b；hv : v != 0；hw : w < b ^ u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.log_eq_iff`：log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x != 0
) (y : Ordinal) : log b x = y ↔ b ^ y <= x ∧ x < b ^ (y + 1)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `bot_lt_of_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
· 使用定理 `Ordinal.left_eq_zero_of_add_eq_zero`：left_eq_zero_of_add_eq_zero {a b : 
Ordinal} (h : a + b = 0) : a = 0
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Order.add_one_le_iff`：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.lt_opow_succ_log_self`：lt_opow_succ_log_self {b : Ordinal} (hb :
 1 < b) (x : Ordinal) : x < b ^ succ (log b x)
-/
theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : v ≠ 0) (hw : w < b ^ u) :
    log b (b ^ u * v + w) = u + log b v := by
  rw [log_eq_iff hb]
  · constructor
    · grw [opow_add, opow_log_le_self b hv, ← le_self_add]
    · grw [hw, ← mul_add_one, add_assoc, opow_add]
      gcongr
      rw [add_one_le_iff]
      exact lt_opow_succ_log_self hb _
  · exact fun h ↦ mul_ne_zero (opow_ne_zero u (bot_lt_of_lt hb).ne') hv <|
      left_eq_zero_of_add_eq_zero h
/-
**Ordinal.log_opow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_opow_mul {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v != 0) : lo
g b (b ^ u * v) = u + log b v
参数：hb : 1 < b；u : Ordinal；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.log_opow_mul_add`：log_opow_mul_add {b u v w : Ordinal} (hb : 1 <
 b) (hv : v != 0) (hw : w < b ^ u) : log b (b ^ u * v + w) = u + log b v
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `bot_lt_of_lt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → ⊥ < a
-/
theorem log_opow_mul {b v : Ordinal} (hb : 1 < b) (u : Ordinal) (hv : v ≠ 0) :
    log b (b ^ u * v) = u + log b v := by
  simpa using log_opow_mul_add hb hv (opow_pos u (bot_lt_of_lt hb))
/-
**Ordinal.log_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b ^ x) = x
参数：hb : 1 < b；x : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ordinal.log_one_right`：log_one_right (b : Ordinal) : log b 1 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.log_opow_mul`：log_opow_mul {b v : Ordinal} (hb : 1 < b) (u : Ord
inal) (hv : v != 0) : log b (b ^ u * v) = u + log b v
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
-/
theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b ^ x) = x := by
  convert! log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]
/-
**Ordinal.div_opow_log_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_opow_log_pos (b : Ordinal) {o : Ordinal} (ho : o != 0) : 0 < o / b ^ l
og b o
参数：b : Ordinal；ho : o != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ordinal.opow_zero`：opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1
· 使用定理 `Ordinal.div_one`：div_one (a : Ordinal) : a / 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.div_pos`：div_pos {b c : Ordinal} (h : c != 0) : 0 < b / c ↔ c <=
 b
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
-/
theorem div_opow_log_pos (b : Ordinal) {o : Ordinal} (ho : o ≠ 0) : 0 < o / b ^ log b o := by
  rcases eq_zero_or_pos b with (rfl | hb)
  · simpa using pos_iff_ne_zero.2 ho
  · rw [div_pos (opow_ne_zero _ hb.ne')]
    exact opow_log_le_self b ho
/-
**Ordinal.div_opow_log_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / b ^ log b o
 < b
参数：o : Ordinal；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_mul_iff_div_lt`：lt_mul_iff_div_lt {a b c : Ordinal} (ha : a !
= 0) : c < a * b ↔ c / a < b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.opow_succ`：opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a
· 使用定理 `Ordinal.lt_opow_succ_log_self`：lt_opow_succ_log_self {b : Ordinal} (hb :
 1 < b) (x : Ordinal) : x < b ^ succ (log b x)
-/
theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / b ^ log b o < b := by
  rw [← lt_mul_iff_div_lt (opow_pos _ (zero_lt_one.trans hb)).ne', ← opow_succ]
  exact lt_opow_succ_log_self hb o
/-
**Ordinal.div_two_opow_log** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：div_two_opow_log {o : Ordinal} (ho : o != 0) : o / 2 ^ log 2 o = 1
参数：ho : o != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.div_opow_log_lt`：div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb
 : 1 < b) : o / b ^ log b o < b
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.div_opow_log_pos`：div_opow_log_pos (b : Ordinal) {o : Ordinal} (
ho : o != 0) : 0 < o / b ^ log b o
-/
theorem div_two_opow_log {o : Ordinal} (ho : o ≠ 0) : o / 2 ^ log 2 o = 1 := by
  apply le_antisymm
  · simpa [← one_add_one_eq_two] using div_opow_log_lt o one_lt_two
  · simpa [one_le_iff_ne_zero, pos_iff_ne_zero] using div_opow_log_pos 2 ho
/-
**Ordinal.two_opow_log_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：two_opow_log_add {o : Ordinal} (ho : o != 0) : 2 ^ log 2 o + o % 2 ^ log 2
 o = o
参数：ho : o != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.div_two_opow_log`：div_two_opow_log {o : Ordinal} (ho : o != 0) :
 o / 2 ^ log 2 o = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
-/
theorem two_opow_log_add {o : Ordinal} (ho : o ≠ 0) : 2 ^ log 2 o + o % 2 ^ log 2 o = o := by
  convert! div_add_mod .. using 2
  rw [div_two_opow_log ho, mul_one]
/-
**Ordinal.add_log_le_log_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x != 0) (hy : y != 
0) : log b x + log b y <= log b (x * y)
参数：b : Ordinal；hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_le_iff_le_log`：opow_le_iff_le_log {b x c : Ordinal} (hb : 1
 < b) (hx : x != 0) : b ^ c <= x ↔ c <= log b x
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Ordinal.opow_add`：opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^
 c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (hx : x ≠ 0) (hy : y ≠ 0) :
    log b x + log b y ≤ log b (x * y) := by
  obtain hb | hb := lt_or_ge 1 b
  · rw [← opow_le_iff_le_log hb (mul_ne_zero hx hy), opow_add]
    exact mul_le_mul' (opow_log_le_self b hx) (opow_log_le_self b hy)
  · simpa only [log_of_left_le_one hb, zero_add] using le_rfl

@[deprecated opow_mul_lt_opow (since := "2026-06-01")]
/-
**Ordinal.omega0_opow_mul_nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : Nat) : ω ^ a * n <
 ω ^ b
参数：h : a < b；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.opow_mul_lt_opow`：opow_mul_lt_opow {b u v x : Ordinal} (hv : v <
 b) (hu : u < x) : b ^ u * v < b ^ x
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : ℕ) : ω ^ a * n < ω ^ b :=
  opow_mul_lt_opow (natCast_lt_omega0 n) h
/-
**Ordinal.sub_omega0_opow_log_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：sub_omega0_opow_log_lt {a : Ordinal} (ha : a != 0) : a - ω ^ log ω a < a
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `Ordinal.div_opow_log_lt`：div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb
 : 1 < b) : o / b ^ log b o < b
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.div_pos`：div_pos {b c : Ordinal} (h : c != 0) : 0 < b / c ↔ c <=
 b
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `Ordinal.opow_log_le_self`：opow_log_le_self (b : Ordinal) {x : Ordinal} (
hx : x != 0) : b ^ log b x <= x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one_add`：mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = 
a + a * b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.add_sub_cancel`：add_sub_cancel (a b : Ordinal) : a + b - a = b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ordinal.opow_mul_add_lt_opow_mul`：opow_mul_add_lt_opow_mul {b u w x : Or
dinal} {v : Ordinal} (hw : w < b ^ u) (hv : v < x) : b ^ u * v + w < b ^ u * x
· 使用定理 `Ordinal.mod_lt`：mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
（共 34 条，此处仅展示前 30 条）
-/
theorem sub_omega0_opow_log_lt {a : Ordinal} (ha : a ≠ 0) : a - ω ^ log ω a < a := by
  obtain ⟨n, hn⟩ := lt_omega0.1 <| div_opow_log_lt a one_lt_omega0
  conv_lhs => left; rw [← div_add_mod a (ω ^ log ω a), hn]
  cases n with
  | zero =>
    simpa using ((div_pos (opow_ne_zero _ omega0_ne_zero)).2 (opow_log_le_self _ ha)).trans_eq hn
  | succ n =>
    rw [add_comm, Nat.cast_add, Nat.cast_one, mul_one_add, add_assoc, Ordinal.add_sub_cancel]
    apply (opow_mul_add_lt_opow_mul _ (lt_add_one _)).trans_le
    · rw [Ordinal.mul_le_iff_le_div, hn] <;> simp
    · exact mod_lt _ (opow_ne_zero _ omega0_ne_zero)
/-
**Ordinal.lt_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_omega0_opow {a b : Ordinal} (hb : b != 0) : a < ω ^ b ↔ exists c < b, e
xists n : Nat, a < ω ^ c * n
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lt_log_of_lt_opow`：lt_log_of_lt_opow {b x c : Ordinal} (hc : c !
= 0) : x < b ^ c -> log b x < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0`：lt_omega0 {o : Ordinal} : o < ω ↔ exists n : Nat, o =
 n
· 使用定理 `Ordinal.div_opow_log_lt`：div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb
 : 1 < b) : o / b ^ log b o < b
· 使用定理 `Ordinal.one_lt_omega0`：one_lt_omega0 : 1 < ω
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.lt_mul_succ_div`：lt_mul_succ_div (a) {b : Ordinal} (h : b != 0) 
: a < b * succ (a / b)
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ordinal.opow_mul_lt_opow`：opow_mul_lt_opow {b u v x : Ordinal} (hv : v <
 b) (hu : u < x) : b ^ u * v < b ^ x
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
-/
theorem lt_omega0_opow {a b : Ordinal} (hb : b ≠ 0) :
    a < ω ^ b ↔ ∃ c < b, ∃ n : ℕ, a < ω ^ c * n := by
  refine ⟨fun ha ↦ ⟨_, lt_log_of_lt_opow hb ha, ?_⟩,
    fun ⟨c, hc, n, hn⟩ ↦ hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) hc)⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  use n + 1
  rw [Nat.cast_add_one, ← hn]
  exact lt_mul_succ_div a (opow_ne_zero _ omega0_ne_zero)
/-
**Ordinal.lt_omega0_opow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ exists n : Nat, a <
 ω ^ b * n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_omega0_opow`：lt_omega0_opow {a b : Ordinal} (hb : b != 0) : a
 < ω ^ b ↔ exists c < b, exists n : Nat, a < ω ^ c * n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Ordinal.opow_le_opow`：opow_le_opow {a b c d : Ordinal} (hac : a <= c) (h
bd : b <= d) (hc : 0 < c) : a ^ b <= c ^ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Order.lt_succ_iff`：lt_succ_iff : a < succ b ↔ a <= b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.omega0_pos`：omega0_pos : 0 < ω
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ordinal.opow_mul_lt_opow`：opow_mul_lt_opow {b u v x : Ordinal} (hv : v <
 b) (hu : u < x) : b ^ u * v < b ^ x
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
-/
theorem lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ ∃ n : ℕ, a < ω ^ b * n := by
  refine ⟨fun ha ↦ ?_, fun ⟨n, hn⟩ ↦ hn.trans (opow_mul_lt_opow (natCast_lt_omega0 n) (lt_succ b))⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (add_pos_of_right zero_lt_one b).ne').1 ha
  refine ⟨n, hn.trans_le ?_⟩
  grw [lt_succ_iff.1 hc]
  exact omega0_pos
/-
**Ordinal.lt_omega0_omega0_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_omega0_omega0_opow {a b : Ordinal} (hb : b != 0) : a < ω ^ ω ^ b ↔ exis
ts c < b, exists n : Nat, a < ω ^ (ω ^ c * n)
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.lt_omega0_opow`：lt_omega0_opow {a b : Ordinal} (hb : b != 0) : a
 < ω ^ b ↔ exists c < b, exists n : Nat, a < ω ^ c * n
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Ordinal.opow_mul_lt_opow`：opow_mul_lt_opow {b u v x : Ordinal} (hv : v <
 b) (hu : u < x) : b ^ u * v < b ^ x
· 使用定理 `Ordinal.natCast_lt_omega0`：natCast_lt_omega0 (n : Nat) : ↑n < ω
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem lt_omega0_omega0_opow {a b : Ordinal} (hb : b ≠ 0) :
    a < ω ^ ω ^ b ↔ ∃ c < b, ∃ n : ℕ, a < ω ^ (ω ^ c * n) := by
  simp_rw [lt_omega0_opow (opow_ne_zero _ omega0_ne_zero), lt_omega0_opow hb]
  constructor
  · intro ⟨a, ⟨b, hb, ⟨m, hm⟩⟩, ⟨n, hn⟩⟩
    exact ⟨_, hb, _, hn.trans <| opow_mul_lt_opow (natCast_lt_omega0 _) <|
      hm.trans_le (mul_le_mul_right (Nat.cast_le.2 m.le_succ) _)⟩
  · intro ⟨a, ha, ⟨n, hn⟩⟩
    refine ⟨ω ^ a * n, ⟨a, ha, n + 1, ?_⟩, 1, ?_⟩
    · simp [mul_lt_mul_iff_right₀, opow_pos]
    · simpa

/-! ### Interaction with `Nat.cast` -/

@[simp, norm_cast]
/-
**Ordinal.natCast_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
参数：m n : ℕ；m ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Interaction with `Nat.cast`
-/
theorem natCast_pow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n : ℕ) = (m : Ordinal) ^ n
  | 0 => by simp
  | n + 1 => by simp [pow_succ, natCast_pow m n]

@[deprecated natCast_pow (since := "2026-01-31")]
/-
**Ordinal.natCast_opow** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：natCast_opow (m : Nat) : forall n : Nat, ↑(m ^ n : Nat) = (m : Ordinal) ^ 
(n : Ordinal)
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem natCast_opow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n : ℕ) = (m : Ordinal) ^ (n : Ordinal) := by
  simp
/-
**Ordinal.iSup_pow_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_pow_natCast {o : Ordinal} (ho : 0 < o) : ⨆ n : Nat, o ^ n = o ^ ω
参数：ho : 0 < o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
· 使用定理 `Ordinal.apply_omega0_of_isNormal`：apply_omega0_of_isNormal {f : Ordinal.
{u} -> Ordinal.{v}} (hf : IsNormal f) : ⨆ n : Nat, f n = f ω
· 使用定理 `Ordinal.isNormal_opow`：isNormal_opow {a : Ordinal} (h : 1 < a) : IsNorma
l (a ^ · : Ordinal -> Ordinal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ordinal.one_opow`：one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_pow_natCast {o : Ordinal} (ho : 0 < o) : ⨆ n : ℕ, o ^ n = o ^ ω := by
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · simpa using apply_omega0_of_isNormal (isNormal_opow ho₁)
  · simp

@[simp, norm_cast]
/-
**Ordinal.natCast_log** 是 Mathlib 中的一个引理，位于命名空间 `Ordinal`。
形式化陈述：natCast_log (m n : Nat) : ↑(Nat.log m n) = Ordinal.log ↑m ↑n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_of_left_le_one`：log_of_left_le_one {b : Nat} (hb : b <= 1) (n) :
 log b n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Ordinal.log_of_left_le_one`：log_of_left_le_one {b : Ordinal} (h : b <= 1
) (x : Ordinal) : log b x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `Ordinal.log_zero_right`：log_zero_right (b : Ordinal) : log b 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ordinal.log_eq_iff`：log_eq_iff {b x : Ordinal} (hb : 1 < b) (hx : x != 0
) (y : Ordinal) : log b x = y ↔ b ^ y <= x ∧ x < b ^ (y + 1)
· 使用定理 `Ordinal.opow_natCast`：opow_natCast (a : Ordinal) (n : Nat) : a ^ (n : Or
dinal) = a ^ n
· 使用定理 `Nat.log_eq_iff`：log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) :
 log b n = m ↔ b ^ m <= n ∧ n < b ^ (m + 1)
-/
lemma natCast_log (m n : ℕ) : ↑(Nat.log m n) = Ordinal.log ↑m ↑n := by
  obtain hm | hm := le_or_gt m 1
  case inl => rw_mod_cast [Nat.log_of_left_le_one hm, log_of_left_le_one (mod_cast hm)]
  obtain rfl | hn := eq_or_ne n 0
  case inl => simp
  rw_mod_cast [eq_comm, log_eq_iff (mod_cast hm) (mod_cast hn), ← Nat.log_eq_iff (.inr ⟨hm, hn⟩)]

end Ordinal

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Port this meta code.

-- namespace Tactic

-- open Ordinal Mathlib.Meta.Positivity

-- /-- Extension for the `positivity` tactic: `ordinal.opow` takes positive values on positive
-- inputs. -/
-- @[positivity]
-- unsafe def positivity_opow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` opow_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Ordinal`
--     _ =>
--     failed

-- end Tactic

