/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the tanh function

In this file we define an inverse of tanh as a function from ℝ to (-1, 1).

## Main definitions

- `Real.artanh`: An inverse function of `Real.tanh` as a function from ℝ to (-1, 1).

- `Real.tanhPartialEquiv`: `Real.tanh` and `Real.artanh` bundled as a `PartialEquiv`
  from ℝ to (-1, 1).

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

- `Real.tanh_bijOn`, `Real.tanh_injective`, `Real.tanh_surjOn`: `Real.tanh` is
  bijective, injective and surjective as a function from ℝ to (-1, 1)

- `Real.artanh_bijOn`, `Real.artanh_injOn`, `Real.artanh_surjOn`: `Real.artanh` is bijective,
  injective and surjective as a function from (-1, 1) to ℝ

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `artanh` is defined using a logarithm, `artanh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
/-
**Real.artanh** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：artanh (x : Real)
参数：x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`artanh` is defined using a logarithm, `artanh x = log √((1 + x) / (1 - x))`.
-/
def artanh (x : ℝ) :=
  log √((1 + x) / (1 - x))
/-
**Real.artanh_eq_half_log** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_eq_half_log {x : Real} (hx : x in Icc (-1) 1) : artanh x = 1 / 2 * 
log ((1 + x) / (1 - x))
参数：hx : x in Icc (-1) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.artanh.eq_1`：∀ (x : ℝ), Real.artanh x = Real.log √((1 + x) / (1 - x
))
· 使用定理 `Real.log_sqrt`：log_sqrt {x : Real} (hx : 0 <= x) : log (√x) = log x / 2
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_div_mul_eq_div`：one_div_mul_eq_div : 1 / a * b = b / a
-/
theorem artanh_eq_half_log {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    artanh x = 1 / 2 * log ((1 + x) / (1 - x)) := by
  rw [artanh, log_sqrt <| div_nonneg (by grind) (by grind), one_div_mul_eq_div]
/-
**Real.exp_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_artanh {x : Real} (hx : x in Ioo (-1) 1) : exp (artanh x) = √((1 + x) 
/ (1 - x))
参数：hx : x in Ioo (-1) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem exp_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : exp (artanh x) = √((1 + x) / (1 - x)) :=
  exp_log <| sqrt_pos_of_pos <| div_pos (by grind) (by grind)

@[simp]
/-
**Real.artanh_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_zero : artanh 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem artanh_zero : artanh 0 = 0 := by simp [artanh]
/-
**Real.sinh_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_artanh {x : Real} (hx : x in Ioo (-1) 1) : sinh (artanh x) = x / √(1 
- x ^ 2)
参数：hx : x in Ioo (-1) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
-/
theorem sinh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : sinh (artanh x) = x / √(1 - x ^ 2) := by
  have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  rw [← one_pow, sq_sub_sq 1 x, sqrt_mul]
    <;> grind [artanh, sinh_eq, exp_neg, exp_log, sqrt_div]
/-
**Real.cosh_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_artanh {x : Real} (hx : x in Ioo (-1) 1) : cosh (artanh x) = 1 / √(1 
- x ^ 2)
参数：hx : x in Ioo (-1) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
-/
theorem cosh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : cosh (artanh x) = 1 / √(1 - x ^ 2) := by
  have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  rw [← one_pow, sq_sub_sq 1 x, sqrt_mul]
    <;> grind [artanh, cosh_eq, exp_neg, exp_log, sqrt_div]

/-- `artanh` is the right inverse of `tanh` over (-1, 1). -/
/-
**Real.tanh_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tanh_artanh {x : Real} (hx : x in Ioo (-1) 1) : tanh (artanh x) = x
参数：hx : x in Ioo (-1) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)

--- 原说明 ---
`artanh` is the right inverse of `tanh` over (-1, 1).
-/
theorem tanh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : tanh (artanh x) = x := by
  have := sq_sub_sq 1 x
  grind [tanh_eq_sinh_div_cosh, sinh_artanh, cosh_artanh, sqrt_ne_zero', mul_pos]

/-- `artanh` is the left inverse of `tanh`. -/
/-
**Real.artanh_tanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_tanh (x : Real) : artanh (tanh x) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.artanh.eq_1`：∀ (x : ℝ), Real.artanh x = Real.log √((1 + x) / (1 - x
))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ x = y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Real.tanh_eq`：tanh_eq (x : Real) : tanh x = (exp x - exp (-x)) / (exp x 
+ exp (-x))
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
`artanh` is the left inverse of `tanh`.
-/
theorem artanh_tanh (x : ℝ) : artanh (tanh x) = x := by
  have h : 0 < (1 + tanh x) / (1 - tanh x) :=
    div_pos (by grind [neg_one_lt_tanh]) (by grind [tanh_lt_one])
  rw [artanh, ← exp_eq_exp, exp_log (sqrt_pos_of_pos h),
    ← sq_eq_sq₀ (le_of_lt <| sqrt_pos_of_pos h) (exp_nonneg x),
    sq_sqrt (le_of_lt h), tanh_eq, exp_neg]
  field
/-
**Real.strictMonoOn_one_add_div_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_one_add_div_one_sub : StrictMonoOn (fun (x : Real) => (1 + x)
 / (1 - x)) (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.FieldSimp.lt_eq_cancel_lt`：lt_eq_cancel_lt {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M] {e₁ e
₂ f₁ f₂ L : M} (H₁ : e₁ = L * …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_pos`：cons_pos [GroupWithZero M] [Partia
lOrder M] [PosMulStrictMono M] [PosMulReflectLT M] [ZeroLEOneClass M] (r : Int) 
{x : M} (hx : 0 < x) {l : …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem strictMonoOn_one_add_div_one_sub :
    StrictMonoOn (fun (x : ℝ) => (1 + x) / (1 - x)) (Ioo (-1) 1) := by
  intro x hx y hy h
  field_simp [show 0 < 1 - x by grind, show 0 < 1 - y by grind]
  grind
/-
**Real.strictMonoOn_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_artanh : StrictMonoOn artanh (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.comp`：StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : Stric
tMonoOn f s) (hs : Set.MapsTo f s t) : StrictMonoOn (g ∘ f) s
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
· 使用定理 `Real.strictMonoOn_sqrt`：strictMonoOn_sqrt : StrictMonoOn sqrt (Ici 0)
· 使用定理 `Real.strictMonoOn_one_add_div_one_sub`：strictMonoOn_one_add_div_one_sub 
: StrictMonoOn (fun (x : Real) => (1 + x) / (1 - x)) (Ioo (-1) 1)
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
-/
theorem strictMonoOn_artanh : StrictMonoOn artanh (Ioo (-1) 1) := by
  apply strictMonoOn_log.comp ?_ fun x hx ↦ sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  apply strictMonoOn_sqrt.comp strictMonoOn_one_add_div_one_sub
    fun x hx ↦ show 0 ≤ (1 + x) / (1 - x) by exact div_nonneg (by grind) (by grind)
/-
**Real.artanh_le_artanh_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_le_artanh_iff {x y : Real} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-
1) 1) : artanh x <= artanh y ↔ x <= y
参数：hx : x in Ioo (-1) 1；hy : y in Ioo (-1) 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Real.strictMonoOn_artanh`：strictMonoOn_artanh : StrictMonoOn artanh (Ioo
 (-1) 1)
-/
theorem artanh_le_artanh_iff {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    artanh x ≤ artanh y ↔ x ≤ y :=
  strictMonoOn_artanh.le_iff_le hx hy
/-
**Real.artanh_lt_artanh_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_lt_artanh_iff {x y : Real} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-
1) 1) : artanh x < artanh y ↔ x < y
参数：hx : x in Ioo (-1) 1；hy : y in Ioo (-1) 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `Real.strictMonoOn_artanh`：strictMonoOn_artanh : StrictMonoOn artanh (Ioo
 (-1) 1)
-/
theorem artanh_lt_artanh_iff {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    artanh x < artanh y ↔ x < y :=
  strictMonoOn_artanh.lt_iff_lt hx hy
/-
**Real.artanh_le_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_le_artanh {x y : Real} (hx : -1 < x) (hy : y < 1) (hxy : x <= y) : 
artanh x <= artanh y
参数：hx : -1 < x；hy : y < 1；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.artanh_le_artanh_iff`：artanh_le_artanh_iff {x y : Real} (hx : x in 
Ioo (-1) 1) (hy : y in Ioo (-1) 1) : artanh x <= artanh y ↔ x <= y
-/
theorem artanh_le_artanh {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x ≤ y) :
    artanh x ≤ artanh y :=
  (artanh_le_artanh_iff (by grind) (by grind)).mpr hxy
/-
**Real.artanh_lt_artanh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_lt_artanh {x y : Real} (hx : -1 < x) (hy : y < 1) (hxy : x < y) : a
rtanh x < artanh y
参数：hx : -1 < x；hy : y < 1；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.artanh_lt_artanh_iff`：artanh_lt_artanh_iff {x y : Real} (hx : x in 
Ioo (-1) 1) (hy : y in Ioo (-1) 1) : artanh x < artanh y ↔ x < y
-/
theorem artanh_lt_artanh {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x < y) :
    artanh x < artanh y :=
  (artanh_lt_artanh_iff (by grind) (by grind)).mpr hxy
/-
**Real.artanh_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_eq_zero_iff {x : Real} : artanh x = 0 ↔ x <= -1 ∨ x = 0 ∨ 1 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem artanh_eq_zero_iff {x : ℝ} : artanh x = 0 ↔ x ≤ -1 ∨ x = 0 ∨ 1 ≤ x := by
  grind [artanh, log_eq_zero, div_nonpos_iff]
/-
**Real.artanh_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_pos {x : Real} (hx : x in Ioo 0 1) : 0 < artanh x
参数：hx : x in Ioo 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.artanh_zero`：artanh_zero : artanh 0 = 0
· 使用定理 `Real.artanh_lt_artanh_iff`：artanh_lt_artanh_iff {x y : Real} (hx : x in 
Ioo (-1) 1) (hy : y in Ioo (-1) 1) : artanh x < artanh y ↔ x < y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem artanh_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < artanh x := by
  rw [← artanh_zero, artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.1
/-
**Real.artanh_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_neg {x : Real} (hx : x in Ioo (-1) 0) : artanh x < 0
参数：hx : x in Ioo (-1) 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.artanh_zero`：artanh_zero : artanh 0 = 0
· 使用定理 `Real.artanh_lt_artanh_iff`：artanh_lt_artanh_iff {x y : Real} (hx : x in 
Ioo (-1) 1) (hy : y in Ioo (-1) 1) : artanh x < artanh y ↔ x < y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem artanh_neg {x : ℝ} (hx : x ∈ Ioo (-1) 0) : artanh x < 0 := by
  rw [← artanh_zero, artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.2
/-
**Real.artanh_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_nonneg {x : Real} (hx : 0 <= x) : 0 <= artanh x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.artanh_zero`：artanh_zero : artanh 0 = 0
· 使用定理 `Real.artanh_le_artanh_iff`：artanh_le_artanh_iff {x y : Real} (hx : x in 
Ioo (-1) 1) (hy : y in Ioo (-1) 1) : artanh x <= artanh y ↔ x <= y
-/
theorem artanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ artanh x := by
  by_cases x < 1
  case pos =>
    rw [← artanh_zero, artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]
/-
**Real.artanh_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_nonpos {x : Real} (hx : x <= 0) : artanh x <= 0
参数：hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.artanh_zero`：artanh_zero : artanh 0 = 0
· 使用定理 `Real.artanh_le_artanh_iff`：artanh_le_artanh_iff {x y : Real} (hx : x in 
Ioo (-1) 1) (hy : y in Ioo (-1) 1) : artanh x <= artanh y ↔ x <= y
-/
theorem artanh_nonpos {x : ℝ} (hx : x ≤ 0) : artanh x ≤ 0 := by
  by_cases -1 < x
  case pos =>
    rw [← artanh_zero, artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

/-- `Real.tanh` as a `PartialEquiv`. -/
/-
**Real.tanhPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：tanhPartialEquiv : PartialEquiv Real Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `Real.artanh_tanh`：artanh_tanh (x : Real) : artanh (tanh x) = x
· 使用定理 `Real.tanh_artanh`：tanh_artanh {x : Real} (hx : x in Ioo (-1) 1) : tanh (
artanh x) = x

--- 原说明 ---
`Real.tanh` as a `PartialEquiv`.
-/
def tanhPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := tanh
  invFun := artanh
  source := univ
  target := Ioo (-1) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr
/-
**Real.tanh_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tanh_bijOn : BijOn tanh univ (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.BijOn (↑e) e.source e.target
-/
theorem tanh_bijOn : BijOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.bijOn
/-
**Real.tanh_injective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tanh_injective : Injective tanh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.injOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InjOn (↑e) e.source
· 使用定理 `trivial`：True
-/
theorem tanh_injective : Injective tanh := fun _ _ ↦ tanhPartialEquiv.injOn trivial trivial
/-
**Real.tanh_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tanh_surjOn : SurjOn tanh univ (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.surjOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.SurjOn (↑e) e.source e.target
-/
theorem tanh_surjOn : SurjOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.surjOn
/-
**Real.artanh_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_bijOn : BijOn artanh (Ioo (-1) 1) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.BijOn (↑e) e.source e.target
-/
theorem artanh_bijOn : BijOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.bijOn
/-
**Real.artanh_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_injOn : InjOn artanh (Ioo (-1) 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.injOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InjOn (↑e) e.source
-/
theorem artanh_injOn : InjOn artanh (Ioo (-1) 1) := tanhPartialEquiv.symm.injOn
/-
**Real.artanh_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：artanh_surjOn : SurjOn artanh (Ioo (-1) 1) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.surjOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.SurjOn (↑e) e.source e.target
-/
theorem artanh_surjOn : SurjOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.surjOn

end Real

