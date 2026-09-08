/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Chebyshev polynomials over the reals: Chebyshev–Gauss

The Chebyshev–Gauss property calculates an integral of a polynomial of degree `< 2 * n`
with respect to the weight function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` by a sum
over appropriate evaluations of the polynomial.

## Main statements

* integral_eq_sumZeroes: The integral of a polynomial of degree `< 2 * n` with respect to the weight
  function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`.

## Implementation

The statement is proved for Chebyshev polynomials using the complex exponential representation
of `cos`, and then deduced for arbitrary polynomials.
-/
public section

namespace Polynomial.Chebyshev

open Real Polynomial Finset
open Complex (exp I)

/-
**Polynomial.Chebyshev.exp_sub_one_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exp_sub_one_ne_zero {n : ℕ} {k : ℤ} (hn : n ≠ 0) (hk : ¬ (2 * n : ℤ) ∣ k) :
    exp (k / n * π * I) ≠ 1 := by
  contrapose hk
  obtain ⟨m, hx⟩ := Complex.exp_eq_one_iff.mp hk
  have h : k = 2 * n * m := by
    apply (@Int.cast_inj ℂ _ _).mp
    linear_combination (norm := (push_cast; field [show (n : ℂ) ≠ 0 by aesop])) hx * (n / π / I)
  use m
/-
**Polynomial.Chebyshev.sum_exp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebyshev`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sum_exp {n : ℕ} {k : ℤ} (hn : n ≠ 0) (hk : ¬ (2 * n : ℤ) ∣ k) :
    ∑ i ∈ range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I) =
      (exp (k / (2 * n) * π * I) / (exp (k / n * π * I) - 1)) * ((-1) ^ k - 1) := by
  suffices (∑ i ∈ range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I)) *
    exp (-(k / (2 * n) * π * I)) * (exp (k / n * π * I) - 1) = (-1) ^ k - 1 by
    rw [Complex.exp_neg] at this
    have hf {s a b t : ℂ} (h : s * a⁻¹ * b = t) (ha : a ≠ 0) (hb : b ≠ 0) : s = a / b * t := by
      linear_combination (norm := field) h * a / b
    apply hf this (Complex.exp_ne_zero _) (by grind [exp_sub_one_ne_zero])
  convert! geom_sum_mul (exp (k / n * π * I)) n using 1
  · simp_rw [sum_mul]
    congr! 1 with i hi
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    grind
  · rw [← Complex.exp_nat_mul,
      show (n * (k / n * π * I)) = k * (π * I) by field [show (n : ℂ) ≠ 0 by aesop],
      Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Weighted sum of `P (x)` where `x` goes over `cos ((2 * i + 1) / (2 * n) * π)` for
  `0 ≤ i < n`. -/
/-
**Polynomial.Chebyshev.sumZeroes** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Chebyshev
`。
形式化陈述：sumZeroes (n : Nat) (P : Real[X]) : Real
参数：n : Nat；P : Real[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weighted sum of `P (x)` where `x` goes over `cos ((2 * i + 1) / (2 * n) * π)` fo
r
  `0 ≤ i < n`.
-/
noncomputable def sumZeroes (n : ℕ) (P : ℝ[X]) : ℝ :=
    (π / n) * ∑ i ∈ range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))

@[simp]
/-
**Polynomial.Chebyshev.sumZeroes_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheby
shev`。
形式化陈述：sumZeroes_sum (n : Nat) {ι : Type*} (s : Finset ι) (P : ι -> Real[X]) : su
mZeroes n (∑ i in s, P i) = ∑ i in s, sumZeroes n (P i)
参数：n : Nat；s : Finset ι；P : ι -> Real[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
-/
theorem sumZeroes_sum (n : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) :
    sumZeroes n (∑ i ∈ s, P i) = ∑ i ∈ s, sumZeroes n (P i) := by
  simp_rw [sumZeroes, eval_finsetSum]
  rw [sum_comm, mul_sum]

@[simp]
/-
**Polynomial.Chebyshev.sumZeroes_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheb
yshev`。
形式化陈述：sumZeroes_smul (n : Nat) (c : Real) (P : Real[X]) : sumZeroes n (c • P) = 
c * sumZeroes n P
参数：n : Nat；c : Real；P : Real[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
theorem sumZeroes_smul (n : ℕ) (c : ℝ) (P : ℝ[X]) :
    sumZeroes n (c • P) = c * sumZeroes n P := by
  simp_rw [sumZeroes, eval_smul, ← smul_sum, smul_eq_mul]; ring
/-
**Polynomial.Chebyshev.sumZeroes_T_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Ch
ebyshev`。
形式化陈述：sumZeroes_T_zero {n : Nat} (hn : n != 0) : sumZeroes n (T Real 0) = π
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.Chebyshev.T_zero`：T_zero : T R 0 = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 46 条，此处仅展示前 30 条）
-/
theorem sumZeroes_T_zero {n : ℕ} (hn : n ≠ 0) : sumZeroes n (T ℝ 0) = π := by
  simp [sumZeroes, show π / n * n = π by field]
/-
**Polynomial.Chebyshev.sumZeroes_T_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：sumZeroes_T_of_not_dvd {n : Nat} {k : Int} (hk : ¬ (2 * n : Int) ∣ k) : su
mZeroes n (T Real k) = 0
参数：hk : ¬ (2 * n : Int) ∣ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Polynomial.Chebyshev.T_eval_one`：T_eval_one (n : Int) : (T R n).eval 1 =
 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Complex.two_cos`：two_cos : 2 * cos x = exp (x * I) + exp (-x * I)
· 使用引理 `Int.cast_negOnePow`：cast_negOnePow (K : Type*) (n : Int) [DivisionRing K
] : n.negOnePow = (-1 : K) ^ n
· 使用引理 `Int.negOnePow_neg`：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePo
w
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Cheby
shevGauss.0.Polynomial.Chebyshev.sum_exp`：∀ {n : ℕ} {k : ℤ},   n ≠ 0 →     ¬2 * 
↑n ∣ k →       ∑ i ∈ Finset.range n, Complex.exp (↑k * ((2 * ↑i + 1) / (2 * ↑n) 
* ↑Real.pi) * Complex.…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
（共 130 条，此处仅展示前 30 条）
-/
theorem sumZeroes_T_of_not_dvd {n : ℕ} {k : ℤ} (hk : ¬ (2 * n : ℤ) ∣ k) :
    sumZeroes n (T ℝ k) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sumZeroes]
  suffices ∑ i ∈ range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by
    rw [sumZeroes, mul_eq_zero_iff_left (by aesop)]
    rw [← mul_sum, mul_eq_zero_iff_left (by norm_num)] at this
    simpa [T_real_cos]
  suffices (∑ i ∈ range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) : ℂ) = 0 by norm_cast at this ⊢
  suffices ∑ i ∈ range n, 2 * Complex.cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by aesop
  simp_rw [Complex.two_cos, ← neg_mul, ← Int.cast_neg]
  have : (-1 : ℂ) ^ (-k) = (-1) ^ k := by rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]; simp
  rw [sum_add_distrib, sum_exp hn hk, sum_exp hn (by aesop),
    Int.cast_neg, neg_div, neg_mul, neg_mul, Complex.exp_neg,
    neg_div, neg_mul, neg_mul, Complex.exp_neg, this, ← add_mul, mul_eq_zero_of_left]
  set z := exp (k / (2 * n) * π * I) with hz
  have hz₂ : exp (k / n * π * I) = z ^ 2 := by rw [hz, ← Complex.exp_nat_mul]; grind
  rw [hz₂, ← inv_pow z 2]
  field [show z ≠ 0 by grind [Complex.exp_ne_zero],
    show (z ^ 2 - 1 ≠ 0) ∧ (1 - z ^ 2 ≠ 0) by grind [exp_sub_one_ne_zero]]

/-- The integral of a polynomial of degree `< 2 * n` with respect to the weight function
  `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`. -/
/-
**Polynomial.Chebyshev.integral_eq_sumZeroes** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Chebyshev`。
形式化陈述：integral_eq_sumZeroes {n : Nat} {P : Real[X]} (hn : n != 0) (hP : P.degree
 < 2 * n) : ∫ x, P.eval x ∂measureT = sumZeroes n P
参数：hn : n != 0；hP : P.degree < 2 * n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Submodule.mem_span_image_finset_iff_exists_fun'`：Submodule.mem_span_imag
e_finset_iff_exists_fun' {s : Finset α} : x in span R (v '' s) ↔ exists c : α ->
 R, ∑ i in s, c i • v i = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.Sequence.span_degreeLT`：span_degreeLT {m : Nat} (hCoeff : for
all i < m, IsUnit (S i).leadingCoeff) : span R (S '' Set.Iio m) = degreeLT R m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `Polynomial.Chebyshev.integrable_measureT`：integrable_measureT {f : Real 
-> Real} (hf : ContinuousOn f (Set.Icc (-1) 1)) : Integrable f measureT
· 使用定理 `Polynomial.continuousOn`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : 
TopologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R)   {s : Set R}, 
ContinuousOn …
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of a polynomial of degree `< 2 * n` with respect to the weight func
tion
  `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of i
ts values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`.
-/
theorem integral_eq_sumZeroes {n : ℕ} {P : ℝ[X]} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂measureT = sumZeroes n P := by
  have hmem : P ∈ degreeLT ℝ (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (2 * n) = Finset.range (2 * n) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_finsetSum, eval_smul]
  rw [MeasureTheory.integral_finsetSum, sumZeroes_sum]
  · simp_rw [sumZeroes_smul, smul_eq_mul, MeasureTheory.integral_const_mul]
    congr! with i hrange
    simp_rw [chebyshevTsequence]
    by_cases i = 0
    case pos hi => rw [hi, Nat.cast_zero, integral_eval_T_real_measureT_zero, sumZeroes_T_zero hn]
    case neg hi =>
      have : ¬ (2 * n : ℤ) ∣ i := by
        refine (Int.not_dvd_iff_lt_mul_succ _ (by grind)).mpr ⟨0, ⟨by grind, ?_⟩⟩
        rw_mod_cast [zero_add, mul_one]
        exact mem_range.mp hrange
      rw [integral_eval_T_real_measureT_of_ne_zero (by grind), sumZeroes_T_of_not_dvd this]
  · simp_rw [← eval_smul]
    exact fun i hi => integrable_measureT (by fun_prop)

end Polynomial.Chebyshev

