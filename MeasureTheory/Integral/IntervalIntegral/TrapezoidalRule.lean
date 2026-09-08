/-
Copyright (c) 2025 P. Michael Kielstra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: P. Michael Kielstra
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Field

/-!
# The trapezoidal rule

This file contains a definition of integration on `[[a, b]]` via the trapezoidal rule, along with
an error bound in terms of a bound on the second derivative of the integrand.

## Main results
- `trapezoidal_error_le`: the convergence theorem for the trapezoidal rule.

## References
We follow the proof on (Wikipedia)[https://en.wikipedia.org/wiki/Trapezoidal_rule] for the error
bound.
-/

@[expose] public section

open MeasureTheory intervalIntegral Interval Finset HasDerivWithinAt Set

/-- Integration of `f` from `a` to `b` using the trapezoidal rule with `N+1` total evaluations of
`f`.  (Note the off-by-one problem here: `N` counts the number of trapezoids, not the number of
evaluations.) -/
@[wikidata Q833293]
/-
**trapezoidal_integral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：trapezoidal_integral (f : Real -> Real) (N : Nat) (a b : Real) : Real
参数：f : Real -> Real；N : Nat；a b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Integration of `f` from `a` to `b` using the trapezoidal rule with `N+1` total e
valuations of
`f`.  (Note the off-by-one problem here: `N` counts the number of trapezoids, no
t the number of
evaluations.)
-/
noncomputable def trapezoidal_integral (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ((b - a) / N) * ((f a + f b) / 2 + ∑ k ∈ range (N - 1), f (a + (k + 1) * (b - a) / N))

/-- The absolute error of trapezoidal integration. -/
/-
**trapezoidal_error** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：trapezoidal_error (f : Real -> Real) (N : Nat) (a b : Real) : Real
参数：f : Real -> Real；N : Nat；a b : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute error of trapezoidal integration.
-/
noncomputable def trapezoidal_error (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  (trapezoidal_integral f N a b) - (∫ x in a..b, f x)

/-- Just like exact integration, the trapezoidal approximation retains the same magnitude but
changes sign when the endpoints are swapped. -/
/-
**trapezoidal_integral_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_integral_symm (f : Real -> Real) {N : Nat} (N_nonzero : 0 < N)
 (a b : Real) : trapezoidal_integral f N a b = -(trapezoidal_integral f N b a)
参数：f : Real -> Real；N_nonzero : 0 < N；a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用引理 `neg_div'`：neg_div' (a b : R) : -(b / a) = -b / a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_range_reflect`：sum_range_reflect {δ : Type*} [AddCommMonoid δ
] (f : Nat -> δ) (n : Nat) : (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f
 j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
Just like exact integration, the trapezoidal approximation retains the same magn
itude but
changes sign when the endpoints are swapped.
-/
theorem trapezoidal_integral_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    trapezoidal_integral f N a b = -(trapezoidal_integral f N b a) := by
  unfold trapezoidal_integral
  rw [neg_mul_eq_neg_mul, neg_div', neg_sub, add_comm (f b) (f a), ← sum_range_reflect]
  congr 2
  apply sum_congr rfl
  intro k hk
  norm_cast
  rw [tsub_tsub, add_comm 1, Nat.cast_add, Nat.cast_sub (mem_range.mp hk), Nat.cast_sub N_nonzero]
  apply congr_arg
  field

/-- The absolute error of the trapezoidal rule does not change when the endpoints are swapped. -/
/-
**trapezoidal_error_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_error_symm (f : Real -> Real) {N : Nat} (N_nonzero : 0 < N) (a
 b : Real) : trapezoidal_error f N a b = -trapezoidal_error f N b a
参数：f : Real -> Real；N_nonzero : 0 < N；a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trapezoidal_integral_symm`：trapezoidal_integral_symm (f : Real -> Real) 
{N : Nat} (N_nonzero : 0 < N) (a b : Real) : trapezoidal_integral f N a b = -(tr
apezoidal_integ…
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a

--- 原说明 ---
The absolute error of the trapezoidal rule does not change when the endpoints ar
e swapped.
-/
theorem trapezoidal_error_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    trapezoidal_error f N a b = -trapezoidal_error f N b a := by
  unfold trapezoidal_error
  rw [trapezoidal_integral_symm f N_nonzero a b, integral_symm, neg_sub_neg, neg_sub]

/-- Just like exact integration, the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
/-
**trapezoidal_integral_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_integral_eq (f : Real -> Real) (N : Nat) (a : Real) : trapezoi
dal_integral f N a a = 0
参数：f : Real -> Real；N : Nat；a : Real。
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
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Just like exact integration, the trapezoidal integration from `a` to `a` is zero
.
-/
theorem trapezoidal_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : trapezoidal_integral f N a a = 0 := by
  simp [trapezoidal_integral]

/-- The error of the trapezoidal integration from `a` to `a` is zero. -/
@[simp]
/-
**trapezoidal_error_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_error_eq (f : Real -> Real) (N : Nat) (a : Real) : trapezoidal
_error f N a a = 0
参数：f : Real -> Real；N : Nat；a : Real。
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
· 使用定理 `trapezoidal_integral_eq`：trapezoidal_integral_eq (f : Real -> Real) (N :
 Nat) (a : Real) : trapezoidal_integral f N a a = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The error of the trapezoidal integration from `a` to `a` is zero.
-/
theorem trapezoidal_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) : trapezoidal_error f N a a = 0 := by
  simp [trapezoidal_error]

/-- An exact formula for integration with a single trapezoid (the "midpoint rule"). -/
@[simp]
/-
**trapezoidal_integral_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_integral_one (f : Real -> Real) (a b : Real) : trapezoidal_int
egral f 1 a b = (b - a) / 2 * (f a + f b)
参数：f : Real -> Real；a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An exact formula for integration with a single trapezoid (the "midpoint rule").
-/
theorem trapezoidal_integral_one (f : ℝ → ℝ) (a b : ℝ) :
    trapezoidal_integral f 1 a b = (b - a) / 2 * (f a + f b) := by
  simp [trapezoidal_integral, mul_comm_div]

/-- A basic trapezoidal equivalent to `IntervalIntegral.sum_integral_adjacent_intervals`. More
general theorems are certainly possible, but many of them can be derived from repeated applications
of this one. -/
/-
**sum_trapezoidal_integral_adjacent_intervals** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_trapezoidal_integral_adjacent_intervals {f : Real -> Real} {N : Nat} {
a h : Real} (N_nonzero : 0 < N) : ∑ i in range N, trapezoidal_integral f 1 (a + 
i * h) (a + (i + 1) * h) = trapezoidal_integral f N a (a + N * h)
参数：N_nonzero : 0 < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `trapezoidal_integral_one`：trapezoidal_integral_one (f : Real -> Real) (a
 b : Real) : trapezoidal_integral f 1 a b = (b - a) / 2 * (f a + f b)
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 102 条，此处仅展示前 30 条）

--- 原说明 ---
A basic trapezoidal equivalent to `IntervalIntegral.sum_integral_adjacent_interv
als`. More
general theorems are certainly possible, but many of them can be derived from re
peated applications
of this one.
-/
theorem sum_trapezoidal_integral_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) : ∑ i ∈ range N, trapezoidal_integral f 1 (a + i * h) (a + (i + 1) * h)
      = trapezoidal_integral f N a (a + N * h) := by
  simp_rw [trapezoidal_integral_one, add_sub_add_left_eq_sub, ← sub_mul, trapezoidal_integral,
    add_sub_cancel_left, one_mul, ← mul_sum, ← mul_div, show N * (h / N) = h by field]
  rw [sum_add_distrib, ← Nat.sub_one_add_one_eq_of_pos N_nonzero, sum_range_succ', sum_range_succ,
    add_add_add_comm, ← sum_add_distrib, add_comm, Nat.sub_one_add_one_eq_of_pos N_nonzero]
  simp_rw [Nat.cast_sub N_nonzero, Nat.cast_add, Nat.cast_one, ← two_mul, ← mul_sum]
  ring_nf

/-- A simplified version of the previous theorem, for use in proofs by induction and the like. -/
/-
**trapezoidal_integral_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_integral_ext {f : Real -> Real} {N : Nat} {a h : Real} (N_nonz
ero : 0 < N) : trapezoidal_integral f N a (a + N * h) + trapezoidal_integral f 1
 (a + N * h) (a + (N + 1) * h) = trapezoidal_integral f (N + 1) a (a + (N + 1) *
 h)
参数：N_nonzero : 0 < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `sum_trapezoidal_integral_adjacent_intervals`：sum_trapezoidal_integral_ad
jacent_intervals {f : Real -> Real} {N : Nat} {a h : Real} (N_nonzero : 0 < N) :
 ∑ i in range N, trapezoidal_inte…
· 使用定理 `Nat.add_pos_left`：∀ {m : ℕ}, 0 < m → ∀ (n : ℕ), 0 < m + n
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n

--- 原说明 ---
A simplified version of the previous theorem, for use in proofs by induction and
 the like.
-/
theorem trapezoidal_integral_ext {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N) :
    trapezoidal_integral f N a (a + N * h) + trapezoidal_integral f 1 (a + N * h) (a + (N + 1) * h)
      = trapezoidal_integral f (N + 1) a (a + (N + 1) * h) := by
  rw [← Nat.cast_add_one, ← sum_trapezoidal_integral_adjacent_intervals N_nonzero,
      ← sum_trapezoidal_integral_adjacent_intervals (Nat.add_pos_left N_nonzero 1),
      sum_range_succ, Nat.cast_add_one]

/-- Since we have `sum_[]_adjacent_intervals` theorems for both exact and trapezoidal integration,
it's natural to combine them into a similar formula for the error.  This theorem is in particular
used in the proof of the general error bound. -/
/-
**sum_trapezoidal_error_adjacent_intervals** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_trapezoidal_error_adjacent_intervals {f : Real -> Real} {N : Nat} {a h
 : Real} (N_nonzero : 0 < N) (h_f_int : IntervalIntegrable f volume a (a + N * h
)) : ∑ i in range N, trapezoidal_error f 1 (a + i * h) (a + (i + 1) * h) = trape
zoidal_error f N a (a + N * h)
参数：N_nonzero : 0 < N；h_f_int : IntervalIntegrable f volume a (a + N * h)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `sum_trapezoidal_integral_adjacent_intervals`：sum_trapezoidal_integral_ad
jacent_intervals {f : Real -> Real} {N : Nat} {a h : Real} (N_nonzero : 0 < N) :
 ∑ i in range N, trapezoidal_inte…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `intervalIntegral.sum_integral_adjacent_intervals`：sum_integral_adjacent_
intervals {a : Nat -> Real} {n : Nat} (hint : forall k < n, IntervalIntegrable f
 μ (a k) (a <| k + 1)) : ∑ k in Finset…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用引理 `Set.mem_uIcc_of_le`：mem_uIcc_of_le (ha : a <= x) (hb : x <= b) : x in [[
a, b]]
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Since we have `sum_[]_adjacent_intervals` theorems for both exact and trapezoida
l integration,
it's natural to combine them into a similar formula for the error.  This theorem
 is in particular
used in the proof of the general error bound.
-/
theorem sum_trapezoidal_error_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N)
    (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
    ∑ i ∈ range N, trapezoidal_error f 1 (a + i * h) (a + (i + 1) * h)
      = trapezoidal_error f N a (a + N * h) := by
  unfold trapezoidal_error
  rw [sum_sub_distrib, sum_trapezoidal_integral_adjacent_intervals N_nonzero]
  norm_cast
  rw [sum_integral_adjacent_intervals]
  · simp
  · intro k hk
    suffices ∀ {k : ℕ}, k ≤ N → a + k * h ∈ [[a, a + N * h]] from
      IntervalIntegrable.mono h_f_int (Set.uIcc_subset_uIcc (this hk.le) (this hk)) le_rfl
    rcases le_total h 0 with h_neg | h_pos <;> intro k hk <;> rw [← Nat.cast_le (α := ℝ)] at hk
    · simpa [Set.mem_uIcc] using .inr
        ⟨mul_le_mul_of_nonpos_right hk h_neg, mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg h_neg⟩
    · exact Set.mem_uIcc_of_le (le_add_of_nonneg_right (by positivity)) (by grw [hk])

/-- The most basic case possible: two ordered points, with N = 1. This lemma is used in the proof of
the general error bound later on. -/
/-
**trapezoidal_error_le_of_lt'** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The most basic case possible: two ordered points, with N = 1. This lemma is used
 in the proof of
the general error bound later on.
-/
private lemma trapezoidal_error_le_of_lt' {f : ℝ → ℝ} {ζ : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (h_df : DifferentiableOn ℝ f (Icc a b))
    (h_ddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ ζ) :
    |trapezoidal_error f 1 a b| ≤ (b - a) ^ 3 * ζ / 12 := by
  rw [mul_div_assoc, mul_comm]
  let g (t : ℝ) := trapezoidal_error f 1 a t
  -- Hand-computed expressions for g' and g''.
  let dg (t : ℝ) := (1 / 2) * (f a + f t) + ((t - a) / 2) * (derivWithin f (Icc a b) t) - f t
  let ddg (t : ℝ) := ((t - a) / 2) * (iteratedDerivWithin 2 f (Icc a b) t)
  -- Compute g' by applying standard derivative identities.
  have h_dg (y : ℝ) (hy : y ∈ Icc a b) : HasDerivWithinAt g (dg y) (Icc a b) y := by
    unfold g trapezoidal_error trapezoidal_integral
    simp only [Nat.cast_one, div_one, tsub_self, Finset.range_zero, sum_empty, add_zero]
    simp_rw [← mul_comm_div]
    refine fun_sub (fun_mul (div_const (sub_const _ (hasDerivWithinAt_id _ _)) _)
      (const_add _ (h_df y hy).hasDerivWithinAt)) ?_
    have := Fact.mk hy -- Needed for integral_hasDerivWithinAt_right
    apply integral_hasDerivWithinAt_right
    · exact (h_df.continuousOn.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1
    · exact h_df.continuousOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc y
    · exact h_df.continuousOn.continuousWithinAt hy
  -- Compute g'', once again applying standard derivative identities.
  have h_ddg (y : ℝ) (hx : y ∈ Icc a b) : HasDerivWithinAt dg (ddg y) (Icc a b) y := by
    -- The eventual expression for g'' has several terms that cancel, which we have to undo here
    -- so that the various HasDerivWithinAt theorems will have everything they need.
    let dfaky := derivWithin f (Icc a b) y
    rw [(by ring : ddg y = (1 / 2) * dfaky + ((1 / 2) * dfaky + ddg y) - dfaky)]
    refine fun_sub (fun_add (const_mul _ (const_add _ (h_df y hx).hasDerivWithinAt))
      (fun_mul (div_const (sub_const _ (hasDerivWithinAt_id _ _)) _) ?_))
      (h_df y hx).hasDerivWithinAt
    rw [iteratedDerivWithin_eq_iterate]
    exact (h_ddf y hx).hasDerivWithinAt
  -- Technically this would work for all x ≥ a, but we only need it for x ∈ Icc a b (and it makes
  -- more pure-mathematical sense that way).
  have bound_ddg (x : ℝ) (hx : x ∈ Icc a b) : |ddg x| ≤ (ζ / 2) * ((x - a) ^ 1) := by
    simp_rw [pow_one, ddg, abs_mul, abs_div, abs_two]
    grw [fpp_bound x, abs_of_nonneg (sub_nonneg.mpr hx.1), div_mul_comm]
  have key {φ φ' : ℝ → ℝ} (h : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x) (h0 : φ a = 0)
      {c : ℝ} {n : ℕ} (h_bound : ∀ t ∈ Icc a b, |φ' t| ≤ c * (t - a) ^ n) :
      ∀ t ∈ Icc a b, |φ t| ≤ c / (n + 1) * (t - a) ^ (n + 1) := by
    intro t ht
    have hB (x) : HasDerivAt (fun y ↦ c / (n + 1) * (y - a) ^ (n + 1)) (c * (x - a) ^ n) x := by
      convert!
        (hasDerivAt_const x (c / (n + 1))).mul
          (((hasDerivAt_id x).sub (hasDerivAt_const x a)).pow (n + 1)) using 1
      simp [sub_eq_add_neg, field]
    simpa [Real.norm_eq_abs, h0] using image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (fun x hx ↦ (h x hx).continuousWithinAt)
      (fun x hx ↦ by grind [Icc_mem_nhdsGE_of_mem, mono_of_mem_nhdsWithin])
      (by simp [h0]) hB (fun x hx ↦ h_bound x (Ico_subset_Icc_self hx)) ht
  exact (key h_dg (trapezoidal_error_eq f 1 a) (key h_ddg (by ring) bound_ddg) b
    ⟨a_lt_b.le, le_rfl⟩).trans_eq (by ring_nf)

/-- The hard part of the trapezoidal rule error bound: proving it in the case of a non-empty closed
interval with ordered endpoints. This lemma is used in the proof of the general error bound later
on. -/
/-
**trapezoidal_error_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hard part of the trapezoidal rule error bound: proving it in the case of a n
on-empty closed
interval with ordered endpoints. This lemma is used in the proof of the general 
error bound later
on.
-/
private lemma trapezoidal_error_le_of_lt {f : ℝ → ℝ} {ζ : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (h_df : DifferentiableOn ℝ f (Icc a b))
    (h_ddf : DifferentiableOn ℝ (derivWithin f (Icc a b)) (Icc a b))
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f (Icc a b) x| ≤ ζ)
    {N : ℕ} (N_nonzero : 0 < N) :
    |trapezoidal_error f N a b| ≤ (b - a) ^ 3 * ζ / (12 * N ^ 2) := by
  let h := (b - a) / N
  let ak (k : ℕ) := a + k * h
  have h0 : ∀ k : ℕ, ak (k + 1) - ak k = h := by simp [ak, ← sub_mul]
  have hab : 0 < b - a := sub_pos.mpr a_lt_b
  have hpos : 0 < h := by positivity
  have hb : b = a + N * h := by field
  rw [hb, ← sum_trapezoidal_error_adjacent_intervals N_nonzero
    (hb ▸ h_df.continuousOn.intervalIntegrable_of_Icc a_lt_b.le)]
  grw [abs_sum_le_sum_abs]
  suffices ∀ k ∈ range N, |trapezoidal_error f 1 (ak k) (ak (k + 1))| ≤ (ζ / 12) * h ^ 3 by
    norm_cast
    calc
      _ ≤ ∑ k ∈ range N, ζ / 12 * h ^ 3 := sum_le_sum this
      _ = N * (ζ / 12 * h ^ 3)          := by simp [sum_const]
      _ = _                             := by push_cast; field
  intro k hk
  rw [Finset.mem_range] at hk
  have h1 : a ≤ ak k := by simp only [ak, le_add_iff_nonneg_right]; positivity
  have h2 : ak (k + 1) ≤ b := by simp only [ak, hb]; grw [Nat.lt_iff_add_one_le.mp hk]
  have h3 : Icc (ak k) (ak (k + 1)) ⊆ Icc a b := Icc_subset_Icc h1 h2
  have h4 : ak k < ak (k + 1) := by rwa [← sub_pos, h0]
  have h5 : EqOn (derivWithin f (Icc a b))
      (derivWithin f (Icc (ak k) (ak (k + 1)))) (Icc (ak k) (ak (k + 1))) := by
    intro x hx
    rw [← derivWithin_subset h3 (uniqueDiffOn_Icc h4 x hx) (h_df x (h3 hx))]
  have h6 : EqOn (iteratedDerivWithin 2 f (Icc a b))
    (iteratedDerivWithin 2 f (Icc (ak k) (ak (k + 1)))) (Icc (ak k) (ak (k + 1))) := by
    intro x hx
    simp only [iteratedDerivWithin_succ', iteratedDerivWithin_zero]
    rw [← derivWithin_subset h3 (uniqueDiffOn_Icc h4 x hx) (h_ddf x (h3 hx))]
    exact derivWithin_congr h5 (h5 hx)
  have h7 (x : ℝ) : |iteratedDerivWithin 2 f (Set.Icc (ak k) (ak (k + 1))) x| ≤ ζ := by
    by_cases hx : x ∈ Icc (ak k) (ak (k + 1))
    · grw [← h6 hx, fpp_bound]
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
        (by rwa [closure_Icc]), abs_zero]
      exact (abs_nonneg _).trans (fpp_bound 0)
  refine (trapezoidal_error_le_of_lt' (ζ := ζ) h4 (h_df.mono h3) ?_ h7).trans_eq ?_
  · refine h_ddf.congr_mono (fun x hx ↦ ?_) h3
    exact derivWithin_subset h3 (uniqueDiffOn_Icc h4 x hx) (h_df x (h3 hx))
  · rw [h0, mul_div_assoc, mul_comm]

/-- The standard error bound for trapezoidal integration on the general interval `[[a, b]]`. -/
/-
**trapezoidal_error_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_error_le {f : Real -> Real} {a b : Real} (h_df : Differentiabl
eOn Real f [[a, b]]) (h_ddf : DifferentiableOn Real (derivWithin f [[a, b]]) [[a
, b]]) {ζ : Real} (fpp_bound : forall x, |iteratedDerivWithin 2 f [[a, b]] x| <=
 ζ) {N : Nat} (N_nonzero : 0 < N) : |trapezoidal_error f N a b| <= |b - a| ^ 3 *
 ζ / (12 * N ^ 2)
参数：h_df : DifferentiableOn Real f [[a, b]]；h_ddf : DifferentiableOn Real (derivW
ithin f [[a, b]]) [[a, b]]；fpp_bound : forall x, |iteratedDerivWithin 2 f [[a, b
]] x| <= ζ；N_nonzero : 0 < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
.0.trapezoidal_error_le_of_lt`：∀ {f : ℝ → ℝ} {ζ a b : ℝ},   a < b →     Differen
tiableOn ℝ f (Set.Icc a b) →       DifferentiableOn ℝ (derivWithin f (Set.Icc a 
b)) (Set.Ic…
· 使用引理 `Set.uIcc_of_lt`：uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `trapezoidal_error_eq`：trapezoidal_error_eq (f : Real -> Real) (N : Nat) 
(a : Real) : trapezoidal_error f N a a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The standard error bound for trapezoidal integration on the general interval `[[
a, b]]`.
-/
theorem trapezoidal_error_le {f : ℝ → ℝ} {a b : ℝ}
    (h_df : DifferentiableOn ℝ f [[a, b]])
    (h_ddf : DifferentiableOn ℝ (derivWithin f [[a, b]]) [[a, b]]) {ζ : ℝ}
    (fpp_bound : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) {N : ℕ} (N_nonzero : 0 < N) :
    |trapezoidal_error f N a b| ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  rcases lt_trichotomy a b with h_lt | h_eq | h_gt
  -- Standard case: a < b
  · rw [uIcc_of_lt h_lt] at *
    rw [abs_of_pos (sub_pos.mpr h_lt)]
    exact trapezoidal_error_le_of_lt h_lt h_df h_ddf fpp_bound N_nonzero
  -- Trivial case: a = b
  · simp [h_eq]
  -- Slightly trickier case: a > b (requires flipping the direction and sign of the true and
  -- approximate integrals)
  · rw [uIcc_of_gt h_gt] at *
    rw [abs_of_neg (sub_neg.mpr h_gt), neg_sub, trapezoidal_error_symm f N_nonzero a b, abs_neg]
    exact trapezoidal_error_le_of_lt h_gt h_df h_ddf fpp_bound N_nonzero

/-- The error bound for trapezoidal integration in the slightly weaker, but very common, case where
`f` is `C^2`. -/
/-
**trapezoidal_error_le_of_c2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trapezoidal_error_le_of_c2 {f : Real -> Real} {a b : Real} (h_f_c2 : ContD
iffOn Real 2 f [[a, b]]) {ζ : Real} (fpp_bound : forall x, |iteratedDerivWithin 
2 f [[a, b]] x| <= ζ) {N : Nat} (N_nonzero : 0 < N) : |trapezoidal_error f N a b
| <= |b - a| ^ 3 * ζ / (12 * N ^ 2)
参数：h_f_c2 : ContDiffOn Real 2 f [[a, b]]；fpp_bound : forall x, |iteratedDerivWit
hin 2 f [[a, b]] x| <= ζ；N_nonzero : 0 < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `trapezoidal_error_eq`：trapezoidal_error_eq (f : Real -> Real) (N : Nat) 
(a : Real) : trapezoidal_error f N a a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedDerivWithin_one`：iteratedDerivWithin_one : iteratedDerivWithin 1
 f s = derivWithin f s
· 使用定理 `ContDiffOn.differentiableOn_iteratedDerivWithin`：ContDiffOn.differentiab
leOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m
 < n) (hs : UniqueDiffOn 𝕜 s) : Diffe…
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `uniqueDiffOn_uIcc`：uniqueDiffOn_uIcc {a b : Real} (hab : a != b) : Uniqu
eDiffOn Real (uIcc a b)
· 使用定理 `trapezoidal_error_le`：trapezoidal_error_le {f : Real -> Real} {a b : Rea
l} (h_df : DifferentiableOn Real f [[a, b]]) (h_ddf : DifferentiableOn Real (der
ivWithin f…
· 使用定理 `ContDiffOn.differentiableOn`：ContDiffOn.differentiableOn (h : ContDiffOn
 𝕜 n f s) (hn : n != 0) : DifferentiableOn 𝕜 f s
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0

--- 原说明 ---
The error bound for trapezoidal integration in the slightly weaker, but very com
mon, case where
`f` is `C^2`.
-/
theorem trapezoidal_error_le_of_c2 {f : ℝ → ℝ} {a b : ℝ} (h_f_c2 : ContDiffOn ℝ 2 f [[a, b]])
    {ζ : ℝ} (fpp_bound : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) {N : ℕ}
    (N_nonzero : 0 < N) : |trapezoidal_error f N a b| ≤ |b - a| ^ 3 * ζ / (12 * N ^ 2) := by
  -- This use of rcases slightly duplicates effort from the proof of trapezoidal_error_le, but doing
  -- it any other way that I can think of would be worse.
  rcases eq_or_ne a b with h_eq | h_ne
  · simp [h_eq]
  -- Once we have a ≠ b, all the necessary assumptions on f follow pretty quickly from its being
  -- C^2.
  have h_ddf : DifferentiableOn ℝ (derivWithin f [[a, b]]) [[a, b]] := by
    rw [← iteratedDerivWithin_one]
    exact h_f_c2.differentiableOn_iteratedDerivWithin (by norm_cast) (uniqueDiffOn_uIcc h_ne)
  exact trapezoidal_error_le (h_f_c2.differentiableOn two_ne_zero) h_ddf fpp_bound N_nonzero
