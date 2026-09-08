/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Fourier transform of the Gaussian

We prove that the Fourier transform of the Gaussian function is another Gaussian:

* `integral_cexp_quadratic`: general formula for `∫ (x : ℝ), exp (b * x ^ 2 + c * x + d)`
* `fourierIntegral_gaussian`: for all complex `b` and `t` with `0 < re b`, we have
  `∫ x:ℝ, exp (I * t * x) * exp (-b * x^2) = (π / b) ^ (1 / 2) * exp (-t ^ 2 / (4 * b))`.
* `fourierIntegral_gaussian_pi`: a variant with `b` and `t` scaled to give a more symmetric
  statement, and formulated in terms of the Fourier transform operator `𝓕`.

We also give versions of these formulas in finite-dimensional inner product spaces, see
`integral_cexp_neg_mul_sq_norm_add` and `fourierIntegral_gaussian_innerProductSpace`.

-/

@[expose] public section

/-!
## Fourier integral of Gaussian functions
-/

open Real Set MeasureTheory Filter Asymptotics intervalIntegral

open scoped Real Topology FourierTransform RealInnerProductSpace

open Complex hiding exp continuous_exp

noncomputable section

namespace GaussianFourier

variable {b : ℂ}

/-- The integral of the Gaussian function over the vertical edges of a rectangle
with vertices at `(±T, 0)` and `(±T, c)`. -/
/-
**GaussianFourier.verticalIntegral** 是 Mathlib 中的一个定义，位于命名空间 `GaussianFourier`。
形式化陈述：verticalIntegral (b : Complex) (c T : Real) : Complex
参数：b : Complex；c T : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The integral of the Gaussian function over the vertical edges of a rectangle
with vertices at `(±T, 0)` and `(±T, c)`.
-/
def verticalIntegral (b : ℂ) (c T : ℝ) : ℂ :=
  ∫ y : ℝ in (0 : ℝ)..c, I * (cexp (-b * (T + y * I) ^ 2) - cexp (-b * (T - y * I) ^ 2))

/-- Explicit formula for the norm of the Gaussian function along the vertical
edges. -/
/-
**GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I** 是 Mathlib 中的一个定理，位于命名空间 `Gaus
sianFourier`。
形式化陈述：norm_cexp_neg_mul_sq_add_mul_I (b : Complex) (c T : Real) : ‖cexp (-b * (T
 + c * I) ^ 2)‖ = exp (-(b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2))
参数：b : Complex；c T : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit formula for the norm of the Gaussian function along the vertical
edges.
-/
theorem norm_cexp_neg_mul_sq_add_mul_I (b : ℂ) (c T : ℝ) :
    ‖cexp (-b * (T + c * I) ^ 2)‖ = exp (-(b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2)) := by
  rw [Complex.norm_exp, neg_mul, neg_re, ← re_add_im b]
  simp only [sq, re_add_im, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  ring_nf
/-
**GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I'** 是 Mathlib 中的一个定理，位于命名空间 `Gau
ssianFourier`。
形式化陈述：norm_cexp_neg_mul_sq_add_mul_I' (hb : b.re != 0) (c T : Real) : ‖cexp (-b 
* (T + c * I) ^ 2)‖ = exp (-(b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 
2 / b.re + b.re)))
参数：hb : b.re != 0；c T : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_ofNat`：∀ {α : Type u_1} [inst : GroupWith
Zero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a ↑n = a ^ n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
（共 87 条，此处仅展示前 30 条）
-/
theorem norm_cexp_neg_mul_sq_add_mul_I' (hb : b.re ≠ 0) (c T : ℝ) :
    ‖cexp (-b * (T + c * I) ^ 2)‖ =
      exp (-(b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re + b.re))) := by
  have :
    b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2 =
      b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re + b.re) := by
    field
  rw [norm_cexp_neg_mul_sq_add_mul_I, this]
/-
**GaussianFourier.verticalIntegral_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `GaussianFo
urier`。
形式化陈述：verticalIntegral_norm_le (hb : 0 < b.re) (c : Real) {T : Real} (hT : 0 <= 
T) : ‖verticalIntegral b c T‖ <= (2 : Real) * |c| * exp (-(b.re * T ^ 2 - (2 : R
eal) * |b.im| * |c| * T - b.re * c ^ 2))
参数：hb : 0 < b.re；c : Real；hT : 0 <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I`：norm_cexp_neg_mul_sq_add
_mul_I (b : Complex) (c T : Real) : ‖cexp (-b * (T + c * I) ^ 2)‖ = exp (-(b.re 
* T ^ 2 - 2 * b.im * c * T - b.re * …
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `sq_le_sq`：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
· 使用定理 `intervalIntegral.norm_integral_le_of_norm_le_const`：norm_integral_le_of_
norm_le_const {a b C : Real} {f : Real -> E} (h : forall x in Ι a b, ‖f x‖ <= C)
 : ‖∫ x in a..b, f x‖ <= C * |b - a|
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Set.abs_sub_left_of_mem_uIcc`：abs_sub_left_of_mem_uIcc (h : c in [[a, b]
]) : |c - a| <= |b - a|
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
（共 44 条，此处仅展示前 30 条）
-/
theorem verticalIntegral_norm_le (hb : 0 < b.re) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖verticalIntegral b c T‖ ≤
      (2 : ℝ) * |c| * exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
  -- first get uniform bound for integrand
  have vert_norm_bound :
    ∀ {T : ℝ},
      0 ≤ T →
        ∀ {c y : ℝ},
          |y| ≤ |c| →
            ‖cexp (-b * (T + y * I) ^ 2)‖ ≤
              exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
    intro T hT c y hy
    rw [norm_cexp_neg_mul_sq_add_mul_I b]
    gcongr exp (-(_ - ?_ * _ - _ * ?_))
    · (conv_lhs => rw [mul_assoc]); (conv_rhs => rw [mul_assoc])
      gcongr _ * ?_
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      gcongr
    · rwa [sq_le_sq]
  -- now main proof
  apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans
  · rw [sub_zero]
    conv_lhs => simp only [mul_comm _ |c|]
    conv_rhs =>
      conv =>
        congr
        rw [mul_comm]
      rw [mul_assoc]
  · intro y hy
    have absy : |y| ≤ |c| := by
      simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
    rw [norm_mul, norm_I, one_mul, two_mul]
    refine (norm_sub_le _ _).trans (add_le_add (vert_norm_bound hT absy) ?_)
    rw [← abs_neg y] at absy
    simpa only [neg_mul, ofReal_neg] using! vert_norm_bound hT absy
/-
**GaussianFourier.tendsto_verticalIntegral** 是 Mathlib 中的一个定理，位于命名空间 `GaussianFo
urier`。
形式化陈述：tendsto_verticalIntegral (hb : 0 < b.re) (c : Real) : Tendsto (verticalInt
egral b c) atTop (𝓝 0)
参数：hb : 0 < b.re；c : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 47 条，此处仅展示前 30 条）
-/
theorem tendsto_verticalIntegral (hb : 0 < b.re) (c : ℝ) :
    Tendsto (verticalIntegral b c) atTop (𝓝 0) := by
  -- complete proof using squeeze theorem:
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop (0 : ℝ)).mp
        (Eventually.of_forall fun T hT => verticalIntegral_norm_le hb c hT))
  rw [(by ring : 0 = 2 * |c| * 0)]
  refine (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)).const_mul _
  apply tendsto_atTop_add_const_right
  simp_rw [sq, ← mul_assoc, ← sub_mul]
  refine Tendsto.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _ ?_) tendsto_id
  exact (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
/-
**GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I** 是 Mathlib 中的一个定理，位
于命名空间 `GaussianFourier`。
形式化陈述：integrable_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : Real) : Int
egrable fun x : Real => cexp (-b * (x + c * I) ^ 2)
参数：hb : 0 < b.re；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add_const`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.hasFiniteIntegral_norm_iff`：hasFiniteIntegral_norm_iff (f 
: α -> β) : HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I'`：norm_cexp_neg_mul_sq_ad
d_mul_I' (hb : b.re != 0) (c T : Real) : ‖cexp (-b * (T + c * I) ^ 2)‖ = exp (-(
b.re * (T - b.im * c / b.re) ^ 2 - c …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
（共 40 条，此处仅展示前 30 条）
-/
theorem integrable_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
    Integrable fun x : ℝ => cexp (-b * (x + c * I) ^ 2) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq_add_mul_I' hb.ne', neg_sub _ (c ^ 2 * _),
    sub_eq_add_neg _ (b.re * _), Real.exp_add]
  suffices Integrable fun x : ℝ => exp (-(b.re * x ^ 2)) by
    exact (Integrable.comp_sub_right this (b.im * c / b.re)).hasFiniteIntegral.const_mul _
  simp_rw [← neg_mul]
  apply integrable_exp_neg_mul_sq hb
/-
**GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I** 是 Mathlib 中的一个定理，位于命
名空间 `GaussianFourier`。
形式化陈述：integral_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : Real) : ∫ x :
 Real, cexp (-b * (x + c * I) ^ 2) = (π / b) ^ (1 / 2 : Complex)
参数：hb : 0 < b.re；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral`：intervalIntegral_tendst
o_integral (hfi : Integrable f μ) (ha : Tendsto a l atBot) (hb : Tendsto b l atT
op) : Tendsto (fun i => ∫ x in a i..b…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I`：integrable_ce
xp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : Real) : Integrable fun x : Rea
l => cexp (-b * (x + c * I) ^ 2)
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`：integral_bou
ndary_rect_eq_zero_of_differentiableOn (f : Complex -> E) (z w : Complex) (H : D
ifferentiableOn Complex f ([[z.re, w.re]] ×Compl…
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `Differentiable.cexp`：Differentiable.cexp (hc : Differentiable 𝕜 f) : Dif
ferentiable 𝕜 fun x => Complex.exp (f x)
· 使用定理 `Differentiable.const_mul`：Differentiable.const_mul (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => b * a y
· 使用定理 `differentiable_pow`：differentiable_pow (n : Nat) : Differentiable 𝕜 fun 
x : 𝔸 => x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
（共 120 条，此处仅展示前 30 条）
-/
theorem integral_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
    ∫ x : ℝ, cexp (-b * (x + c * I) ^ 2) = (π / b) ^ (1 / 2 : ℂ) := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral (integrable_cexp_neg_mul_sq_add_real_mul_I hb c)
        tendsto_neg_atTop_atBot tendsto_id)
      ?_
  set I₁ := fun T => ∫ x : ℝ in -T..T, cexp (-b * (x + c * I) ^ 2) with HI₁
  let I₂ := fun T : ℝ => ∫ x : ℝ in -T..T, cexp (-b * (x : ℂ) ^ 2)
  let I₄ := fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..c, cexp (-b * (T + y * I) ^ 2)
  let I₅ := fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..c, cexp (-b * (-T + y * I) ^ 2)
  have C : ∀ T : ℝ, I₂ T - I₁ T + I * I₄ T - I * I₅ T = 0 := by
    intro T
    have :=
      integral_boundary_rect_eq_zero_of_differentiableOn (fun z => cexp (-b * z ^ 2)) (-T)
        (T + c * I)
        (by
          refine Differentiable.differentiableOn (Differentiable.const_mul ?_ _).cexp
          exact differentiable_pow 2)
    simpa only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re,
      ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, tsub_zero, add_im, mul_im,
      mul_one, zero_add, smul_eq_mul, ofReal_neg] using this
  simp_rw [id, ← HI₁]
  have : I₁ = fun T : ℝ => I₂ T + verticalIntegral b c T := by
    ext1 T
    specialize C T
    rw [sub_eq_zero] at C
    unfold verticalIntegral
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
    · simp_rw [(fun a b => by rw [sq]; ring_nf : ∀ a b : ℂ, (a - b * I) ^ 2 = (-a + b * I) ^ 2)]
      change I₁ T = I₂ T + I * (I₄ T - I₅ T)
      rw [mul_sub, ← C]
      abel
    all_goals apply Continuous.intervalIntegrable; fun_prop
  rw [this, ← add_zero ((π / b : ℂ) ^ (1 / 2 : ℂ)), ← integral_gaussian_complex hb]
  refine Tendsto.add ?_ (tendsto_verticalIntegral hb c)
  exact
    intervalIntegral_tendsto_integral (integrable_cexp_neg_mul_sq hb) tendsto_neg_atTop_atBot
      tendsto_id
/-
**GaussianFourier._root_.integral_cexp_quadratic** 是 Mathlib 中的一个定理，位于命名空间 `Gaus
sianFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.integral_cexp_quadratic (hb : b.re < 0) (c d : ℂ) :
    ∫ x : ℝ,
      cexp (b * x ^ 2 + c * x + d) = (π / -b) ^ (1 / 2 : ℂ) * cexp (d - c ^ 2 / (4 * b)) := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have h (x : ℝ) : cexp (b * x ^ 2 + c * x + d) =
      cexp (- -b * (x + c / (2 * b)) ^ 2) * cexp (d - c ^ 2 / (4 * b)) := by
    simp_rw [← Complex.exp_add]
    congr 1
    field
  simp_rw [h, MeasureTheory.integral_mul_const]
  rw [← re_add_im (c / (2 * b))]
  simp_rw [← add_assoc, ← ofReal_add]
  rw [integral_add_right_eq_self fun a : ℝ ↦ cexp (- -b * (↑a + ↑(c / (2 * b)).im * I) ^ 2),
    integral_cexp_neg_mul_sq_add_real_mul_I ((neg_re b).symm ▸ (neg_pos.mpr hb))]
/-
**GaussianFourier._root_.integrable_cexp_quadratic'** 是 Mathlib 中的一个引理，位于命名空间 `G
aussianFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.integrable_cexp_quadratic' (hb : b.re < 0) (c d : ℂ) :
    Integrable (fun (x : ℝ) ↦ cexp (b * x ^ 2 + c * x + d)) := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  by_contra H
  simpa [hb', pi_ne_zero, Complex.exp_ne_zero, integral_undef H]
    using integral_cexp_quadratic hb c d
/-
**GaussianFourier._root_.integrable_cexp_quadratic** 是 Mathlib 中的一个引理，位于命名空间 `Ga
ussianFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.integrable_cexp_quadratic (hb : 0 < b.re) (c d : ℂ) :
    Integrable (fun (x : ℝ) ↦ cexp (-b * x ^ 2 + c * x + d)) := by
  have : (-b).re < 0 := by simpa using hb
  exact integrable_cexp_quadratic' this c d
/-
**GaussianFourier._root_.fourierIntegral_gaussian** 是 Mathlib 中的一个定理，位于命名空间 `Gau
ssianFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.fourierIntegral_gaussian (hb : 0 < b.re) (t : ℂ) :
    ∫ x : ℝ, cexp (I * t * x) * cexp (-b * x ^ 2) =
    (π / b) ^ (1 / 2 : ℂ) * cexp (-t ^ 2 / (4 * b)) := by
  conv => enter [1, 2, x]; rw [← Complex.exp_add, add_comm, ← add_zero (-b * x ^ 2 + I * t * x)]
  rw [integral_cexp_quadratic (show (-b).re < 0 by rwa [neg_re, neg_lt_zero]), neg_neg, zero_sub,
    mul_neg, div_neg, neg_neg, mul_pow, I_sq, neg_one_mul, mul_comm]
/-
**GaussianFourier._root_.fourier_gaussian_pi'** 是 Mathlib 中的一个定理，位于命名空间 `Gaussia
nFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.fourier_gaussian_pi' (hb : 0 < b.re) (c : ℂ) :
    (𝓕 fun x : ℝ => cexp (-π * b * x ^ 2 + 2 * π * c * x)) = fun t : ℝ =>
    1 / b ^ (1 / 2 : ℂ) * cexp (-π / b * (t + I * c) ^ 2) := by
  have : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have h : (-↑π * b).re < 0 := by
    simpa only [neg_mul, neg_re, re_ofReal_mul, neg_lt_zero] using mul_pos pi_pos hb
  ext1 t
  simp_rw [fourier_real_eq_integral_exp_smul, smul_eq_mul, ← Complex.exp_add, ← add_assoc]
  have (x : ℝ) : ↑(-2 * π * x * t) * I + -π * b * x ^ 2 + 2 * π * c * x =
    -π * b * x ^ 2 + (-2 * π * I * t + 2 * π * c) * x + 0 := by push_cast; ring
  simp_rw [this, integral_cexp_quadratic h, neg_mul, neg_neg]
  congr 2
  · rw [← div_div, div_self <| ofReal_ne_zero.mpr pi_ne_zero, one_div, inv_cpow, ← one_div]
    rw [Ne, arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl hb.le
  · field_simp
    ring_nf
    simp only [I_sq]
    ring
/-
**GaussianFourier._root_.fourier_gaussian_pi** 是 Mathlib 中的一个定理，位于命名空间 `Gaussian
Fourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.fourier_gaussian_pi (hb : 0 < b.re) :
    (𝓕 fun (x : ℝ) ↦ cexp (-π * b * x ^ 2)) =
    fun t : ℝ ↦ 1 / b ^ (1 / 2 : ℂ) * cexp (-π / b * t ^ 2) := by
  simpa only [mul_zero, zero_mul, add_zero] using fourier_gaussian_pi' hb 0

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-
**GaussianFourier.integrable_cexp_neg_sum_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Gau
ssianFourier`。
形式化陈述：integrable_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι -> Complex}
 (hb : forall i, 0 < (b i).re) (c : ι -> Complex) : Integrable (fun (v : ι -> Re
al) => cexp (-∑ i, b i * (v i : Complex) ^ 2 + ∑ i, c i * v i))
参数：hb : forall i, 0 < (b i).re；c : ι -> Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
 exp (∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.Integrable.fintype_prod`：fintype_prod {E : Type*} {f : ι -
> E -> 𝕜} {mE : MeasurableSpace E} {μ : ι -> Measure E} [forall i, SigmaFinite (
μ i)] (hf : forall i, Integ…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `integrable_cexp_quadratic`：∀ {b : ℂ},   0 < b.re →     ∀ (c d : ℂ), Meas
ureTheory.Integrable (fun x => Complex.exp (-b * ↑x ^ 2 + c * ↑x + d)) MeasureTh
eory.volume
-/
theorem integrable_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℂ}
    (hb : ∀ i, 0 < (b i).re) (c : ι → ℂ) :
    Integrable (fun (v : ι → ℝ) ↦ cexp (-∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum, ← neg_mul]
  apply Integrable.fintype_prod (f := fun i (v : ℝ) ↦ cexp (-b i * v ^ 2 + c i * v)) (fun i ↦ ?_)
  convert! integrable_cexp_quadratic (hb i) (c i) 0 using 3 with x
  simp only [add_zero]
/-
**GaussianFourier.integrable_cexp_neg_mul_sum_add** 是 Mathlib 中的一个定理，位于命名空间 `Gau
ssianFourier`。
形式化陈述：integrable_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c
 : ι -> Complex) : Integrable (fun (v : ι -> Real) => cexp (-b * ∑ i, (v i : Com
plex) ^ 2 + ∑ i, c i * v i))
参数：hb : 0 < b.re；c : ι -> Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `GaussianFourier.integrable_cexp_neg_sum_mul_add`：integrable_cexp_neg_sum
_mul_add {ι : Type*} [Fintype ι] {b : ι -> Complex} (hb : forall i, 0 < (b i).re
) (c : ι -> Complex) : Integrable (fu…
-/
theorem integrable_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ι → ℂ) :
    Integrable (fun (v : ι → ℝ) ↦ cexp (-b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [neg_mul, Finset.mul_sum]
  exact integrable_cexp_neg_sum_mul_add (fun _ ↦ hb) c
/-
**GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace** 是 Math
lib 中的一个定理，位于命名空间 `GaussianFourier`。
形式化陈述：integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace {ι : Type*} [Fintype
 ι] (hb : 0 < b.re) (c : Complex) (w : EuclideanSpace Real ι) : Integrable (fun 
(v : EuclideanSpace Real ι) => cexp (- b * ‖v‖ ^ 2 + c * ⟪w, v⟫))
参数：hb : 0 < b.re；c : Complex；w : EuclideanSpace Real ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `PiLp.volume_preserving_toLp`：PiLp.volume_preserving_toLp : MeasurePreser
ving (@toLp 2 (ι -> Real))
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Complex.ofReal_sum`：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real)
 : Complex) = ∑ i in s, (f i : Complex)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 40 条，此处仅展示前 30 条）
-/
theorem integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ℂ) (w : EuclideanSpace ℝ ι) :
    Integrable (fun (v : EuclideanSpace ℝ ι) ↦ cexp (- b * ‖v‖ ^ 2 + c * ⟪w, v⟫)) := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [neg_mul, Function.comp_def]
  convert! integrable_cexp_neg_mul_sum_add hb (fun i ↦ c * w i) using 3 with v
  simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, ofReal_sum, ofReal_mul, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib,
    mul_assoc]
  norm_cast
  rw [sq_sqrt]
  · simp [Finset.mul_sum, mul_comm]
  · exact Finset.sum_nonneg (fun i _hi ↦ by positivity)

/-- In a real inner product space, the complex exponential of minus the square of the norm plus
a scalar product is integrable. Useful when discussing the Fourier transform of a Gaussian. -/
/-
**GaussianFourier.integrable_cexp_neg_mul_sq_norm_add** 是 Mathlib 中的一个定理，位于命名空间 
`GaussianFourier`。
形式化陈述：integrable_cexp_neg_mul_sq_norm_add (hb : 0 < b.re) (c : Complex) (w : V) 
: Integrable (fun (v : V) => cexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫))
参数：hb : 0 < b.re；c : Complex；w : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `LinearIsometryEquiv.inner_map_eq_flip`：LinearIsometryEquiv.inner_map_eq_
flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') : ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace`：i
ntegrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace {ι : Type*} [Fintype ι] (hb
 : 0 < b.re) (c : Complex) (w : EuclideanSpace Real ι) : In…

--- 原说明 ---
In a real inner product space, the complex exponential of minus the square of th
e norm plus
a scalar product is integrable. Useful when discussing the Fourier transform of 
a Gaussian.
-/
theorem integrable_cexp_neg_mul_sq_norm_add (hb : 0 < b.re) (c : ℂ) (w : V) :
    Integrable (fun (v : V) ↦ cexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫)) := by
  let e := (stdOrthonormalBasis ℝ V).repr.symm
  rw [← e.measurePreserving.integrable_comp_emb e.toHomeomorph.measurableEmbedding]
  convert! integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb c (e.symm w) with v
  simp only [neg_mul, Function.comp_apply, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.inner_map_eq_flip]
/-
**GaussianFourier.integral_cexp_neg_sum_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Gauss
ianFourier`。
形式化陈述：integral_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι -> Complex} (
hb : forall i, 0 < (b i).re) (c : ι -> Complex) : ∫ v : ι -> Real, cexp (-∑ i, b
 i * (v i : Complex) ^ 2 + ∑ i, c i * v i) = ∏ i, (π / b i) ^ (1 / 2 : Complex) 
* cexp (c i ^ 2 / (4 * b i))
参数：hb : forall i, 0 < (b i).re；c : ι -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
 exp (∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.integral_fintype_prod_volume_eq_prod`：integral_fintype_pro
d_volume_eq_prod {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜) [forall i, MeasureSp
ace (E i)] [forall i, SigmaFinite (volum…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
（共 36 条，此处仅展示前 30 条）
-/
theorem integral_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℂ}
    (hb : ∀ i, 0 < (b i).re) (c : ι → ℂ) :
    ∫ v : ι → ℝ, cexp (-∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * v i)
      = ∏ i, (π / b i) ^ (1 / 2 : ℂ) * cexp (c i ^ 2 / (4 * b i)) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum, ← neg_mul]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (v : ℝ) ↦ cexp (-b i * v ^ 2 + c i * v))]
  congr with i
  have : (-b i).re < 0 := by simpa using hb i
  convert! integral_cexp_quadratic this (c i) 0 using 1 <;> simp [div_neg]
/-
**GaussianFourier.integral_cexp_neg_mul_sum_add** 是 Mathlib 中的一个定理，位于命名空间 `Gauss
ianFourier`。
形式化陈述：integral_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c :
 ι -> Complex) : ∫ v : ι -> Real, cexp (-b * ∑ i, (v i : Complex) ^ 2 + ∑ i, c i
 * v i) = (π / b) ^ (Fintype.card ι / 2 : Complex) * cexp ((∑ i, c i ^ 2) / (4 *
 b))
参数：hb : 0 < b.re；c : ι -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `GaussianFourier.integral_cexp_neg_sum_mul_add`：integral_cexp_neg_sum_mul
_add {ι : Type*} [Fintype ι] {b : ι -> Complex} (hb : forall i, 0 < (b i).re) (c
 : ι -> Complex) : ∫ v : ι -> Real,…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ι → ℂ) :
    ∫ v : ι → ℝ, cexp (-b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * v i)
      = (π / b) ^ (Fintype.card ι / 2 : ℂ) * cexp ((∑ i, c i ^ 2) / (4 * b)) := by
  simp_rw [neg_mul, Finset.mul_sum, integral_cexp_neg_sum_mul_add (fun _ ↦ hb) c, one_div,
    Finset.prod_mul_distrib, Finset.prod_const, ← cpow_nat_mul, ← Complex.exp_sum, Fintype.card,
    Finset.sum_div, div_eq_mul_inv]
/-
**GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace** 是 Mathli
b 中的一个定理，位于命名空间 `GaussianFourier`。
形式化陈述：integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace {ι : Type*} [Fintype ι
] (hb : 0 < b.re) (c : Complex) (w : EuclideanSpace Real ι) : ∫ v : EuclideanSpa
ce Real ι, cexp (- b * ‖v‖ ^ 2 + c * ⟪w, v⟫) = (π / b) ^ (Fintype.card ι / 2 : C
omplex) * cexp (c ^ 2 * ‖w‖ ^ 2 / (4 * b))
参数：hb : 0 < b.re；c : Complex；w : EuclideanSpace Real ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `PiLp.volume_preserving_toLp`：PiLp.volume_preserving_toLp : MeasurePreser
ving (@toLp 2 (ι -> Real))
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 43 条，此处仅展示前 30 条）
-/
theorem integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ℂ) (w : EuclideanSpace ℝ ι) :
    ∫ v : EuclideanSpace ℝ ι, cexp (- b * ‖v‖ ^ 2 + c * ⟪w, v⟫) =
      (π / b) ^ (Fintype.card ι / 2 : ℂ) * cexp (c ^ 2 * ‖w‖ ^ 2 / (4 * b)) := by
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [neg_mul]
  convert! integral_cexp_neg_mul_sum_add hb (fun i ↦ c * w i) using 5 with _x y
  · simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, neg_mul, neg_inj, mul_eq_mul_left_iff]
    norm_cast
    left
    rw [sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi ↦ by positivity)
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ofReal_sum, ofReal_mul,
      Finset.mul_sum, mul_assoc]
    simp_rw [mul_comm]
  · simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum]
    congr
    norm_cast
    rw [sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi ↦ by positivity)
/-
**GaussianFourier.integral_cexp_neg_mul_sq_norm_add** 是 Mathlib 中的一个定理，位于命名空间 `G
aussianFourier`。
形式化陈述：integral_cexp_neg_mul_sq_norm_add (hb : 0 < b.re) (c : Complex) (w : V) : 
∫ v : V, cexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫) = (π / b) ^ (Module.finrank Real V / 2
 : Complex) * cexp (c ^ 2 * ‖w‖ ^ 2 / (4 * b))
参数：hb : 0 < b.re；c : Complex；w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instCountableFin`：∀ {n : ℕ}, Countable (Fin n)
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIsometryEquiv.inner_map_eq_flip`：LinearIsometryEquiv.inner_map_eq_
flip (f : E ≃ₗᵢ[𝕜] E') (x : E) (y : E') : ⟪f x, y⟫_𝕜 = ⟪x, f.symm y⟫_𝕜
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace`：int
egral_cexp_neg_mul_sq_norm_add_of_euclideanSpace {ι : Type*} [Fintype ι] (hb : 0
 < b.re) (c : Complex) (w : EuclideanSpace Real ι) : ∫ v …
-/
theorem integral_cexp_neg_mul_sq_norm_add
    (hb : 0 < b.re) (c : ℂ) (w : V) :
    ∫ v : V, cexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫) =
      (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (c ^ 2 * ‖w‖ ^ 2 / (4 * b)) := by
  let e := (stdOrthonormalBasis ℝ V).repr.symm
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  convert! integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb c (e.symm w) <;>
    simp [LinearIsometryEquiv.inner_map_eq_flip]
/-
**GaussianFourier.integral_cexp_neg_mul_sq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Gauss
ianFourier`。
形式化陈述：integral_cexp_neg_mul_sq_norm (hb : 0 < b.re) : ∫ v : V, cexp (-b * ‖v‖ ^ 
2) = (π / b) ^ (Module.finrank Real V / 2 : Complex)
参数：hb : 0 < b.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`：integral_cexp_neg_mul
_sq_norm_add (hb : 0 < b.re) (c : Complex) (w : V) : ∫ v : V, cexp (-b * ‖v‖ ^ 2
 + c * ⟪w, v⟫) = (π / b) ^ (Module.finr…
-/
theorem integral_cexp_neg_mul_sq_norm (hb : 0 < b.re) :
    ∫ v : V, cexp (-b * ‖v‖ ^ 2) = (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) := by
  simpa using integral_cexp_neg_mul_sq_norm_add hb 0 (0 : V)

set_option backward.isDefEq.respectTransparency.types false in
/-
**GaussianFourier.integral_rexp_neg_mul_sq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Gauss
ianFourier`。
形式化陈述：integral_rexp_neg_mul_sq_norm {b : Real} (hb : 0 < b) : ∫ v : V, rexp (-b 
* ‖v‖ ^ 2) = (π / b) ^ (Module.finrank Real V / 2 : Real)
参数：hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `LinearIsometry.integral_comp_comm`：integral_comp_comm (L : E ->ₗᵢ[𝕜] F) 
(φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GaussianFourier.integral_cexp_neg_mul_sq_norm`：integral_cexp_neg_mul_sq_
norm (hb : 0 < b.re) : ∫ v : V, cexp (-b * ‖v‖ ^ 2) = (π / b) ^ (Module.finrank 
Real V / 2 : Complex)
-/
theorem integral_rexp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    ∫ v : V, rexp (-b * ‖v‖ ^ 2) = (π / b) ^ (Module.finrank ℝ V / 2 : ℝ) := by
  rw [← ofReal_inj]
  convert! integral_cexp_neg_mul_sq_norm (show 0 < (b : ℂ).re from hb) (V := V)
  · change ofRealLI (∫ (v : V), rexp (-b * ‖v‖ ^ 2)) = ∫ (v : V), cexp (-↑b * ↑‖v‖ ^ 2)
    rw [← ofRealLI.integral_comp_comm]
    simp [ofRealLI]
  · rw [← ofReal_div, ofReal_cpow (by positivity)]
    simp
/-
**GaussianFourier._root_.fourier_gaussian_innerProductSpace'** 是 Mathlib 中的一个定理，
位于命名空间 `GaussianFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.fourier_gaussian_innerProductSpace' (hb : 0 < b.re) (x w : V) :
    𝓕 (fun v ↦ cexp (-b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪x, v⟫)) w =
      (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * ‖x - w‖ ^ 2 / b) := by
  simp only [neg_mul, fourier_eq', ofReal_neg, ofReal_mul, ofReal_ofNat,
    smul_eq_mul, ← Complex.exp_add, real_inner_comm w]
  convert! integral_cexp_neg_mul_sq_norm_add hb (2 * π * Complex.I) (x - w) using 3 with v
  · congr 1
    simp [inner_sub_left]
    ring
  · have : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
    simp [mul_pow]
    ring
/-
**GaussianFourier._root_.fourier_gaussian_innerProductSpace** 是 Mathlib 中的一个定理，位
于命名空间 `GaussianFourier`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.fourier_gaussian_innerProductSpace (hb : 0 < b.re) (w : V) :
    𝓕 (fun (v : V) ↦ cexp (-b * ‖v‖ ^ 2)) w =
      (π / b) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * ‖w‖ ^ 2 / b) := by
  simpa using fourier_gaussian_innerProductSpace' hb 0 w

end InnerProductSpace

end GaussianFourier

