/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Euler Product for the Riemann Zeta Function and Dirichlet L-Series

The first main result of this file is the Euler Product formula for the Riemann ζ function
$$\prod_p \frac{1}{1 - p^{-s}}
   = \lim_{n \to \infty} \prod_{p < n} \frac{1}{1 - p^{-s}} = \zeta(s)$$
for $s$ with real part $> 1$ ($p$ runs through the primes).
`riemannZeta_eulerProduct` is the second equality above. There are versions
`riemannZeta_eulerProduct_hasProd` and `riemannZeta_eulerProduct_tprod` in terms of `HasProd`
and `tprod`, respectively.

The second result is `dirichletLSeries_eulerProduct` (with variants
`dirichletLSeries_eulerProduct_hasProd` and `dirichletLSeries_eulerProduct_tprod`),
which is the analogous statement for Dirichlet L-series.
-/

@[expose] public section

open Complex

variable {s : ℂ}

/-- When `s ≠ 0`, the map `n ↦ n^(-s)` is completely multiplicative and vanishes at zero. -/
noncomputable
/-
**riemannZetaSummandHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZetaSummandHom (hs : s != 0) : Nat ->*₀ Complex where toFun n
参数：hs : s != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

/-- When `χ` is a Dirichlet character and `s ≠ 0`, the map `n ↦ χ n * n^(-s)` is completely
multiplicative and vanishes at zero. -/
noncomputable
/-
**dirichletSummandHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dirichletSummandHom {n : Nat} (χ : DirichletCharacter Complex n) (hs : s !
= 0) : Nat ->*₀ Complex where toFun n
参数：χ : DirichletCharacter Complex n；hs : s != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def dirichletSummandHom {n : ℕ} (χ : DirichletCharacter ℂ n) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := χ n * (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..

/-- When `s.re > 1`, the map `n ↦ n^(-s)` is norm-summable. -/
/-
**summable_riemannZetaSummand** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_riemannZetaSummand (hs : 1 < s.re) : Summable (fun n => ‖riemannZ
etaSummandHom (ne_zero_of_one_lt_re hs) n‖)
参数：hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_nonneg`：norm_cpow_eq_rpow_re_of_nonneg {
x : Real} (hx : 0 <= x) {y : Complex} (hy : re y != 0) : ‖(x : Complex) ^ y‖ = x
 ^ re y
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用引理 `Complex.re_neg_ne_zero_of_one_lt_re`：re_neg_ne_zero_of_one_lt_re {s : Co
mplex} (hs : 1 < s.re) : (-s).re != 0
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.summable_nat_rpow_inv`：summable_nat_rpow_inv {p : Real} : Summable 
(fun n => ((n : Real) ^ p)⁻¹ : Nat -> Real) ↔ 1 < p

--- 原说明 ---
When `s.re > 1`, the map `n ↦ n^(-s)` is norm-summable.
-/
lemma summable_riemannZetaSummand (hs : 1 < s.re) :
    Summable (fun n ↦ ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert! Real.summable_nat_rpow_inv.mpr hs with n
  rw [← ofReal_natCast,
    norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) <| re_neg_ne_zero_of_one_lt_re hs,
    neg_re, Real.rpow_neg <| Nat.cast_nonneg n]
/-
**tsum_riemannZetaSummand** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_riemannZetaSummand (hs : 1 < s.re) : ∑' (n : Nat), riemannZetaSummand
Hom (ne_zero_of_one_lt_re hs) n = riemannZeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用引理 `summable_riemannZetaSummand`：summable_riemannZetaSummand (hs : 1 < s.re)
 : Summable (fun n => ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zeta_eq_tsum_one_div_nat_add_one_cpow`：zeta_eq_tsum_one_div_nat_add_one_
cpow {s : Complex} (hs : 1 < re s) : riemannZeta s = ∑' n : Nat, 1 / (n + 1 : Co
mplex) ^ s
· 使用定理 `Summable.tsum_eq_zero_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [ins
t_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, S
ummable f → ∑' …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `MonoidWithZeroHom.mk.congr_simp`：∀ {α : Type u_7} {β : Type u_8} [inst :
 MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   (toZeroHom toZeroHom_1 : Zero
Hom α β) (e_toZeroHom…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tsum_riemannZetaSummand (hs : 1 < s.re) :
    ∑' (n : ℕ), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s := by
  have hsum := summable_riemannZetaSummand hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.of_norm.tsum_eq_zero_add, map_zero, zero_add]
  simp only [riemannZetaSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Nat.cast_add, Nat.cast_one, one_div]

/-- When `s.re > 1`, the map `n ↦ χ(n) * n^(-s)` is norm-summable. -/
/-
**summable_dirichletSummand** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_dirichletSummand {N : Nat} (χ : DirichletCharacter Complex N) (hs
 : 1 < s.re) : Summable (fun n => ‖dirichletSummandHom χ (ne_zero_of_one_lt_re h
s) n‖)
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `DirichletCharacter.norm_le_one`：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1
· 使用引理 `summable_riemannZetaSummand`：summable_riemannZetaSummand (hs : 1 < s.re)
 : Summable (fun n => ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖)

--- 原说明 ---
When `s.re > 1`, the map `n ↦ χ(n) * n^(-s)` is norm-summable.
-/
lemma summable_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ by positivity)
    (fun n ↦ mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

open scoped LSeries.notation in
/-
**tsum_dirichletSummand** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_dirichletSummand {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1
 < s.re) : ∑' (n : Nat), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗
χ s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `MonoidWithZeroHom.mk.congr_simp`：∀ {α : Type u_7} {β : Type u_8} [inst :
 MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   (toZeroHom toZeroHom_1 : Zero
Hom α β) (e_toZeroHom…
· 使用引理 `LSeries.term_of_ne_zero'`：term_of_ne_zero' {s : Complex} (hs : s != 0) (
f : Nat -> Complex) (n : Nat) : term f s n = f n / n ^ s
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tsum_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    ∑' (n : ℕ), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗χ s := by
  simp only [dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

open Filter Nat Topology EulerProduct

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `HasProd`. -/
/-
**riemannZeta_eulerProduct_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) : HasProd (fun p : Primes
 => (1 - (p : Complex) ^ (-s))⁻¹) (riemannZeta s)
参数：hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tsum_riemannZetaSummand`：tsum_riemannZetaSummand (hs : 1 < s.re) : ∑' (n
 : Nat), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s
· 使用定理 `EulerProduct.eulerProduct_completely_multiplicative_hasProd`：eulerProduc
t_completely_multiplicative_hasProd {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) :
 HasProd (fun p : Primes => (1 - f p)⁻¹) (∑' n, f…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `summable_riemannZetaSummand`：summable_riemannZetaSummand (hs : 1 < s.re)
 : Summable (fun n => ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖)

--- 原说明 ---
The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `HasProd`.
-/
theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative_hasProd <| summable_riemannZetaSummand hs

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `tprod`. -/
/-
**riemannZeta_eulerProduct_tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_eulerProduct_tprod (hs : 1 < s.re) : ∏' p : Primes, (1 - (p : 
Complex) ^ (-s))⁻¹ = riemannZeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `riemannZeta_eulerProduct_hasProd`：riemannZeta_eulerProduct_hasProd (hs :
 1 < s.re) : HasProd (fun p : Primes => (1 - (p : Complex) ^ (-s))⁻¹) (riemannZe
ta s)

--- 原说明 ---
The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `tprod`.
-/
theorem riemannZeta_eulerProduct_tprod (hs : 1 < s.re) :
    ∏' p : Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  (riemannZeta_eulerProduct_hasProd hs).tprod_eq

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products. -/
/-
**riemannZeta_eulerProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_eulerProduct (hs : 1 < s.re) : Tendsto (fun n : Nat => ∏ p in 
primesBelow n, (1 - (p : Complex) ^ (-s))⁻¹) atTop (𝓝 (riemannZeta s))
参数：hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tsum_riemannZetaSummand`：tsum_riemannZetaSummand (hs : 1 < s.re) : ∑' (n
 : Nat), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n = riemannZeta s
· 使用定理 `EulerProduct.eulerProduct_completely_multiplicative`：eulerProduct_comple
tely_multiplicative {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) : Tendsto (fun n 
: Nat => ∏ p in primesBelow n, (1 - f p)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `summable_riemannZetaSummand`：summable_riemannZetaSummand (hs : 1 < s.re)
 : Summable (fun n => ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖)

--- 原说明 ---
The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products.
-/
theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (riemannZeta s)) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative <| summable_riemannZetaSummand hs

open scoped LSeries.notation

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `HasProd`. -/
/-
**DirichletCharacter.LSeries_eulerProduct_hasProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirichletCharacter.LSeries_eulerProduct_hasProd {N : Nat} (χ : DirichletCh
aracter Complex N) (hs : 1 < s.re) : HasProd (fun p : Primes => (1 - χ p * (p : 
Complex) ^ (-s))⁻¹) (L ↗χ s)
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tsum_dirichletSummand`：tsum_dirichletSummand {N : Nat} (χ : DirichletCha
racter Complex N) (hs : 1 < s.re) : ∑' (n : Nat), dirichletSummandHom χ (ne_zero
_of_one_lt_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EulerProduct.eulerProduct_completely_multiplicative_hasProd`：eulerProduc
t_completely_multiplicative_hasProd {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) :
 HasProd (fun p : Primes => (1 - f p)⁻¹) (∑' n, f…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `summable_dirichletSummand`：summable_dirichletSummand {N : Nat} (χ : Diri
chletCharacter Complex N) (hs : 1 < s.re) : Summable (fun n => ‖dirichletSummand
Hom χ (ne_zero_…

--- 原说明 ---
The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `HasProd`.
-/
theorem DirichletCharacter.LSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (L ↗χ s) := by
  rw [← tsum_dirichletSummand χ hs]
  convert! eulerProduct_completely_multiplicative_hasProd <| summable_dirichletSummand χ hs

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `tprod`. -/
/-
**DirichletCharacter.LSeries_eulerProduct_tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirichletCharacter.LSeries_eulerProduct_tprod {N : Nat} (χ : DirichletChar
acter Complex N) (hs : 1 < s.re) : ∏' p : Primes, (1 - χ p * (p : Complex) ^ (-s
))⁻¹ = L ↗χ s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `DirichletCharacter.LSeries_eulerProduct_hasProd`：DirichletCharacter.LSer
ies_eulerProduct_hasProd {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < 
s.re) : HasProd (fun p : Primes => (1…

--- 原说明 ---
The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `tprod`.
-/
theorem DirichletCharacter.LSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    ∏' p : Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = L ↗χ s :=
  (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products. -/
/-
**DirichletCharacter.LSeries_eulerProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirichletCharacter.LSeries_eulerProduct {N : Nat} (χ : DirichletCharacter 
Complex N) (hs : 1 < s.re) : Tendsto (fun n : Nat => ∏ p in primesBelow n, (1 - 
χ p * (p : Complex) ^ (-s))⁻¹) atTop (𝓝 (L ↗χ s))
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tsum_dirichletSummand`：tsum_dirichletSummand {N : Nat} (χ : DirichletCha
racter Complex N) (hs : 1 < s.re) : ∑' (n : Nat), dirichletSummandHom χ (ne_zero
_of_one_lt_…
· 使用定理 `EulerProduct.eulerProduct_completely_multiplicative`：eulerProduct_comple
tely_multiplicative {f : Nat ->*₀ F} (hsum : Summable (‖f ·‖)) : Tendsto (fun n 
: Nat => ∏ p in primesBelow n, (1 - f p)⁻…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `summable_dirichletSummand`：summable_dirichletSummand {N : Nat} (χ : Diri
chletCharacter Complex N) (hs : 1 < s.re) : Summable (fun n => ‖dirichletSummand
Hom χ (ne_zero_…

--- 原说明 ---
The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products.
-/
theorem DirichletCharacter.LSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop
      (𝓝 (L ↗χ s)) := by
  rw [← tsum_dirichletSummand χ hs]
  apply eulerProduct_completely_multiplicative <| summable_dirichletSummand χ hs

open LSeries

/-- A variant of the Euler product for Dirichlet L-series. -/
/-
**DirichletCharacter.LSeries_eulerProduct_exp_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirichletCharacter.LSeries_eulerProduct_exp_log {N : Nat} (χ : DirichletCh
aracter Complex N) {s : Complex} (hs : 1 < s.re) : exp (∑' p : Nat.Primes, -log 
(1 - χ p * p ^ (-s))) = L ↗χ s
参数：χ : DirichletCharacter Complex N；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.ne_zero_of_one_lt_re`：ne_zero_of_one_lt_re {s : Complex} (hs : 1
 < s.re) : s != 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `dirichletSummandHom.eq_1`：∀ {s : ℂ} {n : ℕ} (χ : DirichletCharacter ℂ n)
 (hs : s ≠ 0),   dirichletSummandHom χ hs = { toFun := fun n_1 => χ ↑n_1 * ↑n_1 
^ (-s), map_ze…
· 使用定理 `MonoidWithZeroHom.mk.congr_simp`：∀ {α : Type u_7} {β : Type u_8} [inst :
 MulZeroOneClass α] [inst_1 : MulZeroOneClass β]   (toZeroHom toZeroHom_1 : Zero
Hom α β) (e_toZeroHom…
· 使用定理 `EulerProduct.exp_tsum_primes_log_eq_tsum`：exp_tsum_primes_log_eq_tsum {f
 : Nat ->*₀ Complex} (hsum : Summable (‖f ·‖)) : exp (∑' p : Nat.Primes, -log (1
 - f p)) = ∑' n : Nat, f n
· 使用引理 `summable_dirichletSummand`：summable_dirichletSummand {N : Nat} (χ : Diri
chletCharacter Complex N) (hs : 1 < s.re) : Summable (fun n => ‖dirichletSummand
Hom χ (ne_zero_…

--- 原说明 ---
A variant of the Euler product for Dirichlet L-series.
-/
theorem DirichletCharacter.LSeries_eulerProduct_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  let f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, map_zero]
    · simp only [ne_eq, hn, not_false_eq_true, term_of_ne_zero, div_eq_mul_inv,
        dirichletSummandHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, f]
  simpa only [LSeries, h]
    using! exp_tsum_primes_log_eq_tsum (f := f) <| summable_dirichletSummand χ hs

open DirichletCharacter

/-- A variant of the Euler product for the L-series of `ζ`. -/
/-
**ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : Complex} (hs : 1
 < s.re) : exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `DirichletCharacter.LSeries_eulerProduct_exp_log`：DirichletCharacter.LSer
ies_eulerProduct_exp_log {N : Nat} (χ : DirichletCharacter Complex N) {s : Compl
ex} (hs : 1 < s.re) : exp (∑' p : Nat…
· 使用引理 `DirichletCharacter.modOne_eq_one`：modOne_eq_one {R : Type*} [CommMonoidW
ithZero R] {χ : DirichletCharacter R 1} : ((χ ·) : Nat -> R) = 1

--- 原说明 ---
A variant of the Euler product for the L-series of `ζ`.
-/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert!
    modOne_eq_one (R := ℂ) ▸
      DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- A variant of the Euler product for the Riemann zeta function. -/
/-
**riemannZeta_eulerProduct_exp_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_eulerProduct_exp_log {s : Complex} (hs : 1 < s.re) : exp (∑' p
 : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log`：ArithmeticFunction
.LSeries_zeta_eulerProduct_exp_log {s : Complex} (hs : 1 < s.re) : exp (∑' p : N
at.Primes, -Complex.log (1 - p ^ (-s))) = …
· 使用引理 `LSeries_one_eq_riemannZeta`：LSeries_one_eq_riemannZeta {s : Complex} (hs
 : 1 < s.re) : L 1 s = riemannZeta s

--- 原说明 ---
A variant of the Euler product for the Riemann zeta function.
-/
theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

/-!
### Changing the level of a Dirichlet `L`-series
-/

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L-series
of `χ` considered as a Dirichlet character of level `N` from the L-series of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`. -/
/-
**DirichletCharacter.LSeries_changeLevel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DirichletCharacter.LSeries_changeLevel {M N : Nat} [NeZero N] (hMN : M ∣ N
) (χ : DirichletCharacter Complex M) {s : Complex} (hs : 1 < s.re) : LSeries ↗(c
hangeLevel hMN χ) s = LSeries ↗χ s * ∏ p in N.primeFactors, (1 - χ p * p ^ (-s))
参数：hMN : M ∣ N；χ : DirichletCharacter Complex M；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `prod_eq_tprod_mulIndicator`：prod_eq_tprod_mulIndicator (f : β -> α) (s :
 Finset β) (L
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirichletCharacter.LSeries_eulerProduct_tprod`：DirichletCharacter.LSerie
s_eulerProduct_tprod {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < s.re
) : ∏' p : Primes, (1 - χ p * (p : …
· 使用定理 `tprod_subtype`：tprod_subtype (s : Set β) (f : β -> α) : ∏' x : s, f x = 
∏' x, s.mulIndicator f x
· 使用定理 `Multipliable.tprod_mul`：∀ {α : Type u_1} {β : Type u_2} [inst : CommMono
id α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2S
pace α] [Con…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
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
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `multipliable_subtype_iff_mulIndicator`：multipliable_subtype_iff_mulIndic
ator {s : Set β} : Multipliable (f ∘ (↑) : s -> α) ↔ Multipliable (s.mulIndicato
r f)
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `DirichletCharacter.LSeries_eulerProduct_hasProd`：DirichletCharacter.LSer
ies_eulerProduct_hasProd {N : Nat} (χ : DirichletCharacter Complex N) (hs : 1 < 
s.re) : HasProd (fun p : Primes => (1…
· 使用引理 `Multipliable.of_finite`：Multipliable.of_finite [Finite β] [L.HasSupport]
 {f : β -> α} : Multipliable f L
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.mulIndicator_apply`：mulIndicator_apply (s : Set α) (f : α -> M) (a :
 α) [Decidable (a in s)] : mulIndicator s f a = if a in s then f a else 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain th
e L-series
of `χ` considered as a Dirichlet character of level `N` from the L-series of `χ`
 by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`.
-/
lemma DirichletCharacter.LSeries_changeLevel {M N : ℕ} [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rw [prod_eq_tprod_mulIndicator, ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs]
  -- convert to a form suitable for `tprod_subtype`
  have (f : Primes → ℂ) : ∏' (p : Primes), f p = ∏' (p : ↑{p : ℕ | p.Prime}), f p := rfl
  rw [this, tprod_subtype _ fun p : ℕ ↦ (1 - (changeLevel hMN χ) p * p ^ (-s))⁻¹,
    this, tprod_subtype _ fun p : ℕ ↦ (1 - χ p * p ^ (-s))⁻¹, ← Multipliable.tprod_mul]
  rotate_left -- deal with convergence goals first
  · exact multipliable_subtype_iff_mulIndicator.mp
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  · exact multipliable_subtype_iff_mulIndicator.mp Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors,
      ne_eq, mul_ite, mul_one]
    by_cases h : p.Prime; swap
    · simp only [h, false_and, if_false]
    simp only [h, true_and, if_true]
    by_cases hp' : p ∣ N; swap
    · simp only [hp', false_and, ↓reduceIte, inv_inj, sub_right_inj, mul_eq_mul_right_iff,
        cpow_eq_zero_iff, Nat.cast_eq_zero, h.ne_zero, ne_eq, neg_eq_zero, or_false]
      have hq : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd h).mpr hp'
      simp only [hq.unit_spec ▸ DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hq.unit,
        ZMod.cast_natCast hMN]
    · simp only [hp', NeZero.ne N, not_false_eq_true, and_self, ↓reduceIte]
      have : ¬IsUnit (p : ZMod N) := by rwa [ZMod.isUnit_prime_iff_not_dvd h, not_not]
      rw [MulChar.map_nonunit _ this, zero_mul, sub_zero, inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero, ne_comm]
      -- Remains to show `χ p * p ^ (-s) ≠ 1`. We show its norm is strictly `< 1`.
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖χ p‖ ≤ 1 := χ.norm_le_one p
      have hb : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := norm_prime_cpow_le_one_half ⟨p, h⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt (by norm_num)).ne

section LogDirichlet

open Real hiding log exp_nat_mul exp_add
open ArithmeticFunction Primes Summable

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}

/-- For `1 < s.re`, the sum over primes of `-log (1 - χ p * p ^ (-s))` — the logarithm of the Euler
product — equals the `L`-series of `n ↦ χ n * Λ n / Real.log n`.
-/
/-
**DirichletCharacter.eulerProduct_log_eq_LSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) : ∑' p : Pr
imes, -log (1 - χ p * p ^ (-s)) = LSeries (fun n => χ n * Λ n / Real.log n) s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `DirichletCharacter.norm_le_one`：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Complex.norm_natCast_cpow_of_pos`：norm_natCast_cpow_of_pos {n : Nat} (hn
 : 0 < n) (s : Complex) : ‖(n : Complex) ^ s‖ = (n : Real) ^ (s.re)
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.rpow_lt_one_of_one_lt_of_neg`：rpow_lt_one_of_one_lt_of_neg {x z : R
eal} (hx : 1 < x) (hz : z < 0) : x ^ z < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 194 条，此处仅展示前 30 条）

--- 原说明 ---
For `1 < s.re`, the sum over primes of `-log (1 - χ p * p ^ (-s))` — the logarit
hm of the Euler
product — equals the `L`-series of `n ↦ χ n * Λ n / Real.log n`.
-/
theorem DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) :
    ∑' p : Primes, -log (1 - χ p * p ^ (-s)) = LSeries (fun n ↦ χ n * Λ n / Real.log n) s := by
  have hpow_le (p : Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    grw [norm_mul, norm_le_one, norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    apply rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  rw [tsum_congr (fun p ↦ (hasSum_taylorSeries_neg_log' (hpow_le p)).tsum_eq.symm),
    LSeries_def₀ (by simp)]
  let f : ℕ → ℂ := fun n ↦ χ n * Λ n / Real.log n * ((n : ℂ) ^ (-s))
  calc
    _ = ∑' (p : Primes) (k : ℕ), (χ (p ^ (k + 1)) * ((p ^ (k + 1) : ℕ) : ℂ) ^ (-s)) *
          Λ (p ^ (k + 1)) / Real.log (p ^ (k + 1)) := by
      refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
      have : Complex.log p ≠ 0 := mod_cast p.prop.log_ne_zero
      simp [mul_pow, ← cpow_nat_mul, ← natCast_cpow_natCast_mul, vonMangoldt_apply_pow,
        vonMangoldt_apply_prime p.2, field]
    _ = ∑' n : {n : ℕ // IsPrimePow n}, f n := by
      rw [← tsum_primes_pow_eq]
      · exact tsum_congr fun p ↦ tsum_congr fun k ↦ (by unfold f; simp; ring)
      · apply comp_injective _ Subtype.coe_injective (f := f)
        apply of_norm_bounded_eventually_nat (g := (↑· ^ (-s.re)))
        · simp [hs]
        · filter_upwards [eventually_gt_atTop 1] with n hn
          simp only [f, norm_mul, norm_div, norm_real, norm_eq_abs]
          grw [norm_le_one, vonMangoldt_le_log]
          have := log_pos (x := n) (mod_cast hn)
          field_simp
          rw [← ofReal_natCast n, norm_cpow_eq_rpow_re_of_nonneg (by simp) (by simp; grind)]
          simp
    _ = _ := by
      simp only [div_eq_mul_inv _ (_ ^ _), ← cpow_neg]
      suffices (Function.support f) ⊆ {n | IsPrimePow n} from
        tsum_subtype_eq_of_support_subset this
      intro n hn
      contrapose! hn
      simp [f, vonMangoldt_eq_zero_iff.mpr hn]

/-- For `1 < s.re`, the Dirichlet L-function is the exponential of the `L`-series of
`n ↦ χ n * Λ n / Real.log n`.
-/
/-
**DirichletCharacter.LSeries_eq_exp_LSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirichletCharacter.LSeries_eq_exp_LSeries (hs : 1 < s.re) : exp (LSeries (
fun (n : Nat) => χ n * Λ n / Real.log n) s) = L ↗χ s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirichletCharacter.eulerProduct_log_eq_LSeries`：DirichletCharacter.euler
Product_log_eq_LSeries (hs : 1 < s.re) : ∑' p : Primes, -log (1 - χ p * p ^ (-s)
) = LSeries (fun n => χ n * Λ n / Re…
· 使用定理 `DirichletCharacter.LSeries_eulerProduct_exp_log`：DirichletCharacter.LSer
ies_eulerProduct_exp_log {N : Nat} (χ : DirichletCharacter Complex N) {s : Compl
ex} (hs : 1 < s.re) : exp (∑' p : Nat…

--- 原说明 ---
For `1 < s.re`, the Dirichlet L-function is the exponential of the `L`-series of
`n ↦ χ n * Λ n / Real.log n`.
-/
theorem DirichletCharacter.LSeries_eq_exp_LSeries (hs : 1 < s.re) :
    exp (LSeries (fun (n : ℕ) ↦ χ n * Λ n / Real.log n) s) = L ↗χ s := by
  rw [← eulerProduct_log_eq_LSeries χ hs, LSeries_eulerProduct_exp_log χ hs]
/-
**riemannZeta_eq_exp_LSeries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_eq_exp_LSeries {s : Complex} (hs : 1 < s.re) : exp (LSeries (f
un (n : Nat) => Λ n / Real.log n) s) = riemannZeta s
参数：hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries_one_eq_riemannZeta`：LSeries_one_eq_riemannZeta {s : Complex} (hs
 : 1 < s.re) : L 1 s = riemannZeta s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DirichletCharacter.LSeries_eq_exp_LSeries`：DirichletCharacter.LSeries_eq
_exp_LSeries (hs : 1 < s.re) : exp (LSeries (fun (n : Nat) => χ n * Λ n / Real.l
og n) s) = L ↗χ s
-/
theorem riemannZeta_eq_exp_LSeries {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries (fun (n : ℕ) ↦ Λ n / Real.log n) s) = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter ℂ 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

/-- For real `s > 1`, the logarithm of the (real) Riemann zeta function equals
`∑' n, Λ n / (n ^ s * Real.log n)`, where `Λ` is the von Mangoldt function.
-/
/-
**log_riemannZeta_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：log_riemannZeta_eq {s : Real} (hs : 1 < s) : Real.log (riemannZeta (s : Co
mplex)).re = ∑' n, Λ n / (n ^ s * Real.log n)
参数：hs : 1 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `riemannZeta_eq_exp_LSeries`：riemannZeta_eq_exp_LSeries {s : Complex} (hs
 : 1 < s.re) : exp (LSeries (fun (n : Nat) => Λ n / Real.log n) s) = riemannZeta
 s
· 使用引理 `LSeries_def₀`：LSeries_def₀ {f : Nat -> Complex} (hf : f 0 = 0) (s : Comp
lex) : LSeries f s = ∑' n, f n / (n ^ s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.natCast_log`：natCast_log {n : Nat} : Real.log n = log n
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
For real `s > 1`, the logarithm of the (real) Riemann zeta function equals
`∑' n, Λ n / (n ^ s * Real.log n)`, where `Λ` is the von Mangoldt function.
-/
theorem log_riemannZeta_eq {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re = ∑' n, Λ n / (n ^ s * Real.log n) := by
  rw [← riemannZeta_eq_exp_LSeries (by simpa using hs), LSeries_def₀ (by simp)]
  convert Real.log_exp _
  convert exp_ofReal_re _
  push_cast
  congr! 2 with p
  rw [ofReal_cpow (by positivity)]
  simp [field]

end LogDirichlet

