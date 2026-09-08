/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Hensel's lemma on `ℤ_p`

This file proves Hensel's lemma on `ℤ_p`, roughly following Keith Conrad's writeup:
<http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>

Hensel's lemma gives a simple condition for the existence of a root of a polynomial.

The proof and motivation are described in the paper
[R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019].

## References

* <http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/Hensel%27s_lemma>

## Tags

p-adic, p adic, padic, p-adic integer
-/

public section


noncomputable section

open Topology

-- We begin with some general lemmas that are used below in the computation.
/-
**padic_polynomial_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padic_polynomial_dist {p : Nat} [Fact p.Prime] {R : Type*} [CommSemiring R
] [Algebra R Int_[p]] (F : Polynomial R) (x y : Int_[p]) : ‖F.aeval x - F.aeval 
y‖ <= ‖x - y‖
参数：F : Polynomial R；x y : Int_[p]。
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
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem padic_polynomial_dist {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
    (F : Polynomial R) (x y : ℤ_[p]) :
    ‖F.aeval x - F.aeval y‖ ≤ ‖x - y‖ := by
  let ⟨z, hz⟩ := (F.map (algebraMap R ℤ_[p])).evalSubFactor x y
  simp only [Polynomial.eval_map_algebraMap] at hz
  calc
    ‖F.aeval x - F.aeval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ ≤ 1 * ‖x - y‖ := by gcongr; apply PadicInt.norm_le_one
    _ = ‖x - y‖ := by simp

open Filter Metric
/-
**comp_tendsto_lim** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem comp_tendsto_lim {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]}
    (ncs : CauSeq ℤ_[p] norm) : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 (F.eval ncs.lim)) :=
  Filter.Tendsto.comp (@Polynomial.continuousAt _ _ _ _ F _) ncs.tendsto_limit

section

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {ncs : CauSeq ℤ_[p] norm} {F : Polynomial R}
  {a : ℤ_[p]} (ncs_der_val : ∀ n, ‖F.derivative.aeval (ncs n)‖ = ‖F.derivative.aeval a‖)

/-
**ncs_tendsto_lim** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ncs_tendsto_lim :
    Tendsto (fun i => ‖F.derivative.aeval (ncs i)‖) atTop (𝓝 ‖F.derivative.aeval ncs.lim‖) := by
  refine Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) ?_
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

include ncs_der_val
/-
**ncs_tendsto_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ncs_tendsto_const :
    Tendsto (fun i => ‖F.derivative.aeval (ncs i)‖) atTop (𝓝 ‖F.derivative.aeval a‖) := by
  convert! @tendsto_const_nhds ℝ _ ℕ _ _; rw [ncs_der_val]
/-
**norm_deriv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_deriv_eq : ‖F.derivative.aeval ncs.lim‖ = ‖F.derivative.aeval a‖ :=
  tendsto_nhds_unique ncs_tendsto_lim (ncs_tendsto_const ncs_der_val)

end

section


variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {ncs : CauSeq ℤ_[p] norm} {F : Polynomial R}
  (hnorm : Tendsto (fun i => ‖F.aeval (ncs i)‖) atTop (𝓝 0))
include hnorm

/-
**tendsto_zero_of_norm_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tendsto_zero_of_norm_tendsto_zero :
    Tendsto (fun i => F.aeval (ncs i)) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hnorm)
/-
**limit_zero_of_norm_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：limit_zero_of_norm_tendsto_zero : F.aeval ncs.lim = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.comp_tendsto_lim`：∀ {p : ℕ
} [inst : Fact (Nat.Prime p)] {F : Polynomial ℤ_[p]} (ncs : CauSeq ℤ_[p] norm), 
  Filter.Tendsto (fun i => Polynomial.eval (↑ncs i) …
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.tendsto_zero_of_norm_tends
to_zero`：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemi
ring R] [inst_2 : Algebra R ℤ_[p]]   {ncs : CauSeq ℤ_[p] norm} {F : P…
-/
theorem limit_zero_of_norm_tendsto_zero : F.aeval ncs.lim = 0 := by
  refine tendsto_nhds_unique ?_ (tendsto_zero_of_norm_tendsto_zero hnorm)
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

end

/-
**a_soln_is_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem a_soln_is_unique {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R]
    [Algebra R ℤ_[p]] {F : Polynomial R} {a : ℤ_[p]} (ha : F.aeval a = 0) (z' : ℤ_[p])
    (hz' : F.aeval z' = 0) (hnormz' : ‖z' - a‖ < ‖F.derivative.aeval a‖) : z' = a := by
  let h := z' - a
  let ⟨q, hq⟩ := (F.map (algebraMap R ℤ_[p])).binomExpansion a h
  simp only [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hq
  have : (F.derivative.aeval a + q * h) * h = 0 := by calc
    _ = F.aeval (a + h) := by rw [hq, ha, zero_add, sq, right_distrib, mul_assoc]
    _ = _ := show F.aeval (a + (z' - a)) = 0 by simp [hz']
  have : h = 0 := by_contra fun hne ↦
    have : F.derivative.aeval a + q * h = 0 :=
      (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
    have : F.derivative.aeval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
    lt_irrefl ‖F.derivative.aeval a‖
      (calc
        ‖F.derivative.aeval a‖ = ‖q‖ * ‖h‖ := by simp [this]
        _ ≤ 1 * ‖h‖ := by gcongr; apply PadicInt.norm_le_one
        _ < ‖F.derivative.aeval a‖ := by simpa)
  exact eq_of_sub_eq_zero (by rw [← this])

section Hensel

open Nat

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  (F : Polynomial R) (a : ℤ_[p])

/-- `T` is an auxiliary value that is used to control the behavior of the polynomial `F`. -/
/-
**T_gen** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`T` is an auxiliary value that is used to control the behavior of the polynomial
 `F`.
-/
private def T_gen : ℝ := ‖F.aeval a / ((F.derivative.aeval a ^ 2 : ℤ_[p]) : ℚ_[p])‖

local notation "T" => @T_gen p _ _ _ _ F a

variable {p F a}
/-
**T_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_def : T = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ ^ 2 := by
  simp [T_gen]
/-
**T_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_nonneg : 0 ≤ T := norm_nonneg _
/-
**T_pow_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_pow_nonneg (n : ℕ) : 0 ≤ T ^ n := pow_nonneg T_nonneg _

variable (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)
include hnorm
/-
**deriv_sq_norm_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem deriv_sq_norm_pos : 0 < ‖F.derivative.aeval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg _) hnorm
/-
**deriv_sq_norm_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem deriv_sq_norm_ne_zero : ‖F.derivative.aeval a‖ ^ 2 ≠ 0 :=
  ne_of_gt (deriv_sq_norm_pos hnorm)
/-
**deriv_norm_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem deriv_norm_ne_zero : ‖F.derivative.aeval a‖ ≠ 0 := fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])
/-
**deriv_norm_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem deriv_norm_pos : 0 < ‖F.derivative.aeval a‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))
/-
**deriv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem deriv_ne_zero : F.derivative.aeval a ≠ 0 :=
  mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)
/-
**T_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_lt_one : T < 1 := by
  have h := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm
  rw [T_def]; exact h
/-
**T_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_pow {n : ℕ} (hn : n ≠ 0) : T ^ n < 1 := pow_lt_one₀ T_nonneg (T_lt_one hnorm) hn
/-
**T_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_pow' (n : ℕ) : T ^ 2 ^ n < 1 := T_pow hnorm (pow_ne_zero _ two_ne_zero)

/-- We will construct a sequence of elements of `ℤ_p` satisfying successive values of `ih`. -/
/-
**ih_gen** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We will construct a sequence of elements of `ℤ_p` satisfying successive values o
f `ih`.
-/
private def ih_gen (n : ℕ) (z : ℤ_[p]) : Prop :=
  ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧ ‖F.aeval z‖ ≤
    ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n

local notation "ih" => @ih_gen p _ _ _ _ F a
/-
**ih_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ih_0 : ih 0 a :=
  ⟨rfl, by simp [T_def, mul_div_cancel₀ _ (ne_of_gt (deriv_sq_norm_pos hnorm))]⟩
/-
**calc_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem calc_norm_le_one {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    ‖(↑(F.aeval z) : ℚ_[p]) / ↑(F.derivative.aeval z)‖ ≤ 1 :=
  calc
    ‖(↑(F.aeval z) : ℚ_[p]) / ↑(F.derivative.aeval z)‖ =
        ‖(↑(F.aeval z) : ℚ_[p])‖ / ‖(↑(F.derivative.aeval z) : ℚ_[p])‖ :=
      norm_div _ _
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := by simp [hz.1]
    _ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ ≤ 1 := mul_le_one₀ (PadicInt.norm_le_one _) (T_pow_nonneg _) (le_of_lt (T_pow' hnorm _))
/-
**calc_deriv_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem calc_deriv_dist {z z' z1 : ℤ_[p]} (hz' : z' = z - z1)
    (hz1 : ‖z1‖ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖) {n} (hz : ih n z) :
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
  calc
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ ≤ ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖z1‖ := by simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = ‖F.aeval z‖ / ‖F.derivative.aeval a‖ := hz1
    _ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
    _ < ‖F.derivative.aeval a‖ := (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2
      (T_pow' hnorm _)


set_option backward.isDefEq.respectTransparency false in
/-
**calc_eval_z'** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def calc_eval_z' {z z' z1 : ℤ_[p]} (hz' : z' = z - z1) {n} (hz : ih n z)
    (h1 : ‖(↑(F.aeval z) : ℚ_[p]) / ↑(F.derivative.aeval z)‖ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
    { q : ℤ_[p] // F.aeval z' = q * z1 ^ 2 } := by
  have hdzne : F.derivative.aeval z ≠ 0 :=
    mt norm_eq_zero.2 (by rw [hz.1]; apply deriv_norm_ne_zero; assumption)
  have hdzne' : (↑(F.derivative.aeval z) : ℚ_[p]) ≠ 0 := fun h => hdzne (Subtype.ext_iff.2 h)
  obtain ⟨q, hq⟩ := (F.map (algebraMap R ℤ_[p])).binomExpansion z (-z1)
  have : ‖(↑(F.derivative.aeval z) * (↑(F.aeval z) / ↑(F.derivative.aeval z)) : ℚ_[p])‖ ≤ 1 := by
    simpa using mul_le_one₀ (PadicInt.norm_le_one _) (norm_nonneg _) h1
  have : F.derivative.aeval z * -z1 = -F.aeval z := by
    calc
      F.derivative.aeval z * -z1 =
          F.derivative.aeval z * -⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩ := by rw [hzeq]
      _ = -(F.derivative.aeval z * ⟨↑(F.aeval z) / ↑(F.derivative.aeval z), h1⟩) := mul_neg _ _
      _ = -⟨F.derivative.aeval z * (F.aeval z / (F.derivative.aeval z : ℤ_[p]) : ℚ_[p]), this⟩ :=
        (Subtype.ext <| by simp only [PadicInt.coe_neg, PadicInt.coe_mul])
      _ = -F.aeval z := by simp only [mul_div_cancel₀ _ hdzne', Subtype.coe_eta]
  exact ⟨q, by simpa [sub_eq_add_neg, neg_mul_eq_mul_neg, this, hz'] using hq⟩

set_option linter.defProp false in
/-
**calc_eval_z'_norm** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def calc_eval_z'_norm {z z' z1 : ℤ_[p]} {n} (hz : ih n z) {q}
    (heq : F.aeval z' = q * z1 ^ 2)
    (h1 : ‖(↑(F.aeval z) : ℚ_[p]) / ↑(F.derivative.aeval z)‖ ≤ 1) (hzeq : z1 = ⟨_, h1⟩) :
    ‖F.aeval z'‖ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by
  calc
    ‖F.aeval z'‖ = ‖q‖ * ‖z1‖ ^ 2 := by simp [heq]
    _ ≤ 1 * ‖z1‖ ^ 2 := by gcongr; apply PadicInt.norm_le_one
    _ = ‖F.aeval z‖ ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by simp [hzeq, hz.1, div_pow]
    _ ≤ (‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.aeval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.aeval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]


/-- Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer. -/
/-
**ih_n** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+
1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer.
-/
private def ih_n {n : ℕ} {z : ℤ_[p]} (hz : ih n z) : { z' : ℤ_[p] // ih (n + 1) z' } :=
  have h1 : ‖(↑(F.aeval z) : ℚ_[p]) / ↑(F.derivative.aeval z)‖ ≤ 1 := calc_norm_le_one hnorm hz
  let z1 : ℤ_[p] := ⟨_, h1⟩
  let z' : ℤ_[p] := z - z1
  ⟨z',
    have hdist : ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
      calc_deriv_dist hnorm rfl (by simp [z1, hz.1]) hz
    have hfeq : ‖F.derivative.aeval z'‖ = ‖F.derivative.aeval a‖ := by
      rw [sub_eq_add_neg, ← hz.1, ← norm_neg (F.derivative.aeval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨_, heq⟩ := calc_eval_z' hnorm rfl hz h1 rfl
    have hnle : ‖F.aeval z'‖ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hz heq h1 rfl
    ⟨hfeq, hnle⟩⟩
/-
**newton_seq_aux** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def newton_seq_aux : ∀ n : ℕ, { z : ℤ_[p] // ih n z }
  | 0 => ⟨a, ih_0 hnorm⟩
  | k + 1 => ih_n hnorm (newton_seq_aux k).2
/-
**newton_seq_gen** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def newton_seq_gen (n : ℕ) : ℤ_[p] :=
  (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm
/-
**newton_seq_deriv_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_deriv_norm (n : ℕ) :
    ‖F.derivative.aeval (newton_seq n)‖ = ‖F.derivative.aeval a‖ :=
  (newton_seq_aux hnorm n).2.1
/-
**newton_seq_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_norm_le (n : ℕ) :
    ‖F.aeval (newton_seq n)‖ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n :=
  (newton_seq_aux hnorm n).2.2

set_option backward.isDefEq.respectTransparency false in
/-
**newton_seq_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_norm_eq (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ =
    ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval (newton_seq n)‖ := by
  rw [newton_seq_gen, newton_seq_gen, newton_seq_aux, ih_n]
  simp [sub_eq_add_neg, add_comm]
/-
**newton_seq_succ_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_succ_dist (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
  calc
    ‖newton_seq (n + 1) - newton_seq n‖ =
        ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval (newton_seq n)‖ :=
      newton_seq_norm_eq hnorm _
    _ = ‖F.aeval (newton_seq n)‖ / ‖F.derivative.aeval a‖ := by rw [newton_seq_deriv_norm]
    _ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ := by
      gcongr
      apply newton_seq_norm_le
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _
/-
**newton_seq_dist_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_dist_aux (n : ℕ) :
    ∀ k : ℕ, ‖newton_seq (n + k) - newton_seq n‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n
  | 0 => by simp [T_pow_nonneg, mul_nonneg]
  | k + 1 =>
    have : 2 ^ n ≤ 2 ^ (n + k) := by
      apply pow_right_mono₀
      · simp
      · apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ ≤ max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ ≤ max (‖F.derivative.aeval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.aeval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _ _) (newton_seq_dist_aux _ _))
      _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
        max_eq_right <|
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
            (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _)
/-
**newton_seq_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_dist {n k : ℕ} (hnk : n ≤ k) :
    ‖newton_seq k - newton_seq n‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n := by
  have hex : ∃ m, k = n + m := Nat.exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex']; apply newton_seq_dist_aux
/-
**bound'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bound' : Tendsto (fun n : ℕ => ‖F.derivative.aeval a‖ * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.aeval a‖]
  exact
    tendsto_const_nhds.mul
      (Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (T_lt_one hnorm))
        (tendsto_pow_atTop_atTop_of_one_lt (by simp)))
/-
**bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bound :
    ∀ {ε}, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → ‖F.derivative.aeval a‖ * T ^ 2 ^ n < ε := fun hε ↦
  eventually_atTop.1 <| (bound' hnorm).eventually <| gt_mem_nhds hε
/-
**bound'_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bound'_sq :
    Tendsto (fun n : ℕ => ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.aeval a‖, sq]
  simp only [mul_assoc]
  apply Tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption
/-
**newton_seq_is_cauchy** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_is_cauchy : IsCauSeq norm newton_seq := fun _ε hε ↦
  (bound hnorm hε).imp fun _N hN _j hj ↦ (newton_seq_dist hnorm hj).trans_lt <| hN le_rfl
/-
**newton_cau_seq** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def newton_cau_seq : CauSeq ℤ_[p] norm := ⟨_, newton_seq_is_cauchy hnorm⟩
/-
**soln_gen** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def soln_gen : ℤ_[p] := (newton_cau_seq hnorm).lim

local notation "soln" => soln_gen hnorm
/-
**soln_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem soln_spec {ε : ℝ} (hε : ε > 0) :
    ∃ N : ℕ, ∀ {i : ℕ}, i ≥ N → ‖soln - newton_cau_seq hnorm i‖ < ε :=
  Setoid.symm (CauSeq.equiv_lim (newton_cau_seq hnorm)) _ hε
/-
**soln_deriv_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem soln_deriv_norm : ‖F.derivative.aeval soln‖ = ‖F.derivative.aeval a‖ :=
  norm_deriv_eq (newton_seq_deriv_norm hnorm)
/-
**newton_seq_norm_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_norm_tendsto_zero :
    Tendsto (fun i => ‖F.aeval (newton_cau_seq hnorm i)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm) (bound'_sq hnorm)
/-
**newton_seq_dist_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_dist_tendsto' :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖) atTop (𝓝 ‖soln - a‖) :=
  (continuous_norm.tendsto _).comp ((newton_cau_seq hnorm).tendsto_limit.sub tendsto_const_nhds)
/-
**eval_soln** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem eval_soln : F.aeval soln = 0 :=
  limit_zero_of_norm_tendsto_zero (newton_seq_norm_tendsto_zero hnorm)

variable (hnsol : F.aeval a ≠ 0)
include hnsol
/-
**T_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem T_pos : T > 0 := by
  rw [T_def]
  exact div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)
/-
**newton_seq_succ_dist_weak** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_succ_dist_weak (n : ℕ) :
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ < ‖F.aeval a‖ / ‖F.derivative.aeval a‖ :=
  have : 2 ≤ 2 ^ (n + 1) := by
    have := pow_right_mono₀ (by simp : 1 ≤ 2) (Nat.le_add_left _ _ : 1 ≤ n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist hnorm _
    _ ≤ ‖F.derivative.aeval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _)
        (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _))
    _ < ‖F.derivative.aeval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (T_pos hnorm hnsol)
        (T_lt_one hnorm) (by norm_num)) (deriv_norm_pos hnorm))
    _ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ := by
      rw [T_gen, sq, pow_one, norm_div, ← mul_div_assoc, PadicInt.padic_norm_e_of_padicInt,
        PadicInt.coe_mul, norm_mul]
      apply mul_div_mul_left
      apply deriv_norm_ne_zero; assumption

set_option backward.isDefEq.respectTransparency false in
/-
**newton_seq_dist_to_a** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_dist_to_a :
    ∀ n : ℕ, 0 < n → ‖newton_seq n - a‖ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖
  | 1, _h => by simp [sub_eq_add_neg, add_assoc, newton_seq_gen, newton_seq_aux, ih_n]
  | k + 2, _h =>
    have hlt : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ < ‖newton_seq (k + 1) - a‖ := by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)]; apply newton_seq_succ_dist_weak
      assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ≠ ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ := by
        rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := max_eq_right_of_lt hlt
      _ = ‖Polynomial.aeval a F‖ / ‖Polynomial.aeval a (Polynomial.derivative F)‖ :=
        newton_seq_dist_to_a (k + 1) (succ_pos _)
/-
**newton_seq_dist_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem newton_seq_dist_tendsto :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖)
    atTop (𝓝 (‖F.aeval a‖ / ‖F.derivative.aeval a‖)) :=
  tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨1, fun _ hx => (newton_seq_dist_to_a hnorm hnsol _ hx).symm⟩)
/-
**soln_dist_to_a** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem soln_dist_to_a : ‖soln - a‖ = ‖F.aeval a‖ / ‖F.derivative.aeval a‖ :=
  tendsto_nhds_unique (newton_seq_dist_tendsto' hnorm) (newton_seq_dist_tendsto hnorm hnsol)
/-
**soln_dist_to_a_lt_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem soln_dist_to_a_lt_deriv : ‖soln - a‖ < ‖F.derivative.aeval a‖ := by
  rw [soln_dist_to_a, div_lt_iff₀ (deriv_norm_pos _), ← sq] <;> assumption
/-
**soln_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem soln_unique (z : ℤ_[p]) (hev : F.aeval z = 0)
    (hnlt : ‖z - a‖ < ‖F.derivative.aeval a‖) : z = soln := by
  have hsoln : ‖z - soln‖ < ‖F.derivative.aeval soln‖ := by
    rw [soln_deriv_norm]
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ ≤ max ‖z - a‖ ‖a - soln‖ := PadicInt.nonarchimedean _ _
      _ < ‖F.derivative.aeval a‖ :=
        max_lt hnlt ((norm_sub_rev soln a ▸ (soln_dist_to_a_lt_deriv hnorm)) hnsol)
  exact a_soln_is_unique (eval_soln hnorm) z hev hsoln

end Hensel

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {F : Polynomial R} {a : ℤ_[p]}

variable (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)
include hnorm

/-
**a_is_soln** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem a_is_soln (ha : F.aeval a = 0) :
    F.aeval a = 0 ∧
      ‖a - a‖ < ‖F.derivative.aeval a‖ ∧
        ‖F.derivative.aeval a‖ = ‖F.derivative.aeval a‖ ∧
          ∀ z', F.aeval z' = 0 → ‖z' - a‖ < ‖F.derivative.aeval a‖ → z' = a :=
  ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩
/-
**hensels_lemma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hensels_lemma : exists z : Int_[p], F.aeval z = 0 ∧ ‖z - a‖ < ‖F.derivativ
e.aeval a‖ ∧ ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧ forall z', F.aeva
l z' = 0 -> ‖z' - a‖ < ‖F.derivative.aeval a‖ -> z' = z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.a_is_soln`：∀ {p : ℕ} [inst
 : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebr
a R ℤ_[p]]   {F : Polynomial R} {a : ℤ_[p]}, …
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.eval_soln`：∀ {p : ℕ} [inst
 : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Algebr
a R ℤ_[p]]   {F : Polynomial R} {a : ℤ_[p]}  …
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.soln_dist_to_a_lt_deriv`：∀
 {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] [i
nst_2 : Algebra R ℤ_[p]]   {F : Polynomial R} {a : ℤ_[p]}  …
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.soln_deriv_norm`：∀ {p : ℕ}
 [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : 
Algebra R ℤ_[p]]   {F : Polynomial R} {a : ℤ_[p]}  …
· 使用定理 `_private.Mathlib.NumberTheory.Padics.Hensel.0.soln_unique`：∀ {p : ℕ} [in
st : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Alge
bra R ℤ_[p]]   {F : Polynomial R} {a : ℤ_[p]}  …
-/
theorem hensels_lemma :
    ∃ z : ℤ_[p],
      F.aeval z = 0 ∧
        ‖z - a‖ < ‖F.derivative.aeval a‖ ∧
          ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧
            ∀ z', F.aeval z' = 0 → ‖z' - a‖ < ‖F.derivative.aeval a‖ → z' = z := by
  classical
  exact if ha : F.aeval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    exact ⟨soln_gen hnorm, eval_soln hnorm,
      soln_dist_to_a_lt_deriv hnorm ha, soln_deriv_norm hnorm, fun z => soln_unique hnorm ha z⟩
