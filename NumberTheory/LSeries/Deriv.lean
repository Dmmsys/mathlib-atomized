/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.HalfPlane

/-!
# Differentiability and derivatives of L-series

## Main results

* We show that the `LSeries` of `f` is differentiable at `s` when `re s` is greater than
  the abscissa of absolute convergence of `f` (`LSeries.hasDerivAt`) and that its derivative
  there is the negative of the `LSeries` of the point-wise product `log * f` (`LSeries.deriv`).

* We prove similar results for iterated derivatives (`LSeries.iteratedDeriv`).

* We use this to show that `LSeries f` is holomorphic on the right half-plane of
  absolute convergence (`LSeries.analyticOnNhd`).

## Implementation notes

We introduce `LSeries.logMul` as an abbreviation for the point-wise product `log * f`, to avoid
the problem that this expression does not type-check.
-/

public section

open Complex LSeries

/-!
### The derivative of an L-series
-/

/-- The (point-wise) product of `log : ℕ → ℂ` with `f`. -/
/-
**LSeries.logMul** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LSeries.logMul (f : Nat -> Complex) (n : Nat) : Complex
参数：f : Nat -> Complex；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (point-wise) product of `log : ℕ → ℂ` with `f`.
-/
noncomputable abbrev LSeries.logMul (f : ℕ → ℂ) (n : ℕ) : ℂ := log n * f n

/-- The derivative of the terms of an L-series. -/
/-
**LSeries.hasDerivAt_term** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.hasDerivAt_term (f : Nat -> Complex) (n : Nat) (s : Complex) : Has
DerivAt (fun z => term f z n) (-(term (logMul f) s n)) s
参数：f : Nat -> Complex；n : Nat；s : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `HasDerivAt.const_cpow`：HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h
0 : c != 0 ∨ f x != 0) : HasDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c 
* f') x
· 使用定理 `hasDerivAt_neg'`：hasDerivAt_neg' : HasDerivAt (fun x => -x) (-1) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0

--- 原说明 ---
The derivative of the terms of an L-series.
-/
lemma LSeries.hasDerivAt_term (f : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    HasDerivAt (fun z ↦ term f z n) (-(term (logMul f) s n)) s := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hasDerivAt_const]
  simp_rw [term_of_ne_zero hn, ← neg_div, ← neg_mul, mul_comm, mul_div_assoc, div_eq_mul_inv,
    ← cpow_neg]
  exact HasDerivAt.const_mul (f n) (by simpa only [mul_comm, ← mul_neg_one (log n), ← mul_assoc]
    using (hasDerivAt_neg' s).const_cpow (Or.inl <| Nat.cast_ne_zero.mpr hn))

/- This lemma proves two things at once, since their proofs are intertwined; we give separate
non-private lemmas below that extract the two statements. -/
/-
**LSeries.LSeriesSummable_logMul_and_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma proves two things at once, since their proofs are intertwined; we giv
e separate
non-private lemmas below that extract the two statements.
-/
private lemma LSeries.LSeriesSummable_logMul_and_hasDerivAt {f : ℕ → ℂ} {s : ℂ}
    (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s ∧ HasDerivAt (LSeries f) (-LSeries (logMul f) s) s := by
  -- The L-series of `f` is summable at some real `x < re s`.
  obtain ⟨x, hxs, hf⟩ := LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re h
  obtain ⟨y, hxy, hys⟩ := exists_between hxs
  -- We work in the right half-plane `y < re z`, for some `y` such that `x < y < re s`, on which
  -- we have a uniform summable bound on `‖term f z ·‖`.
  let S : Set ℂ := {z | y < z.re}
  have h₀ : Summable (fun n ↦ ‖term f x n‖) := summable_norm_iff.mpr hf
  have h₁ (n) : DifferentiableOn ℂ (term f · n) S :=
    fun z _ ↦ (hasDerivAt_term f n _).differentiableAt.differentiableWithinAt
  have h₂ : IsOpen S := isOpen_lt continuous_const continuous_re
  have h₃ (n z) (hz : z ∈ S) : ‖term f z n‖ ≤ ‖term f x n‖ :=
    norm_term_le_of_re_le_re f (by simpa using! (hxy.trans hz).le) n
  have H := hasSum_deriv_of_summable_norm h₀ h₁ h₂ h₃ hys
  simp_rw [(hasDerivAt_term f _ _).deriv] at H
  refine ⟨summable_neg_iff.mp H.summable, ?_⟩
  simpa [← H.tsum_eq, tsum_neg] using! ((differentiableOn_tsum_of_summable_norm
    h₀ h₁ h₂ h₃).differentiableAt <| h₂.mem_nhds hys).hasDerivAt

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then the L-series
of `f` is differentiable with derivative the negative of the L-series of the point-wise
product of `log` with `f`. -/
/-
**LSeries_hasDerivAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_hasDerivAt {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsCo
nv f < s.re) : HasDerivAt (LSeries f) (-LSeries (logMul f) s) s
参数：h : abscissaOfAbsConv f < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Deriv.0.LSeries.LSeriesSummable_lo
gMul_and_hasDerivAt`：∀ {f : ℕ → ℂ} {s : ℂ},   LSeries.abscissaOfAbsConv f < ↑s.r
e →     LSeriesSummable (LSeries.logMul f) s ∧ HasDerivAt (LSeries f) (-LSeries 
(…

--- 原说明 ---
If `re s` is greater than the abscissa of absolute convergence of `f`, then the 
L-series
of `f` is differentiable with derivative the negative of the L-series of the poi
nt-wise
product of `log` with `f`.
-/
lemma LSeries_hasDerivAt {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    HasDerivAt (LSeries f) (-LSeries (logMul f) s) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).2

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then
the derivative of this L-series at `s` is the negative of the L-series of `log * f`. -/
/-
**LSeries_deriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_deriv {f : Nat -> Complex} {s : Complex} (h : abscissaOfAbsConv f 
< s.re) : deriv (LSeries f) s = -LSeries (logMul f) s
参数：h : abscissaOfAbsConv f < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用引理 `LSeries_hasDerivAt`：LSeries_hasDerivAt {f : Nat -> Complex} {s : Complex
} (h : abscissaOfAbsConv f < s.re) : HasDerivAt (LSeries f) (-LSeries (logMul f)
 s) s

--- 原说明 ---
If `re s` is greater than the abscissa of absolute convergence of `f`, then
the derivative of this L-series at `s` is the negative of the L-series of `log *
 f`.
-/
lemma LSeries_deriv {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    deriv (LSeries f) s = -LSeries (logMul f) s :=
  (LSeries_hasDerivAt h).deriv

/-- The derivative of the L-series of `f` agrees with the negative of the L-series of
`log * f` on the right half-plane of absolute convergence. -/
/-
**LSeries_deriv_eqOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_deriv_eqOn {f : Nat -> Complex} : {s | abscissaOfAbsConv f < s.re}
.EqOn (deriv (LSeries f)) (-LSeries (logMul f))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用引理 `Complex.isOpen_re_gt_EReal`：isOpen_re_gt_EReal (x : EReal) : IsOpen {z :
 Complex | x < z.re}
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用引理 `LSeries_hasDerivAt`：LSeries_hasDerivAt {f : Nat -> Complex} {s : Complex
} (h : abscissaOfAbsConv f < s.re) : HasDerivAt (LSeries f) (-LSeries (logMul f)
 s) s

--- 原说明 ---
The derivative of the L-series of `f` agrees with the negative of the L-series o
f
`log * f` on the right half-plane of absolute convergence.
-/
lemma LSeries_deriv_eqOn {f : ℕ → ℂ} :
    {s | abscissaOfAbsConv f < s.re}.EqOn (deriv (LSeries f)) (-LSeries (logMul f)) :=
  deriv_eqOn (isOpen_re_gt_EReal _) fun _ hs ↦ (LSeries_hasDerivAt hs).hasDerivWithinAt

/-- If the L-series of `f` is summable at `s` and `re s < re s'`, then the L-series of the
point-wise product of `log` with `f` is summable at `s'`. -/
/-
**LSeriesSummable_logMul_of_lt_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeriesSummable_logMul_of_lt_re {f : Nat -> Complex} {s : Complex} (h : ab
scissaOfAbsConv f < s.re) : LSeriesSummable (logMul f) s
参数：h : abscissaOfAbsConv f < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Deriv.0.LSeries.LSeriesSummable_lo
gMul_and_hasDerivAt`：∀ {f : ℕ → ℂ} {s : ℂ},   LSeries.abscissaOfAbsConv f < ↑s.r
e →     LSeriesSummable (LSeries.logMul f) s ∧ HasDerivAt (LSeries f) (-LSeries 
(…

--- 原说明 ---
If the L-series of `f` is summable at `s` and `re s < re s'`, then the L-series 
of the
point-wise product of `log` with `f` is summable at `s'`.
-/
lemma LSeriesSummable_logMul_of_lt_re {f : ℕ → ℂ} {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    LSeriesSummable (logMul f) s :=
  (LSeriesSummable_logMul_and_hasDerivAt h).1

/-- The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`. -/
@[simp]
/-
**LSeries.abscissaOfAbsConv_logMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_logMul {f : Nat -> Complex} : abscissaOfAbsConv 
(logMul f) = abscissaOfAbsConv f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'`：LSeries.absc
issaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : Nat -> Complex} {x : EReal} 
(h : forall y : Real, x < y -> LSeriesSummable f…
· 使用引理 `LSeriesSummable_logMul_of_lt_re`：LSeriesSummable_logMul_of_lt_re {f : Na
t -> Complex} {s : Complex} (h : abscissaOfAbsConv f < s.re) : LSeriesSummable (
logMul f) s
· 使用定理 `Summable.of_norm_bounded_eventually_nat`：Summable.of_norm_bounded_eventu
ally_nat {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : forallᶠ i in at
Top, ‖f i‖ <= g i) : Summable…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.ceil_le`：ceil_le : ⌈a⌉₊ <= n ↔ a <= n
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The abscissa of absolute convergence of the point-wise product of `log` and `f`
is the same as that of `f`.
-/
lemma LSeries.abscissaOfAbsConv_logMul {f : ℕ → ℂ} :
    abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f := by
  apply le_antisymm <;> refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun s hs ↦ ?_
  · exact LSeriesSummable_logMul_of_lt_re <| by simp [hs]
  · refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re <| by simp [hs])
      |>.norm.of_norm_bounded_eventually_nat (g := fun n ↦ ‖term (logMul f) s n‖) ?_
    filter_upwards [Filter.eventually_ge_atTop <| max 1 (Nat.ceil (Real.exp 1))] with n hn
    simp only [term_of_ne_zero (show n ≠ 0 by omega), logMul, norm_mul, mul_div_assoc,
      ← natCast_log, norm_real]
    refine le_mul_of_one_le_left (norm_nonneg _) (.trans ?_ <| Real.le_norm_self _)
    simpa using Real.log_le_log (Real.exp_pos 1) <| Nat.ceil_le.mp <| (le_max_right _ _).trans hn

/-!
### Higher derivatives of L-series
-/

/-- The abscissa of absolute convergence of the point-wise product of a power of `log` and `f`
is the same as that of `f`. -/
@[simp]
/-
**LSeries.absicssaOfAbsConv_logPowMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.absicssaOfAbsConv_logPowMul {f : Nat -> Complex} {m : Nat} : absci
ssaOfAbsConv (logMul^[m] f) = abscissaOfAbsConv f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用引理 `LSeries.abscissaOfAbsConv_logMul`：LSeries.abscissaOfAbsConv_logMul {f : 
Nat -> Complex} : abscissaOfAbsConv (logMul f) = abscissaOfAbsConv f

--- 原说明 ---
The abscissa of absolute convergence of the point-wise product of a power of `lo
g` and `f`
is the same as that of `f`.
-/
lemma LSeries.absicssaOfAbsConv_logPowMul {f : ℕ → ℂ} {m : ℕ} :
    abscissaOfAbsConv (logMul^[m] f) = abscissaOfAbsConv f := by
  induction m with
  | zero => simp
  | succ n ih => simp [ih, Function.iterate_succ', Function.comp_def,
      -Function.comp_apply, -Function.iterate_succ]

/-- If `re s` is greater than the abscissa of absolute convergence of `f`, then
the `m`th derivative of this L-series is `(-1)^m` times the L-series of `log^m * f`. -/
/-
**LSeries_iteratedDeriv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_iteratedDeriv {f : Nat -> Complex} (m : Nat) {s : Complex} (h : ab
scissaOfAbsConv f < s.re) : iteratedDeriv m (LSeries f) s = (-1) ^ m * LSeries (
logMul^[m] f) s
参数：m : Nat；h : abscissaOfAbsConv f < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x
· 使用定理 `iteratedDeriv_succ`：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv
 (iteratedDeriv n f)
· 使用定理 `derivWithin_of_isOpen`：derivWithin_of_isOpen (hs : IsOpen s) (hx : x in 
s) : derivWithin f s x = deriv f x
· 使用引理 `Complex.isOpen_re_gt_EReal`：isOpen_re_gt_EReal (x : EReal) : IsOpen {z :
 Complex | x < z.re}
· 使用定理 `deriv_const_mul_field'`：deriv_const_mul_field' (u : 𝕜') : (deriv fun x =
> u * v x) = fun x => u * deriv v x
· 使用引理 `LSeries_deriv`：LSeries_deriv {f : Nat -> Complex} {s : Complex} (h : abs
cissaOfAbsConv f < s.re) : deriv (LSeries f) s = -LSeries (logMul f) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries.absicssaOfAbsConv_logPowMul`：LSeries.absicssaOfAbsConv_logPowMul
 {f : Nat -> Complex} {m : Nat} : abscissaOfAbsConv (logMul^[m] f) = abscissaOfA
bsConv f
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)

--- 原说明 ---
If `re s` is greater than the abscissa of absolute convergence of `f`, then
the `m`th derivative of this L-series is `(-1)^m` times the L-series of `log^m *
 f`.
-/
lemma LSeries_iteratedDeriv {f : ℕ → ℂ} (m : ℕ) {s : ℂ} (h : abscissaOfAbsConv f < s.re) :
    iteratedDeriv m (LSeries f) s = (-1) ^ m * LSeries (logMul^[m] f) s := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    have ih' : {s | abscissaOfAbsConv f < re s}.EqOn (iteratedDeriv m (LSeries f))
        ((-1) ^ m * LSeries (logMul^[m] f)) := fun _ hs ↦ ih hs
    have := derivWithin_congr ih' (ih h)
    simp_rw [derivWithin_of_isOpen (isOpen_re_gt_EReal _) h] at this
    rw [iteratedDeriv_succ, this]
    simp [Pi.mul_def, pow_succ, Function.iterate_succ',
      LSeries_deriv <| absicssaOfAbsConv_logPowMul.symm ▸ h, -Function.iterate_succ]

/-!
### The L-series is holomorphic
-/

/-- The L-series of `f` is complex differentiable in its open half-plane of absolute
convergence. -/
/-
**LSeries_differentiableOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_differentiableOn (f : Nat -> Complex) : DifferentiableOn Complex (
LSeries f) {s | abscissaOfAbsConv f < s.re}
参数：f : Nat -> Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用引理 `LSeries_hasDerivAt`：LSeries_hasDerivAt {f : Nat -> Complex} {s : Complex
} (h : abscissaOfAbsConv f < s.re) : HasDerivAt (LSeries f) (-LSeries (logMul f)
 s) s

--- 原说明 ---
The L-series of `f` is complex differentiable in its open half-plane of absolute
convergence.
-/
lemma LSeries_differentiableOn (f : ℕ → ℂ) :
    DifferentiableOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  fun _ hz ↦ (LSeries_hasDerivAt hz).differentiableAt.differentiableWithinAt

/-- The L-series of `f` is holomorphic on its open half-plane of absolute convergence. -/
/-
**LSeries_analyticOnNhd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_analyticOnNhd (f : Nat -> Complex) : AnalyticOnNhd Complex (LSerie
s f) {s | abscissaOfAbsConv f < s.re}
参数：f : Nat -> Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `LSeries_differentiableOn`：LSeries_differentiableOn (f : Nat -> Complex) 
: DifferentiableOn Complex (LSeries f) {s | abscissaOfAbsConv f < s.re}
· 使用引理 `Complex.isOpen_re_gt_EReal`：isOpen_re_gt_EReal (x : EReal) : IsOpen {z :
 Complex | x < z.re}

--- 原说明 ---
The L-series of `f` is holomorphic on its open half-plane of absolute convergenc
e.
-/
lemma LSeries_analyticOnNhd (f : ℕ → ℂ) :
    AnalyticOnNhd ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_differentiableOn f).analyticOnNhd <| isOpen_re_gt_EReal _
/-
**LSeries_analyticOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_analyticOn (f : Nat -> Complex) : AnalyticOn Complex (LSeries f) {
s | abscissaOfAbsConv f < s.re}
参数：f : Nat -> Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.analyticOn`：AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜
 f s) : AnalyticOn 𝕜 f s
· 使用引理 `LSeries_analyticOnNhd`：LSeries_analyticOnNhd (f : Nat -> Complex) : Anal
yticOnNhd Complex (LSeries f) {s | abscissaOfAbsConv f < s.re}
-/
lemma LSeries_analyticOn (f : ℕ → ℂ) :
    AnalyticOn ℂ (LSeries f) {s | abscissaOfAbsConv f < s.re} :=
  (LSeries_analyticOnNhd f).analyticOn
