/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.Linearity

/-!
# A converging L-series determines its coefficients

We show that two functions `f` and `g : ℕ → ℂ` whose L-series agree and both converge somewhere
must agree on all nonzero arguments. See `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`
and `LSeries_injOn`.
-/

public section

open LSeries Complex

-- The following two lemmas need both `LSeries.Linearity` and `LSeries.Convergence`,
-- so cannot live in either of these files.

/-- The abscissa of absolute convergence of `f + g` is at most the maximum of those
of `f` and `g`. -/
/-
**LSeries.abscissaOfAbsConv_add_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_add_le (f g : Nat -> Complex) : abscissaOfAbsCon
v (f + g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g)
参数：f g : Nat -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.abscissaOfAbsConv_binop_le`：LSeries.abscissaOfAbsConv_binop_le {
F : (Nat -> Complex) -> (Nat -> Complex) -> (Nat -> Complex)} (hF : forall {f g 
s}, LSeriesSummable f s …
· 使用引理 `LSeriesSummable.add`：LSeriesSummable.add {f g : Nat -> Complex} {s : Com
plex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeriesSummable (f
 + g) s

--- 原说明 ---
The abscissa of absolute convergence of `f + g` is at most the maximum of those
of `f` and `g`.
-/
lemma LSeries.abscissaOfAbsConv_add_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f + g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.add f g

/-- The abscissa of absolute convergence of `f - g` is at most the maximum of those
of `f` and `g`. -/
/-
**LSeries.abscissaOfAbsConv_sub_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.abscissaOfAbsConv_sub_le (f g : Nat -> Complex) : abscissaOfAbsCon
v (f - g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g)
参数：f g : Nat -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.abscissaOfAbsConv_binop_le`：LSeries.abscissaOfAbsConv_binop_le {
F : (Nat -> Complex) -> (Nat -> Complex) -> (Nat -> Complex)} (hF : forall {f g 
s}, LSeriesSummable f s …
· 使用引理 `LSeriesSummable.sub`：LSeriesSummable.sub {f g : Nat -> Complex} {s : Com
plex} (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) : LSeriesSummable (f
 - g) s

--- 原说明 ---
The abscissa of absolute convergence of `f - g` is at most the maximum of those
of `f` and `g`.
-/
lemma LSeries.abscissaOfAbsConv_sub_le (f g : ℕ → ℂ) :
    abscissaOfAbsConv (f - g) ≤ max (abscissaOfAbsConv f) (abscissaOfAbsConv g) :=
  abscissaOfAbsConv_binop_le LSeriesSummable.sub f g

private
/-
**cpow_mul_div_cpow_eq_div_div_cpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cpow_mul_div_cpow_eq_div_div_cpow (m n : Nat) (z : Complex) (x : Real) : (
n + 1) ^ (x : Complex) * (z / m ^ (x : Complex)) = z / (m / (n + 1)) ^ (x : Comp
lex)
参数：m n : Nat；z : Complex；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cpow_mul_div_cpow_eq_div_div_cpow (m n : ℕ) (z : ℂ) (x : ℝ) :
    (n + 1) ^ (x : ℂ) * (z / m ^ (x : ℂ)) = z / (m / (n + 1)) ^ (x : ℂ) := by
  have Hn : (0 : ℝ) ≤ (n + 1 : ℝ)⁻¹ := by positivity
  rw [← mul_div_assoc, mul_comm, div_eq_mul_inv z, mul_div_assoc]
  congr
  simp_rw [div_eq_mul_inv]
  rw [show (n + 1 : ℂ)⁻¹ = (n + 1 : ℝ)⁻¹ by simp,
    show (n + 1 : ℂ) = (n + 1 : ℝ) by norm_cast, show (m : ℂ) = (m : ℝ) by norm_cast,
    mul_cpow_ofReal_nonneg m.cast_nonneg Hn, mul_inv, mul_comm]
  congr
  rw [← cpow_neg, show (-x : ℂ) = (-1 : ℝ) * x by simp, cpow_mul_ofReal_nonneg Hn,
    Real.rpow_neg_one, inv_inv]

set_option backward.isDefEq.respectTransparency false in
open Filter Real in
/-- If the coefficients `f m` of an L-series are zero for `m ≤ n` and the L-series converges
at some point, then `f (n+1)` is the limit of `(n+1)^x * LSeries f x` as `x → ∞`. -/
/-
**LSeries.tendsto_cpow_mul_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.tendsto_cpow_mul_atTop {f : Nat -> Complex} {n : Nat} (h : forall 
m <= n, f m = 0) (ha : abscissaOfAbsConv f < ⊤) : Tendsto (fun x : Real => (n + 
1) ^ (x : Complex) * LSeries f x) atTop (nhds (f (n + 1)))
参数：h : forall m <= n, f m = 0；ha : abscissaOfAbsConv f < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `OrderBot.bot_le`：∀ {α : Type u} {inst : LE α} [self : OrderBot α] (a : α
), ⊥ ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.Injectivity.0.cpow_mul_div_cpow_eq
_div_div_cpow`：∀ (m n : ℕ) (z : ℂ) (x : ℝ), (↑n + 1) ^ ↑x * (z / ↑m ^ ↑x) = z / 
(↑m / (↑n + 1)) ^ ↑x
（共 126 条，此处仅展示前 30 条）

--- 原说明 ---
If the coefficients `f m` of an L-series are zero for `m ≤ n` and the L-series c
onverges
at some point, then `f (n+1)` is the limit of `(n+1)^x * LSeries f x` as `x → ∞`
.
-/
lemma LSeries.tendsto_cpow_mul_atTop {f : ℕ → ℂ} {n : ℕ} (h : ∀ m ≤ n, f m = 0)
    (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : ℝ ↦ (n + 1) ^ (x : ℂ) * LSeries f x) atTop (nhds (f (n + 1))) := by
  obtain ⟨y, hay, hyt⟩ := exists_between ha
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hay).ne'⟩
  -- `F x m` is the `m`th term of `(n+1)^x * LSeries f x`, except that `F x (n+1) = 0`
  let F := fun (x : ℝ) ↦ {m | n + 1 < m}.indicator (fun m ↦ f m / (m / (n + 1) : ℂ) ^ (x : ℂ))
  have hF₀ (x : ℝ) {m : ℕ} (hm : m ≤ n + 1) : F x m = 0 := by simp [F, not_lt_of_ge hm]
  have hF (x : ℝ) {m : ℕ} (hm : m ≠ n + 1) : F x m = ((n + 1) ^ (x : ℂ)) * term f x m := by
    rcases lt_trichotomy m (n + 1) with H | rfl | H
    · simp [Nat.not_lt_of_gt H, term, h m <| Nat.lt_succ_iff.mp H, F]
    · exact (hm rfl).elim
    · simp [H, term, (n.zero_lt_succ.trans H).ne', F, cpow_mul_div_cpow_eq_div_div_cpow]
  have hs {x : ℝ} (hx : x ≥ y) : Summable fun m ↦ (n + 1) ^ (x : ℂ) * term f x m := by
    refine (summable_mul_left_iff <| natCast_add_one_cpow_ne_zero n _).mpr <|
       LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    simpa only [ofReal_re] using hay.trans_le <| EReal.coe_le_coe_iff.mpr hx
  -- we can write `(n+1)^x * LSeries f x` as `f (n+1)` plus the series over `F x`
  have key : ∀ x ≥ y, (n + 1) ^ (x : ℂ) * LSeries f x = f (n + 1) + ∑' m : ℕ, F x m := by
    intro x hx
    rw [LSeries, ← tsum_mul_left, (hs hx).tsum_eq_add_tsum_ite (n + 1), pow_mul_term_eq f x n]
    congr
    ext1 m
    rcases eq_or_ne m (n + 1) with rfl | hm
    · simp [hF₀ x le_rfl]
    · simp [hm, hF]
  -- reduce to showing that `∑' m, F x m → 0` as `x → ∞`
  conv => enter [3, 1]; rw [← add_zero (f _)]
  refine Tendsto.congr'
    (eventuallyEq_of_mem (s := {x | y ≤ x}) (mem_atTop y) key).symm <| tendsto_const_nhds.add ?_
  -- get the prerequisites for applying dominated convergence
  have hys : Summable (F y) := by
    refine ((hs le_rfl).indicator {m | n + 1 < m}).congr fun m ↦ ?_
    by_cases! hm : n + 1 < m
    · simp [hF, hm, hm.ne']
    · simp [hm, hF₀ _ hm]
  have hc (k : ℕ) : Tendsto (F · k) atTop (nhds 0) := by
    rcases lt_or_ge (n + 1) k with H | H
    · have H₀ : (0 : ℝ) ≤ k / (n + 1) := by positivity
      have H₀' : (0 : ℝ) ≤ (n + 1) / k := by positivity
      have H₁ : (k / (n + 1) : ℂ) = (k / (n + 1) : ℝ) := by push_cast; rfl
      have H₂ : (n + 1) / k < (1 : ℝ) :=
        (div_lt_one <| mod_cast n.succ_pos.trans H).mpr <| mod_cast H
      simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, F]
      conv =>
        enter [1, x]
        rw [div_eq_mul_inv, H₁, ← ofReal_cpow H₀, ← ofReal_inv, ← Real.inv_rpow H₀, inv_div]
      conv => enter [3, 1]; rw [← mul_zero (f k)]
      exact
        (tendsto_rpow_atTop_of_base_lt_one _ (neg_one_lt_zero.trans_le H₀') H₂).ofReal.const_mul _
    · simp [hF₀ _ H]
  rw [show (0 : ℂ) = tsum (fun _ : ℕ ↦ 0) from tsum_zero.symm]
  refine tendsto_tsum_of_dominated_convergence hys.norm hc <| eventually_iff.mpr ?_
  filter_upwards [mem_atTop y] with y' hy' k
  -- it remains to show that `‖F y' k‖ ≤ ‖F y k‖` (for `y' ≥ y`)
  rcases lt_or_ge (n + 1) k with H | H
  · simp only [Set.mem_ofPred_eq, H, Set.indicator_of_mem, norm_div, norm_cpow_real,
      Complex.norm_natCast, F]
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    have hkn : 1 ≤ (k / (n + 1 :) : ℝ) :=
      (one_le_div (by positivity)).mpr <| mod_cast Nat.le_of_succ_le H
    gcongr
  · simp [hF₀ _ H]

open Filter in
/-- If the L-series of `f` converges at some point, then `f 1` is the limit of `LSeries f x`
as `x → ∞`. -/
/-
**LSeries.tendsto_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.tendsto_atTop {f : Nat -> Complex} (ha : abscissaOfAbsConv f < ⊤) 
: Tendsto (fun x : Real => LSeries f x) atTop (nhds (f 1))
参数：ha : abscissaOfAbsConv f < ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries.abscissaOfAbsConv_congr`：LSeries.abscissaOfAbsConv_congr {f g : 
Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) : abscissaOfAbsConv f = ab
scissaOfAbsConv g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LSeries.tendsto_cpow_mul_atTop`：LSeries.tendsto_cpow_mul_atTop {f : Nat 
-> Complex} {n : Nat} (h : forall m <= n, f m = 0) (ha : abscissaOfAbsConv f < ⊤
) : Tendsto (fun x :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0

--- 原说明 ---
If the L-series of `f` converges at some point, then `f 1` is the limit of `LSer
ies f x`
as `x → ∞`.
-/
lemma LSeries.tendsto_atTop {f : ℕ → ℂ} (ha : abscissaOfAbsConv f < ⊤) :
    Tendsto (fun x : ℝ ↦ LSeries f x) atTop (nhds (f 1)) := by
  let F (n : ℕ) : ℂ := if n = 0 then 0 else f n
  have hF₀ : F 0 = 0 := rfl
  have hF {n : ℕ} (hn : n ≠ 0) : F n = f n := if_neg hn
  have ha' : abscissaOfAbsConv F < ⊤ := (abscissaOfAbsConv_congr hF).symm ▸ ha
  simp_rw [← LSeries_congr hF]
  convert! LSeries.tendsto_cpow_mul_atTop (n := 0) (fun _ hm ↦ Nat.le_zero.mp hm ▸ hF₀) ha' using 1
  simp
/-
**LSeries_eq_zero_of_abscissaOfAbsConv_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : Nat -> Complex} (h : absc
issaOfAbsConv f = ⊤) : LSeries f = 0
参数：h : abscissaOfAbsConv f = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LSeries.eq_zero_of_not_LSeriesSummable`：LSeries.eq_zero_of_not_LSeriesSu
mmable (f : Nat -> Complex) (s : Complex) : ¬ LSeriesSummable f s -> LSeries f s
 = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `LSeriesSummable.abscissaOfAbsConv_le`：LSeriesSummable.abscissaOfAbsConv_
le {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) : abscissaOfAbsC
onv f <= s.re
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma LSeries_eq_zero_of_abscissaOfAbsConv_eq_top {f : ℕ → ℂ} (h : abscissaOfAbsConv f = ⊤) :
    LSeries f = 0 := by
  ext1 s
  exact LSeries.eq_zero_of_not_LSeriesSummable f s <| mt LSeriesSummable.abscissaOfAbsConv_le <|
    h ▸ fun H ↦ (H.trans_lt <| EReal.coe_lt_top _).false

open Filter Nat in
/-- The `LSeries` of `f` is zero for large real arguments if and only if either `f n = 0`
for all `n ≠ 0` or the L-series converges nowhere. -/
/-
**LSeries_eventually_eq_zero_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_eventually_eq_zero_iff' {f : Nat -> Complex} : (fun x : Real => LS
eries f x) =ᶠ[atTop] 0 ↔ (forall n != 0, f n = 0) ∨ abscissaOfAbsConv f = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `LSeries_eq_zero_of_abscissaOfAbsConv_eq_top`：LSeries_eq_zero_of_abscissa
OfAbsConv_eq_top {f : Nat -> Complex} (h : abscissaOfAbsConv f = ⊤) : LSeries f 
= 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LSeries.abscissaOfAbsConv_congr`：LSeries.abscissaOfAbsConv_congr {f g : 
Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) : abscissaOfAbsConv f = ab
scissaOfAbsConv g
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The `LSeries` of `f` is zero for large real arguments if and only if either `f n
 = 0`
for all `n ≠ 0` or the L-series converges nowhere.
-/
lemma LSeries_eventually_eq_zero_iff' {f : ℕ → ℂ} :
    (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] 0 ↔ (∀ n ≠ 0, f n = 0) ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using!
      Eventually.of_forall <| by simp [LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h]
  · simp only [ne_eq, h, or_false]
    refine ⟨fun H ↦ ?_, fun H ↦ Eventually.of_forall fun x ↦ ?_⟩
    · let F (n : ℕ) : ℂ := if n = 0 then 0 else f n
      have hF₀ : F 0 = 0 := rfl
      have hF {n : ℕ} (hn : n ≠ 0) : F n = f n := if_neg hn
      suffices ∀ n, F n = 0 from fun n hn ↦ (hF hn).symm.trans (this n)
      have ha : ¬ abscissaOfAbsConv F = ⊤ := abscissaOfAbsConv_congr hF ▸ h
      have h' (x : ℝ) : LSeries F x = LSeries f x := LSeries_congr hF x
      have H' (n : ℕ) : (fun x : ℝ ↦ n ^ (x : ℂ) * LSeries F x) =ᶠ[atTop] fun _ ↦ 0 := by
        simp only [h']
        rw [eventuallyEq_iff_exists_mem] at H ⊢
        obtain ⟨s, hs⟩ := H
        exact ⟨s, hs.1, fun x hx ↦ by simp [hs.2 hx]⟩
      intro n
      induction n using Nat.strongRecOn with | ind n ih =>
      -- it suffices to show that `n ^ x * LSeries F x` tends to `F n` as `x` tends to `∞`
      suffices Tendsto (fun x : ℝ ↦ n ^ (x : ℂ) * LSeries F x) atTop (nhds (F n)) by
        replace this := this.congr' <| H' n
        simp only [tendsto_const_nhds_iff] at this
        exact this.symm
      cases n with
      | zero => exact Tendsto.congr' (H' 0).symm <| by simp [hF₀]
      | succ n =>
          simpa using! LSeries.tendsto_cpow_mul_atTop (fun m hm ↦ ih m <| lt_succ_of_le hm) <|
            Ne.lt_top ha
    · simp [LSeries_congr (fun {n} ↦ H n) x, show (fun _ : ℕ ↦ (0 : ℂ)) = 0 from rfl]

open Nat in
/-- Assuming `f 0 = 0`, the `LSeries` of `f` is zero if and only if either `f = 0` or the
L-series converges nowhere. -/
/-
**LSeries_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_eq_zero_iff {f : Nat -> Complex} (hf : f 0 = 0) : LSeries f = 0 ↔ 
f = 0 ∨ abscissaOfAbsConv f = ⊤
参数：hf : f 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `LSeries_eq_zero_of_abscissaOfAbsConv_eq_top`：LSeries_eq_zero_of_abscissa
OfAbsConv_eq_top {f : Nat -> Complex} (h : abscissaOfAbsConv f = ⊤) : LSeries f 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LSeries_eventually_eq_zero_iff'`：LSeries_eventually_eq_zero_iff' {f : Na
t -> Complex} : (fun x : Real => LSeries f x) =ᶠ[atTop] 0 ↔ (forall n != 0, f n 
= 0) ∨ abscissaOfAbsC…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用引理 `LSeries_zero`：LSeries_zero : LSeries 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Assuming `f 0 = 0`, the `LSeries` of `f` is zero if and only if either `f = 0` o
r the
L-series converges nowhere.
-/
lemma LSeries_eq_zero_iff {f : ℕ → ℂ} (hf : f 0 = 0) :
    LSeries f = 0 ↔ f = 0 ∨ abscissaOfAbsConv f = ⊤ := by
  by_cases h : abscissaOfAbsConv f = ⊤
  · simpa [h] using! LSeries_eq_zero_of_abscissaOfAbsConv_eq_top h
  · simp only [h, or_false]
    refine ⟨fun H ↦ ?_, fun H ↦ H ▸ LSeries_zero⟩
    convert! (LSeries_eventually_eq_zero_iff'.mp ?_).resolve_right h
    · refine ⟨fun H' _ _ ↦ by rw [H', Pi.zero_apply], fun H' ↦ ?_⟩
      ext (- | m)
      · simp [hf]
      · simp [H']
    · simpa only [H] using! Filter.EventuallyEq.rfl

open Filter in
/-- If the `LSeries` of `f` and of `g` converge somewhere and agree on large real arguments,
then the L-series of `f - g` is zero for large real arguments. -/
/-
**LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq {f g : Nat -> Compl
ex} (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤) (h : (fun x : 
Real => LSeries f x) =ᶠ[atTop] fun x => LSeries g x) : (fun x : Real => LSeries 
(f - g) x) =ᶠ[atTop] (0 : Real -> Complex)
参数：hf : abscissaOfAbsConv f < ⊤；hg : abscissaOfAbsConv g < ⊤；h : (fun x : Real =
> LSeries f x) =ᶠ[atTop] fun x => LSeries g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `OrderBot.bot_le`：∀ {α : Type u} {inst : LE α} [self : OrderBot α] (a : α
), ⊥ ≤ a
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用引理 `LSeries_sub`：LSeries_sub {f g : Nat -> Complex} {s : Complex} (hf : LSer
iesSummable f s) (hg : LSeriesSummable g s) : LSeries (f - g) s = LSeries f s - 
L…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0

--- 原说明 ---
If the `LSeries` of `f` and of `g` converge somewhere and agree on large real ar
guments,
then the L-series of `f - g` is zero for large real arguments.
-/
lemma LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq {f g : ℕ → ℂ}
    (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤)
    (h : (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] fun x ↦ LSeries g x) :
    (fun x : ℝ ↦ LSeries (f - g) x) =ᶠ[atTop] (0 : ℝ → ℂ) := by
  rw [EventuallyEq, eventually_atTop] at h ⊢
  obtain ⟨x₀, hx₀⟩ := h
  obtain ⟨yf, hyf₁, hyf₂⟩ := exists_between hf
  obtain ⟨yg, hyg₁, hyg₂⟩ := exists_between hg
  lift yf to ℝ using ⟨hyf₂.ne, ((OrderBot.bot_le _).trans_lt hyf₁).ne'⟩
  lift yg to ℝ using ⟨hyg₂.ne, ((OrderBot.bot_le _).trans_lt hyg₁).ne'⟩
  refine ⟨max x₀ (max yf yg), fun x hx ↦ ?_⟩
  have Hf : LSeriesSummable f x := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ hyf₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
    exact (le_max_left _ yg).trans <| (le_max_right x₀ _).trans hx
  have Hg : LSeriesSummable g x := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (ofReal_re x).symm ▸ hyg₁.trans_le (EReal.coe_le_coe_iff.mpr ?_)
    exact (le_max_right yf _).trans <| (le_max_right x₀ _).trans hx
  rw [LSeries_sub Hf Hg, hx₀ x <| (le_max_left ..).trans hx, sub_self, Pi.zero_apply]

open Filter in
/-- If the `LSeries` of `f` and of `g` converge somewhere and agree on large real arguments,
then `f n = g n` whenever `n ≠ 0`. -/
/-
**LSeries.eq_of_LSeries_eventually_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries.eq_of_LSeries_eventually_eq {f g : Nat -> Complex} (hf : abscissaO
fAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤) (h : (fun x : Real => LSeries f x
) =ᶠ[atTop] fun x => LSeries g x) {n : Nat} (hn : n != 0) : f n = g n
参数：hf : abscissaOfAbsConv f < ⊤；hg : abscissaOfAbsConv g < ⊤；h : (fun x : Real =
> LSeries f x) =ᶠ[atTop] fun x => LSeries g x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq`：LSeries_sub_even
tuallyEq_zero_of_LSeries_eventually_eq {f g : Nat -> Complex} (hf : abscissaOfAb
sConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤) …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `LSeries.abscissaOfAbsConv_sub_le`：LSeries.abscissaOfAbsConv_sub_le (f g 
: Nat -> Complex) : abscissaOfAbsConv (f - g) <= max (abscissaOfAbsConv f) (absc
issaOfAbsConv g)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `LSeries_eventually_eq_zero_iff'`：LSeries_eventually_eq_zero_iff' {f : Na
t -> Complex} : (fun x : Real => LSeries f x) =ᶠ[atTop] 0 ↔ (forall n != 0, f n 
= 0) ∨ abscissaOfAbsC…

--- 原说明 ---
If the `LSeries` of `f` and of `g` converge somewhere and agree on large real ar
guments,
then `f n = g n` whenever `n ≠ 0`.
-/
lemma LSeries.eq_of_LSeries_eventually_eq {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) (h : (fun x : ℝ ↦ LSeries f x) =ᶠ[atTop] fun x ↦ LSeries g x)
    {n : ℕ} (hn : n ≠ 0) :
    f n = g n := by
  have hsub : (fun x : ℝ ↦ LSeries (f - g) x) =ᶠ[atTop] (0 : ℝ → ℂ) :=
    LSeries_sub_eventuallyEq_zero_of_LSeries_eventually_eq hf hg h
  have ha : abscissaOfAbsConv (f - g) ≠ ⊤ :=
    lt_top_iff_ne_top.mp <| (abscissaOfAbsConv_sub_le f g).trans_lt <| max_lt hf hg
  simpa only [Pi.sub_apply, sub_eq_zero]
    using (LSeries_eventually_eq_zero_iff'.mp hsub).resolve_right ha n hn

/-- If the `LSeries` of `f` and of `g` both converge somewhere, then they are equal if and only
if `f n = g n` whenever `n ≠ 0`. -/
/-
**LSeries_eq_iff_of_abscissaOfAbsConv_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_eq_iff_of_abscissaOfAbsConv_lt_top {f g : Nat -> Complex} (hf : ab
scissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤) : LSeries f = LSeries g ↔ 
forall n != 0, f n = g n
参数：hf : abscissaOfAbsConv f < ⊤；hg : abscissaOfAbsConv g < ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.eq_of_LSeries_eventually_eq`：LSeries.eq_of_LSeries_eventually_eq
 {f g : Nat -> Complex} (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g
 < ⊤) (h : (fun x : Real …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s

--- 原说明 ---
If the `LSeries` of `f` and of `g` both converge somewhere, then they are equal 
if and only
if `f n = g n` whenever `n ≠ 0`.
-/
lemma LSeries_eq_iff_of_abscissaOfAbsConv_lt_top {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤)
    (hg : abscissaOfAbsConv g < ⊤) :
    LSeries f = LSeries g ↔ ∀ n ≠ 0, f n = g n := by
  refine ⟨fun H n hn ↦ ?_, fun H ↦ funext (LSeries_congr fun {n} ↦ H n)⟩
  refine eq_of_LSeries_eventually_eq hf hg ?_ hn
  exact Filter.Eventually.of_forall fun x ↦ congr_fun H x

/-- The map `f ↦ LSeries f` is injective on functions `f` such that `f 0 = 0` and the L-series
of `f` converges somewhere. -/
/-
**LSeries_injOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LSeries_injOn : Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`：LSeries_eq_iff_of_abscissaOf
AbsConv_lt_top {f g : Nat -> Complex} (hf : abscissaOfAbsConv f < ⊤) (hg : absci
ssaOfAbsConv g < ⊤) : LSeries f …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.zero_ne_add_one`：∀ (n : ℕ), 0 ≠ n + 1

--- 原说明 ---
The map `f ↦ LSeries f` is injective on functions `f` such that `f 0 = 0` and th
e L-series
of `f` converges somewhere.
-/
lemma LSeries_injOn : Set.InjOn LSeries {f | f 0 = 0 ∧ abscissaOfAbsConv f < ⊤} := by
  intro f hf g hg h
  push _ ∈ _ at hf hg
  replace h := (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf.2 hg.2).mp h
  ext1 n
  cases n with
  | zero => exact hf.1.trans hg.1.symm
  | succ n => exact h _ n.zero_ne_add_one.symm
