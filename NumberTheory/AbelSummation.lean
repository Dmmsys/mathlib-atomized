/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Order.IsLocallyClosed

/-!
# Abel's summation formula

We prove several versions of Abel's summation formula.

## Results

* `sum_mul_eq_sub_sub_integral_mul`: general statement of the formula for a sum between two
  (nonnegative) reals `a` and `b`.

* `sum_mul_eq_sub_integral_mul`: a specialized version of `sum_mul_eq_sub_sub_integral_mul` for
  the case `a = 0`.

* `sum_mul_eq_sub_integral_mul₀`: a specialized version of `sum_mul_eq_sub_integral_mul` for
  when the first coefficient of the sequence is `0`. This is useful for `ArithmeticFunction`.

Primed versions of the three results above are also stated for when the endpoints are `Nat`.

* `tendsto_sum_mul_atTop_nhds_one_sub_integral`: limit version of `sum_mul_eq_sub_integral_mul`
  when `a` tends to `∞`.

* `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`: limit version of `sum_mul_eq_sub_integral_mul₀`
  when `a` tends to `∞`.

* `summable_mul_of_bigO_atTop`: let `c : ℕ → 𝕜` and `f : ℝ → 𝕜` with `𝕜 = ℝ` or `ℂ`, prove the
  summability of `n ↦ (c n) * (f n)` using Abel's formula under some `bigO` assumptions at infinity.

## References

* <https://en.wikipedia.org/wiki/Abel%27s_summation_formula>

-/

public section

noncomputable section

open Finset MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}

namespace abelSummationProof

open intervalIntegral IntervalIntegrable

/-
**abelSummationProof.sumlocc** 是 Mathlib 中的一个定理，位于命名空间 `abelSummationProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem sumlocc {m : ℕ} (n : ℕ) :
    ∀ᵐ t, t ∈ Set.Icc (n : ℝ) (n + 1) → ∑ k ∈ Icc m ⌊t⌋₊, c k = ∑ k ∈ Icc m n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

open scoped Interval in
/-
**abelSummationProof.integralmulsum** 是 Mathlib 中的一个定理，位于命名空间 `abelSummationProo
f`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem integralmulsum (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (t₁ t₂ : ℝ) (n : ℕ) (h : t₁ ≤ t₂)
    (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1) (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
    ∫ t in t₁..t₂, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      (f t₂ - f t₁) * ∑ k ∈ Icc 0 n, c k := by
  have h_inc₁ : Ι t₁ t₂ ⊆ Set.Icc n (n + 1) :=
    Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ ⊆ Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_deriv_eq_sub (fun t ht ↦ hf_diff t (h_inc₂ ht)),
      ← intervalIntegral.integral_mul_const]
  · refine integral_congr_ae ?_
    filter_upwards [sumlocc c n] with t h h'
    rw [h (h_inc₁ h')]
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (hf_int.mono_set ?_)
    rwa [← Set.uIcc_of_le h]
/-
**abelSummationProof.ineqofmemIco** 是 Mathlib 中的一个定理，位于命名空间 `abelSummationProof`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ineqofmemIco {k : ℕ} (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have := (Set.mem_Ico.mp hk).1
    exact le_of_lt <| (Nat.floor_lt' (by lia)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2
/-
**abelSummationProof.ineqofmemIco'** 是 Mathlib 中的一个定理，位于命名空间 `abelSummationProof
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ineqofmemIco' {k : ℕ} (hk : k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b :=
  ineqofmemIco (by rwa [← Finset.coe_Ico])
/-
**abelSummationProof._root_.integrableOn_mul_sum_Icc** 是 Mathlib 中的一个定理，位于命名空间 `
abelSummationProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.integrableOn_mul_sum_Icc {m : ℕ} (ha : 0 ≤ a) {g : ℝ → 𝕜}
    (hg_int : IntegrableOn g (Set.Icc a b)) :
    IntegrableOn (fun t ↦ g t * ∑ k ∈ Icc m ⌊t⌋₊, c k) (Set.Icc a b) := by
  obtain hab | hab := le_or_gt a b
  · obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
    · have : ∀ᵐ t, t ∈ Set.Icc a b → ∑ k ∈ Icc m ⌊a⌋₊, c k = ∑ k ∈ Icc m ⌊t⌋₊, c k := by
        filter_upwards [sumlocc c ⌊a⌋₊] with t ht₁ ht₂
        rw [ht₁ ⟨(Nat.floor_le ha).trans ht₂.1, hb ▸ ht₂.2.trans (Nat.lt_floor_add_one b).le⟩]
      rw [← ae_restrict_iff' measurableSet_Icc] at this
      exact IntegrableOn.congr_fun_ae
        (hg_int.mul_const _) ((Filter.EventuallyEq.refl _ g).mul this)
    · have h_locint {t₁ t₂ : ℝ} {n : ℕ} (h : t₁ ≤ t₂) (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1)
          (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
          IntervalIntegrable (fun t ↦ g t * ∑ k ∈ Icc m ⌊t⌋₊, c k) volume t₁ t₂ := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le h]
        exact (IntegrableOn.mono_set (hg_int.mul_const _) (Set.Icc_subset_Icc h₃ h₄)).congr
          <| ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc h₁ h₂)
            <| (ae_restrict_iff' measurableSet_Icc).mpr
              (by filter_upwards [sumlocc c n] with t h ht using by rw [h ht])
      have aux1 : 0 ≤ b := (Nat.pos_of_floor_pos <| (Nat.zero_le _).trans_lt hb).le
      have aux2 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff aux1]
      have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
      have aux4 : a ≤ ⌊b⌋₊ := le_of_lt (by rwa [← Nat.floor_lt ha])
      -- now break up into 3 subintervals
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (aux3.trans aux2)]
      have I1 : IntervalIntegrable _ volume a ↑(⌊a⌋₊ + 1) :=
        h_locint (mod_cast aux3) (Nat.floor_le ha) (mod_cast le_rfl) le_rfl (mod_cast aux2)
      have I2 : IntervalIntegrable _ volume ↑(⌊a⌋₊ + 1) ⌊b⌋₊ :=
        trans_iterate_Ico hb fun k hk ↦ h_locint (mod_cast k.le_succ)
          le_rfl (mod_cast le_rfl) (ineqofmemIco hk).1 (mod_cast (ineqofmemIco hk).2)
      have I3 : IntervalIntegrable _ volume ⌊b⌋₊ b :=
        h_locint (Nat.floor_le aux1) le_rfl (Nat.lt_floor_add_one _).le aux4 le_rfl
      exact (I1.trans I2).trans I3
  · rw [Set.Icc_eq_empty_of_lt hab]
    exact integrableOn_empty

/-- Abel's summation formula. -/
/-
**abelSummationProof._root_.sum_mul_eq_sub_sub_integral_mul** 是 Mathlib 中的一个定理，位
于命名空间 `abelSummationProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abel's summation formula.
-/
theorem _root_.sum_mul_eq_sub_sub_integral_mul (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ ≤ a := Nat.floor_le ha
  have aux2 : b ≤ ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul,
      integralmulsum c hf_diff hf_int _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl, sub_self]
  have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : ⌊b⌋₊ ≤ b := Nat.floor_le (ha.trans hab)
  have aux6 : a ≤ ⌊b⌋₊ := Nat.floor_lt ha |>.mp hb |>.le
  simp_rw [← smul_eq_mul, sum_Ioc_by_parts (fun k ↦ f k) _ hb, range_eq_Ico,
    Ico_add_one_right_eq_Icc, smul_eq_mul]
  have : ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f k) * ∑ n ∈ Icc 0 k, c n =
        ∑ k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊, ∫ t in k..↑(k + 1), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n := by
    rw [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (by lia), Eq.comm]
    exact sum_congr rfl fun k hk ↦ (integralmulsum c hf_diff hf_int _ _ _ (mod_cast k.le_succ)
      le_rfl (mod_cast le_rfl) (ineqofmemIco' hk).1 <| mod_cast (ineqofmemIco' hk).2)
  rw [this, sum_integral_adjacent_intervals_Ico hb, Nat.cast_add, Nat.cast_one,
    ← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1),
    ← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b),
    integralmulsum c hf_diff hf_int _ _ _ aux3 aux1 le_rfl le_rfl aux4,
    integralmulsum c hf_diff hf_int _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  -- now deal with the integrability side goals
  -- (Note we have 5 goals, but the 1st and 3rd are identical. TODO: find a non-hacky way of dealing
  -- with both at once.)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux5]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_left aux6)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux3]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux4)
  · exact fun k hk ↦ (intervalIntegrable_iff_integrableOn_Icc_of_le (mod_cast k.le_succ)).mpr
      <| (integrableOn_mul_sum_Icc c ha hf_int).mono_set
        <| (Set.Icc_subset_Icc_iff (mod_cast k.le_succ)).mpr <| mod_cast (ineqofmemIco hk)

/-- A version of `sum_mul_eq_sub_sub_integral_mul` where the endpoints are `Nat`. -/
/-
**abelSummationProof._root_.sum_mul_eq_sub_sub_integral_mul'** 是 Mathlib 中的一个定理，
位于命名空间 `abelSummationProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `sum_mul_eq_sub_sub_integral_mul` where the endpoints are `Nat`.
-/
theorem _root_.sum_mul_eq_sub_sub_integral_mul' {n m : ℕ} (h : n ≤ m)
    (hf_diff : ∀ t ∈ Set.Icc (n : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (n : ℝ) m)) :
    ∑ k ∈ Ioc n m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) - f n * (∑ k ∈ Icc 0 n, c k) -
        ∫ t in Set.Ioc (n : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  convert! sum_mul_eq_sub_sub_integral_mul c n.cast_nonneg (Nat.cast_le.mpr h) hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

end abelSummationProof

section specialversions

/-- Specialized version of `sum_mul_eq_sub_sub_integral_mul` for the case `a = 0` -/
/-
**sum_mul_eq_sub_integral_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_mul_eq_sub_integral_mul {b : Real} (hb : 0 <= b) (hf_diff : forall t i
n Set.Icc 0 b, DifferentiableAt Real f t) (hf_int : IntegrableOn (deriv f) (Set.
Icc 0 b)) : ∑ k in Icc 0 ⌊b⌋₊, f k * c k = f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t 
in Set.Ioc 0 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k
参数：hb : 0 <= b；hf_diff : forall t in Set.Icc 0 b, DifferentiableAt Real f t；hf_i
nt : IntegrableOn (deriv f) (Set.Icc 0 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_zero`：floor_zero : ⌊(0 : R)⌋₊ = 0
· 使用定理 `sum_mul_eq_sub_sub_integral_mul`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c :
 ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ},   0 ≤ a →     a ≤ b →       (∀ t ∈ Set.Icc a b, D
ifferentiableAt ℝ f t…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Specialized version of `sum_mul_eq_sub_sub_integral_mul` for the case `a = 0`
-/
theorem sum_mul_eq_sub_integral_mul {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 0 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 0 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 0 b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons, ← Nat.floor_zero (R := ℝ), sum_mul_eq_sub_sub_integral_mul c le_rfl hb hf_diff
    hf_int, Nat.floor_zero, Nat.cast_zero, Icc_self, sum_singleton]
  ring

/-- A version of `sum_mul_eq_sub_integral_mul` where the endpoint is a `Nat`. -/
/-
**sum_mul_eq_sub_integral_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_mul_eq_sub_integral_mul' (m : Nat) (hf_diff : forall t in Set.Icc (0 :
 Real) m, DifferentiableAt Real f t) (hf_int : IntegrableOn (deriv f) (Set.Icc (
0 : Real) m)) : ∑ k in Icc 0 m, f k * c k = f m * (∑ k in Icc 0 m, c k) - ∫ t in
 Set.Ioc (0 : Real) m, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k
参数：m : Nat；hf_diff : forall t in Set.Icc (0 : Real) m, DifferentiableAt Real f t
；hf_int : IntegrableOn (deriv f) (Set.Icc (0 : Real) m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_natCast`：floor_natCast (n : Nat) : ⌊(n : R)⌋₊ = n
· 使用定理 `sum_mul_eq_sub_integral_mul`：sum_mul_eq_sub_integral_mul {b : Real} (hb 
: 0 <= b) (hf_diff : forall t in Set.Icc 0 b, DifferentiableAt Real f t) (hf_int
 : IntegrableOn (…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)

--- 原说明 ---
A version of `sum_mul_eq_sub_integral_mul` where the endpoint is a `Nat`.
-/
theorem sum_mul_eq_sub_integral_mul' (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (0 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (0 : ℝ) m)) :
    ∑ k ∈ Icc 0 m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) -
        ∫ t in Set.Ioc (0 : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  convert! sum_mul_eq_sub_integral_mul c m.cast_nonneg hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

/-- Specialized version of `sum_mul_eq_sub_integral_mul` when the first coefficient of the sequence
`c` is equal to `0`. -/
/-
**sum_mul_eq_sub_integral_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_mul_eq_sub_integral_mul {b : Real} (hb : 0 <= b) (hf_diff : forall t i
n Set.Icc 0 b, DifferentiableAt Real f t) (hf_int : IntegrableOn (deriv f) (Set.
Icc 0 b)) : ∑ k in Icc 0 ⌊b⌋₊, f k * c k = f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t 
in Set.Ioc 0 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k
参数：hb : 0 <= b；hf_diff : forall t in Set.Icc 0 b, DifferentiableAt Real f t；hf_i
nt : IntegrableOn (deriv f) (Set.Icc 0 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_zero`：floor_zero : ⌊(0 : R)⌋₊ = 0
· 使用定理 `sum_mul_eq_sub_sub_integral_mul`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c :
 ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ},   0 ≤ a →     a ≤ b →       (∀ t ∈ Set.Icc a b, D
ifferentiableAt ℝ f t…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Specialized version of `sum_mul_eq_sub_integral_mul` when the first coefficient 
of the sequence
`c` is equal to `0`.
-/
theorem sum_mul_eq_sub_integral_mul₀ (hc : c 0 = 0) (b : ℝ)
    (hf_diff : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 1 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 1 b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  obtain hb | hb := le_or_gt 1 b
  · have : 1 ≤ ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb
    nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, ← Icc_add_one_left_eq_Ioc,
      Icc_eq_cons_Ioc (by lia), sum_cons]
    rw [zero_add, ← Nat.floor_one (R := ℝ),
      sum_mul_eq_sub_sub_integral_mul c zero_le_one hb hf_diff hf_int, Nat.floor_one, Nat.cast_one,
      Icc_eq_cons_Ioc zero_le_one, sum_cons, show 1 = 0 + 1 by rfl, Nat.Ioc_succ_singleton,
      zero_add, sum_singleton, hc, mul_zero, zero_add]
    ring
  · simp_rw [Nat.floor_eq_zero.mpr hb, Icc_self, sum_singleton, Nat.cast_zero, hc, mul_zero,
      Set.Ioc_eq_empty_of_le hb.le, Measure.restrict_empty, integral_zero_measure, sub_self]

/-- A version of `sum_mul_eq_sub_integral_mul₀` where the endpoint is a `Nat`. -/
/-
**sum_mul_eq_sub_integral_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_mul_eq_sub_integral_mul {b : Real} (hb : 0 <= b) (hf_diff : forall t i
n Set.Icc 0 b, DifferentiableAt Real f t) (hf_int : IntegrableOn (deriv f) (Set.
Icc 0 b)) : ∑ k in Icc 0 ⌊b⌋₊, f k * c k = f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t 
in Set.Ioc 0 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k
参数：hb : 0 <= b；hf_diff : forall t in Set.Icc 0 b, DifferentiableAt Real f t；hf_i
nt : IntegrableOn (deriv f) (Set.Icc 0 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_zero`：floor_zero : ⌊(0 : R)⌋₊ = 0
· 使用定理 `sum_mul_eq_sub_sub_integral_mul`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c :
 ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ},   0 ≤ a →     a ≤ b →       (∀ t ∈ Set.Icc a b, D
ifferentiableAt ℝ f t…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `sum_mul_eq_sub_integral_mul₀` where the endpoint is a `Nat`.
-/
theorem sum_mul_eq_sub_integral_mul₀' (hc : c 0 = 0) (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) m)) :
    ∑ k ∈ Icc 0 m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) -
        ∫ t in Set.Ioc (1 : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  convert! sum_mul_eq_sub_integral_mul₀ c hc m hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

/-- Specialized version of `sum_mul_eq_sub_integral_mul` when `c 0 = c 1 = 0`. -/
/-
**sum_mul_eq_sub_integral_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_mul_eq_sub_integral_mul {b : Real} (hb : 0 <= b) (hf_diff : forall t i
n Set.Icc 0 b, DifferentiableAt Real f t) (hf_int : IntegrableOn (deriv f) (Set.
Icc 0 b)) : ∑ k in Icc 0 ⌊b⌋₊, f k * c k = f b * (∑ k in Icc 0 ⌊b⌋₊, c k) - ∫ t 
in Set.Ioc 0 b, deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k
参数：hb : 0 <= b；hf_diff : forall t in Set.Icc 0 b, DifferentiableAt Real f t；hf_i
nt : IntegrableOn (deriv f) (Set.Icc 0 b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_zero`：floor_zero : ⌊(0 : R)⌋₊ = 0
· 使用定理 `sum_mul_eq_sub_sub_integral_mul`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c :
 ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ},   0 ≤ a →     a ≤ b →       (∀ t ∈ Set.Icc a b, D
ifferentiableAt ℝ f t…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Specialized version of `sum_mul_eq_sub_integral_mul` when `c 0 = c 1 = 0`.
-/
theorem sum_mul_eq_sub_integral_mul₁ (hc : c 0 = 0) (hc1 : c 1 = 0) (b : ℝ)
    (hf_diff : ∀ t ∈ Set.Icc 2 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 2 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 2 b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  by_cases! hb : b < 2
  · -- Easy case, everything is 0
    have H₁ : ∀ n ∈ Icc 0 ⌊b⌋₊, c n = 0 := by grind [(Nat.floor_lt' two_ne_zero).mpr hb]
    have H₂ : ∀ n ∈ Icc 0 ⌊b⌋₊, f n * c n = 0 := by grind
    simp [sum_eq_zero H₁, sum_eq_zero H₂, Set.Ioc_eq_empty_of_le hb.le]
  -- Split off the first two terms of the sum
  have : 2 ≤ ⌊b⌋₊ := Nat.le_floor hb
  have H : ∑ k ∈ Icc 0 ⌊b⌋₊, f ↑k * c k = f (2 :) * c 2 + ∑ k ∈ Ioc 2 ⌊b⌋₊, f ↑k * c k := by
    rw [add_sum_Ioc_eq_sum_Icc (f := fun (k : ℕ) ↦ f k * c k) this,
      show Icc 0 ⌊b⌋₊ = {0, 1} ∪ Icc 2 ⌊b⌋₊ by grind]
    exact sum_union_eq_right fun k hk hk' ↦ by grind
  rw [H]
  -- Apply Abel summation to the remainder
  nth_rewrite 3 [show 2 = ⌊(2 : ℝ)⌋₊ by simp]
  rw [sum_mul_eq_sub_sub_integral_mul c zero_le_two hb hf_diff hf_int]
  simp [show Icc 0 2 = {0, 1, 2} by rfl, hc, hc1]
  grind

end specialversions

section limit

open Filter Topology abelSummationProof intervalIntegral

/-
**locallyIntegrableOn_mul_sum_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyIntegrableOn_mul_sum_Icc {m : Nat} (ha : 0 <= a) {g : Real -> 𝕜} (h
g : LocallyIntegrableOn g (Set.Ici a)) : LocallyIntegrableOn (fun t => g t * ∑ k
 in Icc m ⌊t⌋₊, c k) (Set.Ici a)
参数：ha : 0 <= a；hg : LocallyIntegrableOn g (Set.Ici a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.locallyIntegrableOn_iff`：locallyIntegrableOn_iff [PseudoMe
trizableSpace ε] [LocallyCompactSpace X] (hs : IsLocallyClosed s) : LocallyInteg
rableOn f s μ ↔ forall (k :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `isLocallyClosed_Ici`：isLocallyClosed_Ici [Preorder X] [ClosedIciTopology
 X] : IsLocallyClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsCompact.sInf_mem`：IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α}
 (hs : IsCompact s) (ne_s : s.Nonempty) : sInf s in s
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `integrableOn_mul_sum_Icc`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c : ℕ → 𝕜)
 {a b : ℝ} {m : ℕ},   0 ≤ a →     ∀ {g : ℝ → 𝕜},       MeasureTheory.IntegrableO
n g (Set.Icc a…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `Set.Icc_subset_Ici_iff`：Icc_subset_Ici_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Ici a₂ ↔ a₂ <= a₁
· 使用定理 `Real.sInf_le_sSup`：sInf_le_sSup (s : Set Real) (h₁ : BddBelow s) (h₂ : B
ddAbove s) : sInf s <= sSup s
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsCompact.bddAbove`：IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddAbove s
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Bornology.IsBounded.subset_Icc_sInf_sSup`：∀ {α : Type u_1} [inst : Borno
logy α] [inst_1 : ConditionallyCompleteLattice α] [IsOrderBornology α] {s : Set 
α},   Bornology.IsBounded s → …
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `MeasureTheory.integrableOn_empty`：integrableOn_empty : IntegrableOn f ∅ 
μ
-/
theorem locallyIntegrableOn_mul_sum_Icc {m : ℕ} (ha : 0 ≤ a) {g : ℝ → 𝕜}
    (hg : LocallyIntegrableOn g (Set.Ici a)) :
    LocallyIntegrableOn (fun t ↦ g t * ∑ k ∈ Icc m ⌊t⌋₊, c k) (Set.Ici a) := by
  refine (locallyIntegrableOn_iff isLocallyClosed_Ici).mpr fun K hK₁ hK₂ ↦ ?_
  by_cases hK₃ : K.Nonempty
  · have h_inf : a ≤ sInf K := (hK₁ (hK₂.sInf_mem hK₃))
    refine IntegrableOn.mono_set ?_ (Bornology.IsBounded.subset_Icc_sInf_sSup hK₂.isBounded)
    refine integrableOn_mul_sum_Icc _ (ha.trans h_inf) ?_
    refine hg.integrableOn_compact_subset ?_ isCompact_Icc
    exact (Set.Icc_subset_Ici_iff (Real.sInf_le_sSup _ hK₂.bddBelow hK₂.bddAbove)).mpr h_inf
  · rw [Set.not_nonempty_iff_eq_empty.mp hK₃]
    exact integrableOn_empty
/-
**tendsto_sum_mul_atTop_nhds_one_sub_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_sum_mul_atTop_nhds_one_sub_integral (hf_diff : forall t in Set.Ici
 0, DifferentiableAt Real f t) (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 
0)) {l : 𝕜} (h_lim : Tendsto (fun n : Nat => f n * ∑ k in Icc 0 n, c k) atTop (𝓝
 l)) {g : Real -> 𝕜} (hg_dom : (fun t => deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) =O[
atTop] g) (hg_int : IntegrableAtFilter g atTop) : Tendsto (fun n : Nat => ∑ k in
 Icc 0 n, f k * c k) atTop (𝓝 (l - ∫ t in Set.Ioi 0, deriv f t * ∑ k in Icc 0 ⌊t
⌋₊, c k))
参数：hf_diff : forall t in Set.Ici 0, DifferentiableAt Real f t；hf_int : LocallyIn
tegrableOn (deriv f) (Set.Ici 0)；h_lim : Tendsto (fun n : Nat => f n * ∑ k in Ic
c 0 n, c k) atTop (𝓝 l)；hg_dom : (fun t => deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) =
O[atTop] g；hg_int : IntegrableAtFilter g atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `integrableOn_Ici_iff_integrableOn_Ioi`：integrableOn_Ici_iff_integrableOn
_Ioi (hb : ‖f b‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_of_isBigO_atTop`：∀ {α : T
ype u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E}
 {g : α → F} {a : α}   [inst_1 : TopologicalSpace α]…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
（共 43 条，此处仅展示前 30 条）
-/
theorem tendsto_sum_mul_atTop_nhds_one_sub_integral
    (hf_diff : ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ f t)
    (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 0)) {l : 𝕜}
    (h_lim : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Icc 0 n, c k) atTop (𝓝 l))
    {g : ℝ → 𝕜} (hg_dom : (fun t ↦ deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] g)
    (hg_int : IntegrableAtFilter g atTop) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * c k) atTop
      (𝓝 (l - ∫ t in Set.Ioi 0, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
  have h_lim' : Tendsto (fun n : ℕ ↦ ∫ t in Set.Ioc (0 : ℝ) n, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 0, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr (fun _ ↦ by rw [← integral_of_le (Nat.cast_nonneg _)]) ?_
    refine intervalIntegral_tendsto_integral_Ioi _ ?_ tendsto_natCast_atTop_atTop
    exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi
      <| (locallyIntegrableOn_mul_sum_Icc c le_rfl hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
  refine (h_lim.sub h_lim').congr (fun _ ↦ ?_)
  rw [sum_mul_eq_sub_integral_mul' _ _ (fun t ht ↦ hf_diff _ ht.1)]
  exact hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc
/-
**tendsto_sum_mul_atTop_nhds_one_sub_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_sum_mul_atTop_nhds_one_sub_integral (hf_diff : forall t in Set.Ici
 0, DifferentiableAt Real f t) (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 
0)) {l : 𝕜} (h_lim : Tendsto (fun n : Nat => f n * ∑ k in Icc 0 n, c k) atTop (𝓝
 l)) {g : Real -> 𝕜} (hg_dom : (fun t => deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) =O[
atTop] g) (hg_int : IntegrableAtFilter g atTop) : Tendsto (fun n : Nat => ∑ k in
 Icc 0 n, f k * c k) atTop (𝓝 (l - ∫ t in Set.Ioi 0, deriv f t * ∑ k in Icc 0 ⌊t
⌋₊, c k))
参数：hf_diff : forall t in Set.Ici 0, DifferentiableAt Real f t；hf_int : LocallyIn
tegrableOn (deriv f) (Set.Ici 0)；h_lim : Tendsto (fun n : Nat => f n * ∑ k in Ic
c 0 n, c k) atTop (𝓝 l)；hg_dom : (fun t => deriv f t * ∑ k in Icc 0 ⌊t⌋₊, c k) =
O[atTop] g；hg_int : IntegrableAtFilter g atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `integrableOn_Ici_iff_integrableOn_Ioi`：integrableOn_Ici_iff_integrableOn
_Ioi (hb : ‖f b‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_of_isBigO_atTop`：∀ {α : T
ype u_1} {E : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup E] {f : α → E}
 {g : α → F} {a : α}   [inst_1 : TopologicalSpace α]…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
（共 43 条，此处仅展示前 30 条）
-/
theorem tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (hc : c 0 = 0)
    (hf_diff : ∀ t ∈ Set.Ici 1, DifferentiableAt ℝ f t)
    (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 1)) {l : 𝕜}
    (h_lim : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Icc 0 n, c k) atTop (𝓝 l))
    {g : ℝ → ℝ} (hg_dom : (fun t ↦ deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] g)
    (hg_int : IntegrableAtFilter g atTop) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * c k) atTop
      (𝓝 (l - ∫ t in Set.Ioi 1, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
  have h : (fun n : ℕ ↦ ∫ (x : ℝ) in (1 : ℝ)..n, deriv f x * ∑ k ∈ Icc 0 ⌊x⌋₊, c k) =ᶠ[atTop]
      (fun n : ℕ ↦ ∫ (t : ℝ) in Set.Ioc 1 ↑n, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
    filter_upwards [eventually_ge_atTop 1] with _ h
    rw [← integral_of_le (Nat.one_le_cast.mpr h)]
  have h_lim' : Tendsto (fun n : ℕ ↦ ∫ t in Set.Ioc (1 : ℝ) n, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 1, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr' h (intervalIntegral_tendsto_integral_Ioi _ ?_ tendsto_natCast_atTop_atTop)
    exact Iff.mp integrableOn_Ici_iff_integrableOn_Ioi
      <| (locallyIntegrableOn_mul_sum_Icc c zero_le_one hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
  refine (h_lim.sub h_lim').congr (fun _ ↦ ?_)
  rw [sum_mul_eq_sub_integral_mul₀' _ hc _ (fun t ht ↦ hf_diff _ ht.1)]
  exact hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc

end limit

section summable

open Filter abelSummationProof

/-
**summable_mul_of_bigO_atTop_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem summable_mul_of_bigO_atTop_aux (m : ℕ)
    (h_bdd : (fun n : ℕ ↦ ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖) =O[atTop] fun _ ↦ (1 : ℝ))
    (hf_int : LocallyIntegrableOn (deriv (fun t ↦ ‖f t‖)) (Set.Ici (m : ℝ)))
    (hf : ∀ n : ℕ, ∑ k ∈ Icc 0 n, ‖f k‖ * ‖c k‖ =
      ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖ -
        ∫ (t : ℝ) in Set.Ioc ↑m ↑n, deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖)
    {g : ℝ → ℝ}
    (hg₁ : (fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : ℕ ↦ f n * c n) := by
  obtain ⟨C₁, hC₁⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h_bdd
  let C₂ := ∫ t in Set.Ioi (m : ℝ), ‖deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖‖
  refine summable_of_sum_range_norm_le (c := max (C₁ + C₂) 1) fun n ↦ ?_
  cases n with
  | zero => simp only [range_zero, norm_mul, sum_empty, le_sup_iff, zero_le_one, or_true]
  | succ n =>
      rw [Nat.range_eq_Icc_zero_sub_one _ n.add_one_ne_zero, add_tsub_cancel_right]
      calc
        _ = ∑ k ∈ Icc 0 n, ‖f k‖ * ‖c k‖ := by simp_rw [norm_mul]
        _ = ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖ -
              ∫ t in Set.Ioc ↑m ↑n, deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖ := ?_
        _ ≤ C₁ - ∫ t in Set.Ioc ↑m ↑n, deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖ := ?_
        _ ≤ C₁ + ∫ t in Set.Ioc ↑m ↑n, ‖deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖‖ := ?_
        _ ≤ C₁ + C₂ := ?_
        _ ≤ max (C₁ + C₂) 1 := le_max_left _ _
      · exact hf _
      · refine tsub_le_tsub_right (le_of_eq_of_le (Real.norm_of_nonneg ?_).symm (hC₁ n)) _
        exact mul_nonneg (norm_nonneg _) (sum_nonneg fun _ _ ↦ norm_nonneg _)
      · grw [sub_eq_add_neg, neg_le_abs, abs_integral_le_integral_abs]
        simp
      · unfold C₂
        grw [setIntegral_mono_set ?_ (.of_forall fun _ ↦ norm_nonneg _)
          Set.Ioc_subset_Ioi_self.eventuallyLE]
        rw [← integrableOn_Ici_iff_integrableOn_Ioi, IntegrableOn,
          integrable_norm_iff (by fun_prop)]
        exact (locallyIntegrableOn_mul_sum_Icc _ m.cast_nonneg hf_int).integrableOn_of_isBigO_atTop
          hg₁ hg₂
/-
**summable_mul_of_bigO_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_mul_of_bigO_atTop (hf_diff : forall t in Set.Ici 0, Differentiabl
eAt Real (fun x => ‖f x‖) t) (hf_int : LocallyIntegrableOn (deriv (fun t => ‖f t
‖)) (Set.Ici 0)) (h_bdd : (fun n : Nat => ‖f n‖ * ∑ k in Icc 0 n, ‖c k‖) =O[atTo
p] fun _ => (1 : Real)) {g : Real -> Real} (hg₁ : (fun t => deriv (fun t => ‖f t
‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g) (hg₂ : IntegrableAtFilter g atTop)
 : Summable (fun n : Nat => f n * c n)
参数：hf_diff : forall t in Set.Ici 0, DifferentiableAt Real (fun x => ‖f x‖) t；hf_
int : LocallyIntegrableOn (deriv (fun t => ‖f t‖)) (Set.Ici 0)；h_bdd : (fun n : 
Nat => ‖f n‖ * ∑ k in Icc 0 n, ‖c k‖) =O[atTop] fun _ => (1 : Real)；hg₁ : (fun t
 => deriv (fun t => ‖f t‖) t * ∑ k in Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g；hg₂ : Integ
rableAtFilter g atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.AbelSummation.0.summable_mul_of_bigO_atTop
_aux`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} (m : ℕ),   ((fu
n n => ‖f ↑n‖ * ∑ k ∈ Finset.Icc 0 n, ‖c k‖) =O[Filter.atTop] fun …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sum_mul_eq_sub_integral_mul'`：sum_mul_eq_sub_integral_mul' (m : Nat) (hf
_diff : forall t in Set.Icc (0 : Real) m, DifferentiableAt Real f t) (hf_int : I
ntegrableOn (deriv…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem summable_mul_of_bigO_atTop
    (hf_diff : ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ (fun x ↦ ‖f x‖) t)
    (hf_int : LocallyIntegrableOn (deriv (fun t ↦ ‖f t‖)) (Set.Ici 0))
    (h_bdd : (fun n : ℕ ↦ ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖) =O[atTop] fun _ ↦ (1 : ℝ))
    {g : ℝ → ℝ} (hg₁ : (fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : ℕ ↦ f n * c n) := by
  refine summable_mul_of_bigO_atTop_aux c 0 h_bdd (by rwa [Nat.cast_zero]) (fun n ↦ ?_) hg₁ hg₂
  exact_mod_cast sum_mul_eq_sub_integral_mul' _ _ (fun _ ht ↦ hf_diff _ ht.1)
    (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)

/-- A version of `summable_mul_of_bigO_atTop` that can be useful to avoid difficulties near zero. -/
/-
**summable_mul_of_bigO_atTop'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_mul_of_bigO_atTop' (hf_diff : forall t in Set.Ici 1, Differentiab
leAt Real (fun x => ‖f x‖) t) (hf_int : LocallyIntegrableOn (deriv (fun t => ‖f 
t‖)) (Set.Ici 1)) (h_bdd : (fun n : Nat => ‖f n‖ * ∑ k in Icc 1 n, ‖c k‖) =O[atT
op] fun _ => (1 : Real)) {g : Real -> Real} (hg₁ : (fun t => deriv (fun t => ‖f 
t‖) t * ∑ k in Icc 1 ⌊t⌋₊, ‖c k‖) =O[atTop] g) (hg₂ : IntegrableAtFilter g atTop
) : Summable (fun n : Nat => f n * c n)
参数：hf_diff : forall t in Set.Ici 1, DifferentiableAt Real (fun x => ‖f x‖) t；hf_
int : LocallyIntegrableOn (deriv (fun t => ‖f t‖)) (Set.Ici 1)；h_bdd : (fun n : 
Nat => ‖f n‖ * ∑ k in Icc 1 n, ‖c k‖) =O[atTop] fun _ => (1 : Real)；hg₁ : (fun t
 => deriv (fun t => ‖f t‖) t * ∑ k in Icc 1 ⌊t⌋₊, ‖c k‖) =O[atTop] g；hg₂ : Integ
rableAtFilter g atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ioc`：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a 
b).cons a left_notMem_Ioc
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.Icc_add_one_left_eq_Ioc`：Icc_add_one_left_eq_Ioc (a b : α) : Icc 
(a + 1) b = Ioc a b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Summable.congr_atTop`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 :
 TopologicalSpace α] [IsTopologicalAddGroup α] {f₁ g₁ : ℕ → α},   Summable f₁ → 
f₁ =ᶠ[Filt…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `_private.Mathlib.NumberTheory.AbelSummation.0.summable_mul_of_bigO_atTop
_aux`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} (m : ℕ),   ((fu
n n => ‖f ↑n‖ * ∑ k ∈ Finset.Icc 0 n, ‖c k‖) =O[Filter.atTop] fun …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `summable_mul_of_bigO_atTop` that can be useful to avoid difficulti
es near zero.
-/
theorem summable_mul_of_bigO_atTop'
    (hf_diff : ∀ t ∈ Set.Ici 1, DifferentiableAt ℝ (fun x ↦ ‖f x‖) t)
    (hf_int : LocallyIntegrableOn (deriv (fun t ↦ ‖f t‖)) (Set.Ici 1))
    (h_bdd : (fun n : ℕ ↦ ‖f n‖ * ∑ k ∈ Icc 1 n, ‖c k‖) =O[atTop] fun _ ↦ (1 : ℝ))
    {g : ℝ → ℝ} (hg₁ : (fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 1 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : ℕ ↦ f n * c n) := by
  have h : ∀ n, ∑ k ∈ Icc 1 n, ‖c k‖ = ∑ k ∈ Icc 0 n, ‖(fun n ↦ if n = 0 then 0 else c n) k‖ := by
    intro n
    rw [Icc_eq_cons_Ioc n.zero_le, sum_cons, ← Icc_add_one_left_eq_Ioc, zero_add]
    simp_rw [if_pos, norm_zero, zero_add]
    exact Finset.sum_congr rfl fun _ h ↦ by rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne']
  simp_rw [h] at h_bdd hg₁
  refine Summable.congr_atTop (summable_mul_of_bigO_atTop_aux (fun n ↦ if n = 0 then 0 else c n) 1
    h_bdd (by rwa [Nat.cast_one]) (fun n ↦ ?_) hg₁ hg₂) ?_
  · exact_mod_cast sum_mul_eq_sub_integral_mul₀' _ (by simp only [reduceIte, norm_zero]) n
      (fun _ ht ↦ hf_diff _ ht.1)
      (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
  · filter_upwards [eventually_ne_atTop 0] with k hk
    simp_rw [if_neg hk]

end summable

