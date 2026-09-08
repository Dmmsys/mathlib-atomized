/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich, Vincent Beffara, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.Probability.Notation

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `MeasurableSpace` `M2` to define `μ`:

```lean
example {M1 : MeasurableSpace Ω} [M2 : MeasurableSpace Ω] {μ : Measure Ω} : sorry := sorry
example [M1 : MeasurableSpace Ω] {M2 : MeasurableSpace Ω} {μ : Measure Ω} : sorry := sorry
```

-/

public section


open Set MeasureTheory ENNReal

open scoped NNReal MeasureTheory

variable {Ω 𝕜 : Type*} [RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ≥0∞}
    {X Y : Ω → 𝕜}

namespace ProbabilityTheory

/-- If a random variable `f` in `ℝ≥0∞` is independent of an event `T`, then if you restrict the
  random variable to `T`, then `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
  `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`. -/
/-
**ProbabilityTheory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator {Mf mΩ : Meas
urableSpace Ω} {μ : Measure Ω} (hMf : Mf <= mΩ) (c : Real>=0∞) {T : Set Ω} (h_me
as_T : MeasurableSet T) (h_ind : IndepSets {s | MeasurableSet[Mf] s} {T} μ) (h_m
eas_f : Measurable[Mf] f) : (∫⁻ ω, f ω * T.indicator (fun _ => c) ω ∂μ) = (∫⁻ ω,
 f ω ∂μ) * ∫⁻ ω, T.indicator (fun _ => c) ω ∂μ
参数：hMf : Mf <= mΩ；c : Real>=0∞；h_meas_T : MeasurableSet T；h_ind : IndepSets {s |
 MeasurableSet[Mf] s} {T} μ；h_meas_f : Measurable[Mf] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_induction`：Measurable.ennreal_induction {motive : (α 
-> Real>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s ->
 motive (Set.indic…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用引理 `ProbabilityTheory.IndepSets_iff`：IndepSets_iff (s1 s2 : Set (Set Ω)) (μ 
: Measure Ω) : IndepSets s1 s2 μ ↔ forall t1 t2 : Set Ω, t1 in s1 -> t2 in s2 ->
 (μ (t1 inter t2) = μ…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用引理 `ENNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f 
i) * a = ⨆ i, f i * a
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a random variable `f` in `ℝ≥0∞` is independent of an event `T`, then if you r
estrict the
  random variable to `T`, then `E[f * indicator T c 0]=E[f] * E[indicator T c 0]
`. It is useful for
  `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace`.
-/
theorem lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator {Mf mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hMf : Mf ≤ mΩ) (c : ℝ≥0∞) {T : Set Ω} (h_meas_T : MeasurableSet T)
    (h_ind : IndepSets {s | MeasurableSet[Mf] s} {T} μ) (h_meas_f : Measurable[Mf] f) :
    (∫⁻ ω, f ω * T.indicator (fun _ => c) ω ∂μ) =
      (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, T.indicator (fun _ => c) ω ∂μ := by
  revert f
  have h_mul_indicator : ∀ g, Measurable g → Measurable fun a => g a * T.indicator (fun _ => c) a :=
    fun g h_mg => h_mg.mul (measurable_const.indicator h_meas_T)
  apply @Measurable.ennreal_induction _ Mf
  · intro c' s' h_meas_s'
    simp_rw [← inter_indicator_mul]
    rw [lintegral_indicator (MeasurableSet.inter (hMf _ h_meas_s') h_meas_T),
      lintegral_indicator (hMf _ h_meas_s'), lintegral_indicator h_meas_T]
    simp only [lintegral_const, univ_inter,
      MeasurableSet.univ, Measure.restrict_apply]
    rw [IndepSets_iff] at h_ind
    rw [mul_mul_mul_comm, h_ind s' T h_meas_s' (Set.mem_singleton _)]
  · intro f' g _ h_meas_f' _ h_ind_f' h_ind_g
    have h_measM_f' : Measurable f' := h_meas_f'.mono hMf le_rfl
    simp_rw [Pi.add_apply, right_distrib]
    rw [lintegral_add_left (h_mul_indicator _ h_measM_f'), lintegral_add_left h_measM_f',
      right_distrib, h_ind_f', h_ind_g]
  · intro f h_meas_f h_mono_f h_ind_f
    have h_measM_f : ∀ n, Measurable (f n) := fun n => (h_meas_f n).mono hMf le_rfl
    simp_rw [iSup_mul]
    rw [lintegral_iSup h_measM_f h_mono_f, lintegral_iSup, iSup_mul]
    · simp_rw [← h_ind_f]
    · exact fun n => h_mul_indicator _ (h_measM_f n)
    · exact fun m n h_le a => mul_le_mul_left (h_mono_f h_le a) _

/--
If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
of the random variables, it uses the independence of measurable spaces for the
domains of `f` and `g`. This is similar to the sigma-algebra approach to
independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` for
a more common variant of the product of independent variables. -/
/-
**ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_meas
urableSpace** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace {M
f Mg mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hMf : Mf <= mΩ) (hMg : Mg <= mΩ) (
h_ind : Indep Mf Mg μ) (h_meas_f : Measurable[Mf] f) (h_meas_g : Measurable[Mg] 
g) : ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ
参数：hMf : Mf <= mΩ；hMg : Mg <= mΩ；h_ind : Indep Mf Mg μ；h_meas_f : Measurable[Mf]
 f；h_meas_g : Measurable[Mg] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ennreal_induction`：Measurable.ennreal_induction {motive : (α 
-> Real>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s ->
 motive (Set.indic…
· 使用定理 `ProbabilityTheory.lintegral_mul_indicator_eq_lintegral_mul_lintegral_ind
icator`：lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator {Mf mΩ : Me
asurableSpace Ω} {μ : Measure Ω} (hMf : Mf <= mΩ) (c : Real>=0∞) {T …
· 使用定理 `ProbabilityTheory.indepSets_of_indepSets_of_le_right`：indepSets_of_indep
Sets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)} (h_indep : IndepSets s₁ s₂ μ) (h32 : s
₃ subseteq s₂) : IndepSets s₁ s₃ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `Measurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableMul₂ 
M], Meas…
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independen
ce
of the random variables, it uses the independence of measurable spaces for the
domains of `f` and `g`. This is similar to the sigma-algebra approach to
independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` for
a more common variant of the product of independent variables.
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    {Mf Mg mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hMf : Mf ≤ mΩ) (hMg : Mg ≤ mΩ)
    (h_ind : Indep Mf Mg μ) (h_meas_f : Measurable[Mf] f) (h_meas_g : Measurable[Mg] g) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  revert g
  have h_measM_f : Measurable f := h_meas_f.mono hMf le_rfl
  apply @Measurable.ennreal_induction _ Mg
  · intro c s h_s
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f
    apply indepSets_of_indepSets_of_le_right h_ind
    rwa [singleton_subset_iff]
  · intro f' g _ h_measMg_f' _ h_ind_f' h_ind_g'
    have h_measM_f' : Measurable f' := h_measMg_f'.mono hMg le_rfl
    simp_rw [Pi.add_apply, left_distrib]
    rw [lintegral_add_left h_measM_f',
      lintegral_add_left (h_measM_f.fun_mul h_measM_f'), left_distrib, h_ind_f', h_ind_g']
  · intro f' h_meas_f' h_mono_f' h_ind_f'
    have h_measM_f' : ∀ n, Measurable (f' n) := fun n => (h_meas_f' n).mono hMg le_rfl
    simp_rw [mul_iSup]
    rw [lintegral_iSup, lintegral_iSup h_measM_f' h_mono_f', mul_iSup]
    · simp_rw [← h_ind_f']
    · exact fun n => h_measM_f.mul (h_measM_f' n)
    · exact fun n m (h_le : n ≤ m) a => mul_le_mul_right (h_mono_f' h_le a) _

/-- If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`. -/
/-
**ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun** 是 Mat
hlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurabl
e f) (h_meas_g : Measurable g) (h_indep_fun : f ⟂ᵢ[μ] g) : (∫⁻ ω, (f * g) ω ∂μ) 
= (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ
参数：h_meas_f : Measurable f；h_meas_g : Measurable g；h_indep_fun : f ⟂ᵢ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independen
t_measurableSpace`：lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measu
rableSpace {Mf Mg mΩ : MeasurableSpace Ω} {μ : Measure Ω} (hMf : Mf <= mΩ) (hMg…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `measurable_iff_comap_le`：measurable_iff_comap_le {m₁ : MeasurableSpace α
} {m₂ : MeasurableSpace β} {f : α -> β} : Measurable f ↔ m₂.comap f <= m₁
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If `f` and `g` are independent random variables with values in `ℝ≥0∞`,
then `E[f * g] = E[f] * E[g]`.
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f)
    (h_meas_g : Measurable g) (h_indep_fun : f ⟂ᵢ[μ] g) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
    (Measurable.of_comap_le le_rfl) (Measurable.of_comap_le le_rfl)

/-- If `f` and `g` with values in `ℝ≥0∞` are independent and almost everywhere measurable,
then `E[f * g] = E[f] * E[g]` (slightly generalizing
`lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`). -/
/-
**ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'** 是 Ma
thlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasur
able f μ) (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) : (∫⁻ ω, (f * 
g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ
参数：h_meas_f : AEMeasurable f μ；h_meas_g : AEMeasurable g μ；h_indep_fun : f ⟂ᵢ[μ]
 g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`：
lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (h_meas_f : Measurable f) (
h_meas_g : Measurable g) (h_indep_fun : f ⟂ᵢ[μ] g) : (∫⁻ ω, …
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `ProbabilityTheory.IndepFun.congr`：∀ {Ω : Type u_1} {β : Type u_6} {β' : 
Type u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β}   
{g : Ω → β'} {mβ : Mea…

--- 原说明 ---
If `f` and `g` with values in `ℝ≥0∞` are independent and almost everywhere measu
rable,
then `E[f * g] = E[f] * E[g]` (slightly generalizing
`lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun`).
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) :
    (∫⁻ ω, (f * g) ω ∂μ) = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ := by
  have fg_ae : f * g =ᵐ[μ] h_meas_f.mk _ * h_meas_g.mk _ := h_meas_f.ae_eq_mk.mul h_meas_g.ae_eq_mk
  rw [lintegral_congr_ae h_meas_f.ae_eq_mk, lintegral_congr_ae h_meas_g.ae_eq_mk,
    lintegral_congr_ae fg_ae]
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun h_meas_f.measurable_mk
      h_meas_g.measurable_mk
  exact h_indep_fun.congr h_meas_f.ae_eq_mk h_meas_g.ae_eq_mk
/-
**ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''** 是 M
athlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasu
rable f μ) (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) : ∫⁻ ω, f ω *
 g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ
参数：h_meas_f : AEMeasurable f μ；h_meas_g : AEMeasurable g μ；h_indep_fun : f ⟂ᵢ[μ]
 g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'`
：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable 
f μ) (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) …
-/
theorem lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurable f μ)
    (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) :
    ∫⁻ ω, f ω * g ω ∂μ = (∫⁻ ω, f ω ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' h_meas_f h_meas_g h_indep_fun
/-
**ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：lintegral_prod_eq_prod_lintegral_of_indepFun {ι : Type*} (s : Finset ι) (X
 : ι -> Ω -> Real>=0∞) (hX : iIndepFun X μ) (x_mea : forall i, Measurable (X i))
 : ∫⁻ ω, ∏ i in s, (X i ω) ∂μ = ∏ i in s, ∫⁻ ω, X i ω ∂μ
参数：s : Finset ι；X : ι -> Ω -> Real>=0∞；hX : iIndepFun X μ；x_mea : forall i, Meas
urable (X i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'`
：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' (h_meas_f : AEMeasurable 
f μ) (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g) …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Finset.aemeasurable_prod`：Finset.aemeasurable_prod (s : Finset ι) (hf : 
forall i in s, AEMeasurable (f i) μ) : AEMeasurable (∏ i in s, f i) μ
· 使用定理 `ProbabilityTheory.IndepFun.symm`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β}   {
g : Ω → β'} {x : Meas…
· 使用定理 `ProbabilityTheory.iIndepFun.indepFun_finsetProd_of_notMem`：∀ {Ω : Type u
_1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : 
Type u_10}   {m : MeasurableSpace β} [inst : Co…
-/
theorem lintegral_prod_eq_prod_lintegral_of_indepFun {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ≥0∞) (hX : iIndepFun X μ)
    (x_mea : ∀ i, Measurable (X i)) :
    ∫⁻ ω, ∏ i ∈ s, (X i ω) ∂μ = ∏ i ∈ s, ∫⁻ ω, X i ω ∂μ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, lintegral_const, measure_univ, mul_one]
  | cons j s hj ihs =>
    simp only [← Finset.prod_apply, Finset.prod_cons, ← ihs]
    apply lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'
    · exact (x_mea j).aemeasurable
    · exact s.aemeasurable_prod (fun i _ ↦ (x_mea i).aemeasurable)
    · exact (iIndepFun.indepFun_finsetProd_of_notMem hX x_mea hj).symm

section Integral

variable {𝓧 𝓨 E F G : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- If `X` and `Y` are two independent and integrable random variables, and `B` is a function of
two variables such that `‖B x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ`, then `B X Y` is integrable.

This is useful in particular if `B` is a continuous bilinear map. -/
/-
**ProbabilityTheory.IndepFun.integrable_op** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6} {G : Type u_7}   [inst : TopologicalSpace E] [inst_1
 : ContinuousENorm E] [inst_2 : MeasurableSpace E] [OpensMeasurableSpace E]   [i
nst_4 : TopologicalSpace F] [inst_5 : ContinuousENorm F] [inst_6 : MeasurableSpa
ce F] [OpensMeasurableSpace F]   [inst_8 : TopologicalSpace G] [inst_9 : Continu
ousENorm G] {X : Ω → E} {Y : Ω → F},   ProbabilityTheory.IndepFun X Y μ →     Me
asureTheory.Integrable X μ →       MeasureTheory.Integrable Y μ →         ∀ (B :
 E → F → G),           Continuous (Function.uncurry B) →             ∀ (C : NNRe
al),               (∀ (x : E) (y : F), ‖B x y‖ₑ ≤ ↑C * ‖x‖ₑ * ‖y‖ₑ) → MeasureThe
ory.Integrable (fun ω => B (X ω) (Y ω)) μ
参数：B : E → F → G；Function.uncurry B；C : NNReal；∀ (x : E) (y : F), ‖B x y‖ₑ ≤ ↑C 
* ‖x‖ₑ * ‖y‖ₑ；fun ω => B (X ω) (Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable₂`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ 
: MeasurableSpace α} {μ : M…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_const_mul''`：lintegral_const_mul'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a
 ∂μ
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
`：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurabl
e f μ) (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g)…
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用引理 `measurable_enorm`：measurable_enorm : Measurable (enorm : ε -> Real>=0∞)
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `X` and `Y` are two independent and integrable random variables, and `B` is a
 function of
two variables such that `‖B x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ`, then `B X Y` is integrable
.

This is useful in particular if `B` is a continuous bilinear map.
-/
theorem IndepFun.integrable_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E → F → G) (cB : Continuous B.uncurry) (C : ℝ≥0) (hB : ∀ x y, ‖B x y‖ₑ ≤ C * ‖x‖ₑ * ‖y‖ₑ) :
    Integrable (fun ω ↦ B (X ω) (Y ω)) μ := by
  refine ⟨cB.comp_aestronglyMeasurable₂ hX.1 hY.1, ?_⟩
  unfold HasFiniteIntegral
  calc
  _ ≤ C * ∫⁻ ω, ‖X ω‖ₑ * ‖Y ω‖ₑ ∂μ := by
    rw [← lintegral_const_mul'' _ (by fun_prop)]
    gcongr with ω
    simp [← mul_assoc, hB]
  _ = C * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.1.enorm hY.1.enorm
        (hXY.comp measurable_enorm measurable_enorm)]
  _ < ∞ := mul_lt_top (by finiteness) (mul_lt_top hX.2 hY.2)

/-- A continuous bilinear map applied to two independent and integrable random variables
is integrable. -/
/-
**ProbabilityTheory.IndepFun.integrable_bilin** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6} {G : Type u_7}   {𝕜 : Type u_8} [inst : Nontrivially
NormedField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E]   
[inst_3 : MeasurableSpace E] [OpensMeasurableSpace E] [inst_5 : SeminormedAddCom
mGroup F] [inst_6 : NormedSpace 𝕜 F]   [inst_7 : MeasurableSpace F] [OpensMeasur
ableSpace F] [inst_9 : SeminormedAddCommGroup G] [inst_10 : NormedSpace 𝕜 G]   {
X : Ω → E} {Y : Ω → F},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.I
ntegrable X μ →       MeasureTheory.Integrable Y μ → ∀ (B : E →L[𝕜] F →L[𝕜] G), 
MeasureTheory.Integrable (fun ω => (B (X ω)) (Y ω)) μ
参数：B : E →L[𝕜] F →L[𝕜] G；fun ω => (B (X ω)) (Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ProbabilityTheory.IndepFun.integrable_op`：∀ {Ω : Type u_1} {mΩ : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω} {E : Type u_5} {F : Type u_6} {G : Typ
e u_7}   [inst : TopologicalSp…
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖

--- 原说明 ---
A continuous bilinear map applied to two independent and integrable random varia
bles
is integrable.
-/
theorem IndepFun.integrable_bilin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E →L[𝕜] F →L[𝕜] G) :
    Integrable (fun ω ↦ B (X ω) (Y ω)) μ := by
  refine hXY.integrable_op hX hY (B · ·) (by fun_prop) ‖B‖₊ (fun x y ↦ ?_)
  rw [← toReal_le_toReal (by finiteness) (by finiteness)]
  simp [B.le_opNorm₂]

/-- If `X` and `Y` are two independent random variables, `B X Y` is integrable, `Y` is not
almost-surely `0` and `c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ`, then `X` is integrable.

This is useful for the case where `B` is scalar multiplication, as it will allow to drop
integrability hypotheses. -/
/-
**ProbabilityTheory.IndepFun.integrable_left_of_integrable_op** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6} {G : Type u_7}   [inst : TopologicalSpace E] [inst_1
 : ContinuousENorm E] [inst_2 : MeasurableSpace E] [OpensMeasurableSpace E]   [i
nst_4 : NormedAddGroup F] [inst_5 : MeasurableSpace F] [OpensMeasurableSpace F] 
[inst_7 : TopologicalSpace G]   [inst_8 : ContinuousENorm G] {X : Ω → E} {Y : Ω 
→ F},   ProbabilityTheory.IndepFun X Y μ →     ∀ (B : E → F → G) (c : NNReal),  
     c ≠ 0 →         (∀ (x : E) (y : F), ↑c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ) →         
  MeasureTheory.Integrable (fun ω => B (X ω) (Y ω)) μ →             MeasureTheor
y.AEStronglyMeasurable X μ →               MeasureTheory.AEStronglyMeasurable Y 
μ → ¬Y =ᵐ[μ] 0 → MeasureTheory.Integrable X μ
参数：B : E → F → G；c : NNReal；∀ (x : E) (y : F), ↑c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ；fun ω
 => B (X ω) (Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_enorm`：hasFiniteIntegral_iff_enorm {
f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …
· 使用引理 `measurable_enorm`：measurable_enorm : Measurable (enorm : ε -> Real>=0∞)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
`：lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (h_meas_f : AEMeasurabl
e f μ) (h_meas_g : AEMeasurable g μ) (h_indep_fun : f ⟂ᵢ[μ] g)…
· 使用定理 `MeasureTheory.lintegral_const_mul''`：lintegral_const_mul'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a
 ∂μ
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p

--- 原说明 ---
If `X` and `Y` are two independent random variables, `B X Y` is integrable, `Y` 
is not
almost-surely `0` and `c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ`, then `X` is integrable.

This is useful for the case where `B` is scalar multiplication, as it will allow
 to drop
integrability hypotheses.
-/
theorem IndepFun.integrable_left_of_integrable_op
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [NormedAddGroup F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y)
    (B : E → F → G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ)
    (h'XY : Integrable (fun ω ↦ B (X ω) (Y ω)) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'Y : ¬Y =ᵐ[μ] 0) :
    Integrable X μ := by
  refine ⟨hX, ?_⟩
  have I : (∫⁻ ω, ‖Y ω‖ₑ ∂μ) ≠ 0 := fun H ↦ by
    have I : (fun ω => ‖Y ω‖ₑ : Ω → ℝ≥0∞) =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hY.enorm).1 H
    apply h'Y
    filter_upwards [I] with ω hω
    simpa using hω
  refine hasFiniteIntegral_iff_enorm.mpr <| lt_top_iff_ne_top.2 fun H => ?_
  have J : (‖X ·‖ₑ) ⟂ᵢ[μ] (‖Y ·‖ₑ) := hXY.comp measurable_enorm measurable_enorm
  have : ∞ < ∞ := calc
    ∞ = c * ((∫⁻ ω, ‖X ω‖ₑ ∂μ) * (∫⁻ ω, ‖Y ω‖ₑ ∂μ)) := by
      rw [H, top_mul I, mul_top (by simpa)]
    _ ≤ ∫⁻ ω, ‖B (X ω) (Y ω)‖ₑ ∂μ := by
      rw [← lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hX.enorm hY.enorm J,
        ← lintegral_const_mul'' _ (by fun_prop)]
      gcongr with ω
      simp [hB, ← mul_assoc]
    _ < ∞ := h'XY.2
  contradiction

/-- If `X` and `Y` are two independent random variables, `B X Y` is integrable, `X` is not
almost-surely `0` and `c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ`, then `Y` is integrable.

This is useful for the case where `B` is scalar multiplication, as it will allow to drop
integrability hypotheses. -/
/-
**ProbabilityTheory.IndepFun.integrable_right_of_integrable_op** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6} {G : Type u_7}   [inst : NormedAddGroup E] [inst_1 :
 MeasurableSpace E] [OpensMeasurableSpace E] [inst_3 : TopologicalSpace F]   [in
st_4 : ContinuousENorm F] [inst_5 : MeasurableSpace F] [OpensMeasurableSpace F] 
[inst_7 : TopologicalSpace G]   [inst_8 : ContinuousENorm G] {X : Ω → E} {Y : Ω 
→ F},   ProbabilityTheory.IndepFun X Y μ →     ∀ (B : E → F → G) (c : NNReal),  
     c ≠ 0 →         (∀ (x : E) (y : F), ↑c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ) →         
  MeasureTheory.Integrable (fun ω => B (X ω) (Y ω)) μ →             MeasureTheor
y.AEStronglyMeasurable X μ →               MeasureTheory.AEStronglyMeasurable Y 
μ → ¬X =ᵐ[μ] 0 → MeasureTheory.Integrable Y μ
参数：B : E → F → G；c : NNReal；∀ (x : E) (y : F), ↑c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ；fun ω
 => B (X ω) (Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IndepFun.integrable_left_of_integrable_op`：∀ {Ω : Type
 u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E : Type u_5} {F :
 Type u_6} {G : Type u_7}   [inst : TopologicalSp…
· 使用定理 `ProbabilityTheory.IndepFun.symm`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β}   {
g : Ω → β'} {x : Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If `X` and `Y` are two independent random variables, `B X Y` is integrable, `X` 
is not
almost-surely `0` and `c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ`, then `Y` is integrable.

This is useful for the case where `B` is scalar multiplication, as it will allow
 to drop
integrability hypotheses.
-/
theorem IndepFun.integrable_right_of_integrable_op
    [NormedAddGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace G] [ContinuousENorm G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y)
    (B : E → F → G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ)
    (h'XY : Integrable (fun ω ↦ B (X ω) (Y ω)) μ)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) (h'X : ¬X =ᵐ[μ] 0) :
    Integrable Y μ := by
  refine hXY.symm.integrable_left_of_integrable_op (Function.swap B) c hc (fun y x ↦ ?_)
    h'XY hY hX h'X
  grw [mul_right_comm, hB]

/-- If `X` and `Y` are independent random variables such that `f(X)` and `g(Y)` are integrable
and `B` is a continuous bilinear map, then
`∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ).` -/
/-
**ProbabilityTheory.IndepFun.integral_bilin_comp_comp** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E : Type u_5} {F
 : Type u_6} {G : Type u_7} [inst_1 : MeasurableSpace 𝓧] [inst_2 : MeasurableSpa
ce 𝓨]   [inst_3 : NormedAddCommGroup E] [inst_4 : NormedSpace ℝ E] [inst_5 : Nor
medSpace 𝕜 E] [CompleteSpace E]   [inst_7 : NormedAddCommGroup F] [inst_8 : Norm
edSpace ℝ F] [inst_9 : NormedSpace 𝕜 F] [CompleteSpace F]   [inst_11 : NormedAdd
CommGroup G] [inst_12 : NormedSpace ℝ G] [inst_13 : NormedSpace 𝕜 G] [CompleteSp
ace G] {X : Ω → 𝓧}   {Y : Ω → 𝓨} {f : 𝓧 → E} {g : 𝓨 → F},   ProbabilityTheory.In
depFun X Y μ →     AEMeasurable X μ →       AEMeasurable Y μ →         MeasureTh
eory.Integrable f (MeasureTheory.Measure.map X μ) →           MeasureTheory.Inte
grable g (MeasureTheory.Measure.map Y μ) →             ∀ (B : E →L[𝕜] F →L[𝕜] G)
,               ∫ (ω : Ω), (B (f (X ω))) (g (Y ω)) ∂μ = (B (∫ (ω : Ω), f (X ω) ∂
μ)) (∫ (ω : Ω), g (Y ω) ∂μ)
参数：MeasureTheory.Measure.map X μ；MeasureTheory.Measure.map Y μ；B : E →L[𝕜] F →L[
𝕜] G；ω : Ω；B (f (X ω))；g (Y ω)；B (∫ (ω : Ω), f (X ω) ∂μ)；∫ (ω : Ω), g (Y ω) ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `MeasureTheory.Integrable.isProbabilityMeasure_of_indepFun`：∀ {Ω : Type u
_1} {E : Type u_2} {F : Type u_3} [inst : MeasurableSpace Ω] {μ : MeasureTheory.
Measure Ω}   [inst_1 : NormedAddCommGroup E] [i…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Integrable.comp_aemeasurable`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `ProbabilityTheory.IndepFun.comp₀`：∀ {Ω : Type u_1} {β : Type u_6} {β' : 
Type u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measur
eTheory.Measure Ω} {f …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` and `Y` are independent random variables such that `f(X)` and `g(Y)` are 
integrable
and `B` is a continuous bilinear map, then
`∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ).`
-/
theorem IndepFun.integral_bilin_comp_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → E} {g : 𝓨 → F} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : Integrable f (μ.map X)) (hg : Integrable g (μ.map Y)) (B : E →L[𝕜] F →L[𝕜] G) :
    ∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ) := by
  by_cases h : ∀ᵐ ω ∂μ, f (X ω) = 0
  · have h1 : ∀ᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h] with ω hω
      simp [hω]
    simp [integral_congr_ae h1, integral_congr_ae h]
  borelize E F
  have : IsProbabilityMeasure μ :=
    (hf.comp_aemeasurable hX).isProbabilityMeasure_of_indepFun (f ∘ X) (g ∘ Y) h
      (hXY.comp₀ hX hY hf.1.aemeasurable hg.1.aemeasurable)
  rw [← integral_map (f := fun z ↦ B (f z.1) (g z.2)) (φ := fun ω ↦ (X ω, Y ω)) (by fun_prop),
    hXY.map_prod_eq_prod_map_map hX hY, integral_prod_bilin _ hf hg, integral_map hX hf.1,
    integral_map hY hg.1]
  rw [hXY.map_prod_eq_prod_map_map hX hY]
  exact Continuous.comp_aestronglyMeasurable₂ (g := (B · ·)) (by fun_prop)
    hf.1.comp_fst hg.1.comp_snd

/-- If `X` and `Y` are random variables and `B` is a continuous bilinear map
such that `∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖`, then
`∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ).`

The assumption on `B` allows to drop the integrability condition in
`IndepFun.integral_bilin_comp_comp`, which is useful for the versions where `B` is the scalar
multiplication or the multiplication. -/
/-
**ProbabilityTheory.IndepFun.integral_bilin_comp_comp'** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E : Type u_5} {F
 : Type u_6} {G : Type u_7} [inst_1 : MeasurableSpace 𝓧] [inst_2 : MeasurableSpa
ce 𝓨]   [inst_3 : NormedAddCommGroup E] [inst_4 : NormedSpace ℝ E] [inst_5 : Nor
medSpace 𝕜 E] [CompleteSpace E]   [inst_7 : NormedAddCommGroup F] [inst_8 : Norm
edSpace ℝ F] [inst_9 : NormedSpace 𝕜 F] [CompleteSpace F]   [inst_11 : NormedAdd
CommGroup G] [inst_12 : NormedSpace ℝ G] [inst_13 : NormedSpace 𝕜 G] [CompleteSp
ace G] {X : Ω → 𝓧}   {Y : Ω → 𝓨} {f : 𝓧 → E} {g : 𝓨 → F},   ProbabilityTheory.In
depFun X Y μ →     AEMeasurable X μ →       AEMeasurable Y μ →         MeasureTh
eory.AEStronglyMeasurable f (MeasureTheory.Measure.map X μ) →           MeasureT
heory.AEStronglyMeasurable g (MeasureTheory.Measure.map Y μ) →             ∀ (B 
: E →L[𝕜] F →L[𝕜] G) (c : NNReal),               c ≠ 0 →                 (∀ (x :
 E) (y : F), ↑c * ‖x‖ * ‖y‖ ≤ ‖(B x) y‖) →                   ∫ (ω : Ω), (B (f (X
 ω))) (g (Y ω)) ∂μ = (B (∫ (ω : Ω), f (X ω) ∂μ)) (∫ (ω : Ω), g (Y ω) ∂μ)
参数：MeasureTheory.Measure.map X μ；MeasureTheory.Measure.map Y μ；B : E →L[𝕜] F →L[
𝕜] G；c : NNReal；∀ (x : E) (y : F), ↑c * ‖x‖ * ‖y‖ ≤ ‖(B x) y‖；ω : Ω；B (f (X ω))；
g (Y ω)；B (∫ (ω : Ω), f (X ω) ∂μ)；∫ (ω : Ω), g (Y ω) ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ProbabilityTheory.IndepFun.comp₀`：∀ {Ω : Type u_1} {β : Type u_6} {β' : 
Type u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measur
eTheory.Measure Ω} {f …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_aemeasurable`：comp_aemeasurable 
{γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Me
asure γ} (hg : AEStronglyMeasurable g (Mea…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` and `Y` are random variables and `B` is a continuous bilinear map
such that `∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖`, then
`∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ).`

The assumption on `B` allows to drop the integrability condition in
`IndepFun.integral_bilin_comp_comp`, which is useful for the versions where `B` 
is the scalar
multiplication or the multiplication.
-/
theorem IndepFun.integral_bilin_comp_comp'
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [CompleteSpace G]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → E} {g : 𝓨 → F} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y))
    (B : E →L[𝕜] F →L[𝕜] G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖) :
    ∫ ω, B (f (X ω)) (g (Y ω)) ∂μ = B (∫ ω, f (X ω) ∂μ) (∫ ω, g (Y ω) ∂μ) := by
  borelize E F
  have hfXgY := (hXY.comp₀ hX hY hf.aemeasurable hg.aemeasurable)
  have hfX := (hf.comp_aemeasurable hX)
  have hgY := (hg.comp_aemeasurable hY)
  by_cases h'X : ∀ᵐ ω ∂μ, f (X ω) = 0
  · have h' : ∀ᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'X] with ω hω
      simp [hω]
    simp [integral_congr_ae h'X, integral_congr_ae h']
  by_cases h'Y : ∀ᵐ ω ∂μ, g (Y ω) = 0
  · have h' : ∀ᵐ ω ∂μ, B (f (X ω)) (g (Y ω)) = 0 := by
      filter_upwards [h'Y] with ω hω
      simp [hω]
    simp [integral_congr_ae h'Y, integral_congr_ae h']
  have hB x y : c * ‖x‖ₑ * ‖y‖ₑ ≤ ‖B x y‖ₑ := by
    rw [← toReal_le_toReal]
    · simpa using hB x y
    all_goals finiteness
  by_cases h : Integrable (fun ω ↦ B (f (X ω)) (g (Y ω))) μ
  · have h1 : Integrable f (μ.map X) := (integrable_map_measure hf hX).2 <|
      hfXgY.integrable_left_of_integrable_op (B · ·) c hc hB h hfX hgY h'Y
    have h2 : Integrable g (μ.map Y) := (integrable_map_measure hg hY).2 <|
      hfXgY.integrable_right_of_integrable_op (B · ·) c hc hB h hfX hgY h'X
    exact hXY.integral_bilin_comp_comp hX hY h1 h2 B
  · rw [integral_undef h]
    obtain h | h : ¬(Integrable (fun ω ↦ f (X ω)) μ) ∨ ¬(Integrable (fun ω ↦ g (Y ω)) μ) :=
      not_and_or.1 fun ⟨HX, HY⟩ ↦ h (hfXgY.integrable_bilin HX HY B)
    all_goals simp [integral_undef h]

/-- If `X` and `Y` are independent and integrable random variables and `B`
is a continuous bilinear map, then `∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y].` -/
/-
**ProbabilityTheory.IndepFun.integral_bilin** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6} {G : Type u_7}   [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℝ E] [CompleteSpace E] [inst_3 : MeasurableSpace E] [BorelSpace
 E]   [inst_5 : NormedAddCommGroup F] [inst_6 : NormedSpace ℝ F] [CompleteSpace 
F] [inst_8 : MeasurableSpace F]   [BorelSpace F] [inst_10 : NormedAddCommGroup G
] [inst_11 : NormedSpace ℝ G] [CompleteSpace G] {X : Ω → E} {Y : Ω → F},   Proba
bilityTheory.IndepFun X Y μ →     MeasureTheory.Integrable X μ →       MeasureTh
eory.Integrable Y μ →         ∀ (B : E →L[ℝ] F →L[ℝ] G), ∫ (ω : Ω), (B (X ω)) (Y
 ω) ∂μ = (B (∫ (x : Ω), X x ∂μ)) (∫ (x : Ω), Y x ∂μ)
参数：B : E →L[ℝ] F →L[ℝ] G；ω : Ω；B (X ω)；Y ω；B (∫ (x : Ω), X x ∂μ)；∫ (x : Ω), Y x 
∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ProbabilityTheory.IndepFun.integral_bilin_comp_comp`：∀ {Ω : Type u_1} {𝕜
 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measu
re Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E …
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用引理 `MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_id_map`：aestrong
lyMeasurable_id_map {mβ : MeasurableSpace β} [TopologicalSpace.PseudoMetrizableS
pace β] [BorelSpace β] {f : α -> β} (hf : AEStrongly…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…

--- 原说明 ---
If `X` and `Y` are independent and integrable random variables and `B`
is a continuous bilinear map, then `∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y].`
-/
theorem IndepFun.integral_bilin
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (B : E →L[ℝ] F →L[ℝ] G) :
    ∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y] :=
  hXY.integral_bilin_comp_comp hX.aemeasurable hY.aemeasurable
    ((integrable_map_measure hX.aestronglyMeasurable.aestronglyMeasurable_id_map hX.aemeasurable).2
      hX)
    ((integrable_map_measure hY.aestronglyMeasurable.aestronglyMeasurable_id_map hY.aemeasurable).2
      hY) B

/-- If `X` and `Y` are random variables and `B` is a continuous bilinear map
such that `∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖`, then `∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y].`

The assumption on `B` allows to drop the integrability condition in
`IndepFun.integral_bilin'`, which is useful for the versions where `B` is the scalar
multiplication or the multiplication. -/
/-
**ProbabilityTheory.IndepFun.integral_bilin'** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6} {G : Type u_7}   [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℝ E] [CompleteSpace E] [inst_3 : MeasurableSpace E] [BorelSpace
 E]   [inst_5 : NormedAddCommGroup F] [inst_6 : NormedSpace ℝ F] [CompleteSpace 
F] [inst_8 : MeasurableSpace F]   [BorelSpace F] [inst_10 : NormedAddCommGroup G
] [inst_11 : NormedSpace ℝ G] [CompleteSpace G] {X : Ω → E} {Y : Ω → F},   Proba
bilityTheory.IndepFun X Y μ →     MeasureTheory.AEStronglyMeasurable X μ →      
 MeasureTheory.AEStronglyMeasurable Y μ →         ∀ (B : E →L[ℝ] F →L[ℝ] G) (c :
 NNReal),           c ≠ 0 →             (∀ (x : E) (y : F), ↑c * ‖x‖ * ‖y‖ ≤ ‖(B
 x) y‖) →               ∫ (ω : Ω), (B (X ω)) (Y ω) ∂μ = (B (∫ (x : Ω), X x ∂μ)) 
(∫ (x : Ω), Y x ∂μ)
参数：B : E →L[ℝ] F →L[ℝ] G；c : NNReal；∀ (x : E) (y : F), ↑c * ‖x‖ * ‖y‖ ≤ ‖(B x) y
‖；ω : Ω；B (X ω)；Y ω；B (∫ (x : Ω), X x ∂μ)；∫ (x : Ω), Y x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ProbabilityTheory.IndepFun.integral_bilin_comp_comp'`：∀ {Ω : Type u_1} {
𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Meas
ure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_id_map`：aestrong
lyMeasurable_id_map {mβ : MeasurableSpace β} [TopologicalSpace.PseudoMetrizableS
pace β] [BorelSpace β] {f : α -> β} (hf : AEStrongly…

--- 原说明 ---
If `X` and `Y` are random variables and `B` is a continuous bilinear map
such that `∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖`, then `∫ ω, B (X ω) (Y ω) ∂μ = B μ[X]
 μ[Y].`

The assumption on `B` allows to drop the integrability condition in
`IndepFun.integral_bilin'`, which is useful for the versions where `B` is the sc
alar
multiplication or the multiplication.
-/
theorem IndepFun.integral_bilin'
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ)
    (B : E →L[ℝ] F →L[ℝ] G) (c : ℝ≥0) (hc : c ≠ 0) (hB : ∀ x y, c * ‖x‖ * ‖y‖ ≤ ‖B x y‖) :
    ∫ ω, B (X ω) (Y ω) ∂μ = B μ[X] μ[Y] :=
  hXY.integral_bilin_comp_comp' hX.aemeasurable hY.aemeasurable
    hX.aestronglyMeasurable_id_map hY.aestronglyMeasurable_id_map B c hc hB

/-- The scalar product of two independent and integrable random variables is integrable. -/
/-
**ProbabilityTheory.IndepFun.integrable_smul** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} {F : Type u_6}   [inst : TopologicalSpace E] [inst_1 : ContinuousEN
orm E] [inst_2 : MeasurableSpace E] [OpensMeasurableSpace E]   [inst_4 : Topolog
icalSpace F] [inst_5 : ContinuousENorm F] [inst_6 : MeasurableSpace F] [OpensMea
surableSpace F]   [inst_8 : SMul E F] [ContinuousSMul E F] [ENormSMulClass E F] 
{X : Ω → E} {Y : Ω → F},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.
Integrable X μ → MeasureTheory.Integrable Y μ → MeasureTheory.Integrable (fun ω 
=> X ω • Y ω) μ
参数：fun ω => X ω • Y ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integrable_op`：∀ {Ω : Type u_1} {mΩ : Measura
bleSpace Ω} {μ : MeasureTheory.Measure Ω} {E : Type u_5} {F : Type u_6} {G : Typ
e u_7}   [inst : TopologicalSp…
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The scalar product of two independent and integrable random variables is integra
ble.
-/
theorem IndepFun.integrable_smul
    [TopologicalSpace E] [ContinuousENorm E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [ContinuousENorm F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SMul E F] [ContinuousSMul E F] [ENormSMulClass E F]
    {X : Ω → E} {Y : Ω → F} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (fun ω ↦ (X ω) • (Y ω)) μ :=
  hXY.integrable_op hX hY (· • ·) (by fun_prop) 1 (by simp [enorm_smul])

/-- The product of two independent and integrable random variables is integrable. -/
/-
**ProbabilityTheory.IndepFun.integrable_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {E
 : Type u_5} [inst : TopologicalSpace E]   [inst_1 : ContinuousENorm E] [inst_2 
: Mul E] [ContinuousMul E] [ENormSMulClass E E] [inst_5 : MeasurableSpace E]   [
OpensMeasurableSpace E] {X Y : Ω → E},   ProbabilityTheory.IndepFun X Y μ →     
MeasureTheory.Integrable X μ → MeasureTheory.Integrable Y μ → MeasureTheory.Inte
grable (X * Y) μ
参数：X * Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integrable_smul`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {μ : MeasureTheory.Measure Ω} {E : Type u_5} {F : Type u_6}   [ins
t : TopologicalSpace E] [inst_1 …

--- 原说明 ---
The product of two independent and integrable random variables is integrable.
-/
theorem IndepFun.integrable_mul
    [TopologicalSpace E] [ContinuousENorm E] [Mul E] [ContinuousMul E] [ENormSMulClass E E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {X Y : Ω → E} (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (X * Y) μ := hXY.integrable_smul hX hY

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_left_of_integrable_mul :=
  IndepFun.integrable_left_of_integrable_op

@[deprecated (since := "2026-04-30")] alias IndepFun.integrable_right_of_integrable_mul :=
  IndepFun.integrable_right_of_integrable_op
/-
**ProbabilityTheory.IndepFun.integral_fun_comp_smul_comp** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E : Type u_5} [i
nst_1 : MeasurableSpace 𝓧] [inst_2 : MeasurableSpace 𝓨]   [inst_3 : NormedAddCom
mGroup E] [inst_4 : NormedSpace ℝ E] [inst_5 : NormedSpace 𝕜 E] {X : Ω → 𝓧} {Y :
 Ω → 𝓨}   {f : 𝓧 → 𝕜} {g : 𝓨 → E},   ProbabilityTheory.IndepFun X Y μ →     AEMe
asurable X μ →       AEMeasurable Y μ →         MeasureTheory.AEStronglyMeasurab
le f (MeasureTheory.Measure.map X μ) →           MeasureTheory.AEStronglyMeasura
ble g (MeasureTheory.Measure.map Y μ) →             ∫ (ω : Ω), f (X ω) • g (Y ω)
 ∂μ = (∫ (ω : Ω), f (X ω) ∂μ) • ∫ (ω : Ω), g (Y ω) ∂μ
参数：MeasureTheory.Measure.map X μ；MeasureTheory.Measure.map Y μ；ω : Ω；X ω；Y ω；∫ (
ω : Ω), f (X ω) ∂μ；ω : Ω；Y ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_bilin_comp_comp'`：∀ {Ω : Type u_1} {
𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Meas
ure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IndepFun.integral_fun_comp_smul_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) • g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) • (∫ ω, g (Y ω) ∂μ) := by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin_comp_comp' hX hY hf hg (.lsmul ℝ 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]
/-
**ProbabilityTheory.IndepFun.integral_fun_comp_mul_comp** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} [inst_1 : Measura
bleSpace 𝓧] [inst_2 : MeasurableSpace 𝓨] {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜}   {
g : 𝓨 → 𝕜},   ProbabilityTheory.IndepFun X Y μ →     AEMeasurable X μ →       AE
Measurable Y μ →         MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Mea
sure.map X μ) →           MeasureTheory.AEStronglyMeasurable g (MeasureTheory.Me
asure.map Y μ) →             ∫ (ω : Ω), f (X ω) * g (Y ω) ∂μ = (∫ (ω : Ω), f (X 
ω) ∂μ) * ∫ (ω : Ω), g (Y ω) ∂μ
参数：MeasureTheory.Measure.map X μ；MeasureTheory.Measure.map Y μ；ω : Ω；X ω；Y ω；∫ (
ω : Ω), f (X ω) ∂μ；ω : Ω；Y ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_fun_comp_smul_comp`：∀ {Ω : Type u_1}
 {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Me
asure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E …
-/
lemma IndepFun.integral_fun_comp_mul_comp
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    ∫ ω, f (X ω) * g (Y ω) ∂μ = (∫ ω, f (X ω) ∂μ) * (∫ ω, g (Y ω) ∂μ) :=
  hXY.integral_fun_comp_smul_comp hX hY hf hg
/-
**ProbabilityTheory.IndepFun.integral_comp_smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E : Type u_5} [i
nst_1 : MeasurableSpace 𝓧] [inst_2 : MeasurableSpace 𝓨]   [inst_3 : NormedAddCom
mGroup E] [inst_4 : NormedSpace ℝ E] [inst_5 : NormedSpace 𝕜 E] {X : Ω → 𝓧} {Y :
 Ω → 𝓨}   {f : 𝓧 → 𝕜} {g : 𝓨 → E},   ProbabilityTheory.IndepFun X Y μ →     AEMe
asurable X μ →       AEMeasurable Y μ →         MeasureTheory.AEStronglyMeasurab
le f (MeasureTheory.Measure.map X μ) →           MeasureTheory.AEStronglyMeasura
ble g (MeasureTheory.Measure.map Y μ) →             ∫ (x : Ω), (f ∘ X • g ∘ Y) x
 ∂μ = (∫ (x : Ω), (f ∘ X) x ∂μ) • ∫ (x : Ω), (g ∘ Y) x ∂μ
参数：MeasureTheory.Measure.map X μ；MeasureTheory.Measure.map Y μ；x : Ω；f ∘ X • g ∘
 Y；∫ (x : Ω), (f ∘ X) x ∂μ；x : Ω；g ∘ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_fun_comp_smul_comp`：∀ {Ω : Type u_1}
 {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Me
asure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E …
-/
lemma IndepFun.integral_comp_smul_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → E}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) • (g ∘ Y)] = μ[f ∘ X] • μ[g ∘ Y] :=
  hXY.integral_fun_comp_smul_comp hX hY hf hg
/-
**ProbabilityTheory.IndepFun.integral_comp_mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} [inst_1 : Measura
bleSpace 𝓧] [inst_2 : MeasurableSpace 𝓨] {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜}   {
g : 𝓨 → 𝕜},   ProbabilityTheory.IndepFun X Y μ →     AEMeasurable X μ →       AE
Measurable Y μ →         MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Mea
sure.map X μ) →           MeasureTheory.AEStronglyMeasurable g (MeasureTheory.Me
asure.map Y μ) →             ∫ (x : Ω), (f ∘ X * g ∘ Y) x ∂μ = (∫ (x : Ω), (f ∘ 
X) x ∂μ) * ∫ (x : Ω), (g ∘ Y) x ∂μ
参数：MeasureTheory.Measure.map X μ；MeasureTheory.Measure.map Y μ；x : Ω；f ∘ X * g ∘
 Y；∫ (x : Ω), (f ∘ X) x ∂μ；x : Ω；g ∘ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_fun_comp_mul_comp`：∀ {Ω : Type u_1} 
{𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Mea
sure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} [in…
-/
lemma IndepFun.integral_comp_mul_comp
    {X : Ω → 𝓧} {Y : Ω → 𝓨} {f : 𝓧 → 𝕜} {g : 𝓨 → 𝕜}
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map X)) (hg : AEStronglyMeasurable g (μ.map Y)) :
    μ[(f ∘ X) * (g ∘ Y)] = μ[f ∘ X] * μ[g ∘ Y] :=
  hXY.integral_fun_comp_mul_comp hX hY hf hg
/-
**ProbabilityTheory.IndepFun.integral_smul_eq_smul_integral** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {E : Type u_5}   [inst_1 : NormedAddCommGroup E] 
[inst_2 : NormedSpace ℝ E] [inst_3 : NormedSpace 𝕜 E] [inst_4 : MeasurableSpace 
E]   [BorelSpace E] {X : Ω → 𝕜} {Y : Ω → E},   ProbabilityTheory.IndepFun X Y μ 
→     MeasureTheory.AEStronglyMeasurable X μ →       MeasureTheory.AEStronglyMea
surable Y μ → ∫ (x : Ω), (X • Y) x ∂μ = (∫ (x : Ω), X x ∂μ) • ∫ (x : Ω), Y x ∂μ
参数：x : Ω；X • Y；∫ (x : Ω), X x ∂μ；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_bilin'`：∀ {Ω : Type u_1} {mΩ : Measu
rableSpace Ω} {μ : MeasureTheory.Measure Ω} {E : Type u_5} {F : Type u_6} {G : T
ype u_7}   [inst : NormedAddComm…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IndepFun.integral_smul_eq_smul_integral
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {X : Ω → 𝕜} {Y : Ω → E} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X • Y] = μ[X] • μ[Y] := by
  by_cases hE : CompleteSpace E
  · exact hXY.integral_bilin' hX hY (.lsmul ℝ 𝕜) 1 (by simp) (by simp [norm_smul])
  · simp [integral, hE]
/-
**ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {X Y : Ω → 𝕜},   ProbabilityTheory.IndepFun X Y μ
 →     MeasureTheory.AEStronglyMeasurable X μ →       MeasureTheory.AEStronglyMe
asurable Y μ → ∫ (x : Ω), (X * Y) x ∂μ = (∫ (x : Ω), X x ∂μ) * ∫ (x : Ω), Y x ∂μ
参数：x : Ω；X * Y；∫ (x : Ω), X x ∂μ；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_smul_eq_smul_integral`：∀ {Ω : Type u
_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {E : Type u_5}   [inst_1 : NormedAd…
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
-/
lemma IndepFun.integral_mul_eq_mul_integral
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] :=
  hXY.integral_smul_eq_smul_integral hX hY
/-
**ProbabilityTheory.IndepFun.integral_fun_smul_eq_smul_integral** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {E : Type u_5}   [inst_1 : NormedAddCommGroup E] 
[inst_2 : NormedSpace ℝ E] [inst_3 : NormedSpace 𝕜 E] [inst_4 : MeasurableSpace 
E]   [BorelSpace E] {X : Ω → 𝕜} {Y : Ω → E},   ProbabilityTheory.IndepFun X Y μ 
→     MeasureTheory.AEStronglyMeasurable X μ →       MeasureTheory.AEStronglyMea
surable Y μ → ∫ (ω : Ω), X ω • Y ω ∂μ = (∫ (ω : Ω), X ω ∂μ) • ∫ (ω : Ω), Y ω ∂μ
参数：ω : Ω；∫ (ω : Ω), X ω ∂μ；ω : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_smul_eq_smul_integral`：∀ {Ω : Type u
_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {E : Type u_5}   [inst_1 : NormedAd…
-/
lemma IndepFun.integral_fun_smul_eq_smul_integral
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {X : Ω → 𝕜} {Y : Ω → E} (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω • Y ω ∂μ = (∫ ω, X ω ∂μ) • ∫ ω, Y ω ∂μ :=
  hXY.integral_smul_eq_smul_integral hX hY
/-
**ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral** 是 Mathlib 中的一个定理
，位于命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {X Y : Ω → 𝕜},   ProbabilityTheory.IndepFun X Y μ
 →     MeasureTheory.AEStronglyMeasurable X μ →       MeasureTheory.AEStronglyMe
asurable Y μ → ∫ (ω : Ω), X ω * Y ω ∂μ = (∫ (x : Ω), X x ∂μ) * ∫ (x : Ω), Y x ∂μ
参数：ω : Ω；∫ (x : Ω), X x ∂μ；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_fun_smul_eq_smul_integral`：∀ {Ω : Ty
pe u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTh
eory.Measure Ω} {E : Type u_5}   [inst_1 : NormedAd…
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
-/
lemma IndepFun.integral_fun_mul_eq_mul_integral
    (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = μ[X] * μ[Y] :=
  hXY.integral_fun_smul_eq_smul_integral hX hY

end Integral

/-- Independence of functions `f` and `g` into arbitrary types is characterized by the relation
  `E[(φ ∘ f) * (ψ ∘ g)] = E[φ ∘ f] * E[ψ ∘ g]` for all measurable `φ` and `ψ` with values in `ℝ`
  satisfying appropriate integrability conditions. -/
/-
**ProbabilityTheory.indepFun_iff_integral_comp_mul** 是 Mathlib 中的一个定理，位于命名空间 `Pr
obabilityTheory`。
形式化陈述：indepFun_iff_integral_comp_mul [IsFiniteMeasure μ] {β β' : Type*} {mβ : Me
asurableSpace β} {mβ' : MeasurableSpace β'} {f : Ω -> β} {g : Ω -> β'} {hfm : Me
asurable f} {hgm : Measurable g} : f ⟂ᵢ[μ] g ↔ forall {φ : β -> Real} {ψ : β' ->
 Real}, Measurable φ -> Measurable ψ -> Integrable (φ ∘ f) μ -> Integrable (ψ ∘ 
g) μ -> integral μ (φ ∘ f * ψ ∘ g) = integral μ (φ ∘ f) * integral μ (ψ ∘ g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.integral_comp_mul_comp`：∀ {Ω : Type u_1} {𝕜 :
 Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure
 Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} [in…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.IndepFun_iff`：IndepFun_iff {β γ} [mβ : MeasurableSpace
 β] [mγ : MeasurableSpace γ] (f : Ω -> β) (g : Ω -> γ) (μ : Measure Ω) : f ⟂ᵢ[μ]
 g ↔ forall t1 t2, M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `MeasureTheory.integral_indicator_one`：integral_indicator_one ⦃s : Set X⦄
 (hs : MeasurableSet s) : ∫ x, s.indicator 1 x ∂μ = μ.real s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `Set.inter_indicator_one`：inter_indicator_one : (s inter t).indicator (1 
: ι -> M₀) = s.indicator 1 * t.indicator 1
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)

--- 原说明 ---
Independence of functions `f` and `g` into arbitrary types is characterized by t
he relation
  `E[(φ ∘ f) * (ψ ∘ g)] = E[φ ∘ f] * E[ψ ∘ g]` for all measurable `φ` and `ψ` wi
th values in `ℝ`
  satisfying appropriate integrability conditions.
-/
theorem indepFun_iff_integral_comp_mul [IsFiniteMeasure μ] {β β' : Type*} {mβ : MeasurableSpace β}
    {mβ' : MeasurableSpace β'} {f : Ω → β} {g : Ω → β'} {hfm : Measurable f} {hgm : Measurable g} :
    f ⟂ᵢ[μ] g ↔ ∀ {φ : β → ℝ} {ψ : β' → ℝ}, Measurable φ → Measurable ψ →
      Integrable (φ ∘ f) μ → Integrable (ψ ∘ g) μ →
        integral μ (φ ∘ f * ψ ∘ g) = integral μ (φ ∘ f) * integral μ (ψ ∘ g) := by
  refine ⟨fun hfg _ _ hφ hψ _ _ => hfg.integral_comp_mul_comp
      hfm.aemeasurable hgm.aemeasurable hφ.aestronglyMeasurable hψ.aestronglyMeasurable, ?_⟩
  rw [IndepFun_iff]
  rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  specialize
    h (measurable_one.indicator hA) (measurable_one.indicator hB)
      ((integrable_const 1).indicator (hfm.comp measurable_id hA))
      ((integrable_const 1).indicator (hgm.comp measurable_id hB))
  rwa [← toReal_eq_toReal_iff' (measure_ne_top μ _), toReal_mul, ← measureReal_def,
    ← measureReal_def, ← measureReal_def, ← integral_indicator_one ((hfm hA).inter (hgm hB)),
    ← integral_indicator_one (hfm hA), ← integral_indicator_one (hgm hB), Set.inter_indicator_one]
  exact mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)

variable {ι : Type*} [Fintype ι] {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)}
    {X : (i : ι) → Ω → 𝓧 i} {f : (i : ι) → 𝓧 i → 𝕜}
/-
**ProbabilityTheory.iIndepFun.integral_fun_prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {ι : Type u_3}   [inst_1 : Fintype ι] {𝓧 : ι → Ty
pe u_4} {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {X : (i : ι) → Ω → 𝓧 i}   {f : (i
 : ι) → 𝓧 i → 𝕜},   ProbabilityTheory.iIndepFun X μ →     (∀ (i : ι), AEMeasurab
le (X i) μ) →       (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) (Measur
eTheory.Measure.map (X i) μ)) →         ∫ (ω : Ω), ∏ i, f i (X i ω) ∂μ = ∏ i, ∫ 
(ω : Ω), f i (X i ω) ∂μ
参数：i : ι；𝓧 i；i : ι；i : ι；∀ (i : ι), AEMeasurable (X i) μ；∀ (i : ι), MeasureTheor
y.AEStronglyMeasurable (f i) (MeasureTheory.Measure.map (X i) μ)；ω : Ω；X i ω；ω :
 Ω；X i ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `aemeasurable_pi_lambda`：aemeasurable_pi_lambda (f : α -> Π a, X a) (hf :
 forall a, AEMeasurable (fun c => f c a) μ) : AEMeasurable f μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ProbabilityTheory.iIndepFun.map_fun_eq_pi_map`：∀ {Ω : Type u_1} {ι : Typ
e u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} [inst : Fintype ι
]   {β : ι → Type u_11} {m : (i : ι…
· 使用定理 `Finset.aestronglyMeasurable_fun_prod`：∀ {α : Type u_1} {m₀ : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {M : Type u_5} [inst : CommMonoid M]   [in
st_1 : TopologicalSpace M]…
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_eval`：quasiMeasurePreservin
g_eval (i : ι) : QuasiMeasurePreserving (Function.eval i) (Measure.pi μ) (μ i)
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.integral_fintype_prod_eq_prod`：integral_fintype_prod_eq_pr
od {E : ι -> Type*} (f : (i : ι) -> E i -> 𝕜) {mE : forall i, MeasurableSpace (E
 i)} {μ : (i : ι) -> Measure (E i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma iIndepFun.integral_fun_prod_comp (hX : iIndepFun X μ)
    (mX : ∀ i, AEMeasurable (X i) μ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ.map (X i))) :
    ∫ ω, ∏ i, f i (X i ω) ∂μ = ∏ i, ∫ ω, f i (X i ω) ∂μ := by
  have := hX.isProbabilityMeasure
  change ∫ ω, (fun x ↦ ∏ i, f i (x i)) (X · ω) ∂μ = _
  rw [← integral_map (f := fun x ↦ ∏ i, f i (x i)) (φ := fun ω ↦ (X · ω)),
    hX.map_fun_eq_pi_map mX, integral_fintype_prod_eq_prod]
  · congr with i
    rw [integral_map (mX i) (hf i)]
  · fun_prop
  rw [hX.map_fun_eq_pi_map mX]
  exact Finset.aestronglyMeasurable_fun_prod Finset.univ fun i _ ↦
    (hf i).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
/-
**ProbabilityTheory.iIndepFun.integral_prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {ι : Type u_3}   [inst_1 : Fintype ι] {𝓧 : ι → Ty
pe u_4} {m𝓧 : (i : ι) → MeasurableSpace (𝓧 i)} {X : (i : ι) → Ω → 𝓧 i}   {f : (i
 : ι) → 𝓧 i → 𝕜},   ProbabilityTheory.iIndepFun X μ →     (∀ (i : ι), AEMeasurab
le (X i) μ) →       (∀ (i : ι), MeasureTheory.AEStronglyMeasurable (f i) (Measur
eTheory.Measure.map (X i) μ)) →         ∫ (x : Ω), (∏ i, f i ∘ X i) x ∂μ = ∏ i, 
∫ (x : Ω), (f i ∘ X i) x ∂μ
参数：i : ι；𝓧 i；i : ι；i : ι；∀ (i : ι), AEMeasurable (X i) μ；∀ (i : ι), MeasureTheor
y.AEStronglyMeasurable (f i) (MeasureTheory.Measure.map (X i) μ)；x : Ω；∏ i, f i 
∘ X i；x : Ω；f i ∘ X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.iIndepFun.integral_fun_prod_comp`：∀ {Ω : Type u_1} {𝕜 
: Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω} {ι : Type u_3}   [inst_1 : Fintype …
-/
lemma iIndepFun.integral_prod_comp (hX : iIndepFun X μ)
    (mX : ∀ i, AEMeasurable (X i) μ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ.map (X i))) :
    μ[∏ i, (f i) ∘ (X i)] = ∏ i, μ[(f i) ∘ (X i)] := by
  convert! hX.integral_fun_prod_comp mX hf
  simp

variable {X : (i : ι) → Ω → 𝕜}
/-
**ProbabilityTheory.iIndepFun.integral_prod_eq_prod_integral** 是 Mathlib 中的一个定理，
位于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {ι : Type u_3}   [inst_1 : Fintype ι] {X : ι → Ω 
→ 𝕜},   ProbabilityTheory.iIndepFun X μ →     (∀ (i : ι), MeasureTheory.AEStrong
lyMeasurable (X i) μ) → ∫ (x : Ω), (∏ i, X i) x ∂μ = ∏ i, ∫ (x : Ω), X i x ∂μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (X i) μ；x : Ω；∏ i, X i；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
· 使用定理 `ProbabilityTheory.iIndepFun.integral_prod_comp`：∀ {Ω : Type u_1} {𝕜 : Ty
pe u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
 {ι : Type u_3}   [inst_1 : Fintype …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
lemma iIndepFun.integral_prod_eq_prod_integral
    (hX : iIndepFun X μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ) :
    μ[∏ i, X i] = ∏ i, μ[X i] :=
  hX.integral_prod_comp (fun i ↦ (mX i).aemeasurable) (fun _ ↦ aestronglyMeasurable_id)
/-
**ProbabilityTheory.iIndepFun.integral_fun_prod_eq_prod_integral** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω}
 {μ : MeasureTheory.Measure Ω} {ι : Type u_3}   [inst_1 : Fintype ι] {X : ι → Ω 
→ 𝕜},   ProbabilityTheory.iIndepFun X μ →     (∀ (i : ι), MeasureTheory.AEStrong
lyMeasurable (X i) μ) → ∫ (ω : Ω), ∏ i, X i ω ∂μ = ∏ i, ∫ (x : Ω), X i x ∂μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable (X i) μ；ω : Ω；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
· 使用定理 `ProbabilityTheory.iIndepFun.integral_fun_prod_comp`：∀ {Ω : Type u_1} {𝕜 
: Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measur
e Ω} {ι : Type u_3}   [inst_1 : Fintype …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
lemma iIndepFun.integral_fun_prod_eq_prod_integral
    (hX : iIndepFun X μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ) :
    ∫ ω, ∏ i, X i ω ∂μ = ∏ i, μ[X i] :=
  hX.integral_fun_prod_comp (fun i ↦ (mX i).aemeasurable) (fun _ ↦ aestronglyMeasurable_id)

section SetIntegral

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [m𝓧 : MeasurableSpace 𝓧]
  {X : Ω → 𝓧} {A : Set Ω}

/-- If a random variable `X` is independent of a sigma-algebra `m` and `A` is a set in `m`
then `∫ ω in A, f (X ω) ∂P = P.real A • ∫ ω, f (X ω) ∂P` for a measurable function `f : 𝓧 → E`. -/
/-
**ProbabilityTheory.Indep.setIntegral_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.Indep`。
形式化陈述：∀ {Ω : Type u_5} {𝓧 : Type u_6} {m mΩ : MeasurableSpace Ω} {P : MeasureThe
ory.Measure Ω} [m𝓧 : MeasurableSpace 𝓧]   {X : Ω → 𝓧} {A : Set Ω} {E : Type u_7}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E],   m ≤ mΩ →     ∀ {f :
 𝓧 → E},       ProbabilityTheory.Indep m (MeasurableSpace.comap X m𝓧) P →       
  AEMeasurable X P →           MeasurableSet A →             MeasureTheory.AEStr
onglyMeasurable f (MeasureTheory.Measure.map X P) →               ∫ (ω : Ω) in A
, f (X ω) ∂P = P.real A • ∫ (ω : Ω), f (X ω) ∂P
参数：MeasurableSpace.comap X m𝓧；MeasureTheory.Measure.map X P；ω : Ω；X ω；ω : Ω；X ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ProbabilityTheory.IndepFun.integral_fun_comp_smul_comp`：∀ {Ω : Type u_1}
 {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Me
asure Ω} {𝓧 : Type u_3}   {𝓨 : Type u_4} {E …
· 使用定理 `ProbabilityTheory.Indep.indicator_indepFun`：∀ {Ω : Type u_1} {_mΩ : Meas
urableSpace Ω} {μ : MeasureTheory.Measure Ω} {m : MeasurableSpace Ω} {M : Type u
_10}   {𝓧 : Type u_11} [inst : Z…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `aemeasurable_indicator_const_iff`：aemeasurable_indicator_const_iff {s} [
MeasurableSingletonClass β] (b : β) [NeZero b] : AEMeasurable (s.indicator (fun 
_ => b)) μ ↔ NullMeasu…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
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
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If a random variable `X` is independent of a sigma-algebra `m` and `A` is a set 
in `m`
then `∫ ω in A, f (X ω) ∂P = P.real A • ∫ ω, f (X ω) ∂P` for a measurable functi
on `f : 𝓧 → E`.
-/
lemma Indep.setIntegral_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hm : m ≤ mΩ) {f : 𝓧 → E} (hA1 : Indep m (m𝓧.comap X) P)
    (hX : AEMeasurable X P) (hA2 : MeasurableSet[m] A)
    (hf : AEStronglyMeasurable f (P.map X)) :
    ∫ ω in A, f (X ω) ∂P = P.real A • ∫ ω, f (X ω) ∂P :=
  calc ∫ ω in A, f (X ω) ∂P
    = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) • f (X ω) ∂P := by
        rw [← integral_indicator (hm A hA2)]
        congr with ω
        by_cases hω : ω ∈ A <;> simp [hω]
  _ = P.real A • ∫ ω, f (X ω) ∂P := by
    rw [IndepFun.integral_fun_comp_smul_comp _ _ hX (by fun_prop) hf]
    · simp [hm A hA2]
    · exact hA1.indicator_indepFun 1 hA2
    · exact (aemeasurable_indicator_const_iff 1).2 (hm A hA2).nullMeasurableSet

/-- If a random variable `X` is independent of a sigma-algebra `m` and `A` is a set in `m`
then `∫ ω in A, f (X ω) ∂P = P.real A * ∫ ω, f (X ω) ∂P` for a measurable function `f : 𝓧 → ℝ`. -/
/-
**ProbabilityTheory.Indep.setIntegral_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Probabil
ityTheory.Indep`。
形式化陈述：∀ {Ω : Type u_5} {𝓧 : Type u_6} {m mΩ : MeasurableSpace Ω} {P : MeasureThe
ory.Measure Ω} [m𝓧 : MeasurableSpace 𝓧]   {X : Ω → 𝓧} {A : Set Ω},   m ≤ mΩ →   
  ∀ {f : 𝓧 → ℝ},       ProbabilityTheory.Indep m (MeasurableSpace.comap X m𝓧) P 
→         AEMeasurable X P →           MeasurableSet A →             MeasureTheo
ry.AEStronglyMeasurable f (MeasureTheory.Measure.map X P) →               ∫ (ω :
 Ω) in A, f (X ω) ∂P = P.real A * ∫ (ω : Ω), f (X ω) ∂P
参数：MeasurableSpace.comap X m𝓧；MeasureTheory.Measure.map X P；ω : Ω；X ω；ω : Ω；X ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Indep.setIntegral_eq_smul`：∀ {Ω : Type u_5} {𝓧 : Type 
u_6} {m mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [m𝓧 : MeasurableSp
ace 𝓧]   {X : Ω → 𝓧} {A : Set Ω} …

--- 原说明 ---
If a random variable `X` is independent of a sigma-algebra `m` and `A` is a set 
in `m`
then `∫ ω in A, f (X ω) ∂P = P.real A * ∫ ω, f (X ω) ∂P` for a measurable functi
on `f : 𝓧 → ℝ`.
-/
lemma Indep.setIntegral_eq_mul (hm : m ≤ mΩ) {f : 𝓧 → ℝ} (hA1 : Indep m (m𝓧.comap X) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A)
    (hf : AEStronglyMeasurable f (P.map X)) :
    ∫ ω in A, f (X ω) ∂P = P.real A * ∫ ω, f (X ω) ∂P :=
  hA1.setIntegral_eq_smul hm hX hA hf

end SetIntegral

end ProbabilityTheory

