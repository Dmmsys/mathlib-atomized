/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Taylor's formula with an integral remainder in higher dimensions

In this file we prove Taylor's formula with the remainder term in integral form.

* `map_add_eq_sum_add_integral_iteratedFDeriv`: version for higher dimensions with `iteratedFDeriv`

TODO: add a version that assumes `ContDiffOn f (closedBall x (‖y‖))`

-/

@[expose] public section

open Nat

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

variable {f : E → F} {x y : E} {t : 𝕜} {n : ℕ}

/-
**DifferentiableAt.deriv_comp_add_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.deriv_comp_add_smul (hf : DifferentiableAt 𝕜 f (x + t • y
)) : deriv (fun (s : 𝕜) => f (x + s • y)) t = fderiv 𝕜 f (x + t • y) y
参数：hf : DifferentiableAt 𝕜 f (x + t • y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `Differentiable.smul_const`：Differentiable.smul_const (hc : Differentiabl
e 𝕜 c) (f : F) : Differentiable 𝕜 fun y => c y • f
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `deriv_fun_add`：deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y + g y) x = deriv f x + deriv g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `deriv_id'`：deriv_id' : deriv (@id 𝕜) = fun _ => 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `deriv_smul_const`：deriv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F)
 : deriv (fun y => c y • f) x = deriv c x • f
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `fderiv_comp_deriv`：fderiv_comp_deriv (hl : DifferentiableAt 𝕜 l (f x)) (
hf : DifferentiableAt 𝕜 f x) : deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F -> E) (de
riv f x…
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
-/
theorem DifferentiableAt.deriv_comp_add_smul (hf : DifferentiableAt 𝕜 f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ f (x + s • y)) t = fderiv 𝕜 f (x + t • y) y := by
  have hg : Differentiable 𝕜 (fun (s : 𝕜) ↦ (x + s • y)) := by fun_prop
  convert fderiv_comp_deriv t hf hg.differentiableAt
  · simp
  · simpa using (deriv_smul_const (x := t) differentiableAt_id y).symm
/-
**ContDiffAt.deriv_fderiv_add_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.deriv_fderiv_add_smul (hf : ContDiffAt 𝕜 (n + 1) f (x + t • y))
 : deriv (fun (s : 𝕜) => iteratedFDeriv 𝕜 n f (x + s • y) (fun _ => y)) t = iter
atedFDeriv 𝕜 (n + 1) f (x + t • y) (fun _ => y)
参数：hf : ContDiffAt 𝕜 (n + 1) f (x + t • y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.differentiableAt_iteratedFDeriv`：ContDiffAt.differentiableAt_
iteratedFDeriv {f : E -> F} {n : Nat∞ω} {m : Nat} {x : E} (h : ContDiffAt 𝕜 n f 
x) (hmn : ↑m < n) : Differentiab…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `DifferentiableAt.iteratedFDeriv_succ_apply_left'`：DifferentiableAt.itera
tedFDeriv_succ_apply_left' {n : Nat} {m : Fin (n + 1) -> E} (hf : Differentiable
At 𝕜 (iteratedFDeriv 𝕜 n f) x) : itera…
· 使用定理 `DifferentiableAt.deriv_comp_add_smul`：DifferentiableAt.deriv_comp_add_sm
ul (hf : DifferentiableAt 𝕜 f (x + t • y)) : deriv (fun (s : 𝕜) => f (x + s • y)
) t = fderiv 𝕜 f (x + t • …
· 使用定理 `DifferentiableAt.continuousMultilinear_apply_const`：DifferentiableAt.con
tinuousMultilinear_apply_const (hc : DifferentiableAt 𝕜 c x) (u : forall i, M i)
 : DifferentiableAt 𝕜 (fun y => (c y) u)…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem ContDiffAt.deriv_fderiv_add_smul (hf : ContDiffAt 𝕜 (n + 1) f (x + t • y)) :
    deriv (fun (s : 𝕜) ↦ iteratedFDeriv 𝕜 n f (x + s • y) (fun _ ↦ y)) t =
    iteratedFDeriv 𝕜 (n + 1) f (x + t • y) (fun _ ↦ y) := by
  have hf' : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) (x + t • y) := by
    apply hf.differentiableAt_iteratedFDeriv
    norm_cast
    exact lt_add_one n
  convert (hf'.continuousMultilinear_apply_const _).deriv_comp_add_smul
  exact hf'.iteratedFDeriv_succ_apply_left'

end NontriviallyNormedField

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

variable {f : E → F} {x y : E} {n : ℕ}

variable [CompleteSpace F]

/-- *Taylor's theorem with remainder in integral form*. If `f` is `n + 1` times continuously
differentiable, then `f (x + y)` is given by
`∑ k in 0..n, D^k f(x; y,..,y) / k! + 1/n! ∫ t in 0..1, (1 - t) ^ n • D^{n+1}f (x + t • y; y,..,y)`,
where `D^k f` denotes the iterated derivative of `f`.

In the case that `n = 1`, this is a reformulation of the fundamental theorem of calculus, namely
`f (x + y) = f x + ∫ t in 0..1, D f(x + t • y; y)`. -/
/-
**map_add_eq_sum_add_integral_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_add_eq_sum_add_integral_iteratedFDeriv (hf : forall (t : Real) (_ht : 
t in Set.Icc 0 1), ContDiffAt Real (n + 1) f (x + t • y)) : f (x + y) = ∑ k in F
inset.range (n + 1), (k ! : Real)⁻¹ • (iteratedFDeriv Real k f x (fun _ => y)) +
 (n ! : Real)⁻¹ • ∫ t in 0..1, (1 - t)^n • iteratedFDeriv Real (n + 1) f (x + t 
• y) (fun _ => y)
参数：hf : forall (t : Real) (_ht : t in Set.Icc 0 1), ContDiffAt Real (n + 1) f (x
 + t • y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DifferentiableAt.deriv_comp_add_smul`：DifferentiableAt.deriv_comp_add_sm
ul (hf : DifferentiableAt 𝕜 f (x + t • y)) : deriv (fun (s : 𝕜) => f (x + s • y)
) t = fderiv 𝕜 f (x + t • …
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `iteratedFDeriv_one_apply`：iteratedFDeriv_one_apply (m : Fin 1 -> E) : it
eratedFDeriv 𝕜 1 f x m = fderiv 𝕜 f x (m 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `DifferentiableAt.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `DifferentiableAt.smul_const`：DifferentiableAt.smul_const (hc : Different
iableAt 𝕜 c x) (f : F) : DifferentiableAt 𝕜 (fun y => c y • f) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `ContDiffAt.fderiv_right`：ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f 
x₀) (hmn : m + 1 <= n) : ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀
（共 145 条，此处仅展示前 30 条）

--- 原说明 ---
*Taylor's theorem with remainder in integral form*. If `f` is `n + 1` times cont
inuously
differentiable, then `f (x + y)` is given by
`∑ k in 0..n, D^k f(x; y,..,y) / k! + 1/n! ∫ t in 0..1, (1 - t) ^ n • D^{n+1}f (
x + t • y; y,..,y)`,
where `D^k f` denotes the iterated derivative of `f`.

In the case that `n = 1`, this is a reformulation of the fundamental theorem of 
calculus, namely
`f (x + y) = f x + ∫ t in 0..1, D f(x + t • y; y)`.
-/
theorem map_add_eq_sum_add_integral_iteratedFDeriv (hf : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
    ContDiffAt ℝ (n + 1) f (x + t • y)) :
    f (x + y) = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _ ↦ y)) +
    (n ! : ℝ)⁻¹ • ∫ t in 0..1, (1 - t)^n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ ↦ y) := by
  simp_rw [← Set.uIcc_of_le zero_le_one] at hf
  induction n with
  | zero =>
    -- The base case follows from the fundamental theorem of calculus
    have h_eq : Set.EqOn (fun t ↦ (fderiv ℝ f (x + t • y)) y) (deriv fun (s : ℝ) ↦ f (x + s • y))
        (Set.uIcc 0 1) := by
      intro t ht
      rw [DifferentiableAt.deriv_comp_add_smul]
      exact (hf t ht).differentiableAt (by simp)
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, factorial_zero, cast_one, inv_one,
      iteratedFDeriv_zero_apply, one_smul, pow_zero, reduceAdd, iteratedFDeriv_one_apply]
    rw [← sub_eq_iff_eq_add', Eq.comm, intervalIntegral.integral_congr h_eq]
    have hf' : ∀ (t : ℝ) (ht : t ∈ Set.uIcc 0 1), DifferentiableAt ℝ (fun s ↦ f (x + s • y)) t :=
      fun t ht ↦ ((hf t ht).differentiableAt (by simp)).comp t (by fun_prop)
    have hint : IntervalIntegrable (deriv (fun s ↦ f (x + s • y))) MeasureTheory.volume 0 1 := by
      have h₁ : ContinuousOn (fderiv ℝ f) ((fun t ↦ x + t • y) '' Set.uIcc (0 : ℝ) 1) := by
        intro z ⟨t, ht, hz⟩
        rw [← hz]
        exact (((hf t ht).fderiv_right (le_refl _)).continuousAt (n := 0)).continuousWithinAt
      have h₂ : ContinuousOn (fun x_1 ↦ fderiv ℝ f (x + x_1 • y)) (Set.uIcc (0 : ℝ) 1) := by
        apply h₁.comp (t := (fun t ↦ x + t • y) '' (Set.uIcc (0 : ℝ) 1)) (by fun_prop)
        intro t ht
        use t
      apply (ContinuousOn.congr _ h_eq.symm).intervalIntegrable
      fun_prop
    simpa using intervalIntegral.integral_deriv_eq_sub hf' hint
  | succ n ih =>
    -- We use the inductive hypothesis to cancel all lower order terms
    specialize ih (fun t ht ↦ (hf t ht).of_le (by simp))
    rw [Finset.sum_range_succ, add_assoc]
    convert ih using 2
    -- We define the functions u and v that we will integrate by parts
    set u := fun (k : ℕ) (t : ℝ) ↦ (k ! : ℝ)⁻¹ * (1 - t) ^ k
    have hu : ∀ (t : ℝ), HasDerivAt (u (n + 1)) (-u n t) t := by
      intro t
      unfold u
      have : (-((n ! : ℝ)⁻¹ * (1 - t) ^ n)) =
          ((n + 1) ! : ℝ)⁻¹ * ((n + 1) * (1 - t) ^ n * (-1)) := by
        field_simp
        congr 1
        rw [Nat.factorial_succ]
        grind
      rw [this]
      apply HasDerivAt.const_mul
      convert ((hasDerivAt_id t).const_sub 1).pow (n + 1)
      all_goals norm_cast
    have hu' : Continuous (u n) := by fun_prop
    set v := fun (k : ℕ) (t : ℝ) ↦ iteratedFDeriv ℝ k f (x + t • y) (fun _ ↦ y)
    have hv : ∀ (t : ℝ) (ht : t ∈ Set.uIcc 0 1), HasDerivAt (v (n + 1)) (v (n + 1 + 1) t) t := by
      intro t ht
      unfold v
      rw [← (hf t ht).deriv_fderiv_add_smul]
      have h_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) (x + t • y) := by
        apply (hf t ht).differentiableAt_iteratedFDeriv
        norm_cast
        grind
      refine DifferentiableAt.hasDerivAt ?_
      fun_prop
    have hv' : ContinuousOn (v (n + 1 + 1)) (Set.uIcc 0 1) := by
      intro t ht
      have h_cont : ContinuousAt (iteratedFDeriv ℝ (n + 1 + 1) f) (x + t • y) :=
        ((hf t ht).iteratedFDeriv_right (i := n + 1 + 1) (m := 0) (by simp)).continuousAt
      exact (h_cont.comp (x := t) (by fun_prop)).continuousWithinAt.eval_const _
    -- Now we apply integration by parts and simplify
    simpa [← eq_neg_add_iff_add_eq, ← intervalIntegral.integral_smul, smul_smul, u, v] using
      intervalIntegral.integral_smul_deriv_eq_deriv_smul (fun t _ ↦ hu t) hv
      (hu'.neg.intervalIntegrable _ _) hv'.intervalIntegrable
