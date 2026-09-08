/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Construction of Harmonic Functions

This file constructs examples of harmonic functions.

If `f : ℂ → F` is complex-differentiable, then `f` is harmonic. If `F = ℂ`, then so is its real
part, imaginary part, and complex conjugate. If `f` has no zero, then `log ‖f‖` is harmonic.
-/

public section

open Complex ComplexConjugate InnerProductSpace Topology

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {x : ℂ}

/-!
## Harmonicity of Analytic Functions on the Complex Plane
-/

/--
Continuously complex-differentiable functions on ℂ are harmonic.
-/
/-
**ContDiffAt.harmonicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.harmonicAt (h : ContDiffAt Complex 2 f x) : HarmonicAt f x
参数：h : ContDiffAt Complex 2 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContDiffAt.restrict_scalars`：ContDiffAt.restrict_scalars (h : ContDiffAt
 𝕜' n f x) : ContDiffAt 𝕜 n f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq`：ContDiffAt.restr
ictScalars_iteratedFDeriv_eventuallyEq (h : ContDiffAt 𝕜' n f x) : (restrictScal
ars 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] ite…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousMultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι
 -> R) (m : forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane`：laplacian_eq
_iteratedFDeriv_complexPlane (f : Complex -> F) : Δ f = fun x => iteratedFDeriv 
Real 2 f x ![1, 1] + iteratedFDeriv Real 2 f x !…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.smul_empty`：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x 
: M) (v : Fin 0 → α), x • v = ![]
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Continuously complex-differentiable functions on ℂ are harmonic.
-/
theorem ContDiffAt.harmonicAt (h : ContDiffAt ℂ 2 f x) : HarmonicAt f x := by
  refine ⟨h.restrict_scalars ℝ, ?_⟩
  filter_upwards [h.restrictScalars_iteratedFDeriv_eventuallyEq (𝕜 := ℝ)] with a ha
  have : (iteratedFDeriv ℂ 2 f a) (I • ![1, 1])
      = (∏ i, I) • ((iteratedFDeriv ℂ 2 f a) ![1, 1]) :=
    (iteratedFDeriv ℂ 2 f a).map_smul_univ (fun _ ↦ I) ![1, 1]
  simp_all [laplacian_eq_iteratedFDeriv_complexPlane f, ← ha,
    ContinuousMultilinearMap.coe_restrictScalars]

/-- Analytic functions on ℂ are harmonic. -/
/-
**AnalyticAt.harmonicAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.harmonicAt [CompleteSpace F] (h : AnalyticAt Complex f x) : Har
monicAt f x
参数：h : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.harmonicAt`：ContDiffAt.harmonicAt (h : ContDiffAt Complex 2 f
 x) : HarmonicAt f x
· 使用定理 `AnalyticAt.contDiffAt`：AnalyticAt.contDiffAt [CompleteSpace F] (h : Anal
yticAt 𝕜 f x) : ContDiffAt 𝕜 n f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Analytic functions on ℂ are harmonic.
-/
theorem AnalyticAt.harmonicAt [CompleteSpace F] (h : AnalyticAt ℂ f x) : HarmonicAt f x :=
  h.contDiffAt.harmonicAt

/--
If `f : ℂ → ℂ` is complex-analytic, then its real part is harmonic.
-/
/-
**AnalyticAt.harmonicAt_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.harmonicAt_re {f : Complex -> Complex} (h : AnalyticAt Complex 
f x) : HarmonicAt (fun z => (f z).re) x
参数：h : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.comp_CLM`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] 
  {F : Type u_2} [inst_3 : …
· 使用定理 `AnalyticAt.harmonicAt`：AnalyticAt.harmonicAt [CompleteSpace F] (h : Anal
yticAt Complex f x) : HarmonicAt f x
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
If `f : ℂ → ℂ` is complex-analytic, then its real part is harmonic.
-/
theorem AnalyticAt.harmonicAt_re {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
    HarmonicAt (fun z ↦ (f z).re) x := h.harmonicAt.comp_CLM reCLM

/--
If `f : ℂ → ℂ` is complex-analytic, then its imaginary part is harmonic.
-/
/-
**AnalyticAt.harmonicAt_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.harmonicAt_im {f : Complex -> Complex} (h : AnalyticAt Complex 
f x) : HarmonicAt (fun z => (f z).im) x
参数：h : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicAt.comp_CLM`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] 
  {F : Type u_2} [inst_3 : …
· 使用定理 `AnalyticAt.harmonicAt`：AnalyticAt.harmonicAt [CompleteSpace F] (h : Anal
yticAt Complex f x) : HarmonicAt f x
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
If `f : ℂ → ℂ` is complex-analytic, then its imaginary part is harmonic.
-/
theorem AnalyticAt.harmonicAt_im {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) :
    HarmonicAt (fun z ↦ (f z).im) x :=
  h.harmonicAt.comp_CLM imCLM

/--
If `f : ℂ → ℂ` is complex-analytic, then its complex conjugate is harmonic.
-/
/-
**AnalyticAt.harmonicAt_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.harmonicAt_conj {f : Complex -> Complex} (h : AnalyticAt Comple
x f x) : HarmonicAt (conj f) x
参数：h : AnalyticAt Complex f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `InnerProductSpace.harmonicAt_comp_CLE_iff`：harmonicAt_comp_CLE_iff (l : 
F ≃L[Real] G) : HarmonicAt (l ∘ f) x ↔ HarmonicAt f x
· 使用定理 `AnalyticAt.harmonicAt`：AnalyticAt.harmonicAt [CompleteSpace F] (h : Anal
yticAt Complex f x) : HarmonicAt f x
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
If `f : ℂ → ℂ` is complex-analytic, then its complex conjugate is harmonic.
-/
theorem AnalyticAt.harmonicAt_conj {f : ℂ → ℂ} (h : AnalyticAt ℂ f x) : HarmonicAt (conj f) x :=
  (harmonicAt_comp_CLE_iff conjCLE).2 h.harmonicAt

/-!
## Harmonicity of `log ‖analytic‖`
-/

/- Helper lemma for AnalyticAt.harmonicAt_log_norm -/
/-
**analyticAt_harmonicAt_log_normSq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for AnalyticAt.harmonicAt_log_norm
-/
private lemma analyticAt_harmonicAt_log_normSq {z : ℂ} {g : ℂ → ℂ} (h₁g : AnalyticAt ℂ g z)
    (h₂g : g z ≠ 0) (h₃g : g z ∈ slitPlane) :
    HarmonicAt (Real.log ∘ normSq ∘ g) z := by
  rw [harmonicAt_congr_nhds (f₂ := reCLM ∘ (conjCLE ∘ log ∘ g + log ∘ g))]
  · exact (((harmonicAt_comp_CLE_iff conjCLE).2 ((analyticAt_clog h₃g).comp h₁g).harmonicAt).add
      ((analyticAt_clog h₃g).comp h₁g).harmonicAt).comp_CLM reCLM
  · have t₀ := h₁g.differentiableAt.continuousAt.preimage_mem_nhds
      ((isOpen_slitPlane.inter isOpen_ne).mem_nhds ⟨h₃g, h₂g⟩)
    calc Real.log ∘ normSq ∘ g
    _ =ᶠ[𝓝 z] reCLM ∘ ofRealCLM ∘ Real.log ∘ normSq ∘ g := by aesop
    _ =ᶠ[𝓝 z] reCLM ∘ log ∘ ((conjCLE ∘ g) * g) := by
      filter_upwards with x
      simp only [Function.comp_apply, ofRealCLM_apply, Pi.mul_apply, conjCLE_apply]
      rw [ofReal_log, normSq_eq_conj_mul_self]
      exact normSq_nonneg (g x)
    _ =ᶠ[𝓝 z] reCLM ∘ (log ∘ conjCLE ∘ g + log ∘ g) := by
      filter_upwards [t₀] with x hx
      simp only [Function.comp_apply, Pi.mul_apply, conjCLE_apply, Pi.add_apply]
      congr
      rw [Complex.log_mul_eq_add_log_iff _ hx.2, Complex.arg_conj]
      · simp [Complex.slitPlane_arg_ne_pi hx.1, Real.pi_pos, Real.pi_nonneg]
      · simpa [ne_eq, map_eq_zero] using hx.2
    _ =ᶠ[𝓝 z] ⇑reCLM ∘ (⇑conjCLE ∘ log ∘ g + log ∘ g) := by
      apply Filter.eventuallyEq_iff_exists_mem.2
      use g ⁻¹' (Complex.slitPlane ∩ {0}ᶜ), t₀
      intro x hx
      simp only [Function.comp_apply, Pi.add_apply, conjCLE_apply]
      congr 1
      rw [← Complex.log_conj]
      simp [Complex.slitPlane_arg_ne_pi hx.1]

/--
If `f : ℂ → ℂ` is complex-analytic without zero, then `log ‖f‖` is harmonic.
-/
/-
**AnalyticAt.harmonicAt_log_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.harmonicAt_log_norm {f : Complex -> Complex} {z : Complex} (h₁f
 : AnalyticAt Complex f z) (h₂f : f z != 0) : HarmonicAt (Real.log ‖f ·‖) z
参数：h₁f : AnalyticAt Complex f z；h₂f : f z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `Real.log_sqrt`：log_sqrt {x : Real} (hx : 0 <= x) : log (√x) = log x / 2
· 使用定理 `Complex.normSq_nonneg`：normSq_nonneg (z : Complex) : 0 <= normSq z
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℂ → ℂ` is complex-analytic without zero, then `log ‖f‖` is harmonic.
-/
theorem AnalyticAt.harmonicAt_log_norm {f : ℂ → ℂ} {z : ℂ} (h₁f : AnalyticAt ℂ f z)
    (h₂f : f z ≠ 0) :
    HarmonicAt (Real.log ‖f ·‖) z := by
  have : (Real.log ‖f ·‖) = (2 : ℝ)⁻¹ • (Real.log ∘ Complex.normSq ∘ f) := by
    funext z
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [Complex.norm_def, Real.log_sqrt]
    · linarith
    exact (f z).normSq_nonneg
  rw [this]
  apply HarmonicAt.const_smul
  by_cases h₃f : f z ∈ Complex.slitPlane
  · exact analyticAt_harmonicAt_log_normSq h₁f h₂f h₃f
  · rw [(by aesop : Complex.normSq ∘ f = Complex.normSq ∘ (-f))]
    exact analyticAt_harmonicAt_log_normSq h₁f.neg (by simpa)
      ((mem_slitPlane_or_neg_mem_slitPlane h₂f).resolve_left h₃f)
