/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Eisenstein series q-expansions

We give the q-expansion of Eisenstein series of weight `k` and level 1. In particular, we prove
`EisensteinSeries.q_expansion_bernoulli` which says that for even `k` with `3 ≤ k`
Eisenstein series can be written as `1 - (2k / bernoulli k) ∑' n, σ_{k-1}(n) q^n` where
`q = exp(2πiz)` and `σ_{k-1}(n)` is the sum of the `(k-1)`-th powers of the divisors of `n`.
We need `k` to be even so that the Eisenstein series are non-zero and we require `k ≥ 3` so that
the series converges absolutely.

We also identify the q-expansion coefficients as a `PowerSeries` via
`EisensteinSeries.E_qExpansion_coeff`, and use this to prove that the normalised Eisenstein series
is non-zero (`EisensteinSeries.E_ne_zero`).

The proof relies on the identity
`∑' n : ℤ, 1 / (z + n) ^ (k + 1) = ((-2πi)^(k+1) / k!) ∑' n : ℕ, n^k q^n` which comes from
differentiating the expansion of `π cot(πz)` in terms of exponentials. Since our Eisenstein series
are defined as sums over coprime integer pairs, we also need to relate these to sums over all pairs
of integers, which is done in `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`. This then
gives the q-expansion with a Riemann zeta factor, which we simplify using the formula for
`ζ(k)` in terms of Bernoulli numbers to get the final result.

-/

public section

open Set Metric TopologicalSpace Function Filter Complex ArithmeticFunction
  ModularForm EisensteinSeries

open scoped Real Nat ArithmeticFunction.sigma

open UpperHalfPlane hiding I

local notation "ℍₒ" => upperHalfPlaneSet

/-
**iteratedDerivWithin_cexp_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iteratedDerivWithin_cexp_aux (k m : ℕ) (p : ℝ) {S : Set ℂ} (hs : IsOpen S) :
    EqOn (iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * m * s / p)) S)
    (fun s ↦ (2 * π * I * m / p) ^ k * cexp (2 * π * I * m * s / p)) S := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s ↦ cexp (2 * π * I * m * s / p)) = fun s ↦ cexp (((2 * π * I * m) / p) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf
/-
**aux_IsBigO_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma aux_IsBigO_mul (k l : ℕ) (p : ℝ) {f : ℕ → ℂ}
    (hf : f =O[atTop] fun n ↦ ((n ^ l) : ℝ)) :
    (fun n ↦ f n * (2 * π * I * n / p) ^ k) =O[atTop] fun n ↦ (↑(n ^ (l + k)) : ℝ) := by
  have h0 : (fun n : ℕ ↦ (2 * π * I * n / p) ^ k) =O[atTop] fun n ↦ ((n ^ k) : ℝ) := by
    have h1 : (fun n : ℕ ↦ (2 * π * I * n / p) ^ k) =
        fun n : ℕ ↦ ((2 * π * I / p) ^ k) * n ^ k := by
      ext z
      ring
    simpa [h1] using isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
      ((2 * π * I / p) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop)
  push_cast
  convert! hf.mul h0
  ring

open BoundedContinuousFunction in
/-- The infinite sum of `k`-th iterated derivative of the complex exponential multiplied by a
function that grows polynomially is absolutely and uniformly convergent. -/
/-
**summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp (k l : Nat) {f : 
Nat -> Complex} {p : Real} (hp : 0 < p) (hf : f =O[atTop] (fun n => ((n ^ l) : R
eal))) : SummableLocallyUniformlyOn (fun n => (f n) • iteratedDerivWithin k (fun
 z => cexp (2 * π * I * z / p) ^ n) ℍₒ) ℍₒ
参数：k l : Nat；hp : 0 < p；hf : f =O[atTop] (fun n => ((n ^ l) : Real))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SummableLocallyUniformlyOn_of_locally_bounded`：SummableLocallyUniformlyO
n_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β] {f : α -> β ->
 F} {s : Set β} (hs : IsOpen s) (hu…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `isCompact_iff_isCompact_univ`：isCompact_iff_isCompact_univ : IsCompact s
 ↔ IsCompact (univ : Set s)
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `BoundedContinuousFunction.norm_lt_iff_of_compact`：norm_lt_iff_of_compact
 [CompactSpace α] {f : α ->ᵇ β} {M : Real} (M0 : 0 < M) : ‖f‖ < M ↔ forall x, ‖f
 x‖ < M
· 使用定理 `Real.zero_lt_one`：0 < 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
The infinite sum of `k`-th iterated derivative of the complex exponential multip
lied by a
function that grows polynomially is absolutely and uniformly convergent.
-/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp (k l : ℕ) {f : ℕ → ℂ} {p : ℝ}
    (hp : 0 < p) (hf : f =O[atTop] (fun n ↦ ((n ^ l) : ℝ))) :
    SummableLocallyUniformlyOn (fun n ↦ (f n) •
      iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z / p) ^ n) ℍₒ) ℍₒ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K ↦ Complex.exp (2 * π * I * r / p), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * π * I * (x / p)) = cexp (2 * π * I * x / p) := by
      ring_nf
    simpa using h1 ▸ norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / p), by aesop⟩
  refine ⟨_, by simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
    (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k l p hf))), fun n z hz ↦ ?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ← exp_nsmul', Pi.smul_apply,
    iteratedDerivWithin_cexp_aux k n p isOpen_upperHalfPlaneSet (hK hz), smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    norm_natCast, abs_norm, ge_iff_le, r, c] at *
  rw [← mul_assoc]
  gcongr
  convert! h0
  rw [← norm_pow, ← exp_nsmul']

/-- This is a version of `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` for level one
and q-expansion coefficients all `1`. -/
/-
**summableLocallyUniformlyOn_iteratedDerivWithin_cexp** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k : Nat) : SummableLo
callyUniformlyOn (fun n => iteratedDerivWithin k (fun z => cexp (2 * π * I * z) 
^ n) ℍₒ) ℍₒ
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Real.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Real)‖ = n
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp`：summableLocall
yUniformlyOn_iteratedDerivWithin_smul_cexp (k l : Nat) {f : Nat -> Complex} {p :
 Real} (hp : 0 < p) (hf : f =O[atTop] (fun n =…
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
This is a version of `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` 
for level one
and q-expansion coefficients all `1`.
-/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k : ℕ) :
    SummableLocallyUniformlyOn
      (fun n ↦ iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : ℕ ↦ (1 : ℂ)) =O[atTop] fun n ↦ ((n ^ 1) : ℝ) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast, eventually_atTop]
    exact ⟨1, 1, fun b hb ↦ by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp k 1 (p := 1)
    (by norm_num) h0
/-
**differentiableAt_iteratedDerivWithin_cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_iteratedDerivWithin_cexp (n a : Nat) {s : Set Complex} (h
s : IsOpen s) {r : Complex} (hr : r in s) : DifferentiableAt Complex (iteratedDe
rivWithin a (fun z => cexp (2 * π * I * z) ^ n) s) r
参数：n a : Nat；hs : IsOpen s；hr : r in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `ContDiff.differentiable_iteratedDeriv'`：ContDiff.differentiable_iterated
Deriv' (m : Nat) (h : ContDiff 𝕜 (m + 1) f) : Differentiable 𝕜 (iteratedDeriv m 
f)
· 使用定理 `ContDiff.pow`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : T
ype uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {n : WithTo
p …
· 使用定理 `ContDiff.cexp`：ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun
 x => Complex.exp (f x)
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `DifferentiableOn.congr`：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f
 s) (h' : forall x in s, f₁ x = f x) : DifferentiableOn 𝕜 f₁ s
· 使用定理 `iteratedDerivWithin_of_isOpen`：iteratedDerivWithin_of_isOpen (hs : IsOpe
n s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
lemma differentiableAt_iteratedDerivWithin_cexp (n a : ℕ) {s : Set ℂ} (hs : IsOpen s)
    {r : ℂ} (hr : r ∈ s) : DifferentiableAt ℂ
      (iteratedDerivWithin a (fun z ↦ cexp (2 * π * I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn ℂ (iteratedDeriv a (fun z ↦ cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop
/-
**iteratedDerivWithin_tsum_cexp_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_tsum_cexp_eq (k : Nat) (z : ℍ) : iteratedDerivWithin k
 (fun z => ∑' n : Nat, cexp (2 * π * I * z) ^ n) ℍₒ z = ∑' n : Nat, iteratedDeri
vWithin k (fun s : Complex => cexp (2 * π * I * s) ^ n) ℍₒ z
参数：k : Nat；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_tsum`：iteratedDerivWithin_tsum {f : ι -> 𝕜 -> F} (m 
: Nat) (hs : IsOpen s) {x : 𝕜} (hx : x in s) (hsum : forall t in s, Summable (fu
n n : ι => f n…
· 使用定理 `instIsRCLikeNormedField`：∀ (𝕜 : Type u_3) [h : RCLike 𝕜], IsRCLikeNormed
Field 𝕜
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_geometric_iff_norm_lt_one`：summable_geometric_iff_norm_lt_one :
 (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖ < 1
· 使用定理 `UpperHalfPlane.norm_exp_two_pi_I_lt_one`：UpperHalfPlane.norm_exp_two_pi_
I_lt_one (τ : ℍ) : ‖(Complex.exp (2 * π * Complex.I * τ))‖ < 1
· 使用定理 `summableLocallyUniformlyOn_iteratedDerivWithin_cexp`：summableLocallyUnif
ormlyOn_iteratedDerivWithin_cexp (k : Nat) : SummableLocallyUniformlyOn (fun n =
> iteratedDerivWithin k (fun z => cexp (2…
· 使用引理 `differentiableAt_iteratedDerivWithin_cexp`：differentiableAt_iteratedDeri
vWithin_cexp (n a : Nat) {s : Set Complex} (hs : IsOpen s) {r : Complex} (hr : r
 in s) : DifferentiableAt Compl…
-/
lemma iteratedDerivWithin_tsum_cexp_eq (k : ℕ) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ z =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx ↦ summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl hz ↦ differentiableAt_iteratedDerivWithin_cexp n l
      isOpen_upperHalfPlaneSet hz
/-
**contDiffOn_tsum_cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiffOn_tsum_cexp (k : Nat∞) : ContDiffOn Complex k (fun z : Complex =>
 ∑' n : Nat, cexp (2 * π * I * z) ^ n) ℍₒ
参数：k : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffOn_of_differentiableOn_deriv`：contDiffOn_of_differentiableOn_der
iv {n : Nat∞} (h : forall m : Nat, (m : Nat∞) <= n -> DifferentiableOn 𝕜 (iterat
edDerivWithin m f s) s) : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DifferentiableWithinAt.congr`：DifferentiableWithinAt.congr (h : Differen
tiableWithinAt 𝕜 f s x) (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : Dif
ferentiableWithinA…
· 使用引理 `SummableLocallyUniformlyOn.differentiableOn`：SummableLocallyUniformlyOn.
differentiableOn {ι E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [C
ompleteSpace E] {f : ι -> Complex…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `summableLocallyUniformlyOn_iteratedDerivWithin_cexp`：summableLocallyUnif
ormlyOn_iteratedDerivWithin_cexp (k : Nat) : SummableLocallyUniformlyOn (fun n =
> iteratedDerivWithin k (fun z => cexp (2…
· 使用引理 `differentiableAt_iteratedDerivWithin_cexp`：differentiableAt_iteratedDeri
vWithin_cexp (n a : Nat) {s : Set Complex} (hs : IsOpen s) {r : Complex} (hr : r
 in s) : DifferentiableAt Compl…
· 使用引理 `iteratedDerivWithin_tsum_cexp_eq`：iteratedDerivWithin_tsum_cexp_eq (k : 
Nat) (z : ℍ) : iteratedDerivWithin k (fun z => ∑' n : Nat, cexp (2 * π * I * z) 
^ n) ℍₒ z = ∑' n : Nat…
-/
lemma contDiffOn_tsum_cexp (k : ℕ∞) :
    ContDiffOn ℂ k (fun z : ℂ ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz ↦
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz ↦ differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz ↦ iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)
  (iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)
/-
**iteratedDerivWithin_tsum_exp_aux_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iteratedDerivWithin_tsum_exp_aux_eq {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk, iteratedDerivWithin_fun_neg,
      iteratedDerivWithin_const_mul (by simpa using z.2) (isOpen_upperHalfPlaneSet.uniqueDiffOn)]
    · simp only [iteratedDerivWithin_tsum_cexp_eq, neg_mul]
    · exact (contDiffOn_tsum_cexp k).contDiffWithinAt (by simpa using z.2)
  have h : -(2 * π * I * (2 * π * I) ^ k) * ∑' (n : ℕ), n ^ k * cexp (2 * π * I * z) ^ n =
        -(2 * π * I) * ∑' n : ℕ, (2 * π * I * n) ^ k * cexp (2 * π * I * z) ^ n := by
    simp_rw [← tsum_mul_left]
    congr
    ext y
    ring
  simp only [this, neg_mul, pow_succ', h, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
    OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, or_self, I_ne_zero, or_false]
  congr
  ext n
  have := exp_nsmul' (p := 1) (a := 2 * π * I) (n := n)
  simp_rw [div_one] at this
  simpa [this, UpperHalfPlane.coe] using
    iteratedDerivWithin_cexp_aux k n 1 isOpen_upperHalfPlaneSet z.2

/-- This is one key identity relating infinite series to q-expansions which shows that
`∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n, n ^ k q ^n` where
`q = cexp (2 π I z)`. -/
/-
**EisensteinSeries.qExpansion_identity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EisensteinSeries.qExpansion_identity {k : Nat} (hk : 1 <= k) (z : ℍ) : ∑' 
n : Int, 1 / ((z : Complex) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) * ∑'
 n : Nat, n ^ k * cexp (2 * π * I * z) ^ n
参数：hk : 1 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion.0
.iteratedDerivWithin_tsum_exp_aux_eq`：∀ {k : ℕ},   1 ≤ k →     ∀ (z : UpperHalfP
lane),       iteratedDerivWithin k           (fun z =>             ↑Real.pi * Co
mplex.I -         …
· 使用定理 `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`：iteratedDerivWithin_
cot_pi_mul_eq_mul_tsum_div_pow {k : Nat} (hk : 1 <= k) {z : Complex} (hz : z in 
ℍₒ) : iteratedDerivWithin k (fun x : Com…
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `iteratedDerivWithin_congr`：iteratedDerivWithin_congr (hfg : Set.EqOn f g
 s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n g s) s
· 使用定理 `pi_mul_cot_pi_q_exp`：pi_mul_cot_pi_q_exp (z : ℍ) : π * cot (π * z) = π *
 I - 2 * π * I * ∑' n : Nat, Complex.exp (2 * π * I * z) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `eq_inv_mul_iff_mul_eq₀`：eq_inv_mul_iff_mul_eq₀ (hb : b != 0) : a = b⁻¹ *
 c ↔ b * a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 115 条，此处仅展示前 30 条）

--- 原说明 ---
This is one key identity relating infinite series to q-expansions which shows th
at
`∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n, n ^ k q ^n` wh
ere
`q = cexp (2 π I z)`.
-/
theorem EisensteinSeries.qExpansion_identity {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : (-1) ^ k * k ! * ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
    rw [← iteratedDerivWithin_tsum_exp_aux_eq hk z,
      ← iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk (by simpa using z.2)]
    exact iteratedDerivWithin_congr (fun x hx ↦ by (simpa using pi_mul_cot_pi_q_exp ⟨x, hx⟩))
      (by simpa using z.2)
  simp_rw [(eq_inv_mul_iff_mul_eq₀ (by simp [Nat.factorial_ne_zero])).mpr this, ← tsum_mul_left]
  congr
  ext n
  rw [show (-2 * π * I) ^ (k + 1) = (-1) ^ (k + 1) * (2 * π * I) ^ (k + 1) by rw [← neg_pow]; ring]
  field_simp
  ring_nf
  simp [Nat.mul_two]
/-
**summable_pow_mul_cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_pow_mul_cexp (k : Nat) (e : Nat+) (z : ℍ) : Summable fun c : Nat 
=> (c : Complex) ^ k * cexp (2 * π * I * e * z) ^ c
参数：k : Nat；e : Nat+；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SummableLocallyUniformlyOn.summable`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {x : β} {s : Set β}   [inst
_1 : UniformSpace α] [ins…
· 使用定理 `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp`：summableLocall
yUniformlyOn_iteratedDerivWithin_smul_cexp (k l : Nat) {f : Nat -> Complex} {p :
 Real} (hp : 0 < p) (hf : f =O[atTop] (fun n =…
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
-/
lemma summable_pow_mul_cexp (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ ↦ (c : ℂ) ^ k * cexp (2 * π * I * e * z) ^ c := by
  have he : 0 < (e * (z : ℂ)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n ↦ (n ^ k : ℂ)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  grind [ofReal_one, iteratedDerivWithin_zero, Pi.smul_apply, smul_eq_mul]

/-- This is a version of `EisensteinSeries.qExpansion_identity` for positive naturals,
which shows that  `∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n : ℕ+, n ^ k q ^n`
where `q = cexp (2 π I z)`. -/
/-
**EisensteinSeries.qExpansion_identity_pnat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EisensteinSeries.qExpansion_identity_pnat {k : Nat} (hk : 1 <= k) (z : ℍ) 
: ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !)
 * ∑' n : Nat+, n ^ k * cexp (2 * π * I * z) ^ (n : Nat)
参数：hk : 1 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EisensteinSeries.qExpansion_identity`：EisensteinSeries.qExpansion_identi
ty {k : Nat} (hk : 1 <= k) (z : ℍ) : ∑' n : Int, 1 / ((z : Complex) + n) ^ (k + 
1) = ((-2 * π * I) ^ (k + …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_zero_pnat_eq_tsum_nat`：∀ {G : Type u_2} [inst : AddCommGroup G] [in
st_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, 
Summable f → f 0…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `summable_pow_mul_cexp`：summable_pow_mul_cexp (k : Nat) (e : Nat+) (z : ℍ
) : Summable fun c : Nat => (c : Complex) ^ k * cexp (2 * π * I * e * z) ^ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
This is a version of `EisensteinSeries.qExpansion_identity` for positive natural
s,
which shows that  `∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑'
 n : ℕ+, n ^ k q ^n`
where `q = cexp (2 π I z)`.
-/
theorem EisensteinSeries.qExpansion_identity_pnat {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) = ((-2 * π * I) ^ (k + 1) / k !) *
    ∑' n : ℕ+, n ^ k * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [EisensteinSeries.qExpansion_identity hk z, ← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k ≠ 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp
/-
**summable_eisSummand** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_eisSummand {k : Nat} (hk : 3 <= k) (z : ℍ) : Summable (eisSummand
 k · z)
参数：hk : 3 <= k；z : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `summable_norm_iff`：summable_norm_iff {α E : Type*} [NormedAddCommGroup E
] [NormedSpace Real E] [FiniteDimensional Real E] {f : α -> E} : (Summable fun x
 => ‖f …
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用引理 `EisensteinSeries.summable_norm_eisSummand`：summable_norm_eisSummand {k :
 Int} (hk : 3 <= k) (z : ℍ) : Summable fun (x : Fin 2 -> Int) => ‖(eisSummand k 
x z)‖
· 使用定理 `Int.toNat_le`：∀ {m : ℤ} {n : ℕ}, m.toNat ≤ n ↔ m ≤ ↑n
-/
lemma summable_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable (eisSummand k · z) :=
  summable_norm_iff.mp <| summable_norm_eisSummand (Int.toNat_le.mp hk) z
/-
**summable_prod_eisSummand** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_prod_eisSummand {k : Nat} (hk : 3 <= k) (z : ℍ) : Summable fun x 
: Int × Int => eisSummand k ![x.1, x.2] z
参数：hk : 3 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `summable_eisSummand`：summable_eisSummand {k : Nat} (hk : 3 <= k) (z : ℍ)
 : Summable (eisSummand k · z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `finTwoArrowEquiv_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α) = (piFin
TwoEquiv fun x => α).toFun
· 使用定理 `piFinTwoEquiv_apply`：∀ (α : Fin 2 → Type u), ⇑(piFinTwoEquiv α) = fun f 
=> (f 0, f 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.ofFn_inj`：ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔
 f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma summable_prod_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun x : ℤ × ℤ ↦ eisSummand k ![x.1, x.2] z := by
  refine (finTwoArrowEquiv ℤ).summable_iff.mp <| (summable_eisSummand hk z).congr (fun v ↦ ?_)
  simp [show ![v 0, v 1] = v from List.ofFn_inj.mp rfl]
/-
**tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow {k : Nat} (hk : 3 <= k) (hk2 : 
Even k) (z : ℍ) : ∑' v, eisSummand k v z = 2 * riemannZeta k + 2 * ((-2 * π * I)
 ^ k / (k - 1)!) * ∑' (n : Nat+), σ (k - 1) n * cexp (2 * π * I * z) ^ (n : Nat)
参数：hk : 3 <= k；hk2 : Even k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `finTwoArrowEquiv_symm_apply`：∀ (α : Type u_1), ⇑(finTwoArrowEquiv α).sym
m = fun x => ![x.1, x.2]
· 使用定理 `Summable.tsum_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommGroup α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSp
ace α] […
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `summable_prod_eisSummand`：summable_prod_eisSummand {k : Nat} (hk : 3 <= 
k) (z : ℍ) : Summable fun x : Int × Int => eisSummand k ![x.1, x.2] z
· 使用定理 `tsum_int_eq_zero_add_two_mul_tsum_pnat`：∀ {G : Type u_2} [inst : AddComm
Group G] [inst_1 : UniformSpace G] [IsUniformAddGroup G] [CompleteSpace G] [T2Sp
ace G]   {f : ℤ → G}, Functi…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `tsum_comp_neg`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : Topol
ogicalSpace α] {β : Type u_4} [inst_2 : InvolutiveNeg β]   (f : β → α), ∑' (d : 
β),…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 83 条，此处仅展示前 30 条）
-/
lemma tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' v, eisSummand k v z = 2 * riemannZeta k + 2 * ((-2 * π * I) ^ k / (k - 1)!) *
    ∑' (n : ℕ+), σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq, finTwoArrowEquiv_symm_apply,
    Summable.tsum_prod (summable_prod_eisSummand hk z),
    tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n ↦ ?h₁)
      (by simpa using (summable_prod_eisSummand hk z).prod)]
  case h₁ =>
    nth_rewrite 1 [← tsum_comp_neg]
    exact tsum_congr fun y ↦ by simp [eisSummand, ← neg_add _ (y : ℂ), -neg_add_rev, hk2.neg_pow]
  have H (b : ℕ+) := qExpansion_identity_pnat (k := k - 1) (by grind) ⟨b * z, by simpa using z.2⟩
  simp_rw [show k - 1 + 1 = k by grind, one_div] at H
  simp only [neg_mul] at H
  rw [nsmul_eq_mul, mul_assoc]
  congr
  · simp [eisSummand, two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by grind) hk2]
  · suffices ∑' (m : ℕ+) (n : ℕ+), (n : ℕ) ^ (k - 1) * cexp (2 * π * I * (m * z)) ^ (n : ℕ) =
        ∑' (m : ℕ+) (n : ℕ+), (n : ℕ) ^ (k - 1) * cexp (2 * π * I * z) ^ (m * n : ℕ) by
      simp [eisSummand, H, tsum_mul_left,
        ← tsum_prod_pow_eq_tsum_sigma (k - 1) (norm_exp_two_pi_I_lt_one z), this]
    simp_rw [← Complex.exp_nat_mul]
    exact tsum_congr₂ (fun m n ↦ by push_cast; ring_nf)
/-
**eisSummand_of_gammaSet_eq_divIntMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eisSummand_of_gammaSet_eq_divIntMap (k : Int) (z : ℍ) {n : Nat} (v : gamma
Set 1 n 0) : eisSummand k v z = ((n : Complex) ^ k)⁻¹ * eisSummand k (divIntMap 
n v) z
参数：k : Int；z : ℍ；v : gammaSet 1 n 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EisensteinSeries.gammaSet_eq_gcd_mul_divIntMap`：gammaSet_eq_gcd_mul_divI
ntMap {r : Nat} {v : Fin 2 -> Int} (hv : v in gammaSet 1 r 0) : v = r • (divIntM
ap r v)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eisSummand_of_gammaSet_eq_divIntMap (k : ℤ) (z : ℍ) {n : ℕ} (v : gammaSet 1 n 0) :
    eisSummand k v z = ((n : ℂ) ^ k)⁻¹ * eisSummand k (divIntMap n v) z := by
  simp_rw [eisSummand]
  nth_rw 1 2 [gammaSet_eq_gcd_mul_divIntMap v.2]
  simp [← mul_inv, ← mul_zpow, mul_add, mul_assoc]
/-
**tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries {k : Nat} (hk : 3 <= k
) (z : ℍ) : ∑' v : Fin 2 -> Int, eisSummand k v z = riemannZeta k * eisensteinSe
ries (N
参数：hk : 3 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `eisensteinSeries.eq_1`：∀ {N : ℕ} (a : Fin 2 → ZMod N) (k : ℤ) (z : Upper
HalfPlane),   eisensteinSeries a k z = ∑' (x : ↑(EisensteinSeries.gammaSet N 1 a
)), Eisenst…
· 使用定理 `Summable.tsum_sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommGrou
p α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSpace α] [T0Spac
e α] {γ :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用引理 `EisensteinSeries.summable_norm_eisSummand`：summable_norm_eisSummand {k :
 Int} (hk : 3 <= k) (z : ℍ) : Summable fun (x : Fin 2 -> Int) => ‖(eisSummand k 
x z)‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `zeta_nat_eq_tsum_of_gt_one`：zeta_nat_eq_tsum_of_gt_one {k : Nat} (hk : 1
 < k) : riemannZeta k = ∑' n : Nat, 1 / (n : Complex) ^ k
· 使用定理 `tsum_mul_tsum_of_summable_norm`：tsum_mul_tsum_of_summable_norm [Complete
Space R] {f : ι -> R} {g : ι' -> R} (hf : Summable fun x => ‖f x‖) (hg : Summabl
e fun x => ‖g x‖) : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 73 条，此处仅展示前 30 条）
-/
lemma tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    ∑' v : Fin 2 → ℤ, eisSummand k v z = riemannZeta k * eisensteinSeries (N := 1) 0 k z := by
  have hk1 : 1 < k := by grind
  have hk2 : 3 ≤ (k : ℤ) := mod_cast hk
  simp_rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq, gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries, Summable.tsum_sigma ?hsumm, zeta_nat_eq_tsum_of_gt_one hk1,
    tsum_mul_tsum_of_summable_norm (by simp [hk1]) ((summable_norm_eisSummand hk2 z).subtype _)]
  case hsumm =>
    exact gammaSetDivGcdSigmaEquiv.symm.summable_iff.mpr (summable_norm_eisSummand hk2 z).of_norm
      |>.congr <| by simp
  simp_rw [one_div]
  rw [Summable.tsum_prod' ?h₁ fun b ↦ ?h₂]
  case h₁ =>
    exact summable_mul_of_summable_norm (f := fun (n : ℕ) ↦ ((n : ℂ) ^ k)⁻¹)
      (g := fun (v : gammaSet 1 1 0) ↦ eisSummand k v z) (by simp [hk1])
      ((summable_norm_eisSummand hk2 z).subtype _)
  case h₂ =>
    simpa using ((summable_norm_eisSummand hk2 z).subtype _).of_norm.mul_left (a := ((b : ℂ) ^ k)⁻¹)
  refine tsum_congr fun b ↦ ?_
  rcases eq_or_ne b 0 with rfl | hb
  · simp [show ((0 : ℂ) ^ k)⁻¹ = 0 by aesop, eisSummand_of_gammaSet_eq_divIntMap]
  · have : NeZero b := ⟨hb⟩
    simpa [eisSummand_of_gammaSet_eq_divIntMap k z, tsum_mul_left, hb]
      using (gammaSetDivGcdEquiv b).tsum_eq (eisSummand k · z)

/-- The q-Expansion of normalised Eisenstein series of level one with `riemannZeta` term. -/
/-
**EisensteinSeries.q_expansion_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EisensteinSeries.q_expansion_riemannZeta {k : Nat} (hk : 3 <= k) (hk2 : Ev
en k) (z : ℍ) : E hk z = 1 + (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! * ∑
' n : Nat+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : Int)
参数：hk : 3 <= k；hk2 : Even k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EisensteinSeries.eisensteinSeriesSIF_apply`：eisensteinSeriesSIF_apply (k
 : Int) (z : ℍ) : eisensteinSeriesSIF a k z = eisensteinSeries a k z
· 使用定理 `eisensteinSeries.eq_1`：∀ {N : ℕ} (a : Fin 2 → ZMod N) (k : ℤ) (z : Upper
HalfPlane),   eisensteinSeries a k z = ∑' (x : ↑(EisensteinSeries.gammaSet N 1 a
)), Eisenst…
· 使用引理 `tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow`：tsum_eisSummand_eq_tsum_sigm
a_mul_cexp_pow {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ) : ∑' v, eisSummand
 k v z = 2 * riemannZeta k + 2 *…
· 使用引理 `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`：tsum_eisSummand_eq_
riemannZeta_mul_eisensteinSeries {k : Nat} (hk : 3 <= k) (z : ℍ) : ∑' v : Fin 2 
-> Int, eisSummand k v z = riemannZeta k …
· 使用引理 `riemannZeta_ne_zero_of_one_lt_re`：riemannZeta_ne_zero_of_one_lt_re {s : 
Complex} (hs : 1 < s.re) : riemannZeta s != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `inv_mul_eq_iff_eq_mul₀`：inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b =
 c ↔ b = a * c

--- 原说明 ---
The q-Expansion of normalised Eisenstein series of level one with `riemannZeta` 
term.
-/
lemma EisensteinSeries.q_expansion_riemannZeta {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 + (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! *
    ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℤ) := by
  rw [show E hk z = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k z from rfl,
    eisensteinSeriesSIF_apply 0 k z, eisensteinSeries]
  have HE1 := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 z
  have HE2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
  have z2 : riemannZeta k ≠ 0 := riemannZeta_ne_zero_of_one_lt_re <| by norm_cast; grind
  simp [eisSummand, eisensteinSeries, ← inv_mul_eq_iff_eq_mul₀ z2] at HE1 HE2 ⊢
  grind
/-
**eisensteinSeries_coeff_identity** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma eisensteinSeries_coeff_identity {k : ℕ} (hk2 : Even k) (hkn0 : k ≠ 0) :
    (riemannZeta k)⁻¹ * (-2 * π * I) ^ k / (k - 1)! = -(2 * k / bernoulli k) := by
  have h2 : k = 2 * (k / 2 - 1 + 1) := by grind
  set m := k / 2 - 1
  rw [h2, Nat.cast_mul 2 (m + 1), Nat.cast_two, riemannZeta_two_mul_nat (show m + 1 ≠ 0 by grind),
    show (2 * (m + 1))! = 2 * (m + 1) * (2 * m + 1)! by grind [Nat.factorial_succ],
    show 2 * (m + 1) - 1 = 2 * m + 1 by grind, mul_pow, mul_pow, pow_mul I, I_sq]
  norm_cast
  simp [field]
  grind

/-- The q-Expansion of normalised Eisenstein series of level one with `bernoulli` term. -/
/-
**EisensteinSeries.q_expansion_bernoulli** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EisensteinSeries.q_expansion_bernoulli {k : Nat} (hk : 3 <= k) (hk2 : Even
 k) (z : ℍ) : E hk z = 1 - (2 * k / bernoulli k) * ∑' n : Nat+, σ (k - 1) n * ce
xp (2 * π * I * z) ^ (n : Int)
参数：hk : 3 <= k；hk2 : Even k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion.0
.eisensteinSeries_coeff_identity`：∀ {k : ℕ},   Even k →     k ≠ 0 → (riemannZeta
 ↑k)⁻¹ * (-2 * ↑Real.pi * Complex.I) ^ k / ↑(k - 1).factorial = -(2 * ↑k / ↑(ber
noulli k))
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `EisensteinSeries.q_expansion_riemannZeta`：EisensteinSeries.q_expansion_r
iemannZeta {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ) : E hk z = 1 + (rieman
nZeta k)⁻¹ * (-2 * π * I) ^ k …

--- 原说明 ---
The q-Expansion of normalised Eisenstein series of level one with `bernoulli` te
rm.
-/
lemma EisensteinSeries.q_expansion_bernoulli {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 - (2 * k / bernoulli k) *
    ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℤ) := by
  convert! q_expansion_riemannZeta hk hk2 z using 1
  rw [eisensteinSeries_coeff_identity hk2 (by grind), neg_mul, ← sub_eq_add_neg]

section NonZero

open ModularFormClass

local notation "𝕢" => Periodic.qParam

/-- Summability of the divisor-sum q-expansion series `∑ σ_{k-1}(n) q^n`. -/
/-
**EisensteinSeries.summable_sigma_mul_cexp_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EisensteinSeries.summable_sigma_mul_cexp_pow {k : Nat} (hk : 1 <= k) (z : 
ℍ) : Summable fun n : Nat => (σ (k - 1) n : Complex) * cexp (2 * π * I * z) ^ n
参数：hk : 1 <= k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `summable_norm_pow_mul_geometric_of_norm_lt_one`：summable_norm_pow_mul_ge
ometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) : Summable fun n : Nat =
> ‖((n : R) ^ k * r ^ n : R)‖
· 使用定理 `UpperHalfPlane.norm_exp_two_pi_I_lt_one`：UpperHalfPlane.norm_exp_two_pi_
I_lt_one (τ : ℍ) : ‖(Complex.exp (2 * π * Complex.I * τ))‖ < 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Complex.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Complex)‖ = n
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ArithmeticFunction.sigma_le_pow_succ`：sigma_le_pow_succ (k n : Nat) : σ 
k n <= n ^ (k + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
Summability of the divisor-sum q-expansion series `∑ σ_{k-1}(n) q^n`.
-/
lemma EisensteinSeries.summable_sigma_mul_cexp_pow {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    Summable fun n : ℕ ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

/-- The q-expansion coefficients of the normalised Eisenstein series `E k`: the constant term is
`1` and for `m ≥ 1` the `m`-th coefficient is `-(2k / B_k) * σ_{k-1}(m)` where `B_k` is the
`k`-th Bernoulli number. -/
/-
**EisensteinSeries.E_qExpansion_coeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EisensteinSeries.E_qExpansion_coeff {k : Nat} (hk : 3 <= k) (hk2 : Even k)
 (m : Nat) : (qExpansion 1 (E hk)).coeff m = if m = 0 then 1 else -(2 * k / bern
oulli k : Complex) * (σ (k - 1) m)
参数：hk : 3 <= k；hk2 : Even k；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `EisensteinSeries.summable_sigma_mul_cexp_pow`：EisensteinSeries.summable_
sigma_mul_cexp_pow {k : Nat} (hk : 1 <= k) (z : ℍ) : Summable fun n : Nat => (σ 
(k - 1) n : Complex) * cexp (2 * π…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasSum_nat_add_iff'`：∀ {G : Type u_2} [inst : AddCommGroup G] {g : G} [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G}   (k : ℕ), Has
Sum (fun …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `EisensteinSeries.q_expansion_bernoulli`：EisensteinSeries.q_expansion_ber
noulli {k : Nat} (hk : 3 <= k) (hk2 : Even k) (z : ℍ) : E hk z = 1 - (2 * k / be
rnoulli k) * ∑' n : Nat+, σ …
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `tsum_pnat_eq_tsum_succ`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {f : ℕ → M},   ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
The q-expansion coefficients of the normalised Eisenstein series `E k`: the cons
tant term is
`1` and for `m ≥ 1` the `m`-th coefficient is `-(2k / B_k) * σ_{k-1}(m)` where `
B_k` is the
`k`-th Bernoulli number.
-/
lemma EisensteinSeries.E_qExpansion_coeff {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (m : ℕ) :
    (qExpansion 1 (E hk)).coeff m =
    if m = 0 then 1 else -(2 * k / bernoulli k : ℂ) * (σ (k - 1) m) := by
  set β : ℂ := -(2 * k / bernoulli k : ℂ)
  set c : ℕ → ℂ := fun m ↦ if m = 0 then 1 else β * ↑(σ (k - 1) m)
  suffices ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 (1 : ℝ) τ ^ m) (E hk τ) from
    (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL this m).symm
  intro τ
  have hS : Summable fun n : ℕ ↦ (σ (k - 1) (n + 1) : ℂ) * cexp (2 * π * I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (by omega) τ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul, Finset.range_one,
    ite_mul, one_mul, Finset.sum_singleton, pow_zero, c]
  have hval : E hk τ - 1 = β * ∑' n : ℕ, (σ (k - 1) (n + 1)) * cexp (2 * π * I * τ) ^ (n + 1) := by
    have := q_expansion_bernoulli hk hk2 τ
    simp_rw [zpow_natCast] at this
    rw [this, ← tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * τ) ^ n)]
    ring
  rw [hval]
  convert! (hS.mul_left β).hasSum using 1
  · grind [Periodic.qParam, ofReal_one, div_one]
  · rw [tsum_mul_left]

/-- The q-expansion constant coefficient of the normalised Eisenstein series `E k` is `1`. -/
/-
**EisensteinSeries.E_qExpansion_coeff_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EisensteinSeries.E_qExpansion_coeff_zero {k : Nat} (hk : 3 <= k) (hk2 : Ev
en k) : (qExpansion 1 (E hk)).coeff 0 = 1
参数：hk : 3 <= k；hk2 : Even k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `EisensteinSeries.E_qExpansion_coeff`：EisensteinSeries.E_qExpansion_coeff
 {k : Nat} (hk : 3 <= k) (hk2 : Even k) (m : Nat) : (qExpansion 1 (E hk)).coeff 
m = if m = 0 then 1 else …

--- 原说明 ---
The q-expansion constant coefficient of the normalised Eisenstein series `E k` i
s `1`.
-/
lemma EisensteinSeries.E_qExpansion_coeff_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (qExpansion 1 (E hk)).coeff 0 = 1 := by
  simpa using E_qExpansion_coeff hk hk2 0

/-- Normalised Eisenstein series of even weight `k ≥ 3` are non-zero. -/
/-
**EisensteinSeries.E_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EisensteinSeries.E_ne_zero {k : Nat} (hk : 3 <= k) (hk2 : Even k) : E hk !
= 0
参数：hk : 3 <= k；hk2 : Even k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EisensteinSeries.E_qExpansion_coeff_zero`：EisensteinSeries.E_qExpansion_
coeff_zero {k : Nat} (hk : 3 <= k) (hk2 : Even k) : (qExpansion 1 (E hk)).coeff 
0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `UpperHalfPlane.qExpansion_zero`：∀ (h : ℝ), UpperHalfPlane.qExpansion h 0
 = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Normalised Eisenstein series of even weight `k ≥ 3` are non-zero.
-/
theorem EisensteinSeries.E_ne_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : E hk ≠ 0 :=
  fun h ↦ one_ne_zero <| (E_qExpansion_coeff_zero hk hk2).symm.trans (by simp [h, qExpansion_zero])

end NonZero

