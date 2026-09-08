/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral theory of compact operators

This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.

## Main results

* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz, i.e. bounded below.
* `hasEigenvalue_or_mem_resolventSet`: the Fredholm alternative for compact operators, which says
  that if `T` is a compact operator and `μ ≠ 0`, then either `μ` is an eigenvalue of `T`, or `μ`
  is in the resolvent set of `T`.
* `hasEigenvalue_iff_mem_spectrum`: if `T` is a compact operator, then the nonzero eigenvalues of
  `T` are exactly the nonzero points in the spectrum of `T`.

We follow the proof given in Section 2 of
https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/
but adapt it to work in a more general setting of spaces over nontrivially normed fields,
rather than just over `ℝ` or `ℂ`. The main technical hurdle is that we don't have the ability to
rescale vectors to have norm exactly `1`, so we have to work with vectors in a shell instead of on
the unit sphere, and this makes some of the intermediate statements more complicated.
-/

public section

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {T : X →L[𝕜] X} {μ : 𝕜}

open Module End

open Filter Topology in
/-- If `T : X →L[𝕜] X` is a compact operator on a Banach space `X`, and `μ ≠ 0` is not an
eigenvalue of `T`, then `T - μ • 1` is antilipschitz with positive constant.
That is, `T - μ • 1` is bounded below as an operator.

This is a useful step in the proof of the Fredholm alternative for compact operators. -/
/-
**IsCompactOperator.antilipschitz_of_not_hasEigenvalue** 是 Mathlib 中的一个定理，位于命名空间
 `IsCompactOperator`。
形式化陈述：antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T) (hμ : μ != 0
) (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) : exists K, AntilipschitzWith K (T - μ •
 1 : X ->L[𝕜] X)
参数：hT : IsCompactOperator T；hμ : μ != 0；h : ¬ HasEigenvalue (T : End 𝕜 X) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `antilipschitzWith_iff_exists_mul_le_norm`：∀ {𝓕 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]  
 [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
（共 165 条，此处仅展示前 30 条）

--- 原说明 ---
If `T : X →L[𝕜] X` is a compact operator on a Banach space `X`, and `μ ≠ 0` is n
ot an
eigenvalue of `T`, then `T - μ • 1` is antilipschitz with positive constant.
That is, `T - μ • 1` is bounded below as an operator.

This is a useful step in the proof of the Fredholm alternative for compact opera
tors.
-/
theorem antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T) (hμ : μ ≠ 0)
    (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    ∃ K, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  -- Suppose not, and attempt to find an eigenvector with eigenvalue `μ`.
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  contrapose! h
  -- then for every `K > 0`, there is some `x` such that `‖(T - μ • 1) x‖ < K * ‖x‖`.
  replace hK : ∀ K > 0, ∃ x, ‖(T - μ • 1) x‖ < K * ‖x‖ := h
  -- In fact, there is a lower bound `c` such that for every `ε > 0`, there is an `x` with norm
  -- in the interval `[c, 1]` such that `‖(T - μ • 1) x‖ < ε`.
  -- (In the case of an `RCLike` field, where we can rescale, we could even get `‖x‖ = 1`, but we
  -- don't need that.)
  replace hK : ∃ c > 0, ∀ ε > 0, ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < ε := by
    obtain ⟨C, hC⟩ := NormedField.exists_one_lt_norm 𝕜
    refine ⟨‖C‖⁻¹, by positivity, fun ε hε ↦ ?_⟩
    obtain ⟨x, hx⟩ := hK ε (by positivity)
    have : x ≠ 0 := by aesop
    obtain ⟨η, hη, h₁, h₂, h₃⟩ := rescale_to_shell hC (ε := 1) (by simp) this
    refine ⟨η • x, h₁.le, by simpa using h₂, ?_⟩
    grw [map_smul, norm_smul, hx, mul_left_comm, ← norm_smul]
    linear_combination ε * h₁
  obtain ⟨c, hc₀, hc⟩ := hK
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  -- Then find a sequence of vectors `xₙ` with norm in the interval `[c, 1]` such
  -- that `‖(T - μ • 1) xₙ‖ < φ n`, where `φ n` is a sequence of positive numbers tending to zero.
  have (n : ℕ) : ∃ x, ‖x‖ ≤ 1 ∧ c ≤ ‖x‖ ∧ ‖(T - μ • 1) x‖ < φ n := hc (φ n) (hφ_pos n)
  choose x hx_norm_upper hx_norm_lower hx_bound using this
  have hx_lim : Tendsto (fun n ↦ (T - μ • 1) (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  -- Define the sequence of vectors `yₙ := T xₙ`
  let y_ (n : ℕ) : X := T (x n)
  -- which are bounded away from zero.
  have hy_lower : ∃ d > 0, ∀ᶠ n in atTop, d ≤ ‖y_ n‖ := by
    refine ⟨(‖μ‖ * c) / 2, by positivity, ?_⟩
    filter_upwards [hφ.eventually_le_const (show (‖μ‖ * c) / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by simpa using hx_bound n
    have h₂ : ‖μ‖ * ‖x n‖ ≤ ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul] using norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    linear_combination h₂ + h₁ + hn + ‖μ‖ * hx_norm_lower n
  -- The sequence `yₙ` is contained in the image of the closed unit ball under `T`,
  -- which is compact, since `T` is,
  -- so we can extract a convergent subsequence, and say `y_ (ψ n) → y`.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (x := y_) (fun n ↦ hK' ⟨x n, by simp [*], rfl⟩)
  -- However `(T - μ • 1) yₙ = T ((T - μ • 1) xₙ) → 0`
  have hy_lim : Tendsto (fun n ↦ (T - μ • 1) (y_ n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using T.continuous.continuousAt.tendsto.comp hx_lim
  -- so `(T - μ • 1) y = 0`.
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X →L[𝕜] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  -- Since `yₙ` are bounded away from `0`, we must have `y ≠ 0`.
  have hy_ne : y ≠ 0 := by
    obtain ⟨d, hd₀, hd⟩ := hy_lower
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by rwa [eventually_const] at this
    rw [NormedAddGroup.tendsto_nhds_zero] at hψy
    filter_upwards [hψ.tendsto_atTop.eventually hd, hψy d (by positivity)] using by grind
  -- So `y` is an eigenvector of `T` with eigenvalue `μ`,
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact hasEigenvalue_of_hasEigenvector this

set_option backward.isDefEq.respectTransparency.types false in
/--
Given an endomorphism `S` of a normed space that's a closed embedding but not surjective, we can
find a sequence of vectors `f n`, living inside a shell, such that `f n` is in the
range of `S ^ n` but is at least `1` away from any vector in the range of `S ^ (n + 1)`.
This is a useful construction for the proof of the Fredholm alternative for compact operators.
The conditions about `c` and `R` are to mimic those in Riesz's lemma.
-/
/-
**IsCompactOperator.exists_seq** 是 Mathlib 中的一个定理，位于命名空间 `IsCompactOperator`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an endomorphism `S` of a normed space that's a closed embedding but not su
rjective, we can
find a sequence of vectors `f n`, living inside a shell, such that `f n` is in t
he
range of `S ^ n` but is at least `1` away from any vector in the range of `S ^ (
n + 1)`.
This is a useful construction for the proof of the Fredholm alternative for comp
act operators.
The conditions about `c` and `R` are to mimic those in Riesz's lemma.
-/
private theorem exists_seq {S : End 𝕜 X} (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X,
      (∀ n, 1 ≤ ‖f n‖) ∧ (∀ n, ‖f n‖ ≤ R) ∧ (∀ n, f n ∈ (S ^ n).range) ∧
      (∀ n, ∀ y ∈ (S ^ (n + 1)).range, 1 ≤ ‖f n - y‖) := by
  -- Construct the sequence of submodules `V n := (S ^ n).range`, and show that they are closed.
  let V (n : ℕ) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : ℕ) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : ℕ) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hS_anti.isClosedMap _ ih
  -- Apply Riesz's lemma repeatedly using the closed subspace `V (n+1)` inside `V n`.
  have x (n : ℕ) : ∃ x ∈ V n, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ R ∧ ∀ y ∈ V (n + 1), 1 ≤ ‖x - y‖ := by
    have h₁ : IsClosed ((V (n + 1)).comap (V n).subtype : Set (V n)) := by
      simpa using! (hV_closed (n + 1)).preimage_val
    have h₂ : ∃ x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      simpa [iterate_succ, V, (iterate_injective hS_anti.injective n).eq_iff,
        Function.Surjective] using! hS_not_surj
    obtain ⟨⟨x, hx⟩, hxn, hxy⟩ := riesz_lemma_of_norm_lt hc hR h₁ h₂
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Subtype.forall] at hxn hxy
    exact ⟨x, hx, by simpa using! hxy 0, hxn,
      fun y hy ↦ hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  -- Use the existential claim to construct the sequence `f n`.
  choose x hxv hxn hxn' hxy using x
  exact ⟨x, hxn, hxn', hxv, hxy⟩

variable [CompleteSpace X]

/--
The **Fredholm alternative** for compact operators: if `T` is a compact operator and `μ ≠ 0`,
then either `μ` is an eigenvalue of `T`, or `μ` is in the resolvent set of `T`.
See also `hasEigenvalue_iff_mem_spectrum`, which says that the nonzero eigenvalues of a compact
operator are exactly the nonzero points in the spectrum of the operator.
-/
/-
**IsCompactOperator.hasEigenvalue_or_mem_resolventSet** 是 Mathlib 中的一个定理，位于命名空间 
`IsCompactOperator`。
形式化陈述：hasEigenvalue_or_mem_resolventSet (hT : IsCompactOperator T) (hμ : μ != 0)
 : HasEigenvalue (T : End 𝕜 X) μ ∨ μ in resolventSet 𝕜 T
参数：hT : IsCompactOperator T；hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsCompactOperator.antilipschitz_of_not_hasEigenvalue`：antilipschitz_of_n
ot_hasEigenvalue (hT : IsCompactOperator T) (hμ : μ != 0) (h : ¬ HasEigenvalue (
T : End 𝕜 X) μ) : exists K, AntilipschitzW…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.isUnit_iff_bijective`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_3} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] [CompleteSpa…
· 使用定理 `IsUnit.neg_iff`：IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : Is
Unit (-a) ↔ IsUnit a
· 使用定理 `spectrum.mem_resolventSet_iff`：mem_resolventSet_iff {r : R} {a : A} : r 
in resolventSet R a ↔ IsUnit (↑ₐ r - a)
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `_private.Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative.0.
IsCompactOperator.exists_seq`：∀ {𝕜 : Type u_1} {X : Type u_2} [inst : Nontrivial
lyNormedField 𝕜] [inst_1 : NormedAddCommGroup X]   [inst_2 : NormedSpace 𝕜 X] {S
 : Module.…
· 使用定理 `AntilipschitzWith.isClosedEmbedding`：isClosedEmbedding {α : Type*} {β : 
Type*} [EMetricSpace α] [EMetricSpace β] {K : Real>=0} {f : α -> β} [CompleteSpa
ce α] (hf : Antilipschitz…
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 131 条，此处仅展示前 30 条）

--- 原说明 ---
The **Fredholm alternative** for compact operators: if `T` is a compact operator
 and `μ ≠ 0`,
then either `μ` is an eigenvalue of `T`, or `μ` is in the resolvent set of `T`.
See also `hasEigenvalue_iff_mem_spectrum`, which says that the nonzero eigenvalu
es of a compact
operator are exactly the nonzero points in the spectrum of the operator.
-/
theorem hasEigenvalue_or_mem_resolventSet (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T := by
  -- Suppose not, then `μ` is not an eigenvalue and is in the spectrum.
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  -- Defining S := `T - μ • 1`, we deduce that S is antilipschitz and not surjective.
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue hT hμ h₁
  replace h₂ : ¬ (S : X → X).Bijective := by
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at h₂
    convert! h₂
    ext x
    simp [S]
  replace h₂ : ¬ (S : X → X).Surjective := by grind [Function.Bijective, hK.injective]
  -- Take a sequence of vectors `f n` in the range of `S ^ n` such that `‖f n‖` is in the
  -- interval `[1, ‖c‖ + 1]` and such that `f n` is at least `1` away from any vector in the range
  -- of `S ^ (n + 1)`.
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨f, hf_norm_lower, hf_norm_upper, hf_mem, hf_far⟩ := exists_seq h₂
    (hK.isClosedEmbedding S.uniformContinuous) hc (R := ‖c‖ + 1) (by simp)
  replace hf_mem {n m : ℕ} (h : m ≤ n) : f n ∈ ((S : End 𝕜 X) ^ m).range :=
    (S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem _)
  have hf_mem' {n m : ℕ} (h : m ≤ n) : S (f n) ∈ ((S : End 𝕜 X) ^ (m + 1)).range := by
    rw [iterate_succ', LinearMap.range_comp]
    exact ⟨f n, hf_mem h, rfl⟩
  -- Then the points `T (f n)` are bounded away from each other, using the separation property
  -- of the `f n` and the lower bound on their norms.
  have hp : Pairwise fun x₁ x₂ ↦ ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
    have : Std.Symm fun x₁ x₂ ↦ ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by grind [symm_def, norm_sub_rev]
    apply Pairwise.of_lt
    intro m n hmn
    let u : X := μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) = T (f m) - T (f n) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have : u ∈ ((S : End 𝕜 X) ^ (m + 1)).range := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _ (hf_mem' hmn.le) (hf_mem' le_rfl)
      · exact Submodule.smul_mem _ μ (hf_mem hmn)
    grw [← hu, norm_smul, mul_comm, ← hf_far _ u this, one_mul]
  -- However the `f n` are contained in a compact set, so their image under the compact operator `T`
  -- must contain a Cauchy subsequence, which is a contradiction.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (fun n ↦ hK' ⟨f n, by simp [*], rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy ‖μ‖ (by positivity)
  have : ‖T (f (ψ (N + 1))) - T (f (ψ N))‖ < ‖μ‖ := by simpa [dist_eq_norm_sub] using hN (N + 1)
  refine this.not_ge (hp ?_)
  simp [hψ.injective.eq_iff]

/--
If `T` is a compact operator on a Banach space, then the nonzero eigenvalues of `T` are exactly
the nonzero points in the spectrum of `T`. This is a consequence of the Fredholm alternative for
compact operators. -/
/-
**IsCompactOperator.hasEigenvalue_iff_mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `Is
CompactOperator`。
形式化陈述：hasEigenvalue_iff_mem_spectrum (hT : IsCompactOperator T) (hμ : μ != 0) : 
HasEigenvalue (T : End 𝕜 X) μ ↔ μ in spectrum 𝕜 T
参数：hT : IsCompactOperator T；hμ : μ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.spectrum_eq`：spectrum_eq {f : E ->L[𝕜] E} : spectrum
 𝕜 f = spectrum 𝕜 (f : Module.End 𝕜 E)
· 使用定理 `Module.End.HasEigenvalue.mem_spectrum`：∀ {R : Type v} {M : Type w} [inst
 : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Mod
ule.End R M} {μ : R}, f.Has…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`：hasEigenvalue_or_me
m_resolventSet (hT : IsCompactOperator T) (hμ : μ != 0) : HasEigenvalue (T : End
 𝕜 X) μ ∨ μ in resolventSet 𝕜 T

--- 原说明 ---
If `T` is a compact operator on a Banach space, then the nonzero eigenvalues of 
`T` are exactly
the nonzero points in the spectrum of `T`. This is a consequence of the Fredholm
 alternative for
compact operators.
-/
theorem hasEigenvalue_iff_mem_spectrum (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔ μ ∈ spectrum 𝕜 T := by
  constructor
  · intro hμ'
    rw [ContinuousLinearMap.spectrum_eq]
    exact hμ'.mem_spectrum
  · exact (hasEigenvalue_or_mem_resolventSet hT hμ).resolve_right

end IsCompactOperator

