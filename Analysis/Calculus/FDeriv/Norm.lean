/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Differentiability of the norm in a real normed vector space

This file provides basic results about the differentiability of the norm in a real vector space.
Most are of the following kind: if the norm has some differentiability property
(`DifferentiableAt`, `ContDiffAt`, `HasStrictFDerivAt`, `HasFDerivAt`) at `x`, then so it has
at `t • x` when `t ≠ 0`.

## Main statements

* `ContDiffAt.contDiffAt_norm_smul`: If the norm is continuously differentiable up to order `n`
  at `x`, then so it is at `t • x` when `t ≠ 0`.
* `differentiableAt_norm_smul`: If `t ≠ 0`, the norm is differentiable at `x` if and only if
  it is at `t • x`.
* `HasFDerivAt.hasFDerivAt_norm_smul`: If the norm has a Fréchet derivative `f` at `x` and `t ≠ 0`,
  then it has `(SignType t) • f` as a Fréchet derivative at `t · x`.
* `fderiv_norm_smul` : `fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x)`,
  this holds without any differentiability assumptions.
* `DifferentiableAt.fderiv_norm_self`: if the norm is differentiable at `x`,
  then `fderiv ℝ (‖·‖) x x = ‖x‖`.
* `norm_fderiv_norm`: if the norm is differentiable at `x` then the operator norm of its derivative
  is `1` (on a non-trivial space).

## Tags

differentiability, norm

-/

public section

open ContinuousLinearMap Filter NNReal Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : WithTop ℕ∞} {f : StrongDual ℝ E} {x : E} {t : ℝ}

variable (E) in
/-
**not_differentiableAt_norm_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_differentiableAt_norm_zero [Nontrivial E] : ¬DifferentiableAt Real (‖·
‖) (0 : E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exists_lt_norm`：NormedSpace.exists_lt_norm (c : Real) : exis
ts x : E, c < ‖x‖
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 33 条，此处仅展示前 30 条）
-/
theorem not_differentiableAt_norm_zero [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E 0
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t ↦ (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this
/-
**ContDiffAt.contDiffAt_norm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.contDiffAt_norm_smul (ht : t != 0) (h : ContDiffAt Real n (‖·‖)
 x) : ContDiffAt Real n (‖·‖) (t • x)
参数：ht : t != 0；h : ContDiffAt Real n (‖·‖) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_const_smul`：contDiff_const_smul (c : R) : ContDiff 𝕜 n fun p : 
F => c • p
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffAt.const_smul`：ContDiffAt.const_smul {f : E -> F} {x : E} (c : R
) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun y => c • f y) x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem ContDiffAt.contDiffAt_norm_smul (ht : t ≠ 0) (h : ContDiffAt ℝ n (‖·‖) x) :
    ContDiffAt ℝ n (‖·‖) (t • x) := by
  have h1 : ContDiffAt ℝ n (fun y ↦ t⁻¹ • y) (t • x) := (contDiff_const_smul t⁻¹).contDiffAt
  have h2 : ContDiffAt ℝ n (fun y ↦ |t| * ‖y‖) x := h.const_smul |t|
  conv at h2 => enter [4]; rw [← one_smul ℝ x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 1
  ext y
  simp only [Function.comp_apply]
  rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
/-
**contDiffAt_norm_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_norm_smul_iff (ht : t != 0) : ContDiffAt Real n (‖·‖) x ↔ ContD
iffAt Real n (‖·‖) (t • x) where mp h
参数：ht : t != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffAt_norm_smul`：ContDiffAt.contDiffAt_norm_smul (ht : t
 != 0) (h : ContDiffAt Real n (‖·‖) x) : ContDiffAt Real n (‖·‖) (t • x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem contDiffAt_norm_smul_iff (ht : t ≠ 0) :
    ContDiffAt ℝ n (‖·‖) x ↔ ContDiffAt ℝ n (‖·‖) (t • x) where
  mp h := h.contDiffAt_norm_smul ht
  mpr hd := by
    convert! hd.contDiffAt_norm_smul (inv_ne_zero ht)
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
/-
**ContDiffAt.contDiffAt_norm_of_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.contDiffAt_norm_of_smul (h : ContDiffAt Real n (‖·‖) (t • x)) :
 ContDiffAt Real n (‖·‖) x
参数：h : ContDiffAt Real n (‖·‖) (t • x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiffAt_zero`：contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ exists u in 𝓝 x,
 ContinuousOn f u
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_differentiableAt_norm_zero`：not_differentiableAt_norm_zero [Nontrivi
al E] : ¬DifferentiableAt Real (‖·‖) (0 : E)
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_const_of_subsingleton`：eq_const_of_subsingleton {β : Sort*} [Subsingl
eton α] (f : α -> β) (a : α) : f = Function.const α (f a)
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `contDiffAt_norm_smul_iff`：contDiffAt_norm_smul_iff (ht : t != 0) : ContD
iffAt Real n (‖·‖) x ↔ ContDiffAt Real n (‖·‖) (t • x) where mp h
-/
theorem ContDiffAt.contDiffAt_norm_of_smul (h : ContDiffAt ℝ n (‖·‖) (t • x)) :
    ContDiffAt ℝ n (‖·‖) x := by
  rcases eq_or_ne n 0 with rfl | hn
  · apply contDiffAt_zero.2
    exact ⟨univ, univ_mem, continuous_norm.continuousOn⟩
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E by
      rw [eq_const_of_subsingleton (‖·‖) 0]
      exact contDiffAt_const
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E <| h.differentiableAt hn
  · exact contDiffAt_norm_smul_iff ht |>.2 h
/-
**HasStrictFDerivAt.hasStrictFDerivAt_norm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.hasStrictFDerivAt_norm_smul (ht : t != 0) (h : HasStrict
FDerivAt (‖·‖) f x) : HasStrictFDerivAt (‖·‖) ((SignType.sign t : Real) • f) (t 
• x)
参数：ht : t != 0；h : HasStrictFDerivAt (‖·‖) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasStrictFDerivAt.const_smul`：HasStrictFDerivAt.const_smul (h : HasStric
tFDerivAt f f' x) (c : R) : HasStrictFDerivAt (c • f) (c • f') x
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp_smulₛₗ`：comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [S
MulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂] [ContinuousConstSMul R₃ M₃] (
h : M₂ ->SL[σ₂₃] M₃) …
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
（共 38 条，此处仅展示前 30 条）
-/
theorem HasStrictFDerivAt.hasStrictFDerivAt_norm_smul
    (ht : t ≠ 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  have h1 : HasStrictFDerivAt (fun y ↦ t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id ℝ E) (t • x) :=
    hasStrictFDerivAt_id (t • x) |>.const_smul t⁻¹
  have h2 : HasStrictFDerivAt (fun y ↦ |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul ℝ x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 with y
  · rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  ext y
  simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
  rw [eq_inv_mul_iff_mul_eq₀ ht, ← mul_assoc, self_mul_sign]
/-
**HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg (ht : t < 0) (h : HasStri
ctFDerivAt (‖·‖) f x) : HasStrictFDerivAt (‖·‖) (-f) (t • x)
参数：ht : t < 0；h : HasStrictFDerivAt (‖·‖) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictFDerivAt_norm_smul`：HasStrictFDerivAt.hasStri
ctFDerivAt_norm_smul (ht : t != 0) (h : HasStrictFDerivAt (‖·‖) f x) : HasStrict
FDerivAt (‖·‖) ((SignType.sign t : …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne
/-
**HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos (ht : 0 < t) (h : HasStri
ctFDerivAt (‖·‖) f x) : HasStrictFDerivAt (‖·‖) f (t • x)
参数：ht : 0 < t；h : HasStrictFDerivAt (‖·‖) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasStrictFDerivAt.hasStrictFDerivAt_norm_smul`：HasStrictFDerivAt.hasStri
ctFDerivAt_norm_smul (ht : t != 0) (h : HasStrictFDerivAt (‖·‖) f x) : HasStrict
FDerivAt (‖·‖) ((SignType.sign t : …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem HasStrictFDerivAt.hasStrictDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasStrictFDerivAt (‖·‖) f x) :
    HasStrictFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasStrictFDerivAt_norm_smul ht.ne'
/-
**HasFDerivAt.hasFDerivAt_norm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.hasFDerivAt_norm_smul (ht : t != 0) (h : HasFDerivAt (‖·‖) f x
) : HasFDerivAt (‖·‖) ((SignType.sign t : Real) • f) (t • x)
参数：ht : t != 0；h : HasFDerivAt (‖·‖) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.const_smul`：HasFDerivAt.const_smul (h : HasFDerivAt f f' x) 
(c : R) : HasFDerivAt (c • f) (c • f') x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp_smulₛₗ`：comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [S
MulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂] [ContinuousConstSMul R₃ M₃] (
h : M₂ ->SL[σ₂₃] M₃) …
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
（共 38 条，此处仅展示前 30 条）
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul
    (ht : t ≠ 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  have h1 : HasFDerivAt (fun y ↦ t⁻¹ • y) (t⁻¹ • ContinuousLinearMap.id ℝ E) (t • x) :=
    hasFDerivAt_id (t • x) |>.const_smul t⁻¹
  have h2 : HasFDerivAt (fun y ↦ |t| * ‖y‖) (|t| • f) x := h.const_smul |t|
  conv at h2 => enter [3]; rw [← one_smul ℝ x, ← inv_mul_cancel₀ ht, mul_smul]
  convert! h2.comp (t • x) h1 using 2 with y
  · simp only [Function.comp_apply]
    rw [norm_smul, ← mul_assoc, norm_eq_abs, ← abs_mul, mul_inv_cancel₀ ht, abs_one, one_mul]
  · ext y
    simp only [smul_apply, smul_eq_mul, comp_smulₛₗ, map_inv₀, RingHom.id_apply, comp_id]
    rw [eq_inv_mul_iff_mul_eq₀ ht, ← mul_assoc, self_mul_sign]
/-
**HasFDerivAt.hasFDerivAt_norm_smul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.hasFDerivAt_norm_smul_neg (ht : t < 0) (h : HasFDerivAt (‖·‖) 
f x) : HasFDerivAt (‖·‖) (-f) (t • x)
参数：ht : t < 0；h : HasFDerivAt (‖·‖) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasFDerivAt_norm_smul`：HasFDerivAt.hasFDerivAt_norm_smul (ht
 : t != 0) (h : HasFDerivAt (‖·‖) f x) : HasFDerivAt (‖·‖) ((SignType.sign t : R
eal) • f) (t • x)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul_neg
    (ht : t < 0) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) (-f) (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne
/-
**HasFDerivAt.hasFDerivAt_norm_smul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.hasFDerivAt_norm_smul_pos (ht : 0 < t) (h : HasFDerivAt (‖·‖) 
f x) : HasFDerivAt (‖·‖) f (t • x)
参数：ht : 0 < t；h : HasFDerivAt (‖·‖) f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasFDerivAt.hasFDerivAt_norm_smul`：HasFDerivAt.hasFDerivAt_norm_smul (ht
 : t != 0) (h : HasFDerivAt (‖·‖) f x) : HasFDerivAt (‖·‖) ((SignType.sign t : R
eal) • f) (t • x)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem HasFDerivAt.hasFDerivAt_norm_smul_pos
    (ht : 0 < t) (h : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) f (t • x) := by
  simpa [ht] using h.hasFDerivAt_norm_smul ht.ne'
/-
**differentiableAt_norm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_norm_smul (ht : t != 0) : DifferentiableAt Real (‖·‖) x ↔
 DifferentiableAt Real (‖·‖) (t • x) where mp hd
参数：ht : t != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivAt.hasFDerivAt_norm_smul`：HasFDerivAt.hasFDerivAt_norm_smul (ht
 : t != 0) (h : HasFDerivAt (‖·‖) f x) : HasFDerivAt (‖·‖) ((SignType.sign t : R
eal) • f) (t • x)
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem differentiableAt_norm_smul (ht : t ≠ 0) :
    DifferentiableAt ℝ (‖·‖) x ↔ DifferentiableAt ℝ (‖·‖) (t • x) where
  mp hd := (hd.hasFDerivAt.hasFDerivAt_norm_smul ht).differentiableAt
  mpr hd := by
    convert! (hd.hasFDerivAt.hasFDerivAt_norm_smul (inv_ne_zero ht)).differentiableAt
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
/-
**DifferentiableAt.differentiableAt_norm_of_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.differentiableAt_norm_of_smul (h : DifferentiableAt Real 
(‖·‖) (t • x)) : DifferentiableAt Real (‖·‖) x
参数：h : DifferentiableAt Real (‖·‖) (t • x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_differentiableAt_norm_zero`：not_differentiableAt_norm_zero [Nontrivi
al E] : ¬DifferentiableAt Real (‖·‖) (0 : E)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasFDerivAt_of_subsingleton`：hasFDerivAt_of_subsingleton [h : Subsinglet
on E] (f : E -> F) (x : E) : HasFDerivAt f (0 : E ->L[𝕜] F) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_norm_smul`：differentiableAt_norm_smul (ht : t != 0) : D
ifferentiableAt Real (‖·‖) x ↔ DifferentiableAt Real (‖·‖) (t • x) where mp hd
-/
theorem DifferentiableAt.differentiableAt_norm_of_smul (h : DifferentiableAt ℝ (‖·‖) (t • x)) :
    DifferentiableAt ℝ (‖·‖) x := by
  obtain rfl | ht := eq_or_ne t 0
  · suffices Subsingleton E from (hasFDerivAt_of_subsingleton _ _).differentiableAt
    rw [zero_smul] at h
    by_contra!
    exact not_differentiableAt_norm_zero E h
  · exact differentiableAt_norm_smul ht |>.2 h
/-
**DifferentiableAt.fderiv_norm_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.fderiv_norm_self {x : E} (h : DifferentiableAt Real (‖·‖)
 x) : fderiv Real (‖·‖) x x = ‖x‖
参数：h : DifferentiableAt Real (‖·‖) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DifferentiableAt.lineDeriv_eq_fderiv`：DifferentiableAt.lineDeriv_eq_fder
iv (hf : DifferentiableAt 𝕜 f x) : lineDeriv 𝕜 f x v = fderiv 𝕜 f x v
· 使用定理 `lineDeriv.eq_1`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜] {F :
 Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {E : Typ
e u_…
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_mul_const`：deriv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸) :
 deriv (fun y => c y * d) x = deriv c x * d
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_abs`：differentiableAt_abs {x : Real} (hx : x != 0) : Di
fferentiableAt Real (|·|) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `DifferentiableAt.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `deriv_comp`：deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : Differ
entiableAt 𝕜 h x) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
· 使用定理 `deriv_abs`：deriv_abs (x : Real) : deriv (|·|) x = SignType.sign x
· 使用定理 `deriv_const_add_id`：deriv_const_add_id (c : 𝕜) : deriv (c + ·) x = 1
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem DifferentiableAt.fderiv_norm_self {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [← h.lineDeriv_eq_fderiv, lineDeriv]
  have (t : ℝ) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs, ← norm_smul, add_smul, one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change _root_.abs ∘ (fun t ↦ 1 + t)
    rw [deriv_comp, deriv_abs, deriv_const_add_id]
    · simp
    · exact differentiableAt_abs (by simp)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by simp)).comp _ (differentiableAt_id.const_add _)

variable (x t) in
/-
**fderiv_norm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_norm_smul : fderiv Real (‖·‖) (t • x) = (SignType.sign t : Real) • 
(fderiv Real (‖·‖) x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `hasFDerivAt_of_subsingleton`：hasFDerivAt_of_subsingleton [h : Subsinglet
on E] (f : E -> F) (x : E) : HasFDerivAt f (0 : E ->L[𝕜] F) x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `not_differentiableAt_norm_zero`：not_differentiableAt_norm_zero [Nontrivi
al E] : ¬DifferentiableAt Real (‖·‖) (0 : E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAt.hasFDerivAt_norm_smul`：HasFDerivAt.hasFDerivAt_norm_smul (ht
 : t != 0) (h : HasFDerivAt (‖·‖) f x) : HasFDerivAt (‖·‖) ((SignType.sign t : R
eal) • f) (t • x)
（共 33 条，此处仅展示前 30 条）
-/
theorem fderiv_norm_smul :
    fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x) := by
  cases subsingleton_or_nontrivial E
  · simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
        exact fderiv_zero_of_not_differentiableAt <| not_differentiableAt_norm_zero E
      · rw [(hd.hasFDerivAt.hasFDerivAt_norm_smul ht).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt DifferentiableAt.differentiableAt_norm_of_smul hd
/-
**fderiv_norm_smul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_norm_smul_pos (ht : 0 < t) : fderiv Real (‖·‖) (t • x) = fderiv Rea
l (‖·‖) x
参数：ht : 0 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `fderiv_norm_smul`：fderiv_norm_smul : fderiv Real (‖·‖) (t • x) = (SignTy
pe.sign t : Real) • (fderiv Real (‖·‖) x)
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_norm_smul_pos (ht : 0 < t) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]
/-
**fderiv_norm_smul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_norm_smul_neg (ht : t < 0) : fderiv Real (‖·‖) (t • x) = -fderiv Re
al (‖·‖) x
参数：ht : t < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `fderiv_norm_smul`：fderiv_norm_smul : fderiv Real (‖·‖) (t • x) = (SignTy
pe.sign t : Real) • (fderiv Real (‖·‖) x)
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_norm_smul_neg (ht : t < 0) :
    fderiv ℝ (‖·‖) (t • x) = -fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]
/-
**norm_fderiv_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_fderiv_norm [Nontrivial E] (h : DifferentiableAt Real (‖·‖) x) : ‖fde
riv Real (‖·‖) x‖ = 1
参数：h : DifferentiableAt Real (‖·‖) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_differentiableAt_norm_zero`：not_differentiableAt_norm_zero [Nontrivi
al E] : ¬DifferentiableAt Real (‖·‖) (0 : E)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `norm_fderiv_le_of_lipschitz`：norm_fderiv_le_of_lipschitz {f : E -> F} {x
₀ : E} {C : Real>=0} (hlip : LipschitzWith C f) : ‖fderiv 𝕜 f x₀‖ <= C
· 使用定理 `lipschitzWith_one_norm`：∀ {E : Type u_2} [inst : SeminormedAddGroup E], 
LipschitzWith 1 norm
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `DifferentiableAt.fderiv_norm_self`：DifferentiableAt.fderiv_norm_self {x 
: E} (h : DifferentiableAt Real (‖·‖) x) : fderiv Real (‖·‖) x x = ‖x‖
· 使用定理 `Real.le_norm_self`：le_norm_self (r : Real) : r <= ‖r‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem norm_fderiv_norm [Nontrivial E] (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := fun hx ↦ not_differentiableAt_norm_zero E (hx ▸ h)
  refine le_antisymm (NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm) ?_
  apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
  calc
    1 * ‖x‖ = fderiv ℝ (‖·‖) x x := by rw [one_mul, h.fderiv_norm_self]
    _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
    _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := le_opNorm _ _
