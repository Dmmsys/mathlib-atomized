/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# The open mapping theorem for holomorphic functions

This file proves the open mapping theorem for holomorphic functions, namely that an analytic
function on a preconnected set of the complex plane is either constant or open. The main step is to
show a local version of the theorem that states that if `f` is analytic at a point `z₀`, then either
it is constant in a neighborhood of `z₀` or it maps any neighborhood of `z₀` to a neighborhood of
its image `f z₀`. The results extend in higher dimension to `g : E → ℂ`.

The proof of the local version on `ℂ` goes through two main steps: first, assuming that the function
is not constant around `z₀`, use the isolated zero principle to show that `‖f z‖` is bounded below
on a small `sphere z₀ r` around `z₀`, and then use the maximum principle applied to the auxiliary
function `(fun z ↦ ‖f z - v‖)` to show that any `v` close enough to `f z₀` is in `f '' ball z₀ r`.
That second step is implemented in `DiffContOnCl.ball_subset_image_closedBall`.

## Main results

* `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` is the local version of the open mapping
  theorem around a point;
* `AnalyticOnNhd.is_constant_or_isOpen` is the open mapping theorem on a connected open set.

As an immediate corollary, we show that a holomorphic function whose real part is constant is itself
constant.
-/

public section


open Set Filter Metric Complex

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {f : ℂ → ℂ} {g : E → ℂ}
  {z₀ : ℂ} {ε r : ℝ}

/-- If the modulus of a holomorphic function `f` is bounded below by `ε` on a circle, then its range
contains a disk of radius `ε / 2`. -/
/-
**DiffContOnCl.ball_subset_image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DiffContOnCl.ball_subset_image_closedBall (h : DiffContOnCl Complex f (bal
l z₀ r)) (hr : 0 < r) (hf : forall z in sphere z₀ r, ε <= ‖f z - f z₀‖) (hz₀ : e
xistsᶠ z in 𝓝 z₀, f z != f z₀) : ball (f z₀) (ε / 2) subseteq f '' closedBall z₀
 r
参数：h : DiffContOnCl Complex f (ball z₀ r)；hr : 0 < r；hf : forall z in sphere z₀ 
r, ε <= ‖f z - f z₀‖；hz₀ : existsᶠ z in 𝓝 z₀, f z != f z₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DiffContOnCl.sub_const`：sub_const (hf : DiffContOnCl 𝕜 f s) (c : F) : Di
ffContOnCl 𝕜 (fun x => f x - c) s
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `DiffContOnCl.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3
} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedAddCommG…
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `DiffContOnCl.differentiableOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst
_2 : NormedAddCommG…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
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
（共 114 条，此处仅展示前 30 条）

--- 原说明 ---
If the modulus of a holomorphic function `f` is bounded below by `ε` on a circle
, then its range
contains a disk of radius `ε / 2`.
-/
theorem DiffContOnCl.ball_subset_image_closedBall (h : DiffContOnCl ℂ f (ball z₀ r)) (hr : 0 < r)
    (hf : ∀ z ∈ sphere z₀ r, ε ≤ ‖f z - f z₀‖) (hz₀ : ∃ᶠ z in 𝓝 z₀, f z ≠ f z₀) :
    ball (f z₀) (ε / 2) ⊆ f '' closedBall z₀ r := by
  /- This is a direct application of the maximum principle. Pick `v` close to `f z₀`, and look at
    the function `fun z ↦ ‖f z - v‖`: it is bounded below on the circle, and takes a small value
    at `z₀` so it is not constant on the disk, which implies that its infimum is equal to `0` and
    hence that `v` is in the range of `f`. -/
  rintro v hv
  have h1 : DiffContOnCl ℂ (fun z => f z - v) (ball z₀ r) := h.sub_const v
  have h2 : ContinuousOn (fun z => ‖f z - v‖) (closedBall z₀ r) :=
    continuous_norm.comp_continuousOn (closure_ball z₀ hr.ne.symm ▸ h1.continuousOn)
  have h3 : AnalyticOnNhd ℂ f (ball z₀ r) := h.differentiableOn.analyticOnNhd isOpen_ball
  have h4 : ∀ z ∈ sphere z₀ r, ε / 2 ≤ ‖f z - v‖ := fun z hz => by
    linarith [hf z hz, show ‖v - f z₀‖ < ε / 2 from mem_ball_iff_norm.1 hv,
      norm_sub_sub_norm_sub_le_norm_sub (f z) v (f z₀)]
  have h5 : ‖f z₀ - v‖ < ε / 2 := by simpa [← dist_eq_norm, dist_comm] using mem_ball.mp hv
  obtain ⟨z, hz1, hz2⟩ : ∃ z ∈ ball z₀ r, IsLocalMin (fun z => ‖f z - v‖) z :=
    exists_isLocalMin_mem_ball h2 (mem_closedBall_self hr.le) fun z hz => h5.trans_le (h4 z hz)
  refine ⟨z, ball_subset_closedBall hz1, sub_eq_zero.mp ?_⟩
  have h6 := h1.differentiableOn.eventually_differentiableAt (isOpen_ball.mem_nhds hz1)
  refine (eventually_eq_or_eq_zero_of_isLocalMin_norm h6 hz2).resolve_left fun key => ?_
  have h7 : ∀ᶠ w in 𝓝 z, f w = f z := by filter_upwards [key] with h; simp
  replace h7 : ∃ᶠ w in 𝓝[≠] z, f w = f z := (h7.filter_mono nhdsWithin_le_nhds).frequently
  have h8 : IsPreconnected (ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have h9 := h3.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const h8 hz1 h7
  have h10 : f z = f z₀ := (h9 (mem_ball_self hr)).symm
  exact not_eventually.mpr hz₀ (mem_of_superset (ball_mem_nhds z₀ hr) (h10 ▸ h9))

/-- A function `f : ℂ → ℂ` which is analytic at a point `z₀` is either constant in a neighborhood
of `z₀`, or behaves locally like an open function (in the sense that the image of every neighborhood
of `z₀` is a neighborhood of `f z₀`, as in `isOpenMap_iff_nhds_le`). For a function `f : E → ℂ`
the same result holds, see `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`. -/
/-
**AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux (hf : AnalyticAt Co
mplex f z₀) : (forallᶠ z in 𝓝 z₀, f z = f z₀) ∨ 𝓝 (f z₀) <= map f (𝓝 z₀)
参数：hf : AnalyticAt Complex f z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `AnalyticAt.eventually_eq_or_eventually_ne`：eventually_eq_or_eventually_n
e (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : (forallᶠ z in 𝓝 z₀, f z = 
g z) ∨ forallᶠ z in 𝓝[!=] z₀, f…
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_analyticAt`：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `AnalyticOnNhd.differentiableOn`：AnalyticOnNhd.differentiableOn (h : Anal
yticOnNhd 𝕜 f s) : DifferentiableOn 𝕜 f s
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `AnalyticOnNhd.continuousOn`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `lt_inf_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, a < min b
 c ↔ a < b ∧ a < c
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
A function `f : ℂ → ℂ` which is analytic at a point `z₀` is either constant in a
 neighborhood
of `z₀`, or behaves locally like an open function (in the sense that the image o
f every neighborhood
of `z₀` is a neighborhood of `f z₀`, as in `isOpenMap_iff_nhds_le`). For a funct
ion `f : E → ℂ`
the same result holds, see `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`.
-/
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux (hf : AnalyticAt ℂ f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = f z₀) ∨ 𝓝 (f z₀) ≤ map f (𝓝 z₀) := by
  /- The function `f` is analytic in a neighborhood of `z₀`; by the isolated zeros principle, if `f`
    is not constant in a neighborhood of `z₀`, then it is nonzero, and therefore bounded below, on
    every small enough circle around `z₀` and then `DiffContOnCl.ball_subset_image_closedBall`
    provides an explicit ball centered at `f z₀` contained in the range of `f`. -/
  refine or_iff_not_imp_left.mpr fun h => ?_
  refine (nhds_basis_ball.le_basis_iff (nhds_basis_closedBall.map f)).mpr fun R hR => ?_
  have h1 := (hf.eventually_eq_or_eventually_ne analyticAt_const).resolve_left h
  have h2 : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z := (isOpen_analyticAt ℂ f).eventually_mem hf
  obtain ⟨ρ, hρ, h3, h4⟩ :
    ∃ ρ > 0, AnalyticOnNhd ℂ f (closedBall z₀ ρ) ∧ ∀ z ∈ closedBall z₀ ρ, z ≠ z₀ → f z ≠ f z₀ := by
    simpa only [ofPred_and, subset_inter_iff] using!
      nhds_basis_closedBall.mem_iff.mp (h2.and (eventually_nhdsWithin_iff.mp h1))
  replace h3 : DiffContOnCl ℂ f (ball z₀ ρ) :=
    ⟨h3.differentiableOn.mono ball_subset_closedBall,
      (closure_ball z₀ hρ.lt.ne.symm).symm ▸ h3.continuousOn⟩
  let r := ρ ⊓ R
  have hr : 0 < r := lt_inf_iff.mpr ⟨hρ, hR⟩
  have h5 : closedBall z₀ r ⊆ closedBall z₀ ρ := closedBall_subset_closedBall inf_le_left
  have h6 : DiffContOnCl ℂ f (ball z₀ r) := h3.mono (ball_subset_ball inf_le_left)
  have h7 : ∀ z ∈ sphere z₀ r, f z ≠ f z₀ := fun z hz =>
    h4 z (h5 (sphere_subset_closedBall hz)) (ne_of_mem_sphere hz hr.ne.symm)
  have h8 : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have h9 : ContinuousOn (fun x => ‖f x - f z₀‖) (sphere z₀ r) := continuous_norm.comp_continuousOn
    ((h6.sub_const (f z₀)).continuousOn_ball.mono sphere_subset_closedBall)
  obtain ⟨x, hx, hfx⟩ := (isCompact_sphere z₀ r).exists_isMinOn h8 h9
  refine ⟨‖f x - f z₀‖ / 2, half_pos (norm_sub_pos_iff.mpr (h7 x hx)), ?_⟩
  exact (h6.ball_subset_image_closedBall hr (fun z hz => hfx hz) (not_eventually.mp h)).trans
    (by gcongr; exact inf_le_right)

/-- The *open mapping theorem* for holomorphic functions, local version: is a function `g : E → ℂ`
is analytic at a point `z₀`, then either it is constant in a neighborhood of `z₀`, or it maps every
neighborhood of `z₀` to a neighborhood of `z₀`. For the particular case of a holomorphic function on
`ℂ`, see `AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`. -/
/-
**AnalyticAt.eventually_constant_or_nhds_le_map_nhds** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：AnalyticAt.eventually_constant_or_nhds_le_map_nhds {z₀ : E} (hg : Analytic
At Complex g z₀) : (forallᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) <= map g (𝓝 z₀)
参数：hg : AnalyticAt Complex g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `isOpen_analyticAt`：isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x }
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `AnalyticAt.comp`：AnalyticAt.comp {g : F -> G} {f : E -> F} {x : E} (hg :
 AnalyticAt 𝕜 g (f x)) (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (g ∘ f) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `AnalyticAt.add`：AnalyticAt.add (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f + g) x
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `ContinuousLinearMap.analyticAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The *open mapping theorem* for holomorphic functions, local version: is a functi
on `g : E → ℂ`
is analytic at a point `z₀`, then either it is constant in a neighborhood of `z₀
`, or it maps every
neighborhood of `z₀` to a neighborhood of `z₀`. For the particular case of a hol
omorphic function on
`ℂ`, see `AnalyticAt.eventually_constant_or_nhds_le_map_nhds_aux`.
-/
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds {z₀ : E} (hg : AnalyticAt ℂ g z₀) :
    (∀ᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) ≤ map g (𝓝 z₀) := by
  /- The idea of the proof is to use the one-dimensional version applied to the restriction of `g`
    to lines going through `z₀` (indexed by `sphere (0 : E) 1`). If the restriction is eventually
    constant along each of these lines, then the identity theorem implies that `g` is constant on
    any ball centered at `z₀` on which it is analytic, and in particular `g` is eventually constant.
    If on the other hand there is one line along which `g` is not eventually constant, then the
    one-dimensional version of the open mapping theorem can be used to conclude. -/
  let ray : E → ℂ → E := fun z t => z₀ + t • z
  let gray : E → ℂ → ℂ := fun z => g ∘ ray z
  obtain ⟨r, hr, hgr⟩ := isOpen_iff.mp (isOpen_analyticAt ℂ g) z₀ hg
  have h1 : ∀ z ∈ sphere (0 : E) 1, AnalyticOnNhd ℂ (gray z) (ball 0 r) := by
    refine fun z hz t ht => AnalyticAt.comp ?_ ?_
    · exact hgr (by simpa [ray, norm_smul, mem_sphere_zero_iff_norm.mp hz] using! ht)
    · exact analyticAt_const.add
        ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) z).analyticAt t)
  by_cases h : ∀ z ∈ sphere (0 : E) 1, ∀ᶠ t in 𝓝 0, gray z t = gray z 0
  · left
    -- If g is eventually constant along every direction, then it is eventually constant
    refine eventually_of_mem (ball_mem_nhds z₀ hr) fun z hz => ?_
    refine (eq_or_ne z z₀).casesOn (congr_arg g) fun h' => ?_
    replace h' : ‖z - z₀‖ ≠ 0 := by simpa only [Ne, norm_eq_zero, sub_eq_zero]
    let w : E := ‖z - z₀‖⁻¹ • (z - z₀)
    have h3 : ∀ t ∈ ball (0 : ℂ) r, gray w t = g z₀ := by
      have e1 : IsPreconnected (ball (0 : ℂ) r) := (convex_ball 0 r).isPreconnected
      have e2 : w ∈ sphere (0 : E) 1 := by simp [w, norm_smul, inv_mul_cancel₀ h']
      specialize h1 w e2
      apply h1.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const e1 (mem_ball_self hr)
      simpa [ray, gray] using! h w e2
    have h4 : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using! mem_ball.mp hz
    replace h4 : ↑‖z - z₀‖ ∈ ball (0 : ℂ) r := by simpa
    simpa only [ray, gray, w, smul_smul, mul_inv_cancel₀ h', one_smul, add_sub_cancel,
      Function.comp_apply, coe_smul] using! h3 (↑‖z - z₀‖) h4
  · right
    simp only [not_forall] at h
    -- Otherwise, it is open along at least one direction and that implies the result
    obtain ⟨z, hz, hrz⟩ := h
    specialize h1 z hz 0 (mem_ball_self hr)
    have h7 := h1.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hrz
    rw [show gray z 0 = g z₀ by simp [gray, ray], ← map_compose] at h7
    refine h7.trans (map_mono ?_)
    have h10 : Continuous fun t : ℂ => z₀ + t • z := by fun_prop
    simpa using! h10.tendsto 0

/-- The *open mapping theorem* for holomorphic functions, global version: if a function `g : E → ℂ`
is analytic on a connected set `U`, then either it is constant on `U`, or it is open on `U` (in the
sense that it maps any open set contained in `U` to an open set in `ℂ`). -/
/-
**AnalyticOnNhd.is_constant_or_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.is_constant_or_isOpen (hg : AnalyticOnNhd Complex g U) (hU :
 IsPreconnected U) : (exists w, forall z in U, g z = w) ∨ forall s subseteq U, I
sOpen s -> IsOpen (g '' s)
参数：hg : AnalyticOnNhd Complex g U；hU : IsPreconnected U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`：eqOn_of_preconnected
_of_eventuallyEq {f g : E -> F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U) (hg : Ana
lyticOnNhd 𝕜 g U) (hU : IsPreconnected U…
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`：AnalyticAt.eventuall
y_constant_or_nhds_le_map_nhds {z₀ : E} (hg : AnalyticAt Complex g z₀) : (forall
ᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) <= m…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
The *open mapping theorem* for holomorphic functions, global version: if a funct
ion `g : E → ℂ`
is analytic on a connected set `U`, then either it is constant on `U`, or it is 
open on `U` (in the
sense that it maps any open set contained in `U` to an open set in `ℂ`).
-/
theorem AnalyticOnNhd.is_constant_or_isOpen (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) :
    (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s) := by
  by_cases h : ∃ z₀ ∈ U, ∀ᶠ z in 𝓝 z₀, g z = g z₀
  · obtain ⟨z₀, hz₀, h⟩ := h
    exact Or.inl ⟨g z₀, hg.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hU hz₀ h⟩
  · simp only [not_exists, not_and] at h
    refine Or.inr fun s hs1 hs2 => isOpen_iff_mem_nhds.mpr ?_
    rintro z ⟨w, hw1, rfl⟩
    exact (hg w (hs1 hw1)).eventually_constant_or_nhds_le_map_nhds.resolve_left (h w (hs1 hw1))
        (image_mem_map (hs2.mem_nhds hw1))
/-
**AnalyticOnNhd.is_constant_or_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.is_constant_or_isOpenMap (hg : AnalyticOnNhd Complex g .univ
) : (exists w, forall z, g z = w) ∨ IsOpenMap g
参数：hg : AnalyticOnNhd Complex g .univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `AnalyticOnNhd.is_constant_or_isOpen`：AnalyticOnNhd.is_constant_or_isOpen
 (hg : AnalyticOnNhd Complex g U) (hU : IsPreconnected U) : (exists w, forall z 
in U, g z = w) ∨ forall s…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `NormedSpace.instPathConnectedSpace`：∀ {E : Type u_1} [inst : SeminormedA
ddCommGroup E] [NormedSpace ℝ E], PathConnectedSpace E
-/
theorem AnalyticOnNhd.is_constant_or_isOpenMap (hg : AnalyticOnNhd ℂ g .univ) :
    (∃ w, ∀ z, g z = w) ∨ IsOpenMap g :=
  (hg.is_constant_or_isOpen PreconnectedSpace.isPreconnected_univ).imp
    (fun ⟨w, eq⟩ ↦ ⟨w, fun z ↦ eq z ⟨⟩⟩) (· · <| subset_univ _)

/-!
## Holomorphic Functions with Constant Real or Imaginary Part
-/

/--
Corollary to the open mapping theorem: A holomorphic function whose real part is constant is itself
constant.
-/
/-
**AnalyticOnNhd.eq_const_of_re_eq_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eq_const_of_re_eq_const {U : Set Complex} {c₀ : Real} (h₁f :
 AnalyticOnNhd Complex f U) (h₂f : forall x in U, (f x).re = c₀) (h₁U : IsOpen U
) (h₂U : IsConnected U) : exists c, forall x in U, f x = c
参数：h₁f : AnalyticOnNhd Complex f U；h₂f : forall x in U, (f x).re = c₀；h₁U : IsOp
en U；h₂U : IsConnected U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p

--- 原说明 ---
Corollary to the open mapping theorem: A holomorphic function whose real part is
 constant is itself
constant.
-/
theorem AnalyticOnNhd.eq_const_of_re_eq_const {U : Set ℂ} {c₀ : ℝ} (h₁f : AnalyticOnNhd ℂ f U)
    (h₂f : ∀ x ∈ U, (f x).re = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    ∃ c, ∀ x ∈ U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : ℝ), (by aesop : (re '' f '' U) = { c₀ }), isOpenMap_re
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

/--
Corollary to the open mapping theorem: A holomorphic function whose real part is constant is itself
constant.
-/
/-
**AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const {U : Set Complex} {c₀ :
 Real} (h₁f : AnalyticOnNhd Complex f U) (h₂f : forall x in U, (f x).re = c₀) (h
₁U : IsOpen U) (h₂U : IsConnected U) : exists (c : Real), forall x in U, f x = c
₀ + c * I
参数：h₁f : AnalyticOnNhd Complex f U；h₂f : forall x in U, (f x).re = c₀；h₁U : IsOp
en U；h₂U : IsConnected U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eq_const_of_re_eq_const`：AnalyticOnNhd.eq_const_of_re_eq_c
onst {U : Set Complex} {c₀ : Real} (h₁f : AnalyticOnNhd Complex f U) (h₂f : fora
ll x in U, (f x).re = c₀) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Corollary to the open mapping theorem: A holomorphic function whose real part is
 constant is itself
constant.
-/
theorem AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const {U : Set ℂ} {c₀ : ℝ}
    (h₁f : AnalyticOnNhd ℂ f U) (h₂f : ∀ x ∈ U, (f x).re = c₀) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    ∃ (c : ℝ), ∀ x ∈ U, f x = c₀ + c * I := by
  obtain ⟨cc, hcc⟩ := eq_const_of_re_eq_const h₁f h₂f h₁U h₂U
  use cc.im
  simp_rw [Complex.ext_iff]
  aesop

/--
Corollary to the open mapping theorem: A holomorphic function whose imaginary part is constant is
itself constant.
-/
/-
**AnalyticOnNhd.eq_const_of_im_eq_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.eq_const_of_im_eq_const {U : Set Complex} {c₀ : Real} (h₁f :
 AnalyticOnNhd Complex f U) (h₂f : forall x in U, (f x).im = c₀) (h₁U : IsOpen U
) (h₂U : IsConnected U) : exists c, forall x in U, f x = c
参数：h₁f : AnalyticOnNhd Complex f U；h₂f : forall x in U, (f x).im = c₀；h₁U : IsOp
en U；h₂U : IsConnected U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p

--- 原说明 ---
Corollary to the open mapping theorem: A holomorphic function whose imaginary pa
rt is constant is
itself constant.
-/
theorem AnalyticOnNhd.eq_const_of_im_eq_const {U : Set ℂ} {c₀ : ℝ} (h₁f : AnalyticOnNhd ℂ f U)
    (h₂f : ∀ x ∈ U, (f x).im = c₀) (h₁U : IsOpen U) (h₂U : IsConnected U) :
    ∃ c, ∀ x ∈ U, f x = c := by
  obtain ⟨z₀, _⟩ := h₂U.nonempty
  by_contra h₅
  grind [not_isOpen_singleton (c₀ : ℝ), (by aesop : (im '' f '' U) = { c₀ }), isOpenMap_im
    (f '' U) ((h₁f.is_constant_or_isOpen h₂U.isPreconnected).resolve_left h₅ U (by tauto) h₁U)]

/--
Corollary to the open mapping theorem: A holomorphic function whose imaginary part is constant is
itself constant.
-/
/-
**AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const {U : Set Complex} {c₀ :
 Real} (h₁f : AnalyticOnNhd Complex f U) (h₂f : forall x in U, (f x).im = c₀) (h
₁U : IsOpen U) (h₂U : IsConnected U) : exists (c : Real), forall x in U, f x = c
 + c₀ * I
参数：h₁f : AnalyticOnNhd Complex f U；h₂f : forall x in U, (f x).im = c₀；h₁U : IsOp
en U；h₂U : IsConnected U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eq_const_of_im_eq_const`：AnalyticOnNhd.eq_const_of_im_eq_c
onst {U : Set Complex} {c₀ : Real} (h₁f : AnalyticOnNhd Complex f U) (h₂f : fora
ll x in U, (f x).im = c₀) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Corollary to the open mapping theorem: A holomorphic function whose imaginary pa
rt is constant is
itself constant.
-/
theorem AnalyticOnNhd.eq_const_add_im_mul_I_of_re_eq_const {U : Set ℂ} {c₀ : ℝ}
    (h₁f : AnalyticOnNhd ℂ f U) (h₂f : ∀ x ∈ U, (f x).im = c₀) (h₁U : IsOpen U)
    (h₂U : IsConnected U) :
    ∃ (c : ℝ), ∀ x ∈ U, f x = c + c₀ * I := by
  obtain ⟨cc, hcc⟩ := AnalyticOnNhd.eq_const_of_im_eq_const h₁f h₂f h₁U h₂U
  use cc.re
  simp_rw [Complex.ext_iff]
  aesop

/-!
## Holomorphic Functions as Open Quotient Maps
-/

/-
**Polynomial.C_eq_or_isOpenQuotientMap_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.C_eq_or_isOpenQuotientMap_eval (p : Polynomial Complex) : (exis
ts x, C x = p) ∨ IsOpenQuotientMap p.eval
参数：p : Polynomial Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `AnalyticOnNhd.is_constant_or_isOpenMap`：AnalyticOnNhd.is_constant_or_isO
penMap (hg : AnalyticOnNhd Complex g .univ) : (exists w, forall z, g z = w) ∨ Is
OpenMap g
· 使用定理 `AnalyticOnNhd.eval_polynomial`：AnalyticOnNhd.eval_polynomial {A} [Normed
CommRing A] [NormedAlgebra 𝕜 A] (p : A[X]) : AnalyticOnNhd 𝕜 (eval · p) Set.univ
· 使用定理 `Polynomial.funext`：funext [Infinite R] {p q : R[X]} (ext : forall r : R,
 p.eval r = q.eval r) : p = q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgClosed.instInfinite`：∀ {K : Type u_1} [inst : Field K] [IsAlgClosed
 K], Infinite K
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsAlgClosed.eval_surjective`：eval_surjective {p : M[X]} (hp : p.natDegre
e != 0) : Function.Surjective p.eval
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `Polynomial.continuous_aeval`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Topologica
lSpace A] [IsTopo…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α

--- 原说明 ---
## Holomorphic Functions as Open Quotient Maps
-/
theorem Polynomial.C_eq_or_isOpenQuotientMap_eval (p : Polynomial ℂ) :
    (∃ x, C x = p) ∨ IsOpenQuotientMap p.eval := by
  refine or_iff_not_imp_left.mpr fun h ↦ ?_
  obtain ⟨x, eq⟩ | hp := (AnalyticOnNhd.eval_polynomial p).is_constant_or_isOpenMap
  · exact (h ⟨x, funext <| by simpa [eq_comm (a := x)]⟩).elim
  · exact ⟨IsAlgClosed.eval_surjective <| natDegree_eq_zero.not.mpr h, p.continuous_aeval, hp⟩
/-
**Polynomial.isOpenQuotientMap_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.isOpenQuotientMap_eval (p : Polynomial Complex) (hp : p.natDegr
ee != 0) : IsOpenQuotientMap p.eval
参数：p : Polynomial Complex；hp : p.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Polynomial.C_eq_or_isOpenQuotientMap_eval`：Polynomial.C_eq_or_isOpenQuot
ientMap_eval (p : Polynomial Complex) : (exists x, C x = p) ∨ IsOpenQuotientMap 
p.eval
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
-/
theorem Polynomial.isOpenQuotientMap_eval (p : Polynomial ℂ) (hp : p.natDegree ≠ 0) :
    IsOpenQuotientMap p.eval :=
  p.C_eq_or_isOpenQuotientMap_eval.resolve_left <| natDegree_eq_zero.not.mp hp

namespace Complex

/-
**Complex.isOpenQuotientMap_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isOpenQuotientMap_pow (n : Nat) [NeZero n] : IsOpenQuotientMap (· ^ n : Co
mplex -> Complex)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.isOpenQuotientMap_eval`：Polynomial.isOpenQuotientMap_eval (p 
: Polynomial Complex) (hp : p.natDegree != 0) : IsOpenQuotientMap p.eval
· 使用引理 `Polynomial.natDegree_pow`：natDegree_pow (p : R[X]) (n : Nat) : natDegree
 (p ^ n) = n * natDegree p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem isOpenQuotientMap_pow (n : ℕ) [NeZero n] : IsOpenQuotientMap (· ^ n : ℂ → ℂ) := by
  convert! Polynomial.isOpenQuotientMap_eval (.X ^ n) _
  · simp
  · simpa using NeZero.ne n
/-
**Complex.isOpenQuotientMap_pow_compl_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isOpenQuotientMap_pow_compl_zero (n : Nat) [NeZero n] : IsOpenQuotientMap 
fun z : {z : Complex // z != 0} => (⟨z ^ n, pow_ne_zero n z.2⟩ : {z : Complex //
 z != 0}) where surjective z
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsOpenQuotientMap.surjective`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsOpenQuotientMap f →
 Function.Surjecti…
· 使用定理 `Complex.isOpenQuotientMap_pow`：isOpenQuotientMap_pow (n : Nat) [NeZero n
] : IsOpenQuotientMap (· ^ n : Complex -> Complex)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
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
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : T
opologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
（共 32 条，此处仅展示前 30 条）
-/
theorem isOpenQuotientMap_pow_compl_zero (n : ℕ) [NeZero n] :
    IsOpenQuotientMap
      fun z : {z : ℂ // z ≠ 0} ↦ (⟨z ^ n, pow_ne_zero n z.2⟩ : {z : ℂ // z ≠ 0}) where
  surjective z := have ⟨w, h⟩ := (isOpenQuotientMap_pow n).surjective z
    ⟨⟨w, by rintro rfl; exact z.2 (by simpa [zero_pow (NeZero.ne n)] using h.symm)⟩, Subtype.ext h⟩
  continuous := by fun_prop
  isOpenMap := (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr <|
    (isOpenQuotientMap_pow n).isOpenMap.comp isClosed_singleton.1.isOpenMap_subtype_val

set_option backward.isDefEq.respectTransparency.types false in
/-
**Complex.isOpenQuotientMap_zpow_compl_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isOpenQuotientMap_zpow_compl_zero (n : Int) [NeZero n] : IsOpenQuotientMap
 fun z : {z : Complex // z != 0} => (⟨z ^ n, zpow_ne_zero n z.2⟩ : {z : Complex 
// z != 0})
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Complex.isOpenQuotientMap_pow_compl_zero`：isOpenQuotientMap_pow_compl_ze
ro (n : Nat) [NeZero n] : IsOpenQuotientMap fun z : {z : Complex // z != 0} => (
⟨z ^ n, pow_ne_zero n z.2⟩ : {…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOpenQuotientMap.comp`：comp {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf
 : IsOpenQuotientMap f) : IsOpenQuotientMap (g ∘ f)
· 使用定理 `Homeomorph.isOpenQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   IsOpenQuotientMa
p ⇑h
-/
theorem isOpenQuotientMap_zpow_compl_zero (n : ℤ) [NeZero n] :
    IsOpenQuotientMap
      fun z : {z : ℂ // z ≠ 0} ↦ (⟨z ^ n, zpow_ne_zero n z.2⟩ : {z : ℂ // z ≠ 0}) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · have : NeZero n := ⟨Nat.cast_ne_zero.mp (NeZero.ne (n : ℤ))⟩
    exact isOpenQuotientMap_pow_compl_zero n
  · have : NeZero n := ⟨Nat.cast_ne_zero.mp <| neg_ne_zero.mp (NeZero.ne (-n : ℤ))⟩
    convert! (isOpenQuotientMap_pow_compl_zero n).comp (Homeomorph.inv₀ ℂ).isOpenQuotientMap
    simp [Homeomorph.inv₀]

end Complex

