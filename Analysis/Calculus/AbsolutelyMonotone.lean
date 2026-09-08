/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Absolutely monotone functions

A function `f : ℝ → ℝ` is *absolutely monotone* on a set `s` if its iterated derivatives are all
nonnegative on `s`.

## Main definitions

* `AbsolutelyMonotoneOn` — there exists a Taylor series for `f` on `s` with nonnegative terms at
  each point of `s`.

## Main results

* `AbsolutelyMonotoneOn.contDiffOn` — the function is `C^∞` on `s`.
* `AbsolutelyMonotoneOn.of_contDiff` — a globally `C^∞` function with nonnegative iterated
  derivatives on `s` is absolutely monotone on `s`.
* `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` — under `UniqueDiffOn`, the definition
  is equivalent to `f` being `C^∞` on `s` with every iterated derivative within `s` nonnegative.
* `AbsolutelyMonotoneOn.add` — closure under addition.
* `AbsolutelyMonotoneOn.smul` — closure under nonnegative scalar multiplication.

## Implementation

The precise definition is phrased via the existence of a Taylor series with nonnegative terms
(`HasFTaylorSeriesUpToOn`) rather than via `iteratedDerivWithin`. This avoids forcing a
`UniqueDiffOn s` hypothesis on every result: without `UniqueDiffOn`, "the" iterated derivative
within `s` is not canonical, but the existence of a Taylor series is intrinsic to `f` and `s`.
When `s` does satisfy `UniqueDiffOn`, the condition reduces to `f` being `C^∞` on `s` with every
iterated derivative within `s` nonnegative.

## References

* [D. V. Widder, *The Laplace Transform*][widder1941]
-/

public section

open Set Filter
open scoped ContDiff

/-- A function `f : ℝ → ℝ` is **absolutely monotone on a set `s`** if, heuristically, all
iterated derivatives of `f` on `s` are nonnegative. For technical reasons related to unique
differentiability, the precise definition is phrased as the existence of a Taylor series for
`f` on `s` whose `n`th term, evaluated at the all-ones tuple, is nonnegative for every `n` and
every `x ∈ s`. See `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` for the equivalence
under `UniqueDiffOn`. -/
/-
**AbsolutelyMonotoneOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AbsolutelyMonotoneOn (f : Real -> Real) (s : Set Real) : Prop
参数：f : Real -> Real；s : Set Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : ℝ → ℝ` is **absolutely monotone on a set `s`** if, heuristically
, all
iterated derivatives of `f` on `s` are nonnegative. For technical reasons relate
d to unique
differentiability, the precise definition is phrased as the existence of a Taylo
r series for
`f` on `s` whose `n`th term, evaluated at the all-ones tuple, is nonnegative for
 every `n` and
every `x ∈ s`. See `AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg` for the
 equivalence
under `UniqueDiffOn`.
-/
def AbsolutelyMonotoneOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ p : ℝ → FormalMultilinearSeries ℝ ℝ ℝ,
    HasFTaylorSeriesUpToOn ∞ f p s ∧
    ∀ (n : ℕ) ⦃x : ℝ⦄, x ∈ s → 0 ≤ p x n fun _ ↦ (1 : ℝ)

namespace AbsolutelyMonotoneOn

variable {f g : ℝ → ℝ} {s : Set ℝ}

/-- An absolutely monotone function on `s` is `C^∞` on `s`. -/
/-
**AbsolutelyMonotoneOn.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyMonotoneO
n`。
形式化陈述：contDiffOn (hf : AbsolutelyMonotoneOn f s) : ContDiffOn Real ∞ f s
参数：hf : AbsolutelyMonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpToOn.contDiffOn`：HasFTaylorSeriesUpToOn.contDiffOn {n 
: Nat∞} {f' : E -> FormalMultilinearSeries 𝕜 E F} (hf : HasFTaylorSeriesUpToOn n
 f f' s) : ContDiffOn 𝕜…

--- 原说明 ---
An absolutely monotone function on `s` is `C^∞` on `s`.
-/
theorem contDiffOn (hf : AbsolutelyMonotoneOn f s) : ContDiffOn ℝ ∞ f s := by
  obtain ⟨_, hp, _⟩ := hf
  exact hp.contDiffOn

/-- A globally `C^∞` function whose iterated derivatives are nonnegative on `s` is absolutely
monotone on `s`. The set `s` need *not* satisfy `UniqueDiffOn`. -/
/-
**AbsolutelyMonotoneOn.of_contDiff** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyMonotone
On`。
形式化陈述：of_contDiff (hf : ContDiff Real ∞ f) (h : forall n : Nat, forall x in s, 0
 <= iteratedDeriv n f x) : AbsolutelyMonotoneOn f s
参数：hf : ContDiff Real ∞ f；h : forall n : Nat, forall x in s, 0 <= iteratedDeriv 
n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn`：HasFTaylorSeriesUpTo.hasFTa
ylorSeriesUpToOn (h : HasFTaylorSeriesUpTo n f p) (s : Set E) : HasFTaylorSeries
UpToOn n f p s
· 使用定理 `ContDiff.ftaylorSeries`：ContDiff.ftaylorSeries (hf : ContDiff 𝕜 n f) : H
asFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f)
· 使用定理 `iteratedDeriv_eq_iteratedFDeriv`：iteratedDeriv_eq_iteratedFDeriv : itera
tedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1

--- 原说明 ---
A globally `C^∞` function whose iterated derivatives are nonnegative on `s` is a
bsolutely
monotone on `s`. The set `s` need *not* satisfy `UniqueDiffOn`.
-/
theorem of_contDiff (hf : ContDiff ℝ ∞ f) (h : ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDeriv n f x) :
    AbsolutelyMonotoneOn f s := by
  refine ⟨ftaylorSeries ℝ f, (hf.ftaylorSeries).hasFTaylorSeriesUpToOn s, fun n x hx => ?_⟩
  exact iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ) (f := f) ▸ h n x hx

/-- Under `UniqueDiffOn`, a Taylor witness for an absolutely monotone function agrees with
`iteratedDerivWithin`, so the latter is nonnegative on `s`. -/
/-
**AbsolutelyMonotoneOn.iteratedDerivWithin_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Abs
olutelyMonotoneOn`。
形式化陈述：iteratedDerivWithin_nonneg (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDif
fOn Real s) (n : Nat) {x : Real} (hx : x in s) : 0 <= iteratedDerivWithin n f s 
x
参数：hf : AbsolutelyMonotoneOn f s；hs : UniqueDiffOn Real s；n : Nat；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_iteratedFDerivWithin`：iteratedDerivWithin_eq_iter
atedFDerivWithin : iteratedDerivWithin n f s x = (iteratedFDerivWithin 𝕜 n f s x
 : (Fin n -> 𝕜) -> F) fun _ : Fin…

--- 原说明 ---
Under `UniqueDiffOn`, a Taylor witness for an absolutely monotone function agree
s with
`iteratedDerivWithin`, so the latter is nonnegative on `s`.
-/
theorem iteratedDerivWithin_nonneg (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn ℝ s)
    (n : ℕ) {x : ℝ} (hx : x ∈ s) : 0 ≤ iteratedDerivWithin n f s x := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  have heq : p x n = iteratedFDerivWithin ℝ n f s x :=
    hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) hs hx
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, ← heq]
  exact hp_nn n hx

/-- Under `UniqueDiffOn`, a function is absolutely monotone on `s` iff it is `C^∞` on `s` with
every iterated derivative within `s` nonnegative. -/
/-
**AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg** 是 Mathlib 中的一个定理，位于命名空间 
`AbsolutelyMonotoneOn`。
形式化陈述：iff_iteratedDerivWithin_nonneg (hs : UniqueDiffOn Real s) : AbsolutelyMono
toneOn f s ↔ ContDiffOn Real ∞ f s ∧ forall n : Nat, forall x in s, 0 <= iterate
dDerivWithin n f s x
参数：hs : UniqueDiffOn Real s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsolutelyMonotoneOn.contDiffOn`：contDiffOn (hf : AbsolutelyMonotoneOn f
 s) : ContDiffOn Real ∞ f s
· 使用定理 `AbsolutelyMonotoneOn.iteratedDerivWithin_nonneg`：iteratedDerivWithin_non
neg (hf : AbsolutelyMonotoneOn f s) (hs : UniqueDiffOn Real s) (n : Nat) {x : Re
al} (hx : x in s) : 0 <= iteratedDeri…
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `iteratedDerivWithin_eq_iteratedFDerivWithin`：iteratedDerivWithin_eq_iter
atedFDerivWithin : iteratedDerivWithin n f s x = (iteratedFDerivWithin 𝕜 n f s x
 : (Fin n -> 𝕜) -> F) fun _ : Fin…

--- 原说明 ---
Under `UniqueDiffOn`, a function is absolutely monotone on `s` iff it is `C^∞` o
n `s` with
every iterated derivative within `s` nonnegative.
-/
theorem iff_iteratedDerivWithin_nonneg (hs : UniqueDiffOn ℝ s) :
    AbsolutelyMonotoneOn f s ↔
      ContDiffOn ℝ ∞ f s ∧ ∀ n : ℕ, ∀ x ∈ s, 0 ≤ iteratedDerivWithin n f s x := by
  refine ⟨fun hf => ⟨hf.contDiffOn, fun n x hx => hf.iteratedDerivWithin_nonneg hs n hx⟩, ?_⟩
  rintro ⟨hcont, hnn⟩
  refine ⟨ftaylorSeriesWithin ℝ f s, hcont.ftaylorSeriesWithin hs, fun n x hx => ?_⟩
  exact iteratedDerivWithin_eq_iteratedFDerivWithin (𝕜 := ℝ) (f := f) (s := s) ▸ hnn n x hx

/-! ### Closure properties -/

/-- The sum of two absolutely monotone functions is absolutely monotone. -/
/-
**AbsolutelyMonotoneOn.add** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyMonotoneOn`。
形式化陈述：add (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) : Abso
lutelyMonotoneOn (f + g) s
参数：hf : AbsolutelyMonotoneOn f s；hg : AbsolutelyMonotoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpToOn.add`：HasFTaylorSeriesUpToOn.add {n : Nat∞ω} {q g}
 (hf : HasFTaylorSeriesUpToOn n f p s) (hg : HasFTaylorSeriesUpToOn n g q s) : H
asFTaylorSeriesU…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The sum of two absolutely monotone functions is absolutely monotone.
-/
theorem add (hf : AbsolutelyMonotoneOn f s) (hg : AbsolutelyMonotoneOn g s) :
    AbsolutelyMonotoneOn (f + g) s := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  obtain ⟨q, hq, hq_nn⟩ := hg
  refine ⟨p + q, hp.add hq, fun n x hx => ?_⟩
  simp only [Pi.add_apply, FormalMultilinearSeries.add_apply, add_apply]
  exact add_nonneg (hp_nn n hx) (hq_nn n hx)

/-- A nonnegative scalar multiple of an absolutely monotone function is absolutely monotone. -/
/-
**AbsolutelyMonotoneOn.smul** 是 Mathlib 中的一个定理，位于命名空间 `AbsolutelyMonotoneOn`。
形式化陈述：smul {c : Real} (hf : AbsolutelyMonotoneOn f s) (hc : 0 <= c) : Absolutely
MonotoneOn (c • f) s
参数：hf : AbsolutelyMonotoneOn f s；hc : 0 <= c。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FunLike.coe_smul`：coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (
n : M) (f : F) : ↑(n • f) = n • (f : α -> β)
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`：HasFTaylorSeriesUpToOn.
continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] G) (hf : HasFTaylorSeriesUpTo
On n f p s) : HasFTaylorSeriesUpToOn …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
A nonnegative scalar multiple of an absolutely monotone function is absolutely m
onotone.
-/
theorem smul {c : ℝ} (hf : AbsolutelyMonotoneOn f s) (hc : 0 ≤ c) :
    AbsolutelyMonotoneOn (c • f) s := by
  obtain ⟨p, hp, hp_nn⟩ := hf
  -- Witness: post-composition by the CLM `y ↦ c * y`.
  set T : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ with hT
  have hcomp : (T ∘ f) = c • f := by ext x; simp [hT, smul_eq_mul]
  refine ⟨_, hcomp ▸ hp.continuousLinearMap_comp T, fun n x hx => ?_⟩
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, hT,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  exact mul_nonneg hc (hp_nn n hx)

end AbsolutelyMonotoneOn

