/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Data.Fintype.Perm

/-!
# The iterated derivative of an analytic function

If a function is analytic, written as `f (x + y) = ∑ pₙ (y, ..., y)` then its `n`-th iterated
derivative at `x` is given by `(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum
is over all permutations of `{1, ..., n}`. In particular, it is symmetric.

This generalizes the result of `HasFPowerSeriesOnBall.factorial_smul` giving
`D^n f (v, ..., v) = n! * pₙ (v, ..., v)`.

## Main result

* `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum` shows that
  `iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i))`,
  when `f` has `p` as power series within the set `s` on the ball `B (x, r)`.
* `ContDiffAt.iteratedFDeriv_comp_perm` proves the symmetry of the iterated derivative of an
  analytic function, in the form `iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v`
  for any permutation `σ` of `Fin n`.

Versions within sets are also given.

## Implementation

To prove the formula for the iterated derivative, we decompose an analytic function as
the sum of `fun y ↦ pₙ (y, ..., y)` and the rest. For the former, its iterated derivative follows
from the formula for iterated derivatives of multilinear maps
(see `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`). For the latter, we show by
induction on `n` that if the `n`-th term in a power series is zero, then the `n`-th iterated
derivative vanishes (see `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero`).

All these results are proved assuming additionally that the function is analytic on the relevant
set (which does not follow from the fact that the function has a power series, if the target space
is not complete). This makes it possible to avoid all completeness assumptions in the final
statements. When needed, we give versions of some statements assuming completeness and dropping
analyticity, for ease of use.
-/

@[expose] public section

open scoped ENNReal Topology ContDiff
open Equiv Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}

/-- Formal multilinear series associated to the iterated derivative, defined by iterating
`p ↦ p.derivSeries` and currying suitably. It is defined so that, if a function has `p` as a power
series, then its iterated derivative of order `k` has `p.iteratedFDerivSeries k` as a power
series. -/
/-
**FormalMultilinearSeries.iteratedFDerivSeries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FormalMultilinearSeries.iteratedFDerivSeries (p : FormalMultilinearSeries 
𝕜 E F) (k : Nat) : FormalMultilinearSeries 𝕜 E (E [×k]->L[𝕜] F)
参数：p : FormalMultilinearSeries 𝕜 E F；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formal multilinear series associated to the iterated derivative, defined by iter
ating
`p ↦ p.derivSeries` and currying suitably. It is defined so that, if a function 
has `p` as a power
series, then its iterated derivative of order `k` has `p.iteratedFDerivSeries k`
 as a power
series.
-/
noncomputable def FormalMultilinearSeries.iteratedFDerivSeries
    (p : FormalMultilinearSeries 𝕜 E F) (k : ℕ) :
    FormalMultilinearSeries 𝕜 E (E [×k]→L[𝕜] F) :=
  match k with
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries p
  | (k + 1) => (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.compFormalMultilinearSeries
      (p.iteratedFDerivSeries k).derivSeries

/-- If a function has a power series on a ball, then so do its iterated derivatives. -/
/-
**HasFPowerSeriesWithinOnBall.iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 `Ha
sFPowerSeriesWithinOnBall`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {p : FormalMultili
nearSeries 𝕜 E F} {s : Set E} {x : E} {r : ENNReal},   HasFPowerSeriesWithinOnBa
ll f p s x r →     AnalyticOn 𝕜 f s →       ∀ (k : ℕ),         UniqueDiffOn 𝕜 s 
→           x ∈ s → HasFPowerSeriesWithinOnBall (iteratedFDerivWithin 𝕜 k f s) (
p.iteratedFDerivSeries k) s x r
参数：k : ℕ；iteratedFDerivWithin 𝕜 k f s；p.iteratedFDerivSeries k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall`：ContinuousLinearMa
p.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G) (h : HasFPowerSeriesWithinOn
Ball f p s x r) : HasFPowerSeriesWithinOnB…
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_succ_eq_comp_left`：iteratedFDerivWithin_succ_eq_com
p_left {n : Nat} : iteratedFDerivWithin 𝕜 (n + 1) f s = (continuousMultilinearCu
rryLeftEquiv 𝕜 (fun _ : Fin …
· 使用定理 `HasFPowerSeriesWithinOnBall.fderivWithin_of_mem_of_analyticOn`：∀ {𝕜 : Ty
pe u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u} [inst_1 : NormedAddCommG
roup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type v} […
· 使用定理 `AnalyticOn.iteratedFDerivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {F : Type v} […

--- 原说明 ---
If a function has a power series on a ball, then so do its iterated derivatives.
-/
protected theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (k : ℕ) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    HasFPowerSeriesWithinOnBall (iteratedFDerivWithin 𝕜 k f s)
      (p.iteratedFDerivSeries k) s x r := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall h
  | succ k ih =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) ↦ E) F).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall
        (ih.fderivWithin_of_mem_of_analyticOn (h'.iteratedFDerivWithin hs _) hs hx)
/-
**FormalMultilinearSeries.iteratedFDerivSeries_eq_zero** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：FormalMultilinearSeries.iteratedFDerivSeries_eq_zero {k n : Nat} (h : p (n
 + k) = 0) : p.iteratedFDerivSeries k n = 0
参数：h : p (n + k) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用引理 `FormalMultilinearSeries.congr_zero`：congr_zero (p : FormalMultilinearSer
ies 𝕜 E F) {k l : Nat} (h : k = l) (h' : p k = 0) : p l = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.derivSeries_eq_zero`：derivSeries_eq_zero {n : Na
t} (hp : p (n + 1) = 0) : p.derivSeries n = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_add_eq_add_succ`：∀ (a b : ℕ), a.succ + b = a + b.succ
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
-/
lemma FormalMultilinearSeries.iteratedFDerivSeries_eq_zero {k n : ℕ}
    (h : p (n + k) = 0) : p.iteratedFDerivSeries k n = 0 := by
  induction k generalizing n with
  | zero =>
    ext
    have : p n = 0 := p.congr_zero rfl h
    simp [FormalMultilinearSeries.iteratedFDerivSeries, this]
  | succ k ih =>
    ext
    simp only [iteratedFDerivSeries, Nat.succ_eq_add_one,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
      continuousMultilinearCurryLeftEquiv_symm_apply, _root_.zero_apply,
      derivSeries_eq_zero _ (ih (p.congr_zero (Nat.succ_add_eq_add_succ _ _).symm h))]

/-- If the `n`-th term in a power series is zero, then the `n`-th derivative of the corresponding
function vanishes. -/
/-
**HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero (h : HasFPowerSer
iesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s) (hu : UniqueDiffOn 𝕜 s) (hx :
 x in s) {n : Nat} (hn : p n = 0) : iteratedFDerivWithin 𝕜 n f s x = 0
参数：h : HasFPowerSeriesWithinOnBall f p s x r；h' : AnalyticOn 𝕜 f s；hu : UniqueDi
ffOn 𝕜 s；hx : x in s；hn : p n = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesWithinOnBall.coeff_zero`：HasFPowerSeriesWithinOnBall.coef
f_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r) (v : Fin 0 -> E) : pf 0 v =
 f x
· 使用定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FormalMultilinearSeries.iteratedFDerivSeries_eq_zero`：FormalMultilinearS
eries.iteratedFDerivSeries_eq_zero {k n : Nat} (h : p (n + k) = 0) : p.iteratedF
DerivSeries k n = 0
· 使用引理 `FormalMultilinearSeries.congr_zero`：congr_zero (p : FormalMultilinearSer
ies 𝕜 E F) {k l : Nat} (h : k = l) (h' : p k = 0) : p l = 0
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…

--- 原说明 ---
If the `n`-th term in a power series is zero, then the `n`-th derivative of the 
corresponding
function vanishes.
-/
lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_zero
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (hn : p n = 0) :
    iteratedFDerivWithin 𝕜 n f s x = 0 := by
  have : iteratedFDerivWithin 𝕜 n f s x = p.iteratedFDerivSeries n 0 (fun _ ↦ 0) :=
    ((h.iteratedFDerivWithin h' n hu hx).coeff_zero _).symm
  rw [this, p.iteratedFDerivSeries_eq_zero (p.congr_zero (Nat.zero_add n).symm hn), zero_apply]
/-
**ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal {n : Nat} (f : E [×n
]->L[𝕜] F) (x : E) (v : Fin n -> E) : iteratedFDeriv 𝕜 n (fun x => f (fun _ => x
)) x v = ∑ σ : Perm (Fin n), f (fun i => v (σ i))
参数：f : E [×n]->L[𝕜] F；x : E；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `ContinuousLinearMap.iteratedFDeriv_comp_right`：ContinuousLinearMap.itera
tedFDeriv_comp_right (g : G ->L[𝕜] E) {f : E -> F} (hf : ContDiff 𝕜 n f) (x : G)
 {i : Nat} (hi : i <= n) : iterated…
· 使用引理 `ContinuousMultilinearMap.contDiff`：contDiff : ContDiff 𝕜 n f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ContinuousMultilinearMap.iteratedFDeriv_eq`：iteratedFDeriv_eq (n : Nat) 
: iteratedFDeriv 𝕜 n f = f.iteratedFDeriv n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.iteratedFDerivComponent_apply`：∀ {𝕜 : Type u} {
ι : Type v} {E₁ : ι → Type wE₁} {G : Type wG} [inst : NontriviallyNormedField 𝕜]
   [inst_1 : (i : ι) → SeminormedAddCommGrou…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
（共 38 条，此处仅展示前 30 条）
-/
lemma ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    {n : ℕ} (f : E [×n]→L[𝕜] F) (x : E) (v : Fin n → E) :
    iteratedFDeriv 𝕜 n (fun x ↦ f (fun _ ↦ x)) x v = ∑ σ : Perm (Fin n), f (fun i ↦ v (σ i)) := by
  rw [← sum_comp (Equiv.inv (Perm (Fin n)))]
  let g : E →L[𝕜] (Fin n → E) := ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.id 𝕜 E)
  change iteratedFDeriv 𝕜 n (f ∘ g) x v = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl, f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Set.mem_range, Pi.compRightL_apply]
  rw [← sum_comp (Equiv.embeddingEquivOfFinite (Fin n))]
  congr with σ
  congr with i
  obtain ⟨y, rfl⟩ := σ.equivOfFiniteSelfEmbedding.surjective i
  simp [Function.Embedding.equivOfFiniteSelfEmbedding, g]

set_option backward.isDefEq.respectTransparency false in
/-
**HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset** 是 Mathlib 
中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    {n : ℕ} (v : Fin n → E) (h's : s ⊆ Metric.eball x r) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have I : insert x s ∩ Metric.eball x r = s := by
    rw [Set.insert_eq_of_mem hx]
    exact Set.inter_eq_left.2 h's
  have fcont : ContDiffOn 𝕜 (↑n) f s := by
    apply AnalyticOn.contDiffOn _ hs
    simpa [I] using h'
  let g : E → F := fun z ↦ p n (fun _ ↦ z - x)
  have gcont : ContDiff 𝕜 ω g := by
    apply (p n).contDiff.comp
    exact contDiff_pi.2 (fun i ↦ contDiff_id.sub contDiff_const)
  let q : FormalMultilinearSeries 𝕜 E F := fun k ↦ if h : n = k then (h ▸ p n) else 0
  have A : HasFiniteFPowerSeriesOnBall g q x (n + 1) r := by
    apply HasFiniteFPowerSeriesOnBall.mk' _ h.r_pos
    · intro y hy
      rw [Finset.sum_eq_single_of_mem n]
      · simp [q, g]
      · simp
      · intro i hi h'i
        simp [q, h'i.symm]
    · intro m hm
      have : n ≠ m := by lia
      simp [q, this]
  have B : HasFPowerSeriesWithinOnBall g q s x r :=
    A.toHasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
  have J1 : iteratedFDerivWithin 𝕜 n f s x =
      iteratedFDerivWithin 𝕜 n g s x + iteratedFDerivWithin 𝕜 n (f - g) s x := by
    have : f = g + (f - g) := by abel
    nth_rewrite 1 [this]
    rw [iteratedFDerivWithin_add_apply (gcont.of_le le_top).contDiffWithinAt
      (by exact (fcont _ hx).sub (gcont.of_le le_top).contDiffWithinAt) hs hx]
  have J2 : iteratedFDerivWithin 𝕜 n (f - g) s x = 0 := by
    apply (h.sub B).iteratedFDerivWithin_eq_zero (h'.sub ?_) hs hx
    · simp [q]
    · apply gcont.contDiffOn.analyticOn
  have J3 : iteratedFDerivWithin 𝕜 n g s x = iteratedFDeriv 𝕜 n g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs (gcont.of_le le_top).contDiffAt hx
  simp only [J1, J3, J2, add_zero]
  let g' : E → F := fun z ↦ p n (fun _ ↦ z)
  have : g = fun z ↦ g' (z - x) := rfl
  rw [this, iteratedFDeriv_comp_sub]
  exact (p n).iteratedFDeriv_comp_diagonal _ v

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
/-
**HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum (h : HasFPowerSeri
esWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : 
x in s) {n : Nat} (v : Fin n -> E) : iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Pe
rm (Fin n), p n (fun i => v (σ i))
参数：h : HasFPowerSeriesWithinOnBall f p s x r；h' : AnalyticOn 𝕜 f s；hs : UniqueDi
ffOn 𝕜 s；hx : x in s；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
· 使用定理 `Metric.mem_eball_self`：mem_eball_self (h : 0 < ε) : x in eball x ε
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.Analytic.IteratedFDeriv.0.HasFPowerSeriesWithi
nOnBall.iteratedFDerivWithin_eq_sum_of_subset`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用引理 `HasFPowerSeriesWithinOnBall.mono`：HasFPowerSeriesWithinOnBall.mono (hf :
 HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s) : HasFPowerSeriesWith
inOnBall f p t x r whe…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
If a function has a power series in a ball, then its `n`-th iterated derivative 
is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`.
-/
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum
    (h : HasFPowerSeriesWithinOnBall f p s x r) (h' : AnalyticOn 𝕜 f s)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s ∩ Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact h.mono inter_subset_left
  · exact h'.mono inter_subset_left
  · exact hs.inter Metric.isOpen_eball
  · exact ⟨hx, Metric.mem_eball_self h.r_pos⟩
  · exact inter_subset_right

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
/-
**HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum (h : HasFPowerSeriesOnBall f p
 x r) (h' : AnalyticOn 𝕜 f univ) {n : Nat} (v : Fin n -> E) : iteratedFDeriv 𝕜 n
 f x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i))
参数：h : HasFPowerSeriesOnBall f p x r；h' : AnalyticOn 𝕜 f univ；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum`：HasFPowerSeries
WithinOnBall.iteratedFDerivWithin_eq_sum (h : HasFPowerSeriesWithinOnBall f p s 
x r) (h' : AnalyticOn 𝕜 f s) (hs : UniqueDiff…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
If a function has a power series in a ball, then its `n`-th iterated derivative 
is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`.
-/
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    (h : HasFPowerSeriesOnBall f p x r) (h' : AnalyticOn 𝕜 f univ) {n : ℕ} (v : Fin n → E) :
    iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum h' uniqueDiffOn_univ (mem_univ x) v

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
/-
**HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace** 是 M
athlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace [
CompleteSpace F] (h : HasFPowerSeriesWithinOnBall f p s x r) (hs : UniqueDiffOn 
𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E) : iteratedFDerivWithin 𝕜 n f s x v
 = ∑ σ : Perm (Fin n), p n (fun i => v (σ i))
参数：h : HasFPowerSeriesWithinOnBall f p s x r；hs : UniqueDiffOn 𝕜 s；hx : x in s；v
 : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
· 使用定理 `Metric.mem_eball_self`：mem_eball_self (h : 0 < ε) : x in eball x ε
· 使用定理 `HasFPowerSeriesWithinOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.Analytic.IteratedFDeriv.0.HasFPowerSeriesWithi
nOnBall.iteratedFDerivWithin_eq_sum_of_subset`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用引理 `HasFPowerSeriesWithinOnBall.mono`：HasFPowerSeriesWithinOnBall.mono (hf :
 HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s) : HasFPowerSeriesWith
inOnBall f p t x r whe…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `HasFPowerSeriesWithinOnBall.analyticOn`：HasFPowerSeriesWithinOnBall.anal
yticOn (hf : HasFPowerSeriesWithinOnBall f p s x r) : AnalyticOn 𝕜 f (insert x s
 inter Metric.eball x r)
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
If a function has a power series in a ball, then its `n`-th iterated derivative 
is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`.
-/
theorem HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace [CompleteSpace F]
    (h : HasFPowerSeriesWithinOnBall f p s x r)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E) :
    iteratedFDerivWithin 𝕜 n f s x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  have : iteratedFDerivWithin 𝕜 n f s x
      = iteratedFDerivWithin 𝕜 n f (s ∩ Metric.eball x r) x :=
    (iteratedFDerivWithin_inter_open Metric.isOpen_eball (Metric.mem_eball_self h.r_pos)).symm
  rw [this]
  apply HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_subset
  · exact h.mono inter_subset_left
  · apply h.analyticOn.mono
    rw [insert_eq_of_mem hx]
  · exact hs.inter Metric.isOpen_eball
  · exact ⟨hx, Metric.mem_eball_self h.r_pos⟩
  · exact inter_subset_right

/-- If a function has a power series in a ball, then its `n`-th iterated derivative is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`. -/
/-
**HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace [CompleteSpac
e F] (h : HasFPowerSeriesOnBall f p x r) {n : Nat} (v : Fin n -> E) : iteratedFD
eriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i => v (σ i))
参数：h : HasFPowerSeriesOnBall f p x r；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace
`：HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace [Comp
leteSpace F] (h : HasFPowerSeriesWithinOnBall f p s x r) (hs :…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
If a function has a power series in a ball, then its `n`-th iterated derivative 
is given by
`(v₁, ..., vₙ) ↦ ∑ pₙ (v_{σ (1)}, ..., v_{σ (n)})` where the sum is over all
permutations of `{1, ..., n}`.
-/
theorem HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace [CompleteSpace F]
    (h : HasFPowerSeriesOnBall f p x r) {n : ℕ} (v : Fin n → E) :
    iteratedFDeriv 𝕜 n f x v = ∑ σ : Perm (Fin n), p n (fun i ↦ v (σ i)) := by
  simp only [← iteratedFDerivWithin_univ, ← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact h.iteratedFDerivWithin_eq_sum_of_completeSpace uniqueDiffOn_univ (mem_univ _) v

/-- The `n`-th iterated derivative of an analytic function on a set is symmetric. -/
/-
**AnalyticOn.iteratedFDerivWithin_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.iteratedFDerivWithin_comp_perm (h : AnalyticOn 𝕜 f s) (hs : Uni
queDiffOn 𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E) (σ : Perm (Fin n)) : ite
ratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v
参数：h : AnalyticOn 𝕜 f s；hs : UniqueDiffOn 𝕜 s；hx : x in s；v : Fin n -> E；σ : Per
m (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum`：HasFPowerSeries
WithinOnBall.iteratedFDerivWithin_eq_sum (h : HasFPowerSeriesWithinOnBall f p s 
x r) (h' : AnalyticOn 𝕜 f s) (hs : UniqueDiff…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th iterated derivative of an analytic function on a set is symmetric.
-/
theorem AnalyticOn.iteratedFDerivWithin_comp_perm
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E)
    (σ : Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rcases h x hx with ⟨p, r, hp⟩
  rw [hp.iteratedFDerivWithin_eq_sum h hs hx, hp.iteratedFDerivWithin_eq_sum h hs hx]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft σ)]
  simp only [coe_mulLeft, Perm.coe_mul, Function.comp_apply]
/-
**AnalyticOn.domDomCongr_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.domDomCongr_iteratedFDerivWithin (h : AnalyticOn 𝕜 f s) (hs : U
niqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (σ : Perm (Fin n)) : (iteratedFDerivWit
hin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x
参数：h : AnalyticOn 𝕜 f s；hs : UniqueDiffOn 𝕜 s；hx : x in s；σ : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `AnalyticOn.iteratedFDerivWithin_comp_perm`：AnalyticOn.iteratedFDerivWith
in_comp_perm (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : N
at} (v : Fin n -> E) (σ : Perm …
-/
theorem AnalyticOn.domDomCongr_iteratedFDerivWithin
    (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (σ : Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

/-- The `n`-th iterated derivative of an analytic function on a set is symmetric. -/
/-
**ContDiffWithinAt.iteratedFDerivWithin_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.iteratedFDerivWithin_comp_perm (h : ContDiffWithinAt 𝕜 ω 
f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (v : Fin n -> E) (σ : Per
m (Fin n)) : iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f
 s x v
参数：h : ContDiffWithinAt 𝕜 ω f s x；hs : UniqueDiffOn 𝕜 s；hx : x in s；v : Fin n ->
 E；σ : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticOn.iteratedFDerivWithin_comp_perm`：AnalyticOn.iteratedFDerivWith
in_comp_perm (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : N
at} (v : Fin n -> E) (σ : Perm …
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The `n`-th iterated derivative of an analytic function on a set is symmetric.
-/
theorem ContDiffWithinAt.iteratedFDerivWithin_comp_perm
    (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ} (v : Fin n → E)
    (σ : Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [insert_eq_of_mem hx] at hu
  have : iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
    iteratedFDerivWithin_inter_open u_open xu
  rw [← this]
  exact AnalyticOn.iteratedFDerivWithin_comp_perm hu.analyticOn (hs.inter u_open) ⟨hx, xu⟩ _ _
/-
**ContDiffWithinAt.domDomCongr_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContDiffWithinAt.domDomCongr_iteratedFDerivWithin (h : ContDiffWithinAt 𝕜 
ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : Nat} (σ : Perm (Fin n)) : (i
teratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x
参数：h : ContDiffWithinAt 𝕜 ω f s x；hs : UniqueDiffOn 𝕜 s；hx : x in s；σ : Perm (Fi
n n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `ContDiffWithinAt.iteratedFDerivWithin_comp_perm`：ContDiffWithinAt.iterat
edFDerivWithin_comp_perm (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s
) (hx : x in s) {n : Nat} (v : Fin n …
-/
theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin
    (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {n : ℕ}
    (σ : Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  ext
  exact h.iteratedFDerivWithin_comp_perm hs hx _ _

/-- The `n`-th iterated derivative of an analytic function is symmetric. -/
/-
**AnalyticOn.iteratedFDeriv_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.iteratedFDeriv_comp_perm (h : AnalyticOn 𝕜 f univ) {n : Nat} (v
 : Fin n -> E) (σ : Perm (Fin n)) : iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDe
riv 𝕜 n f x v
参数：h : AnalyticOn 𝕜 f univ；v : Fin n -> E；σ : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `AnalyticOn.iteratedFDerivWithin_comp_perm`：AnalyticOn.iteratedFDerivWith
in_comp_perm (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n : N
at} (v : Fin n -> E) (σ : Perm …
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The `n`-th iterated derivative of an analytic function is symmetric.
-/
theorem AnalyticOn.iteratedFDeriv_comp_perm
    (h : AnalyticOn 𝕜 f univ) {n : ℕ} (v : Fin n → E) (σ : Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _
/-
**AnalyticOn.domDomCongr_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOn.domDomCongr_iteratedFDeriv (h : AnalyticOn 𝕜 f univ) {n : Nat} 
(σ : Perm (Fin n)) : (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n
 f x
参数：h : AnalyticOn 𝕜 f univ；σ : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `AnalyticOn.domDomCongr_iteratedFDerivWithin`：AnalyticOn.domDomCongr_iter
atedFDerivWithin (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {n
 : Nat} (σ : Perm (Fin n)) : (ite…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem AnalyticOn.domDomCongr_iteratedFDeriv (h : AnalyticOn 𝕜 f univ) {n : ℕ} (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _

/-- The `n`-th iterated derivative of an analytic function is symmetric. -/
/-
**ContDiffAt.iteratedFDeriv_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.iteratedFDeriv_comp_perm (h : ContDiffAt 𝕜 ω f x) {n : Nat} (v 
: Fin n -> E) (σ : Perm (Fin n)) : iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDer
iv 𝕜 n f x v
参数：h : ContDiffAt 𝕜 ω f x；v : Fin n -> E；σ : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `ContDiffWithinAt.iteratedFDerivWithin_comp_perm`：ContDiffWithinAt.iterat
edFDerivWithin_comp_perm (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn 𝕜 s
) (hx : x in s) {n : Nat} (v : Fin n …
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The `n`-th iterated derivative of an analytic function is symmetric.
-/
theorem ContDiffAt.iteratedFDeriv_comp_perm
    (h : ContDiffAt 𝕜 ω f x) {n : ℕ} (v : Fin n → E) (σ : Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  rw [← iteratedFDerivWithin_univ]
  exact h.iteratedFDerivWithin_comp_perm uniqueDiffOn_univ (mem_univ x) _ _
/-
**ContDiffAt.domDomCongr_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.domDomCongr_iteratedFDeriv (h : ContDiffAt 𝕜 ω f x) {n : Nat} (
σ : Perm (Fin n)) : (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n 
f x
参数：h : ContDiffAt 𝕜 ω f x；σ : Perm (Fin n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `ContDiffWithinAt.domDomCongr_iteratedFDerivWithin`：ContDiffWithinAt.domD
omCongr_iteratedFDerivWithin (h : ContDiffWithinAt 𝕜 ω f s x) (hs : UniqueDiffOn
 𝕜 s) (hx : x in s) {n : Nat} (σ : Perm…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem ContDiffAt.domDomCongr_iteratedFDeriv (h : ContDiffAt 𝕜 ω f x) {n : ℕ} (σ : Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  exact h.domDomCongr_iteratedFDerivWithin uniqueDiffOn_univ (mem_univ x) _
