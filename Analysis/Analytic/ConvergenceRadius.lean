/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Radius of convergence of a power series

This file introduces the notion of the radius of convergence of a power series.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `p.radius`: the largest `r : ℝ≥0∞` such that `‖p n‖ * r^n` grows subexponentially.
* `p.le_radius_of_bound`, `p.le_radius_of_bound_nnreal`, `p.le_radius_of_isBigO`: if `‖p n‖ * r ^ n`
  is bounded above, then `r ≤ p.radius`;
* `p.isLittleO_of_lt_radius`, `p.norm_mul_pow_le_mul_pow_of_lt_radius`,
  `p.isLittleO_one_of_lt_radius`,
  `p.norm_mul_pow_le_of_lt_radius`, `p.nnnorm_mul_pow_le_of_lt_radius`: if `r < p.radius`, then
  `‖p n‖ * r ^ n` tends to zero exponentially;
* `p.lt_radius_of_isBigO`: if `r ≠ 0` and `‖p n‖ * r ^ n = O(a ^ n)` for some `-1 < a < 1`, then
  `r < p.radius`;
* `p.partialSum n x`: the sum `∑_{i = 0}^{n-1} pᵢ xⁱ`.
* `p.sum x`: the sum `∑'_{i = 0}^{∞} pᵢ xⁱ`.

## Implementation details

We only introduce the radius of convergence of a power series, as `p.radius`.
For a power series in finitely many dimensions, there is a finer (directional, coordinate-dependent)
notion, describing the polydisk of convergence. This notion is more specific, and not necessary to
build the general theory. We do not define it here.
-/

@[expose] public section

noncomputable section

variable {𝕜 𝕜' E F G : Type*}

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise

namespace FormalMultilinearSeries

variable [Semiring 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]
variable [TopologicalSpace E] [TopologicalSpace F]
variable [ContinuousAdd E] [ContinuousAdd F]
variable [ContinuousConstSMul 𝕜 E] [ContinuousConstSMul 𝕜 F]

/-- Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the sum `Σ pₙ xⁿ`. A
priori, it only behaves well when `‖x‖ < p.radius`. -/
/-
**FormalMultilinearSeries.sum** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSeries
`。
形式化陈述：{𝕜 : Type u_1} →   {E : Type u_3} →     {F : Type u_4} →       [inst : Sem
iring 𝕜] →         [inst_1 : AddCommMonoid E] →           [inst_2 : AddCommMonoi
d F] →             [inst_3 : _root_.Module 𝕜 E] →               [inst_4 : _root_
.Module 𝕜 F] →                 [inst_5 : TopologicalSpace E] →                  
 [inst_6 : TopologicalSpace F] →                     [inst_7 : ContinuousAdd E] 
→                       [inst_8 : ContinuousAdd F] →                         [in
st_9 : ContinuousConstSMul 𝕜 E] →                           [inst_10 : Continuou
sConstSMul 𝕜 F] → FormalMultilinearSeries 𝕜 E F → E → F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal multilinear series `p` and a vector `x`, then `p.sum x` is the su
m `Σ pₙ xⁿ`. A
priori, it only behaves well when `‖x‖ < p.radius`.
-/
protected def sum (p : FormalMultilinearSeries 𝕜 E F) (x : E) : F :=
  ∑' n : ℕ, p n fun _ => x
/-
**FormalMultilinearSeries.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSe
ries`。
形式化陈述：sum_mem {S : Type*} {s : S} [SetLike S F] [AddSubmonoidClass S F] (h_close
d : IsClosed (s : Set F)) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (h : foral
l k, p k (fun _ : Fin k => x) in s) : p.sum x in s
参数：h_closed : IsClosed (s : Set F)；p : FormalMultilinearSeries 𝕜 E F；x : E；h : f
orall k, p k (fun _ : Fin k => x) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_mem`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : Topologica
lSpace α] {ι : Type u_4} {S : Type u_5} {s : S}   [inst_2 : SetLike S α] [AddS…
-/
theorem sum_mem {S : Type*} {s : S} [SetLike S F] [AddSubmonoidClass S F]
    (h_closed : IsClosed (s : Set F)) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (h : ∀ k, p k (fun _ : Fin k => x) ∈ s) :
    p.sum x ∈ s :=
  tsum_mem h_closed h

variable {𝕜' : Type} [DivisionSemiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F]
  [SMulCommClass 𝕜 𝕜' F]
/-
**FormalMultilinearSeries.const_smul_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：const_smul_sum_apply [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E
 F) (z : E) : a • f.sum z = (a • f).sum z
参数：a : 𝕜'；f : FormalMultilinearSeries 𝕜 E F；z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用引理 `tsum_const_smul''`：tsum_const_smul'' {γ : Type*} [DivisionSemiring γ] [M
odule γ α] [ContinuousConstSMul γ α] [T2Space α] (g : γ) : ∑'[L] (i : β), g • f 
i = g •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem const_smul_sum_apply [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) (z : E) :
    a • f.sum z = (a • f).sum z := by
  unfold FormalMultilinearSeries.sum
  simp [tsum_const_smul'']
/-
**FormalMultilinearSeries.const_smul_sum** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：const_smul_sum [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) : 
a • f.sum = (a • f).sum
参数：a : 𝕜'；f : FormalMultilinearSeries 𝕜 E F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FormalMultilinearSeries.const_smul_sum_apply`：const_smul_sum_apply [T2Sp
ace F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) (z : E) : a • f.sum z = (a •
 f).sum z
-/
theorem const_smul_sum [T2Space F] (a : 𝕜') (f : FormalMultilinearSeries 𝕜 E F) :
    a • f.sum = (a • f).sum := by
  ext z
  apply const_smul_sum_apply

/-- Given a formal multilinear series `p` and a vector `x`, then `p.partialSum n x` is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`. -/
/-
**FormalMultilinearSeries.partialSum** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) (x : E) : F
参数：p : FormalMultilinearSeries 𝕜 E F；n : Nat；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal multilinear series `p` and a vector `x`, then `p.partialSum n x` 
is the sum
`Σ pₖ xᵏ` for `k ∈ {0,..., n-1}`.
-/
def partialSum (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) (x : E) : F :=
  ∑ k ∈ Finset.range n, p k fun _ : Fin k => x

/-- The partial sums of a formal multilinear series are continuous. -/
/-
**FormalMultilinearSeries.partialSum_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：partialSum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : Nat) : Cont
inuous (p.partialSum n)
参数：p : FormalMultilinearSeries 𝕜 E F；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
The partial sums of a formal multilinear series are continuous.
-/
theorem partialSum_continuous (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    Continuous (p.partialSum n) := by
  unfold partialSum
  fun_prop

end FormalMultilinearSeries

/-! ### The radius of a formal multilinear series -/

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}

/-- The radius of a formal multilinear series is the largest `r` such that the sum `Σ ‖pₙ‖ ‖y‖ⁿ`
converges for all `‖y‖ < r`. This implies that `Σ pₙ yⁿ` converges for all `‖y‖ < r`, but these
definitions are *not* equivalent in general. -/
/-
**FormalMultilinearSeries.radius** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSer
ies`。
形式化陈述：radius (p : FormalMultilinearSeries 𝕜 E F) : Real>=0∞
参数：p : FormalMultilinearSeries 𝕜 E F。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radius of a formal multilinear series is the largest `r` such that the sum `
Σ ‖pₙ‖ ‖y‖ⁿ`
converges for all `‖y‖ < r`. This implies that `Σ pₙ yⁿ` converges for all `‖y‖ 
< r`, but these
definitions are *not* equivalent in general.
-/
def radius (p : FormalMultilinearSeries 𝕜 E F) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (C : ℝ) (_ : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C), (r : ℝ≥0∞)

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
/-
**FormalMultilinearSeries.le_radius_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：le_radius_of_bound (C : Real) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (
r : Real) ^ n <= C) : (r : Real>=0∞) <= p.radius
参数：C : Real；h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C。
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
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f

--- 原说明 ---
If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`.
-/
theorem le_radius_of_bound (C : ℝ) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  le_iSup_of_le r <| le_iSup_of_le C <| le_iSup (fun _ => (r : ℝ≥0∞)) h

/-- If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`. -/
/-
**FormalMultilinearSeries.le_radius_of_bound_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `F
ormalMultilinearSeries`。
形式化陈述：le_radius_of_bound_nnreal (C : Real>=0) {r : Real>=0} (h : forall n : Nat,
 ‖p n‖₊ * r ^ n <= C) : (r : Real>=0∞) <= p.radius
参数：C : Real>=0；h : forall n : Nat, ‖p n‖₊ * r ^ n <= C。
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
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius

--- 原说明 ---
If `‖pₙ‖ rⁿ` is bounded in `n`, then the radius of `p` is at least `r`.
-/
theorem le_radius_of_bound_nnreal (C : ℝ≥0) {r : ℝ≥0} (h : ∀ n : ℕ, ‖p n‖₊ * r ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ p.radius :=
  p.le_radius_of_bound C fun n => mod_cast h n

/-- If `‖pₙ‖ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`. -/
/-
**FormalMultilinearSeries.le_radius_of_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：le_radius_of_isBigO (h : (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _
 => (1 : Real)) : ↑r <= p.radius
参数：h : (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)。
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
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_one_nat_atTop_iff`：isBigO_one_nat_atTop_iff {f : Nat 
-> E''} : f =O[atTop] (fun _n => 1 : Nat -> Real) ↔ exists C, forall n, ‖f n‖ <=
 C
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
If `‖pₙ‖ rⁿ = O(1)`, as `n → ∞`, then the radius of `p` is at least `r`.
-/
theorem le_radius_of_isBigO (h : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) :
    ↑r ≤ p.radius :=
  Exists.elim (isBigO_one_nat_atTop_iff.1 h) fun C hC =>
    p.le_radius_of_bound C fun n => (le_abs_self _).trans (hC n)
/-
**FormalMultilinearSeries.le_radius_of_eventually_le** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：le_radius_of_eventually_le (C) (h : forallᶠ n in atTop, ‖p n‖ * (r : Real)
 ^ n <= C) : ↑r <= p.radius
参数：C；h : forallᶠ n in atTop, ‖p n‖ * (r : Real) ^ n <= C。
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
· 使用定理 `FormalMultilinearSeries.le_radius_of_isBigO`：le_radius_of_isBigO (h : (f
un n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : ↑r <= p.radius
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem le_radius_of_eventually_le (C) (h : ∀ᶠ n in atTop, ‖p n‖ * (r : ℝ) ^ n ≤ C) :
    ↑r ≤ p.radius :=
  p.le_radius_of_isBigO <| IsBigO.of_bound C <| h.mono fun n hn => by simpa
/-
**FormalMultilinearSeries.le_radius_of_summable_nnnorm** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：le_radius_of_summable_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r <
= p.radius
参数：h : Summable fun n => ‖p n‖₊ * r ^ n。
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
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound_nnreal`：le_radius_of_bound_nn
real (C : Real>=0) {r : Real>=0} (h : forall n : Nat, ‖p n‖₊ * r ^ n <= C) : (r 
: Real>=0∞) <= p.radius
· 使用定理 `Summable.le_tsum'`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedAddMonoid α]   [CanonicallyOrderedAdd α]
 [inst_…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
-/
theorem le_radius_of_summable_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_bound_nnreal (∑' n, ‖p n‖₊ * r ^ n) fun _ => h.le_tsum' _
/-
**FormalMultilinearSeries.le_radius_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：le_radius_of_summable (h : Summable fun n => ‖p n‖ * (r : Real) ^ n) : ↑r 
<= p.radius
参数：h : Summable fun n => ‖p n‖ * (r : Real) ^ n。
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
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable_nnnorm`：le_radius_of_summa
ble_nnnorm (h : Summable fun n => ‖p n‖₊ * r ^ n) : ↑r <= p.radius
-/
theorem le_radius_of_summable (h : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_summable_nnnorm <| by
    simp only [← coe_nnnorm] at h
    exact mod_cast h
/-
**FormalMultilinearSeries.radius_eq_top_of_forall_nnreal_isBigO** 是 Mathlib 中的一个
定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_eq_top_of_forall_nnreal_isBigO (h : forall r : Real>=0, (fun n => ‖
p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : p.radius = ∞
参数：h : forall r : Real>=0, (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => 
(1 : Real)。
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
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `FormalMultilinearSeries.le_radius_of_isBigO`：le_radius_of_isBigO (h : (f
un n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : ↑r <= p.radius
-/
theorem radius_eq_top_of_forall_nnreal_isBigO
    (h : ∀ r : ℝ≥0, (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] fun _ => (1 : ℝ)) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_isBigO (h r)
/-
**FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_eq_top_of_eventually_eq_zero (h : forallᶠ n in atTop, p n = 0) : p.
radius = ∞
参数：h : forallᶠ n in atTop, p n = 0。
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
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_forall_nnreal_isBigO`：radius_eq
_top_of_forall_nnreal_isBigO (h : forall r : Real>=0, (fun n => ‖p n‖ * (r : Rea
l) ^ n) =O[atTop] fun _ => (1 : Real)) : p.radius =…
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.isBigO_zero`：isBigO_zero : (fun _x => (0 : E')) =O[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem radius_eq_top_of_eventually_eq_zero (h : ∀ᶠ n in atTop, p n = 0) : p.radius = ∞ :=
  p.radius_eq_top_of_forall_nnreal_isBigO fun r =>
    (isBigO_zero _ _).congr' (h.mono fun n hn => by simp [hn]) EventuallyEq.rfl
/-
**FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero** 是 Mathlib 
中的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m +
 n) = 0) : p.radius = ∞
参数：n : Nat；hn : forall m, p (m + n) = 0。
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
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero`：radius_eq_t
op_of_eventually_eq_zero (h : forallᶠ n in atTop, p n = 0) : p.radius = ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem radius_eq_top_of_forall_image_add_eq_zero (n : ℕ) (hn : ∀ m, p (m + n) = 0) :
    p.radius = ∞ :=
  p.radius_eq_top_of_eventually_eq_zero <|
    mem_atTop_sets.2 ⟨n, fun _ hk => tsub_add_cancel_of_le hk ▸ hn _⟩

@[simp]
/-
**FormalMultilinearSeries.constFormalMultilinearSeries_radius** 是 Mathlib 中的一个定理
，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：constFormalMultilinearSeries_radius {v : F} : (constFormalMultilinearSerie
s 𝕜 E v).radius = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero`：radiu
s_eq_top_of_forall_image_add_eq_zero (n : Nat) (hn : forall m, p (m + n) = 0) : 
p.radius = ∞
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Analysis.Analytic.ConvergenceRadius.0.constFormalMultil
inearSeries.match_1.eq_2`：∀ (motive : ℕ → Sort u_1) (x : ℕ) (h_1 : Unit → motive
 0) (h_2 : (x : ℕ) → motive x),   (x = 0 → False) →     (match x with       | 0 
=> h_1…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem constFormalMultilinearSeries_radius {v : F} :
    (constFormalMultilinearSeries 𝕜 E v).radius = ⊤ :=
  (constFormalMultilinearSeries 𝕜 E v).radius_eq_top_of_forall_image_add_eq_zero 1
    (by simp [constFormalMultilinearSeries])

/-- `0` has infinite radius of convergence -/
/-
**FormalMultilinearSeries.zero_radius** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultiline
arSeries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F],   FormalMultilinearSeries.radiu
s 0 = ⊤
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `constFormalMultilinearSeries_zero`：constFormalMultilinearSeries_zero [No
ntriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSp
ace 𝕜 E] [NormedSpace 𝕜…
· 使用定理 `FormalMultilinearSeries.constFormalMultilinearSeries_radius`：constFormal
MultilinearSeries_radius {v : F} : (constFormalMultilinearSeries 𝕜 E v).radius =
 ⊤

--- 原说明 ---
`0` has infinite radius of convergence
-/
@[simp] lemma zero_radius : (0 : FormalMultilinearSeries 𝕜 E F).radius = ∞ := by
  rw [← constFormalMultilinearSeries_zero]
  exact constFormalMultilinearSeries_radius

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1`, `‖p n‖ rⁿ = o(aⁿ)`. -/
/-
**FormalMultilinearSeries.isLittleO_of_lt_radius** 是 Mathlib 中的一个定理，位于命名空间 `Form
alMultilinearSeries`。
形式化陈述：isLittleO_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1,
 (fun n => ‖p n‖ * (r : Real) ^ n) =o[atTop] (a ^ ·)
参数：h : ↑r < p.radius。
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
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_exists_lt_isLittleO_pow`：TFAE_exists_lt_isLittleO_pow (f : Nat -> R
eal) (R : Real) : TFAE [exists a in Ioo (-R) R, f =o[atTop] (a ^ ·), exists a in
 Ioo 0 R, f =o[atT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero ex
ponentially:
for some `0 < a < 1`, `‖p n‖ rⁿ = o(aⁿ)`.
-/
theorem isLittleO_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (a ^ ·) := by
  have := (TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4
  rw [this]
  -- Porting note: was
  -- rw [(TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 4]
  simp only [radius, lt_iSup_iff] at h
  rcases h with ⟨t, C, hC, rt⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at rt
  have : 0 < (t : ℝ) := r.coe_nonneg.trans_lt rt
  rw [← div_lt_one this] at rt
  refine ⟨_, rt, C, Or.inr zero_lt_one, fun n => ?_⟩
  calc
    |‖p n‖ * (r : ℝ) ^ n| = ‖p n‖ * (t : ℝ) ^ n * (r / t : ℝ) ^ n := by
      simp [field, abs_mul, div_pow]
    _ ≤ C * (r / t : ℝ) ^ n := by gcongr; apply hC

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ = o(1)`. -/
/-
**FormalMultilinearSeries.isLittleO_one_of_lt_radius** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：isLittleO_one_of_lt_radius (h : ↑r < p.radius) : (fun n => ‖p n‖ * (r : Re
al) ^ n) =o[atTop] (fun _ => 1 : Nat -> Real)
参数：h : ↑r < p.radius。
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
· 使用定理 `FormalMultilinearSeries.isLittleO_of_lt_radius`：isLittleO_of_lt_radius (
h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, (fun n => ‖p n‖ * (r : Real) 
^ n) =o[atTop] (a ^ ·)
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
· 使用定理 `isLittleO_pow_pow_of_lt_left`：isLittleO_pow_pow_of_lt_left {r₁ r₂ : Real
} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂) : (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ 
^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a

--- 原说明 ---
For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ = o(1)`.
-/
theorem isLittleO_one_of_lt_radius (h : ↑r < p.radius) :
    (fun n => ‖p n‖ * (r : ℝ) ^ n) =o[atTop] (fun _ => 1 : ℕ → ℝ) :=
  let ⟨_, ha, hp⟩ := p.isLittleO_of_lt_radius h
  hp.trans <| (isLittleO_pow_pow_of_lt_left ha.1.le ha.2).congr (fun _ => rfl) one_pow

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero exponentially:
for some `0 < a < 1` and `C > 0`, `‖p n‖ * r ^ n ≤ C * a ^ n`. -/
/-
**FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius** 是 Mathlib 中的一个定
理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo
 (0 : Real) 1, exists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C * a ^ n
参数：h : ↑r < p.radius。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_exists_lt_isLittleO_pow`：TFAE_exists_lt_isLittleO_pow (f : Nat -> R
eal) (R : Real) : TFAE [exists a in Ioo (-R) R, f =o[atTop] (a ^ ·), exists a in
 Ioo 0 R, f =o[atT…
· 使用定理 `FormalMultilinearSeries.isLittleO_of_lt_radius`：isLittleO_of_lt_radius (
h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, (fun n => ‖p n‖ * (r : Real) 
^ n) =o[atTop] (a ^ ·)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` tends to zero ex
ponentially:
for some `0 < a < 1` and `C > 0`, `‖p n‖ * r ^ n ≤ C * a ^ n`.
-/
theorem norm_mul_pow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C * a ^ n := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 1 5).mp
    (p.isLittleO_of_lt_radius h)
  rcases this with ⟨a, ha, C, hC, H⟩
  exact ⟨a, ha, C, hC, fun n => (le_abs_self _).trans (H n)⟩

/-- If `r ≠ 0` and `‖pₙ‖ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`. -/
/-
**FormalMultilinearSeries.lt_radius_of_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：lt_radius_of_isBigO (h₀ : r != 0) {a : Real} (ha : a in Ioo (-1 : Real) 1)
 (hp : (fun n => ‖p n‖ * (r : Real) ^ n) =O[atTop] (a ^ ·)) : ↑r < p.radius
参数：h₀ : r != 0；ha : a in Ioo (-1 : Real) 1；hp : (fun n => ‖p n‖ * (r : Real) ^ n
) =O[atTop] (a ^ ·)。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `TFAE_exists_lt_isLittleO_pow`：TFAE_exists_lt_isLittleO_pow (f : Nat -> R
eal) (R : Real) : TFAE [exists a in Ioo (-R) R, f =o[atTop] (a ^ ·), exists a in
 Ioo 0 R, f =o[atT…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_lt_div_iff_of_pos_left`：div_lt_div_iff_of_pos_left (ha : 0 < a) (hb 
: 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `r ≠ 0` and `‖pₙ‖ rⁿ = O(aⁿ)` for some `-1 < a < 1`, then `r < p.radius`.
-/
theorem lt_radius_of_isBigO (h₀ : r ≠ 0) {a : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hp : (fun n => ‖p n‖ * (r : ℝ) ^ n) =O[atTop] (a ^ ·)) : ↑r < p.radius := by
  have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * (r : ℝ) ^ n) 1).out 2 5)
  rcases this.mp ⟨a, ha, hp⟩ with ⟨a, ha, C, hC, hp⟩
  rw [← pos_iff_ne_zero, ← NNReal.coe_pos] at h₀
  lift a to ℝ≥0 using ha.1.le
  have : (r : ℝ) < r / a := by
    simpa only [div_one] using (div_lt_div_iff_of_pos_left h₀ zero_lt_one ha.1).2 ha.2
  norm_cast at this
  rw [← ENNReal.coe_lt_coe] at this
  refine this.trans_le (p.le_radius_of_bound C fun n => ?_)
  rw [NNReal.coe_div, div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos ha.1 n)]
  exact (le_abs_self _).trans (hp n)

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
/-
**FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius** 是 Mathlib 中的一个定理，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real
>=0} (h : (r : Real>=0∞) < p.radius) : exists C > 0, forall n, ‖p n‖ * (r : Real
) ^ n <= C
参数：p : FormalMultilinearSeries 𝕜 E F；h : (r : Real>=0∞) < p.radius。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`：norm_mul_p
ow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, e
xists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded.
-/
theorem norm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C :=
  let ⟨_, ha, C, hC, h⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  ⟨C, hC, fun n => (h n).trans <| mul_le_of_le_one_right hC.lt.le (pow_le_one₀ ha.1.le ha.2.le)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
/-
**FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius** 是 Mathlib 中的一个定理
，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r
 : Real>=0} (h0 : 0 < r) (h : (r : Real>=0∞) < p.radius) : exists C > 0, forall 
n, ‖p n‖ <= C / (r : Real) ^ n
参数：p : FormalMultilinearSeries 𝕜 E F；h0 : 0 < r；h : (r : Real>=0∞) < p.radius。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius`：norm_mul_pow_le_of
_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>=0∞)
 < p.radius) : exists C > 0, forall n, ‖p …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α

--- 原说明 ---
For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded.
-/
theorem norm_le_div_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h0 : 0 < r) (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖ ≤ C / (r : ℝ) ^ n :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨C, hC, fun n => Iff.mpr (le_div_iff₀ (pow_pos h0 _)) (hp n)⟩

/-- For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded. -/
/-
**FormalMultilinearSeries.nnnorm_mul_pow_le_of_lt_radius** 是 Mathlib 中的一个定理，位于命名
空间 `FormalMultilinearSeries`。
形式化陈述：nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Re
al>=0} (h : (r : Real>=0∞) < p.radius) : exists C > 0, forall n, ‖p n‖₊ * r ^ n 
<= C
参数：p : FormalMultilinearSeries 𝕜 E F；h : (r : Real>=0∞) < p.radius。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius`：norm_mul_pow_le_of
_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>=0∞)
 < p.radius) : exists C > 0, forall n, ‖p …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a

--- 原说明 ---
For `r` strictly smaller than the radius of `p`, then `‖pₙ‖ rⁿ` is bounded.
-/
theorem nnnorm_mul_pow_le_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0}
    (h : (r : ℝ≥0∞) < p.radius) : ∃ C > 0, ∀ n, ‖p n‖₊ * r ^ n ≤ C :=
  let ⟨C, hC, hp⟩ := p.norm_mul_pow_le_of_lt_radius h
  ⟨⟨C, hC.lt.le⟩, hC, mod_cast hp⟩
/-
**FormalMultilinearSeries.le_radius_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Formal
MultilinearSeries`。
形式化陈述：le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : Real} (h : T
endsto (fun n => ‖p n‖ * (r : Real) ^ n) atTop (𝓝 l)) : ↑r <= p.radius
参数：p : FormalMultilinearSeries 𝕜 E F；h : Tendsto (fun n => ‖p n‖ * (r : Real) ^ 
n) atTop (𝓝 l)。
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
· 使用定理 `FormalMultilinearSeries.le_radius_of_isBigO`：le_radius_of_isBigO (h : (f
un n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : ↑r <= p.radius
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem le_radius_of_tendsto (p : FormalMultilinearSeries 𝕜 E F) {l : ℝ}
    (h : Tendsto (fun n => ‖p n‖ * (r : ℝ) ^ n) atTop (𝓝 l)) : ↑r ≤ p.radius :=
  p.le_radius_of_isBigO (h.isBigO_one _)
/-
**FormalMultilinearSeries.le_radius_of_summable_norm** 是 Mathlib 中的一个定理，位于命名空间 `
FormalMultilinearSeries`。
形式化陈述：le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summa
ble fun n => ‖p n‖ * (r : Real) ^ n) : ↑r <= p.radius
参数：p : FormalMultilinearSeries 𝕜 E F；hs : Summable fun n => ‖p n‖ * (r : Real) ^
 n。
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
· 使用定理 `FormalMultilinearSeries.le_radius_of_tendsto`：le_radius_of_tendsto (p : 
FormalMultilinearSeries 𝕜 E F) {l : Real} (h : Tendsto (fun n => ‖p n‖ * (r : Re
al) ^ n) atTop (𝓝 l)) : ↑r <= p.ra…
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
theorem le_radius_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : ↑r ≤ p.radius :=
  p.le_radius_of_tendsto hs.tendsto_atTop_zero
/-
**FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm** 是 Mathlib 中的一个
定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) 
{x : E} (h : p.radius < ‖x‖₊) : ¬Summable fun n => ‖p n‖ * ‖x‖ ^ n
参数：p : FormalMultilinearSeries 𝕜 E F；h : p.radius < ‖x‖₊。
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
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable_norm`：le_radius_of_summabl
e_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summable fun n => ‖p n‖ * (r : 
Real) ^ n) : ↑r <= p.radius
-/
theorem not_summable_norm_of_radius_lt_nnnorm (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (h : p.radius < ‖x‖₊) : ¬Summable fun n => ‖p n‖ * ‖x‖ ^ n :=
  fun hs => not_le_of_gt h (p.le_radius_of_summable_norm hs)
/-
**FormalMultilinearSeries.summable_norm_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Forma
lMultilinearSeries`。
形式化陈述：summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h
 : ↑r < p.radius) : Summable fun n : Nat => ‖p n‖ * (r : Real) ^ n
参数：p : FormalMultilinearSeries 𝕜 E F；h : ↑r < p.radius。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`：norm_mul_p
ow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, e
xists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C…
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem summable_norm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n := by
  obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius h
  exact .of_nonneg_of_le (fun _ ↦ by positivity)
    hp ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)
/-
**FormalMultilinearSeries.summable_norm_apply** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E} (hx : x in
 Metric.eball (0 : E) p.radius) : Summable fun n : Nat => ‖p n fun _ => x‖
参数：p : FormalMultilinearSeries 𝕜 E F；hx : x in Metric.eball (0 : E) p.radius。
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
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.summable_norm_mul_pow`：summable_norm_mul_pow (p 
: FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) : Summable fu
n n : Nat => ‖p n‖ * (r : Real) ^ n
· 使用定理 `mem_eball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : 
E} {r : ENNReal}, a ∈ Metric.eball 0 r ↔ ‖a‖ₑ < r
-/
theorem summable_norm_apply (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Metric.eball (0 : E) p.radius) : Summable fun n : ℕ => ‖p n fun _ => x‖ := by
  rw [mem_eball_zero_iff] at hx
  refine .of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun n ↦ ((p n).le_opNorm _).trans_eq ?_) (p.summable_norm_mul_pow hx)
  simp
/-
**FormalMultilinearSeries.summable_nnnorm_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `For
malMultilinearSeries`。
形式化陈述：summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} 
(h : ↑r < p.radius) : Summable fun n : Nat => ‖p n‖₊ * r ^ n
参数：p : FormalMultilinearSeries 𝕜 E F；h : ↑r < p.radius。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `FormalMultilinearSeries.summable_norm_mul_pow`：summable_norm_mul_pow (p 
: FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : ↑r < p.radius) : Summable fu
n n : Nat => ‖p n‖ * (r : Real) ^ n
-/
theorem summable_nnnorm_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {r : ℝ≥0} (h : ↑r < p.radius) :
    Summable fun n : ℕ => ‖p n‖₊ * r ^ n := by
  rw [← NNReal.summable_coe]
  push_cast
  exact p.summable_norm_mul_pow h
/-
**FormalMultilinearSeries.summable** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearS
eries`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [CompleteSpace F]   (p : FormalM
ultilinearSeries 𝕜 E F) {x : E}, x ∈ Metric.eball 0 p.radius → Summable fun n =>
 (p n) fun x_1 => x
参数：p : FormalMultilinearSeries 𝕜 E F；p n。
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
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `FormalMultilinearSeries.summable_norm_apply`：summable_norm_apply (p : Fo
rmalMultilinearSeries 𝕜 E F) {x : E} (hx : x in Metric.eball (0 : E) p.radius) :
 Summable fun n : Nat => ‖p n fun…
-/
protected theorem summable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Metric.eball (0 : E) p.radius) : Summable fun n : ℕ => p n fun _ => x :=
  (p.summable_norm_apply hx).of_norm
/-
**FormalMultilinearSeries.radius_eq_top_of_summable_norm** 是 Mathlib 中的一个定理，位于命名
空间 `FormalMultilinearSeries`。
形式化陈述：radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : f
orall r : Real>=0, Summable fun n => ‖p n‖ * (r : Real) ^ n) : p.radius = ∞
参数：p : FormalMultilinearSeries 𝕜 E F；hs : forall r : Real>=0, Summable fun n => 
‖p n‖ * (r : Real) ^ n。
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
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable_norm`：le_radius_of_summabl
e_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : Summable fun n => ‖p n‖ * (r : 
Real) ^ n) : ↑r <= p.radius
-/
theorem radius_eq_top_of_summable_norm (p : FormalMultilinearSeries 𝕜 E F)
    (hs : ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n) : p.radius = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r => p.le_radius_of_summable_norm (hs r)
/-
**FormalMultilinearSeries.radius_eq_top_iff_summable_norm** 是 Mathlib 中的一个定理，位于命
名空间 `FormalMultilinearSeries`。
形式化陈述：radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) : p.ra
dius = ∞ ↔ forall r : Real>=0, Summable fun n => ‖p n‖ * (r : Real) ^ n
参数：p : FormalMultilinearSeries 𝕜 E F。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`：norm_mul_p
ow_le_mul_pow_of_lt_radius (h : ↑r < p.radius) : exists a in Ioo (0 : Real) 1, e
xists C > 0, forall n, ‖p n‖ * (r : Real) ^ n <= C…
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `FormalMultilinearSeries.radius_eq_top_of_summable_norm`：radius_eq_top_of
_summable_norm (p : FormalMultilinearSeries 𝕜 E F) (hs : forall r : Real>=0, Sum
mable fun n => ‖p n‖ * (r : Real) ^ n) : p.r…
-/
theorem radius_eq_top_iff_summable_norm (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius = ∞ ↔ ∀ r : ℝ≥0, Summable fun n => ‖p n‖ * (r : ℝ) ^ n := by
  constructor
  · intro h r
    obtain ⟨a, ha : a ∈ Ioo (0 : ℝ) 1, C, - : 0 < C, hp⟩ := p.norm_mul_pow_le_mul_pow_of_lt_radius
      (show (r : ℝ≥0∞) < p.radius from h.symm ▸ ENNReal.coe_lt_top)
    refine .of_norm_bounded
      (g := fun n ↦ (C : ℝ) * a ^ n) ((summable_geometric_of_lt_one ha.1.le ha.2).mul_left _)
      fun n ↦ ?_
    specialize hp n
    rwa [Real.norm_of_nonneg (by positivity)]
  · exact p.radius_eq_top_of_summable_norm

/-- If the radius of `p` is positive, then `‖pₙ‖` grows at most geometrically. -/
/-
**FormalMultilinearSeries.le_mul_pow_of_radius_pos** 是 Mathlib 中的一个定理，位于命名空间 `Fo
rmalMultilinearSeries`。
形式化陈述：le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.ra
dius) : exists (C r : _) (_ : 0 < C) (_ : 0 < r), forall n, ‖p n‖ <= C * r ^ n
参数：p : FormalMultilinearSeries 𝕜 E F；h : 0 < p.radius。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius`：norm_le_div
_pow_of_pos_of_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h0 :
 0 < r) (h : (r : Real>=0∞) < p.radius) : exists …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹

--- 原说明 ---
If the radius of `p` is positive, then `‖pₙ‖` grows at most geometrically.
-/
theorem le_mul_pow_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    ∃ (C r : _) (_ : 0 < C) (_ : 0 < r), ∀ n, ‖p n‖ ≤ C * r ^ n := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨r, r0, rlt⟩
  have rpos : 0 < (r : ℝ) := by simp [ENNReal.coe_pos.1 r0]
  rcases norm_le_div_pow_of_pos_of_lt_radius p rpos rlt with ⟨C, Cpos, hCp⟩
  refine ⟨C, r⁻¹, Cpos, by simp only [inv_pos, rpos], fun n => ?_⟩
  rw [inv_pow, ← div_eq_mul_inv]
  exact hCp n
/-
**FormalMultilinearSeries.radius_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `FormalMulti
linearSeries`。
形式化陈述：radius_le_of_le {𝕜' E' F' : Type*} [NontriviallyNormedField 𝕜'] [NormedAdd
CommGroup E'] [NormedSpace 𝕜' E'] [NormedAddCommGroup F'] [NormedSpace 𝕜' F'] {p
 : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜' E' F'} (h : fo
rall n, ‖p n‖ <= ‖q n‖) : q.radius <= p.radius
参数：h : forall n, ‖p n‖ <= ‖q n‖。
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
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius`：norm_mul_pow_le_of
_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>=0∞)
 < p.radius) : exists C > 0, forall n, ‖p …
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
lemma radius_le_of_le {𝕜' E' F' : Type*}
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E'] [NormedSpace 𝕜' E']
    [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜' E' F'}
    (h : ∀ n, ‖p n‖ ≤ ‖q n‖) : q.radius ≤ p.radius := by
  apply le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  rcases norm_mul_pow_le_of_lt_radius _ hr with ⟨C, -, hC⟩
  apply le_radius_of_bound _ C (fun n ↦ ?_)
  apply le_trans _ (hC n)
  gcongr
  exact h n

/-- The radius of the sum of two formal series is at least the minimum of their two radii. -/
/-
**FormalMultilinearSeries.min_radius_le_radius_add** 是 Mathlib 中的一个定理，位于命名空间 `Fo
rmalMultilinearSeries`。
形式化陈述：min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) : min p.rad
ius q.radius <= (p + q).radius
参数：p q : FormalMultilinearSeries 𝕜 E F。
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
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `FormalMultilinearSeries.isLittleO_one_of_lt_radius`：isLittleO_one_of_lt_
radius (h : ↑r < p.radius) : (fun n => ‖p n‖ * (r : Real) ^ n) =o[atTop] (fun _ 
=> 1 : Nat -> Real)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FormalMultilinearSeries.le_radius_of_isBigO`：le_radius_of_isBigO (h : (f
un n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : ↑r <= p.radius
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
The radius of the sum of two formal series is at least the minimum of their two 
radii.
-/
theorem min_radius_le_radius_add (p q : FormalMultilinearSeries 𝕜 E F) :
    min p.radius q.radius ≤ (p + q).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [lt_min_iff] at hr
  have := ((p.isLittleO_one_of_lt_radius hr.1).add (q.isLittleO_one_of_lt_radius hr.2)).isBigO
  refine (p + q).le_radius_of_isBigO ((isBigO_of_le _ fun n => ?_).trans this)
  rw [← add_mul, norm_mul, norm_mul, norm_norm]
  gcongr
  exact (norm_add_le _ _).trans (le_abs_self _)

@[simp]
/-
**FormalMultilinearSeries.radius_neg** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius
参数：p : FormalMultilinearSeries 𝕜 E F。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem radius_neg (p : FormalMultilinearSeries 𝕜 E F) : (-p).radius = p.radius := by
  simp only [radius, neg_apply, norm_neg]
/-
**FormalMultilinearSeries.radius_le_smul** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：radius_le_smul {p : FormalMultilinearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [
NormedRing 𝕜'] [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [IsBoundedSMul 𝕜' F] : p.rad
ius <= (c • p).radius
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
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `ContinuousMultilinearMap.instIsBoundedSMul`：∀ {𝕜 : Type u} {ι : Type v} 
{E : ι → Type wE} {G : Type wG} [inst : NontriviallyNormedField 𝕜]   [inst_1 : (
i : ι) → SeminormedAddCommGroup …
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem radius_le_smul {p : FormalMultilinearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜']
    [Module 𝕜' F] [SMulCommClass 𝕜 𝕜' F] [IsBoundedSMul 𝕜' F] :
    p.radius ≤ (c • p).radius := by
  simp only [radius, smul_apply]
  refine iSup_mono fun r ↦ iSup_mono' fun C ↦ ⟨‖c‖ * C, iSup_mono' fun h ↦ ?_⟩
  simp only [le_refl, exists_prop, and_true]
  intro n
  grw [norm_smul_le, mul_assoc, h]
/-
**FormalMultilinearSeries.radius_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：radius_smul_eq (p : FormalMultilinearSeries 𝕜 E F) {𝕜' : Type*} {c : 𝕜'} [
NormedDivisionRing 𝕜'] [Module 𝕜' F] [NormSMulClass 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
 (hc : c != 0) : (c • p).radius = p.radius
参数：p : FormalMultilinearSeries 𝕜 E F；hc : c != 0。
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
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `FormalMultilinearSeries.radius_le_smul`：radius_le_smul {p : FormalMultil
inearSeries 𝕜 E F} {𝕜' : Type*} {c : 𝕜'} [NormedRing 𝕜'] [Module 𝕜' F] [SMulComm
Class 𝕜 𝕜' F] [IsBoundedSMul…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem radius_smul_eq (p : FormalMultilinearSeries 𝕜 E F)
    {𝕜' : Type*} {c : 𝕜'} [NormedDivisionRing 𝕜'] [Module 𝕜' F] [NormSMulClass 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (hc : c ≠ 0) :
    (c • p).radius = p.radius := by
  apply eq_of_le_of_ge _ radius_le_smul
  exact radius_le_smul.trans_eq (congr_arg _ <| inv_smul_smul₀ hc p)
/-
**FormalMultilinearSeries.norm_compContinuousLinearMap_le** 是 Mathlib 中的一个引理，位于命
名空间 `FormalMultilinearSeries`。
形式化陈述：norm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E
 ->L[𝕜] F) (n : Nat) : ‖p.compContinuousLinearMap u n‖ <= ‖p n‖ * ‖u‖ ^ n
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F；n : Nat。
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
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ContinuousMultilinearMap.norm_compContinuousLinearMap_le`：norm_compConti
nuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : forall i, E i ->L[𝕜
] E₁ i) : ‖g.compContinuousLinearMap f‖ <= ‖g‖…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
-/
lemma norm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ) :
    ‖p.compContinuousLinearMap u n‖ ≤ ‖p n‖ * ‖u‖ ^ n := by
  simp only [compContinuousLinearMap]
  apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
  simp
/-
**FormalMultilinearSeries.enorm_compContinuousLinearMap_le** 是 Mathlib 中的一个引理，位于
命名空间 `FormalMultilinearSeries`。
形式化陈述：enorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : 
E ->L[𝕜] F) (n : Nat) : ‖p.compContinuousLinearMap u n‖ₑ <= ‖p n‖ₑ * ‖u‖ₑ ^ n
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F；n : Nat。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `FormalMultilinearSeries.norm_compContinuousLinearMap_le`：norm_compContin
uousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : Nat) 
: ‖p.compContinuousLinearMap u n‖ <= ‖p n‖ * …
-/
lemma enorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G)
    (u : E →L[𝕜] F) (n : ℕ) : ‖p.compContinuousLinearMap u n‖ₑ ≤ ‖p n‖ₑ * ‖u‖ₑ ^ n := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (by simp), ← ENNReal.ofReal_mul (by simp)]
  gcongr
  apply norm_compContinuousLinearMap_le
/-
**FormalMultilinearSeries.nnnorm_compContinuousLinearMap_le** 是 Mathlib 中的一个引理，位
于命名空间 `FormalMultilinearSeries`。
形式化陈述：nnnorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u :
 E ->L[𝕜] F) (n : Nat) : ‖p.compContinuousLinearMap u n‖₊ <= ‖p n‖₊ * ‖u‖₊ ^ n
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F；n : Nat。
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
· 使用引理 `FormalMultilinearSeries.norm_compContinuousLinearMap_le`：norm_compContin
uousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : Nat) 
: ‖p.compContinuousLinearMap u n‖ <= ‖p n‖ * …
-/
lemma nnnorm_compContinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G)
    (u : E →L[𝕜] F) (n : ℕ) : ‖p.compContinuousLinearMap u n‖₊ ≤ ‖p n‖₊ * ‖u‖₊ ^ n :=
  norm_compContinuousLinearMap_le p u n
/-
**FormalMultilinearSeries.div_le_radius_compContinuousLinearMap** 是 Mathlib 中的一个
定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：div_le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) 
(u : E ->L[𝕜] F) : p.radius / ‖u‖ₑ <= (p.compContinuousLinearMap u).radius
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F。
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
· 使用定理 `eq_zero_or_nnnorm_pos`：∀ {E : Type u_5} [inst : NormedAddGroup E] (a : E
), a = 0 ∨ 0 < ‖a‖₊
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用引理 `compContinuousLinearMap_zero`：compContinuousLinearMap_zero [Nontrivially
NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [
NormedSpace 𝕜 F] […
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `FormalMultilinearSeries.constFormalMultilinearSeries_radius`：constFormal
MultilinearSeries_radius {v : F} : (constFormalMultilinearSeries 𝕜 E v).radius =
 ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_le_iff`：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x 
≤ z * y)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用引理 `enorm_eq_nnnorm`：enorm_eq_nnnorm (x : E) : ‖x‖ₑ = ‖x‖₊
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius`：norm_mul_pow_le_of
_lt_radius (p : FormalMultilinearSeries 𝕜 E F) {r : Real>=0} (h : (r : Real>=0∞)
 < p.radius) : exists C > 0, forall n, ‖p …
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound`：le_radius_of_bound (C : Real
) {r : Real>=0} (h : forall n : Nat, ‖p n‖ * (r : Real) ^ n <= C) : (r : Real>=0
∞) <= p.radius
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `FormalMultilinearSeries.nnnorm_compContinuousLinearMap_le`：nnnorm_compCo
ntinuousLinearMap_le (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F) (n : N
at) : ‖p.compContinuousLinearMap u n‖₊ <= ‖p n‖…
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 38 条，此处仅展示前 30 条）
-/
theorem div_le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    p.radius / ‖u‖ₑ ≤ (p.compContinuousLinearMap u).radius := by
  obtain (rfl | h_zero) := eq_zero_or_nnnorm_pos u
  · simp
  rw [ENNReal.div_le_iff (by simpa using h_zero) (by simp)]
  refine le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [← ENNReal.div_le_iff (by simpa using h_zero) (by simp), enorm_eq_nnnorm, ← coe_div h_zero.ne']
  obtain ⟨C, hC_pos, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  refine le_radius_of_bound _ C fun n ↦ ?_
  calc
    ‖p.compContinuousLinearMap u n‖ * ↑(r / ‖u‖₊) ^ n ≤ ‖p n‖ * ‖u‖ ^ n * ↑(r / ‖u‖₊) ^ n := by
      gcongr
      exact nnnorm_compContinuousLinearMap_le p u n
    _ = ‖p n‖ * r ^ n := by
      simp only [NNReal.coe_div, coe_nnnorm, div_pow, mul_assoc]
      rw [mul_div_cancel₀]
      rw [← NNReal.coe_pos] at h_zero
      positivity
    _ ≤ C := hC n
/-
**FormalMultilinearSeries.le_radius_compContinuousLinearMap** 是 Mathlib 中的一个定理，位
于命名空间 `FormalMultilinearSeries`。
形式化陈述：le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u :
 E ->ₗᵢ[𝕜] F) : p.radius <= (p.compContinuousLinearMap u.toContinuousLinearMap).
radius
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->ₗᵢ[𝕜] F。
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
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `compContinuousLinearMap_zero`：compContinuousLinearMap_zero [Nontrivially
NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [
NormedSpace 𝕜 F] […
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `FormalMultilinearSeries.constFormalMultilinearSeries_radius`：constFormal
MultilinearSeries_radius {v : F} : (constFormalMultilinearSeries 𝕜 E v).radius =
 ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIsometry.enorm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type 
u_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 :
 SeminormedAddCommGroup F] [inst…
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `FormalMultilinearSeries.div_le_radius_compContinuousLinearMap`：div_le_ra
dius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F
) : p.radius / ‖u‖ₑ <= (p.compContinuousLinearMap u…
-/
theorem le_radius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →ₗᵢ[𝕜] F) :
    p.radius ≤ (p.compContinuousLinearMap u.toContinuousLinearMap).radius := by
  obtain (h | h) := subsingleton_or_nontrivial E
  · simp [Subsingleton.elim u.toContinuousLinearMap 0]
  · simpa [u.norm_toContinuousLinearMap]
      using div_le_radius_compContinuousLinearMap p u.toContinuousLinearMap
/-
**FormalMultilinearSeries.radius_compContinuousLinearMap_le** 是 Mathlib 中的一个定理，位
于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_compContinuousLinearMap_le [Nontrivial F] (p : FormalMultilinearSer
ies 𝕜 F G) (u : E ≃L[𝕜] F) : (p.compContinuousLinearMap u.toContinuousLinearMap)
.radius <= ‖u.symm.toContinuousLinearMap‖ₑ * p.radius
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ≃L[𝕜] F。
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
· 使用定理 `FormalMultilinearSeries.div_le_radius_compContinuousLinearMap`：div_le_ra
dius_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->L[𝕜] F
) : p.radius / ‖u‖ₑ <= (p.compContinuousLinearMap u…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.div_le_iff'`：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x
 ≤ y * z)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
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
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousLinearEquiv.coe_comp_coe_symm`：coe_comp_coe_symm (e : M₁ ≃SL[σ
₁₂] M₂) : (e : M₁ ->SL[σ₁₂] M₂).comp (e.symm : M₂ ->SL[σ₂₁] M₁) = ContinuousLine
arMap.id R₂ M₂
-/
theorem radius_compContinuousLinearMap_le [Nontrivial F]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃L[𝕜] F) :
    (p.compContinuousLinearMap u.toContinuousLinearMap).radius ≤
    ‖u.symm.toContinuousLinearMap‖ₑ * p.radius := by
  have := (p.compContinuousLinearMap u.toContinuousLinearMap).div_le_radius_compContinuousLinearMap
    u.symm.toContinuousLinearMap
  simp only [compContinuousLinearMap_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
    compContinuousLinearMap_id] at this
  rwa [ENNReal.div_le_iff' (by simpa [DFunLike.ext_iff] using exists_ne 0) (by simp)] at this

@[simp]
/-
**FormalMultilinearSeries.radius_compContinuousLinearMap_linearIsometryEquiv_eq*
* 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_compContinuousLinearMap_linearIsometryEquiv_eq [Nontrivial E] (p : 
FormalMultilinearSeries 𝕜 F G) (u : E ≃ₗᵢ[𝕜] F) : (p.compContinuousLinearMap u.t
oLinearIsometry.toContinuousLinearMap).radius = p.radius
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ≃ₗᵢ[𝕜] F。
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
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIsometry.enorm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type 
u_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 :
 SeminormedAddCommGroup F] [inst…
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.radius_compContinuousLinearMap_le`：radius_compCo
ntinuousLinearMap_le [Nontrivial F] (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃
L[𝕜] F) : (p.compContinuousLinearMap u.toContin…
· 使用定理 `FormalMultilinearSeries.le_radius_compContinuousLinearMap`：le_radius_com
pContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E ->ₗᵢ[𝕜] F) : p.r
adius <= (p.compContinuousLinearMap u.toContinu…
-/
theorem radius_compContinuousLinearMap_linearIsometryEquiv_eq [Nontrivial E]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E ≃ₗᵢ[𝕜] F) :
    (p.compContinuousLinearMap u.toLinearIsometry.toContinuousLinearMap).radius = p.radius := by
  refine le_antisymm ?_ <| le_radius_compContinuousLinearMap _ _
  have _ : Nontrivial F := u.symm.toEquiv.nontrivial
  convert! radius_compContinuousLinearMap_le p u.toContinuousLinearEquiv
  have : u.toContinuousLinearEquiv.symm.toContinuousLinearMap =
    u.symm.toLinearIsometry.toContinuousLinearMap := rfl
  simp [this]

/-- This is a version of `radius_compContinuousLinearMap_linearIsometryEquiv_eq` with better
opportunity for unification, at the cost of manually supplying some hypotheses. -/
/-
**FormalMultilinearSeries.radius_compContinuousLinearMap_eq** 是 Mathlib 中的一个定理，位
于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_compContinuousLinearMap_eq [Nontrivial E] (p : FormalMultilinearSer
ies 𝕜 F G) (u : E ->L[𝕜] F) (hu_iso : Isometry u) (hu_surj : Function.Surjective
 u) : (p.compContinuousLinearMap u).radius = p.radius
参数：p : FormalMultilinearSeries 𝕜 F G；u : E ->L[𝕜] F；hu_iso : Isometry u；hu_surj 
: Function.Surjective u。
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
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
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
· 使用定理 `FormalMultilinearSeries.radius_compContinuousLinearMap_linearIsometryEqu
iv_eq`：radius_compContinuousLinearMap_linearIsometryEquiv_eq [Nontrivial E] (p :
 FormalMultilinearSeries 𝕜 F G) (u : E ≃ₗᵢ[𝕜] F) : (p.compContinuou…

--- 原说明 ---
This is a version of `radius_compContinuousLinearMap_linearIsometryEquiv_eq` wit
h better
opportunity for unification, at the cost of manually supplying some hypotheses.
-/
theorem radius_compContinuousLinearMap_eq [Nontrivial E]
    (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (hu_iso : Isometry u)
    (hu_surj : Function.Surjective u) :
    (p.compContinuousLinearMap u).radius = p.radius :=
  let v : E ≃ₗᵢ[𝕜] F :=
    { LinearEquiv.ofBijective u.toLinearMap ⟨hu_iso.injective, hu_surj⟩ with
      norm_map' := hu_iso.norm_map_of_map_zero (map_zero u) }
  radius_compContinuousLinearMap_linearIsometryEquiv_eq p v

@[simp]
/-
**FormalMultilinearSeries.radius_compNeg** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：radius_compNeg [Nontrivial E] (p : FormalMultilinearSeries 𝕜 E F) : (p.com
pContinuousLinearMap (-(.id _ _))).radius = p.radius
参数：p : FormalMultilinearSeries 𝕜 E F。
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
· 使用定理 `FormalMultilinearSeries.radius_compContinuousLinearMap_linearIsometryEqu
iv_eq`：radius_compContinuousLinearMap_linearIsometryEquiv_eq [Nontrivial E] (p :
 FormalMultilinearSeries 𝕜 F G) (u : E ≃ₗᵢ[𝕜] F) : (p.compContinuou…
-/
theorem radius_compNeg [Nontrivial E] (p : FormalMultilinearSeries 𝕜 E F) :
    (p.compContinuousLinearMap (-(.id _ _))).radius = p.radius :=
  radius_compContinuousLinearMap_linearIsometryEquiv_eq _ (.neg 𝕜)

@[simp]
/-
**FormalMultilinearSeries.radius_shift** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：radius_shift (p : FormalMultilinearSeries 𝕜 E F) : p.shift.radius = p.radi
us
参数：p : FormalMultilinearSeries 𝕜 E F。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ContinuousMultilinearMap.curryRight_norm`：ContinuousMultilinearMap.curry
Right_norm (f : ContinuousMultilinearMap 𝕜 Ei G) : ‖f.curryRight‖ = ‖f‖
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup_mono'`：iSup_mono' {g : ι' -> α} (h : forall i, exists i', f i <= g 
i') : iSup f <= iSup g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
（共 41 条，此处仅展示前 30 条）
-/
theorem radius_shift (p : FormalMultilinearSeries 𝕜 E F) : p.shift.radius = p.radius := by
  simp only [radius, shift, Nat.succ_eq_add_one, ContinuousMultilinearMap.curryRight_norm]
  congr
  ext r
  apply eq_of_le_of_ge
  · apply iSup_mono'
    intro C
    use ‖p 0‖ ⊔ (C * r)
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    rcases n with - | m
    · simp
    right
    rw [pow_succ, ← mul_assoc]
    gcongr; apply h
  · apply iSup_mono'
    intro C
    use ‖p 1‖ ⊔ C / r
    apply iSup_mono'
    intro h
    simp only [le_refl, le_sup_iff, exists_prop, and_true]
    intro n
    cases eq_zero_or_pos r with
    | inl hr =>
      rw [hr]
      cases n <;> simp
    | inr hr =>
      right
      rw [← NNReal.coe_pos] at hr
      specialize h (n + 1)
      rw [le_div_iff₀ hr]
      rwa [pow_succ, ← mul_assoc] at h

@[simp]
/-
**FormalMultilinearSeries.radius_unshift** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：radius_unshift (p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)) (z : F) : (p
.unshift z).radius = p.radius
参数：p : FormalMultilinearSeries 𝕜 E (E ->L[𝕜] F)；z : F。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.radius_shift`：radius_shift (p : FormalMultilinea
rSeries 𝕜 E F) : p.shift.radius = p.radius
· 使用定理 `FormalMultilinearSeries.unshift_shift`：unshift_shift {p : FormalMultilin
earSeries 𝕜 E (E ->L[𝕜] F)} {z : F} : (p.unshift z).shift = p
-/
theorem radius_unshift (p : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) :
    (p.unshift z).radius = p.radius := by
  rw [← radius_shift, unshift_shift]
/-
**FormalMultilinearSeries.hasSum** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilinearSer
ies`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_3} {F : Type u_4} [inst : NontriviallyNormedF
ield 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [CompleteSpace F]   (p : FormalM
ultilinearSeries 𝕜 E F) {x : E},   x ∈ Metric.eball 0 p.radius → HasSum (fun n =
> (p n) fun x_1 => x) (p.sum x)
参数：p : FormalMultilinearSeries 𝕜 E F；fun n => (p n) fun x_1 => x；p.sum x。
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
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `FormalMultilinearSeries.summable`：∀ {𝕜 : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 …
-/
protected theorem hasSum [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x : E}
    (hx : x ∈ Metric.eball (0 : E) p.radius) : HasSum (fun n : ℕ => p n fun _ => x) (p.sum x) :=
  (p.summable hx).hasSum
/-
**FormalMultilinearSeries.radius_le_radius_continuousLinearMap_comp** 是 Mathlib 
中的一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E
 F) (f : F ->L[𝕜] G) : p.radius <= (f.compFormalMultilinearSeries p).radius
参数：p : FormalMultilinearSeries 𝕜 E F；f : F ->L[𝕜] G。
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
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `FormalMultilinearSeries.le_radius_of_isBigO`：le_radius_of_isBigO (h : (f
un n => ‖p n‖ * (r : Real) ^ n) =O[atTop] fun _ => (1 : Real)) : ↑r <= p.radius
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `ContinuousLinearMap.norm_compContinuousMultilinearMap_le`：norm_compConti
nuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) : 
‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `FormalMultilinearSeries.isLittleO_one_of_lt_radius`：isLittleO_one_of_lt_
radius (h : ↑r < p.radius) : (fun n => ‖p n‖ * (r : Real) ^ n) =o[atTop] (fun _ 
=> 1 : Nat -> Real)
-/
theorem radius_le_radius_continuousLinearMap_comp (p : FormalMultilinearSeries 𝕜 E F)
    (f : F →L[𝕜] G) : p.radius ≤ (f.compFormalMultilinearSeries p).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  apply le_radius_of_isBigO
  apply (IsBigO.trans_isLittleO _ (p.isLittleO_one_of_lt_radius hr)).isBigO
  refine IsBigO.mul (@IsBigOWith.isBigO _ _ _ _ _ ‖f‖ _ _ _ ?_) (isBigO_refl _ _)
  refine IsBigOWith.of_bound (Eventually.of_forall fun n => ?_)
  simpa only [norm_norm] using! f.norm_compContinuousMultilinearMap_le (p n)

end FormalMultilinearSeries

