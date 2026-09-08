/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Derivative is measurable

In this file we prove that the derivative of any function with complete codomain is a measurable
function. Namely, we prove:

* `measurableSet_of_differentiableAt`: the set `{x | DifferentiableAt 𝕜 f x}` is measurable;
* `measurable_fderiv`: the function `fderiv 𝕜 f` is measurable;
* `measurable_fderiv_apply_const`: for a fixed vector `y`, the function `fun x ↦ fderiv 𝕜 f x y`
  is measurable;
* `measurable_deriv`: the function `deriv f` is measurable (for `f : 𝕜 → F`).

We also show the same results for the right derivative on the real line
(see `measurable_derivWithin_Ici` and `measurable_derivWithin_Ioi`), following the same
proof strategy.

We also prove measurability statements for functions depending on a parameter: for `f : α → E → F`,
we show the measurability of `(p : α × E) ↦ fderiv 𝕜 (f p.1) p.2`. This requires additional
assumptions. We give versions of the above statements (appending `with_param` to their names) when
`f` is continuous and `E` is locally compact.

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map `L`, up to `ε r`. It is an open set.
Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`: we require that at two possibly different
scales `r` and `s`, the function is well approximated by the linear map `L`. It is also open.

We claim that the differentiability set of `f` is exactly
`D = ⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, we require that there is a size `δ` such that, for any two scales
below this size, the function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to `D` (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_set_subset_D`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`‖L - L'‖` is bounded by `ε` (see `norm_sub_le_of_mem_A`). Assume now `x ∈ D`. If one has two maps
`L` and `L'` such that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is
close to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a
linear map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to `D`). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.

To show that the derivative itself is measurable, add in the definition of `B` and `D` a set
`K` of continuous linear maps to which `L` should belong. Then, when `K` is complete, the set `D K`
is exactly the set of points where `f` is differentiable with a derivative in `K`.

## Tags

derivative, measurable function, Borel σ-algebra
-/

@[expose] public section


noncomputable section

open Set Metric Asymptotics Filter ContinuousLinearMap MeasureTheory TopologicalSpace
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-
**ContinuousLinearMap.measurable_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：measurable_apply [MeasurableSpace F] [BorelSpace F] (x : E) : Measurable f
un f : E ->L[𝕜] F => f x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem measurable_apply₂ [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopologyEither (E →L[𝕜] F) E]
    [MeasurableSpace F] [BorelSpace F] : Measurable fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  isBoundedBilinearMap_apply.continuous.measurable

end ContinuousLinearMap

section fderiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} (K : Set (E →L[𝕜] F))

namespace FDerivMeasurableAux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set. -/
/-
**FDerivMeasurableAux.A** 是 Mathlib 中的一个定义，位于命名空间 `FDerivMeasurableAux`。
形式化陈述：A (f : E -> F) (L : E ->L[𝕜] F) (r ε : Real) : Set E
参数：f : E -> F；L : E ->L[𝕜] F；r ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `A f L r ε` is the set of points `x` around which the function `f` is we
ll approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition 
to make sure that
this is an open set.
-/
def A (f : E → F) (L : E →L[𝕜] F) (r ε : ℝ) : Set E :=
  { x | ∃ r' ∈ Ioc (r / 2) r, ∀ y ∈ ball x r', ∀ z ∈ ball x r', ‖f z - f y - L (z - y)‖ < ε * r }

/-- The set `B f K r s ε` is the set of points `x` around which there exists a continuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates well the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`. -/
/-
**FDerivMeasurableAux.B** 是 Mathlib 中的一个定义，位于命名空间 `FDerivMeasurableAux`。
形式化陈述：B (f : E -> F) (K : Set (E ->L[𝕜] F)) (r s ε : Real) : Set E
参数：f : E -> F；K : Set (E ->L[𝕜] F)；r s ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `B f K r s ε` is the set of points `x` around which there exists a conti
nuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates w
ell the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`.
-/
def B (f : E → F) (K : Set (E →L[𝕜] F)) (r s ε : ℝ) : Set E :=
  ⋃ L ∈ K, A f L r ε ∩ A f L s ε

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
/-
**FDerivMeasurableAux.D** 是 Mathlib 中的一个定义，位于命名空间 `FDerivMeasurableAux`。
形式化陈述：D (f : E -> F) (K : Set (E ->L[𝕜] F)) : Set E
参数：f : E -> F；K : Set (E ->L[𝕜] F)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `D f K` is a complicated set constructed using countable intersections a
nd unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f
` is differentiable,
with a derivative in `K`.
-/
def D (f : E → F) (K : Set (E →L[𝕜] F)) : Set E :=
  ⋂ e : ℕ, ⋃ n : ℕ, ⋂ (p ≥ n) (q ≥ n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)
/-
**FDerivMeasurableAux.isOpen_A** 是 Mathlib 中的一个定理，位于命名空间 `FDerivMeasurableAux`。
形式化陈述：isOpen_A (L : E ->L[𝕜] F) (r ε : Real) : IsOpen (A f L r ε)
参数：L : E ->L[𝕜] F；r ε : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 44 条，此处仅展示前 30 条）
-/
theorem isOpen_A (L : E →L[𝕜] F) (r ε : ℝ) : IsOpen (A f L r ε) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨r', r'_mem, hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : ∃ s : ℝ, r / 2 < s ∧ s < r' := exists_between r'_mem.1
  have : s ∈ Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩
  refine ⟨r' - s, by linarith, fun x' hx' => ⟨s, this, ?_⟩⟩
  have B : ball x' s ⊆ ball x r' := ball_subset (le_of_lt hx')
  intro y hy z hz
  exact hr' y (B hy) z (B hz)
/-
**FDerivMeasurableAux.isOpen_B** 是 Mathlib 中的一个定理，位于命名空间 `FDerivMeasurableAux`。
形式化陈述：isOpen_B {K : Set (E ->L[𝕜] F)} {r s ε : Real} : IsOpen (B f K r s ε)
参数：E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isOpen_B {K : Set (E →L[𝕜] F)} {r s ε : ℝ} : IsOpen (B f K r s ε) := by
  simp [B, isOpen_biUnion, IsOpen.inter, isOpen_A]
/-
**FDerivMeasurableAux.A_mono** 是 Mathlib 中的一个定理，位于命名空间 `FDerivMeasurableAux`。
形式化陈述：A_mono (L : E ->L[𝕜] F) (r : Real) {ε δ : Real} (h : ε <= δ) : A f L r ε s
ubseteq A f L r δ
参数：L : E ->L[𝕜] F；r : Real；h : ε <= δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 39 条，此处仅展示前 30 条）
-/
theorem A_mono (L : E →L[𝕜] F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) : A f L r ε ⊆ A f L r δ := by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans_le (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x]
/-
**FDerivMeasurableAux.le_of_mem_A** 是 Mathlib 中的一个定理，位于命名空间 `FDerivMeasurableAux
`。
形式化陈述：le_of_mem_A {r ε : Real} {L : E ->L[𝕜] F} {x : E} (hx : x in A f L r ε) {y
 z : E} (hy : y in closedBall x (r / 2)) (hz : z in closedBall x (r / 2)) : ‖f z
 - f y - L (z - y)‖ <= ε * r
参数：hx : x in A f L r ε；hy : y in closedBall x (r / 2)；hz : z in closedBall x (r 
/ 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem le_of_mem_A {r ε : ℝ} {L : E →L[𝕜] F} {x : E} (hx : x ∈ A f L r ε) {y z : E}
    (hy : y ∈ closedBall x (r / 2)) (hz : z ∈ closedBall x (r / 2)) :
    ‖f z - f y - L (z - y)‖ ≤ ε * r := by
  rcases hx with ⟨r', r'mem, hr'⟩
  apply le_of_lt
  exact hr' _ ((mem_closedBall.1 hy).trans_lt r'mem.1) _ ((mem_closedBall.1 hz).trans_lt r'mem.1)
/-
**FDerivMeasurableAux.mem_A_of_differentiable** 是 Mathlib 中的一个定理，位于命名空间 `FDerivM
easurableAux`。
形式化陈述：mem_A_of_differentiable {ε : Real} (hε : 0 < ε) {x : E} (hx : Differentiab
leAt 𝕜 f x) : exists R > 0, forall r in Ioo (0 : Real) R, x in A f (fderiv 𝕜 f x
) r ε
参数：hε : 0 < ε；hx : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.eventually_nhds_iff_ball`：eventually_nhds_iff_ball {p : α -> Prop
} : (forallᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall y in ball x ε, p y
· 使用定理 `Asymptotics.IsLittleO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   
f =o[l] g → ∀ ⦃c …
· 使用定理 `HasFDerivAt.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Typ…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Ioc b a ↔ b < a
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Abel.unfold_sub`：unfold_sub {α} [SubtractionMonoid α] (a 
b c : α) (h : a + -b = c) : a - b = c
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
（共 88 条，此处仅展示前 30 条）
-/
theorem mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : E} (hx : DifferentiableAt 𝕜 f x) :
    ∃ R > 0, ∀ r ∈ Ioo (0 : ℝ) R, x ∈ A f (fderiv 𝕜 f x) r ε := by
  let δ := (ε / 2) / 2
  obtain ⟨R, R_pos, hR⟩ :
      ∃ R > 0, ∀ y ∈ ball x R, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ δ * ‖y - x‖ :=
    eventually_nhds_iff_ball.1 <| hx.hasFDerivAt.isLittleO.bound <| by positivity
  refine ⟨R, R_pos, fun r hr => ?_⟩
  have : r ∈ Ioc (r / 2) r := right_mem_Ioc.2 <| half_lt_self hr.1
  refine ⟨r, this, fun y hy z hz => ?_⟩
  calc
    ‖f z - f y - (fderiv 𝕜 f x) (z - y)‖ =
        ‖f z - f x - (fderiv 𝕜 f x) (z - x) - (f y - f x - (fderiv 𝕜 f x) (y - x))‖ := by
      simp only [map_sub]; abel_nf
    _ ≤ ‖f z - f x - (fderiv 𝕜 f x) (z - x)‖ + ‖f y - f x - (fderiv 𝕜 f x) (y - x)‖ :=
      norm_sub_le _ _
    _ ≤ δ * ‖z - x‖ + δ * ‖y - x‖ :=
      add_le_add (hR _ (ball_subset_ball hr.2.le hz)) (hR _ (ball_subset_ball hr.2.le hy))
    _ ≤ δ * r + δ * r := by rw [mem_ball_iff_norm] at hz hy; gcongr
    _ = (ε / 2) * r := by ring
    _ < ε * r := by gcongr; exacts [hr.1, half_lt_self hε]
/-
**FDerivMeasurableAux.norm_sub_le_of_mem_A** 是 Mathlib 中的一个定理，位于命名空间 `FDerivMeas
urableAux`。
形式化陈述：norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ‖c‖) {r ε : Real} (hε : 0 < ε) (hr 
: 0 < r) {x : E} {L₁ L₂ : E ->L[𝕜] F} (h₁ : x in A f L₁ r ε) (h₂ : x in A f L₂ r
 ε) : ‖L₁ - L₂‖ <= 4 * ‖c‖ * ε
参数：hc : 1 < ‖c‖；hε : 0 < ε；hr : 0 < r；h₁ : x in A f L₁ r ε；h₂ : x in A f L₂ r ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_of_shell`：opNorm_le_of_shell {f : E ->SL[σ
₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜} (hc : 1 < ‖c‖) (hf : f
orall x, ε / ‖c‖ <= ‖x‖ -> ‖…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
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
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `FDerivMeasurableAux.le_of_mem_A`：le_of_mem_A {r ε : Real} {L : E ->L[𝕜] 
F} {x : E} (hx : x in A f L r ε) {y z : E} (hy : y in closedBall x (r / 2)) (hz 
: z in closedBall x (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 58 条，此处仅展示前 30 条）
-/
theorem norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ‖c‖) {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) {x : E}
    {L₁ L₂ : E →L[𝕜] F} (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : ‖L₁ - L₂‖ ≤ 4 * ‖c‖ * ε := by
  refine opNorm_le_of_shell (half_pos hr) (by positivity) hc ?_
  intro y ley ylt
  rw [div_div, div_le_iff₀' (by positivity)] at ley
  calc
    ‖(L₁ - L₂) y‖ = ‖f (x + y) - f x - L₂ (x + y - x) - (f (x + y) - f x - L₁ (x + y - x))‖ := by
      simp
    _ ≤ ‖f (x + y) - f x - L₂ (x + y - x)‖ + ‖f (x + y) - f x - L₁ (x + y - x)‖ := norm_sub_le _ _
    _ ≤ ε * r + ε * r := by
      apply add_le_add
      · apply le_of_mem_A h₂
        · simp only [le_of_lt (half_pos hr), mem_closedBall, dist_self]
        · simp only [dist_eq_norm, add_sub_cancel_left, mem_closedBall, ylt.le]
      · apply le_of_mem_A h₁
        · simp only [le_of_lt (half_pos hr), mem_closedBall, dist_self]
        · simp only [dist_eq_norm, add_sub_cancel_left, mem_closedBall, ylt.le]
    _ = 2 * ε * r := by ring
    _ ≤ 2 * ε * (2 * ‖c‖ * ‖y‖) := by gcongr
    _ = 4 * ‖c‖ * ε * ‖y‖ := by ring

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
/-
**FDerivMeasurableAux.differentiable_set_subset_D** 是 Mathlib 中的一个定理，位于命名空间 `FDe
rivMeasurableAux`。
形式化陈述：differentiable_set_subset_D : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x 
in K } subseteq D f K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FDerivMeasurableAux.D.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `FDerivMeasurableAux.mem_A_of_differentiable`：mem_A_of_differentiable {ε 
: Real} (hε : 0 < ε) {x : E} (hx : DifferentiableAt 𝕜 f x) : exists R > 0, foral
l r in Ioo (0 : Real) R, x in A f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Easy inclusion: a differentiability point with derivative in `K` belongs to `D f
 K`.
-/
theorem differentiable_set_subset_D :
    { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } ⊆ D f K := by
  intro x hx
  rw [D, mem_iInter]
  intro e
  have : (0 : ℝ) < (1 / 2) ^ e := by positivity
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : ℝ) / 2 < 1)
  simp only [mem_iUnion, mem_iInter, B, mem_inter_iff]
  refine ⟨n, fun p hp q hq => ⟨fderiv 𝕜 f x, hx.2, ⟨?_, ?_⟩⟩⟩ <;>
    · refine hR _ ⟨by positivity, lt_of_le_of_lt ?_ hn⟩
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption)

/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
/-
**FDerivMeasurableAux.D_subset_differentiable_set** 是 Mathlib 中的一个定理，位于命名空间 `FDe
rivMeasurableAux`。
形式化陈述：D_subset_differentiable_set {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) : D
 f K subseteq { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K }
参数：E ->L[𝕜] F；hK : IsComplete K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 192 条，此处仅展示前 30 条）

--- 原说明 ---
Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `
K`.
-/
theorem D_subset_differentiable_set {K : Set (E →L[𝕜] F)} (hK : IsComplete K) :
    D f K ⊆ { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } := by
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  intro x hx
  have :
    ∀ e : ℕ, ∃ n : ℕ, ∀ p q, n ≤ p → n ≤ q →
      ∃ L ∈ K, x ∈ A f L ((1 / 2) ^ p) ((1 / 2) ^ e) ∩ A f L ((1 / 2) ^ q) ((1 / 2) ^ e) := by
    intro e
    have := mem_iInter.1 hx e
    rcases mem_iUnion.1 this with ⟨n, hn⟩
    refine ⟨n, fun p q hp hq => ?_⟩
    simp only [mem_iInter] at hn
    rcases mem_iUnion.1 (hn p hp q hq) with ⟨L, hL⟩
    exact ⟨L, exists_prop.mp <| mem_iUnion.1 hL⟩
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
    such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
    `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
      that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
      scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
      `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
      `2 ^ (- p')`. -/
  have M :
    ∀ e p q e' p' q',
      n e ≤ p →
        n e ≤ q →
          n e' ≤ p' → n e' ≤ q' → e ≤ e' → ‖L e p q - L e' p' q'‖ ≤ 12 * ‖c‖ * (1 / 2) ^ e := by
    intro e p q e' p' q' hp hq hp' hq' he'
    let r := max (n e) (n e')
    have I : ((1 : ℝ) / 2) ^ e' ≤ (1 / 2) ^ e :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he'
    have J1 : ‖L e p q - L e p r‖ ≤ 4 * ‖c‖ * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e p q) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p q hp hq).2.1
      have I2 : x ∈ A f (L e p r) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.1
      exact norm_sub_le_of_mem_A hc P P I1 I2
    have J2 : ‖L e p r - L e' p' r‖ ≤ 4 * ‖c‖ * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e p r) ((1 / 2) ^ r) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.2
      have I2 : x ∈ A f (L e' p' r) ((1 / 2) ^ r) ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2
      exact norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ I I2)
    have J3 : ‖L e' p' r - L e' p' q'‖ ≤ 4 * ‖c‖ * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e' p' r) ((1 / 2) ^ p') ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1
      have I2 : x ∈ A f (L e' p' q') ((1 / 2) ^ p') ((1 / 2) ^ e') := (hn e' p' q' hp' hq').2.1
      exact norm_sub_le_of_mem_A hc P P (A_mono _ _ I I1) (A_mono _ _ I I2)
    calc
      ‖L e p q - L e' p' q'‖ =
          ‖L e p q - L e p r + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')‖ := by
        congr 1; abel
      _ ≤ ‖L e p q - L e p r‖ + ‖L e p r - L e' p' r‖ + ‖L e' p' r - L e' p' q'‖ :=
        norm_add₃_le
      _ ≤ 4 * ‖c‖ * (1 / 2) ^ e + 4 * ‖c‖ * (1 / 2) ^ e + 4 * ‖c‖ * (1 / 2) ^ e := by gcongr
      _ = 12 * ‖c‖ * (1 / 2) ^ e := by ring
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
    is a Cauchy sequence. -/
  let L0 : ℕ → E →L[𝕜] F := fun e => L e (n e) (n e)
  have : CauchySeq L0 := by
    rw [Metric.cauchySeq_iff']
    intro ε εpos
    obtain ⟨e, he⟩ : ∃ e : ℕ, (1 / 2) ^ e < ε / (12 * ‖c‖) :=
      exists_pow_lt_of_lt_one (by positivity) (by norm_num)
    refine ⟨e, fun e' he' => ?_⟩
    rw [dist_comm, dist_eq_norm]
    calc
      ‖L0 e - L0 e'‖ ≤ 12 * ‖c‖ * (1 / 2) ^ e := M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he'
      _ < 12 * ‖c‖ * (ε / (12 * ‖c‖)) := by gcongr
      _ = ε := by field
  -- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.
  obtain ⟨f', f'K, hf'⟩ : ∃ f' ∈ K, Tendsto L0 atTop (𝓝 f') :=
    cauchySeq_tendsto_of_isComplete hK (fun e => (hn e (n e) (n e) le_rfl le_rfl).1) this
  have Lf' : ∀ e p, n e ≤ p → ‖L e (n e) p - f'‖ ≤ 12 * ‖c‖ * (1 / 2) ^ e := by
    intro e p hp
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm
    rw [eventually_atTop]
    exact ⟨e, fun e' he' => M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩
  -- Let us show that `f` has derivative `f'` at `x`.
  have : HasFDerivAt f f' x := by
    simp only [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
      some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
      this makes it possible to cover all scales, and thus to obtain a good linear approximation in
      the whole ball of radius `(1/2)^(n e)`. -/
    intro ε εpos
    have pos : 0 < 4 + 12 * ‖c‖ := by positivity
    obtain ⟨e, he⟩ : ∃ e : ℕ, (1 / 2) ^ e < ε / (4 + 12 * ‖c‖) :=
      exists_pow_lt_of_lt_one (div_pos εpos pos) (by norm_num)
    rw [eventually_nhds_iff_ball]
    refine ⟨(1 / 2) ^ (n e + 1), P, fun y hy => ?_⟩
    -- We need to show that `f (x + y) - f x - f' y` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `‖y‖ ∼ 2 ^ (-k)`.
    by_cases y_pos : y = 0
    · simp [y_pos]
    have yzero : 0 < ‖y‖ := norm_pos_iff.mpr y_pos
    have y_lt : ‖y‖ < (1 / 2) ^ (n e + 1) := by simpa using mem_ball_iff_norm.1 hy
    have yone : ‖y‖ ≤ 1 := le_trans y_lt.le (pow_le_one₀ (by norm_num) (by norm_num))
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ k : ℕ, (1 / 2) ^ (k + 1) < ‖y‖ ∧ ‖y‖ ≤ (1 / 2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)
    -- the scale is large enough (as `y` is small enough)
    have k_gt : n e < k := by
      have : ((1 : ℝ) / 2) ^ (k + 1) < (1 / 2) ^ (n e + 1) := lt_trans hk y_lt
      rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)] at this
      lia
    set m := k - 1
    have m_ge : n e ≤ m := Nat.le_sub_one_of_lt k_gt
    have km : k = m + 1 := (Nat.succ_pred_eq_of_pos k_gt.pos).symm
    rw [km] at hk h'k
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J1 : ‖f (x + y) - f x - L e (n e) m (x + y - x)‖ ≤ (1 / 2) ^ e * (1 / 2) ^ m := by
      apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2
      · simp only [mem_closedBall, dist_self]
        positivity
      · simpa only [dist_eq_norm, add_sub_cancel_left, mem_closedBall, pow_succ, mul_one_div] using
          h'k
    have J2 : ‖f (x + y) - f x - L e (n e) m y‖ ≤ 4 * (1 / 2) ^ e * ‖y‖ :=
      calc
        ‖f (x + y) - f x - L e (n e) m y‖ ≤ (1 / 2) ^ e * (1 / 2) ^ m := by
          simpa only [add_sub_cancel_left] using J1
        _ = 4 * (1 / 2) ^ e * (1 / 2) ^ (m + 2) := by ring
        _ ≤ 4 * (1 / 2) ^ e * ‖y‖ := by gcongr
    -- use the previous estimates to see that `f (x + y) - f x - f' y` is small.
    calc
      ‖f (x + y) - f x - f' y‖ = ‖f (x + y) - f x - L e (n e) m y + (L e (n e) m - f') y‖ :=
        congr_arg _ (by simp)
      _ ≤ 4 * (1 / 2) ^ e * ‖y‖ + 12 * ‖c‖ * (1 / 2) ^ e * ‖y‖ :=
        norm_add_le_of_le J2 <| (le_opNorm _ _).trans <| by gcongr; exact Lf' _ _ m_ge
      _ = (4 + 12 * ‖c‖) * ‖y‖ * (1 / 2) ^ e := by ring
      _ ≤ (4 + 12 * ‖c‖) * ‖y‖ * (ε / (4 + 12 * ‖c‖)) := by gcongr
      _ = ε * ‖y‖ := by field
  rw [← this.fderiv] at f'K
  exact ⟨this.differentiableAt, f'K⟩
/-
**FDerivMeasurableAux.differentiable_set_eq_D** 是 Mathlib 中的一个定理，位于命名空间 `FDerivM
easurableAux`。
形式化陈述：differentiable_set_eq_D (hK : IsComplete K) : { x | DifferentiableAt 𝕜 f x
 ∧ fderiv 𝕜 f x in K } = D f K
参数：hK : IsComplete K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `FDerivMeasurableAux.differentiable_set_subset_D`：differentiable_set_subs
et_D : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } subseteq D f K
· 使用定理 `FDerivMeasurableAux.D_subset_differentiable_set`：D_subset_differentiable
_set {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) : D f K subseteq { x | Different
iableAt 𝕜 f x ∧ fderiv 𝕜 f x in K }
-/
theorem differentiable_set_eq_D (hK : IsComplete K) :
    { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } = D f K :=
  Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end FDerivMeasurableAux

open FDerivMeasurableAux

variable [MeasurableSpace E] [OpensMeasurableSpace E]
variable (𝕜 f)

/-- The set of differentiability points of a function, with derivative in a given complete set,
is Borel-measurable. -/
/-
**measurableSet_of_differentiableAt_of_isComplete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_of_differentiableAt_of_isComplete {K : Set (E ->L[𝕜] F)} (hK
 : IsComplete K) : MeasurableSet { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in 
K }
参数：E ->L[𝕜] F；hK : IsComplete K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FDerivMeasurableAux.differentiable_set_eq_D`：differentiable_set_eq_D (hK
 : IsComplete K) : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } = D f K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `FDerivMeasurableAux.isOpen_B`：isOpen_B {K : Set (E ->L[𝕜] F)} {r s ε : R
eal} : IsOpen (B f K r s ε)

--- 原说明 ---
The set of differentiability points of a function, with derivative in a given co
mplete set,
is Borel-measurable.
-/
theorem measurableSet_of_differentiableAt_of_isComplete {K : Set (E →L[𝕜] F)} (hK : IsComplete K) :
    MeasurableSet { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ K } := by
  simp only [D, differentiable_set_eq_D K hK]
  aesop
    (add safe apply [MeasurableSet.iUnion, MeasurableSet.iInter, isOpen_B])
    (add unsafe IsOpen.measurableSet)

variable [CompleteSpace F]

/-- The set of differentiability points of a function taking values in a complete space is
Borel-measurable. -/
/-
**measurableSet_of_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_of_differentiableAt : MeasurableSet { x | DifferentiableAt 𝕜
 f x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `isComplete_univ`：isComplete_univ {α : Type u} [UniformSpace α] [Complete
Space α] : IsComplete (univ : Set α)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `measurableSet_of_differentiableAt_of_isComplete`：measurableSet_of_differ
entiableAt_of_isComplete {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) : Measurable
Set { x | DifferentiableAt 𝕜 f x ∧ fd…

--- 原说明 ---
The set of differentiability points of a function taking values in a complete sp
ace is
Borel-measurable.
-/
theorem measurableSet_of_differentiableAt : MeasurableSet { x | DifferentiableAt 𝕜 f x } := by
  have : IsComplete (univ : Set (E →L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete 𝕜 f this
  simp

@[fun_prop]
/-
**measurable_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fderiv : Measurable (fderiv 𝕜 f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_isClosed`：measurable_of_isClosed {f : δ -> γ} (hf : forall
 s, IsClosed s -> MeasurableSet (f ⁻¹' s)) : Measurable f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `fderiv_mem_iff`：fderiv_mem_iff {f : E -> F} {s : Set (E ->L[𝕜] F)} {x : 
E} : fderiv 𝕜 f x in s ↔ DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s ∨ ¬Different
iabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `measurableSet_of_differentiableAt_of_isComplete`：measurableSet_of_differ
entiableAt_of_isComplete {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) : Measurable
Set { x | DifferentiableAt 𝕜 f x ∧ fd…
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `measurableSet_of_differentiableAt`：measurableSet_of_differentiableAt : M
easurableSet { x | DifferentiableAt 𝕜 f x }
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
-/
theorem measurable_fderiv : Measurable (fderiv 𝕜 f) := by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    fderiv 𝕜 f ⁻¹' s =
      { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s } ∪
        { x | ¬DifferentiableAt 𝕜 f x } ∩ { _x | (0 : E →L[𝕜] F) ∈ s } :=
    Set.ext fun x => mem_preimage.trans fderiv_mem_iff
  rw [this]
  exact
    (measurableSet_of_differentiableAt_of_isComplete _ _ hs.isComplete).union
      ((measurableSet_of_differentiableAt _ _).compl.inter (MeasurableSet.const _))

@[fun_prop]
/-
**measurable_fderiv_apply_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fderiv_apply_const [MeasurableSpace F] [BorelSpace F] (y : E) :
 Measurable fun x => fderiv 𝕜 f x y
参数：y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ContinuousLinearMap.measurable_apply`：measurable_apply [MeasurableSpace 
F] [BorelSpace F] (x : E) : Measurable fun f : E ->L[𝕜] F => f x
· 使用定理 `measurable_fderiv`：measurable_fderiv : Measurable (fderiv 𝕜 f)
-/
theorem measurable_fderiv_apply_const [MeasurableSpace F] [BorelSpace F] (y : E) :
    Measurable fun x => fderiv 𝕜 f x y :=
  (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv 𝕜 f)

variable {𝕜}

@[fun_prop]
/-
**measurable_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableS
pace F] [BorelSpace F] (f : 𝕜 -> F) : Measurable (deriv f)
参数：f : 𝕜 -> F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fderiv_apply_const`：measurable_fderiv_apply_const [Measurable
Space F] [BorelSpace F] (y : E) : Measurable fun x => fderiv 𝕜 f x y
-/
theorem measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] (f : 𝕜 → F) : Measurable (deriv f) := by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const 𝕜 f 1
/-
**stronglyMeasurable_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [h :
 SecondCountableTopologyEither 𝕜 F] (f : 𝕜 -> F) : StronglyMeasurable (deriv f)
参数：f : 𝕜 -> F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SecondCountableTopologyEither.out`：∀ {α : Type u_6} {β : Type u_7} {inst
 : TopologicalSpace α} {inst_1 : TopologicalSpace β}   [self : SecondCountableTo
pologyEither α β], Seco…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable_separable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `measurable_deriv`：measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableS
pace 𝕜] [MeasurableSpace F] [BorelSpace F] (f : 𝕜 -> F) : Measurable (deriv f)
· 使用定理 `isSeparable_range_deriv`：isSeparable_range_deriv [SeparableSpace 𝕜] (f :
 𝕜 -> F) : IsSeparable (range (deriv f))
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem stronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [h : SecondCountableTopologyEither 𝕜 F] (f : 𝕜 → F) : StronglyMeasurable (deriv f) := by
  borelize F
  rcases h.out with h𝕜 | hF
  · exact stronglyMeasurable_iff_measurable_separable.2
      ⟨measurable_deriv f, isSeparable_range_deriv _⟩
  · exact (measurable_deriv f).stronglyMeasurable
/-
**aemeasurable_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [Measurabl
eSpace F] [BorelSpace F] (f : 𝕜 -> F) (μ : Measure 𝕜) : AEMeasurable (deriv f) μ
参数：f : 𝕜 -> F；μ : Measure 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_deriv`：measurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableS
pace 𝕜] [MeasurableSpace F] [BorelSpace F] (f : 𝕜 -> F) : Measurable (deriv f)
-/
theorem aemeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] (f : 𝕜 → F) (μ : Measure 𝕜) : AEMeasurable (deriv f) μ :=
  (measurable_deriv f).aemeasurable
/-
**aestronglyMeasurable_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [S
econdCountableTopologyEither 𝕜 F] (f : 𝕜 -> F) (μ : Measure 𝕜) : AEStronglyMeasu
rable (deriv f) μ
参数：f : 𝕜 -> F；μ : Measure 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `stronglyMeasurable_deriv`：stronglyMeasurable_deriv [MeasurableSpace 𝕜] [
OpensMeasurableSpace 𝕜] [h : SecondCountableTopologyEither 𝕜 F] (f : 𝕜 -> F) : S
tronglyMeasura…
-/
theorem aestronglyMeasurable_deriv [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [SecondCountableTopologyEither 𝕜 F] (f : 𝕜 → F) (μ : Measure 𝕜) :
    AEStronglyMeasurable (deriv f) μ :=
  (stronglyMeasurable_deriv f).aestronglyMeasurable

end fderiv

section RightDeriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : ℝ → F} (K : Set F)

namespace RightDerivMeasurableAux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `h ↦ h • L`, up to an error `ε`. We tweak the definition to
make sure that this is open on the right. -/
/-
**RightDerivMeasurableAux.A** 是 Mathlib 中的一个定义，位于命名空间 `RightDerivMeasurableAux`。
形式化陈述：A (f : Real -> F) (L : F) (r ε : Real) : Set Real
参数：f : Real -> F；L : F；r ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `A f L r ε` is the set of points `x` around which the function `f` is we
ll approximated
at scale `r` by the linear map `h ↦ h • L`, up to an error `ε`. We tweak the def
inition to
make sure that this is open on the right.
-/
def A (f : ℝ → F) (L : F) (r ε : ℝ) : Set ℝ :=
  { x | ∃ r' ∈ Ioc (r / 2) r, ∀ᵉ (y ∈ Icc x (x + r')) (z ∈ Icc x (x + r')),
    ‖f z - f y - (z - y) • L‖ ≤ ε * r }

/-- The set `B f K r s ε` is the set of points `x` around which there exists a vector
`L` belonging to `K` (a given set of vectors) such that `h • L` approximates well `f (x + h)`
(up to an error `ε`), simultaneously at scales `r` and `s`. -/
/-
**RightDerivMeasurableAux.B** 是 Mathlib 中的一个定义，位于命名空间 `RightDerivMeasurableAux`。
形式化陈述：B (f : Real -> F) (K : Set F) (r s ε : Real) : Set Real
参数：f : Real -> F；K : Set F；r s ε : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `B f K r s ε` is the set of points `x` around which there exists a vecto
r
`L` belonging to `K` (a given set of vectors) such that `h • L` approximates wel
l `f (x + h)`
(up to an error `ε`), simultaneously at scales `r` and `s`.
-/
def B (f : ℝ → F) (K : Set F) (r s ε : ℝ) : Set ℝ :=
  ⋃ L ∈ K, A f L r ε ∩ A f L s ε

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
/-
**RightDerivMeasurableAux.D** 是 Mathlib 中的一个定义，位于命名空间 `RightDerivMeasurableAux`。
形式化陈述：D (f : Real -> F) (K : Set F) : Set Real
参数：f : Real -> F；K : Set F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `D f K` is a complicated set constructed using countable intersections a
nd unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f
` is differentiable,
with a derivative in `K`.
-/
def D (f : ℝ → F) (K : Set F) : Set ℝ :=
  ⋂ e : ℕ, ⋃ n : ℕ, ⋂ (p ≥ n) (q ≥ n), B f K ((1 / 2) ^ p) ((1 / 2) ^ q) ((1 / 2) ^ e)
/-
**RightDerivMeasurableAux.A_mem_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 `RightDerivMeas
urableAux`。
形式化陈述：A_mem_nhdsGT {L : F} {r ε x : Real} (hx : x in A f L r ε) : A f L r ε in 𝓝
[>] x
参数：hx : x in A f L r ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 53 条，此处仅展示前 30 条）
-/
theorem A_mem_nhdsGT {L : F} {r ε x : ℝ} (hx : x ∈ A f L r ε) : A f L r ε ∈ 𝓝[>] x := by
  rcases hx with ⟨r', rr', hr'⟩
  obtain ⟨s, s_gt, s_lt⟩ : ∃ s : ℝ, r / 2 < s ∧ s < r' := exists_between rr'.1
  have : s ∈ Ioc (r / 2) r := ⟨s_gt, le_of_lt (s_lt.trans_le rr'.2)⟩
  filter_upwards [Ioo_mem_nhdsGT <| show x < x + r' - s by linarith] with x' hx'
  use s, this
  have A : Icc x' (x' + s) ⊆ Icc x (x + r') := by
    apply Icc_subset_Icc hx'.1.le
    linarith [hx'.2]
  intro y hy z hz
  exact hr' y (A hy) z (A hz)
/-
**RightDerivMeasurableAux.B_mem_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 `RightDerivMeas
urableAux`。
形式化陈述：B_mem_nhdsGT {K : Set F} {r s ε x : Real} (hx : x in B f K r s ε) : B f K 
r s ε in 𝓝[>] x
参数：hx : x in B f K r s ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `RightDerivMeasurableAux.A_mem_nhdsGT`：A_mem_nhdsGT {L : F} {r ε x : Real
} (hx : x in A f L r ε) : A f L r ε in 𝓝[>] x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem B_mem_nhdsGT {K : Set F} {r s ε x : ℝ} (hx : x ∈ B f K r s ε) :
    B f K r s ε ∈ 𝓝[>] x := by
  obtain ⟨L, LK, hL₁, hL₂⟩ : ∃ L : F, L ∈ K ∧ x ∈ A f L r ε ∧ x ∈ A f L s ε := by
    simpa only [B, mem_iUnion, mem_inter_iff, exists_prop] using hx
  filter_upwards [A_mem_nhdsGT hL₁, A_mem_nhdsGT hL₂] with y hy₁ hy₂
  simp only [B, mem_iUnion, mem_inter_iff, exists_prop]
  exact ⟨L, LK, hy₁, hy₂⟩
/-
**RightDerivMeasurableAux.measurableSet_B** 是 Mathlib 中的一个定理，位于命名空间 `RightDerivM
easurableAux`。
形式化陈述：measurableSet_B {K : Set F} {r s ε : Real} : MeasurableSet (B f K r s ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_mem_nhdsGT`：MeasurableSet.of_mem_nhdsGT {s : Set α} (h 
: forall x in s, s in 𝓝[>] x) : MeasurableSet s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `RightDerivMeasurableAux.B_mem_nhdsGT`：B_mem_nhdsGT {K : Set F} {r s ε x 
: Real} (hx : x in B f K r s ε) : B f K r s ε in 𝓝[>] x
-/
theorem measurableSet_B {K : Set F} {r s ε : ℝ} : MeasurableSet (B f K r s ε) :=
  .of_mem_nhdsGT fun _ hx => B_mem_nhdsGT hx
/-
**RightDerivMeasurableAux.A_mono** 是 Mathlib 中的一个定理，位于命名空间 `RightDerivMeasurable
Aux`。
形式化陈述：A_mono (L : F) (r : Real) {ε δ : Real} (h : ε <= δ) : A f L r ε subseteq A
 f L r δ
参数：L : F；r : Real；h : ε <= δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
（共 36 条，此处仅展示前 30 条）
-/
theorem A_mono (L : F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) : A f L r ε ⊆ A f L r δ := by
  rintro x ⟨r', r'r, hr'⟩
  refine ⟨r', r'r, fun y hy z hz => (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h ?_)⟩
  linarith [hy.1, hy.2, r'r.2]
/-
**RightDerivMeasurableAux.le_of_mem_A** 是 Mathlib 中的一个定理，位于命名空间 `RightDerivMeasu
rableAux`。
形式化陈述：le_of_mem_A {r ε : Real} {L : F} {x : Real} (hx : x in A f L r ε) {y z : R
eal} (hy : y in Icc x (x + r / 2)) (hz : z in Icc x (x + r / 2)) : ‖f z - f y - 
(z - y) • L‖ <= ε * r
参数：hx : x in A f L r ε；hy : y in Icc x (x + r / 2)；hz : z in Icc x (x + r / 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 58 条，此处仅展示前 30 条）
-/
theorem le_of_mem_A {r ε : ℝ} {L : F} {x : ℝ} (hx : x ∈ A f L r ε) {y z : ℝ}
    (hy : y ∈ Icc x (x + r / 2)) (hz : z ∈ Icc x (x + r / 2)) :
    ‖f z - f y - (z - y) • L‖ ≤ ε * r := by
  rcases hx with ⟨r', r'mem, hr'⟩
  have A : x + r / 2 ≤ x + r' := by linarith [r'mem.1]
  exact hr' _ ((Icc_subset_Icc le_rfl A) hy) _ ((Icc_subset_Icc le_rfl A) hz)
/-
**RightDerivMeasurableAux.mem_A_of_differentiable** 是 Mathlib 中的一个定理，位于命名空间 `Rig
htDerivMeasurableAux`。
形式化陈述：mem_A_of_differentiable {ε : Real} (hε : 0 < ε) {x : Real} (hx : Different
iableWithinAt Real f (Ici x) x) : exists R > 0, forall r in Ioo (0 : Real) R, x 
in A f (derivWithin f (Ici x) x) r ε
参数：hε : 0 < ε；hx : DifferentiableWithinAt Real f (Ici x) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsGE_iff_exists_Ico_subset`：mem_nhdsGE_iff_exists_Ico_subset [NoMa
xOrder α] {a : α} {s : Set α} : s in 𝓝[>=] a ↔ exists u in Ioi a, Ico a u subset
eq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 88 条，此处仅展示前 30 条）
-/
theorem mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : ℝ}
    (hx : DifferentiableWithinAt ℝ f (Ici x) x) :
    ∃ R > 0, ∀ r ∈ Ioo (0 : ℝ) R, x ∈ A f (derivWithin f (Ici x) x) r ε := by
  have := hx.hasDerivWithinAt
  simp_rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff] at this
  rcases mem_nhdsGE_iff_exists_Ico_subset.1 (this (half_pos hε)) with ⟨m, xm, hm⟩
  refine ⟨m - x, by linarith [show x < m from xm], fun r hr => ?_⟩
  have : r ∈ Ioc (r / 2) r := ⟨half_lt_self hr.1, le_rfl⟩
  refine ⟨r, this, fun y hy z hz => ?_⟩
  calc
    ‖f z - f y - (z - y) • derivWithin f (Ici x) x‖ =
        ‖f z - f x - (z - x) • derivWithin f (Ici x) x -
            (f y - f x - (y - x) • derivWithin f (Ici x) x)‖ := by
      congr 1; simp only [sub_smul]; abel
    _ ≤
        ‖f z - f x - (z - x) • derivWithin f (Ici x) x‖ +
          ‖f y - f x - (y - x) • derivWithin f (Ici x) x‖ :=
      (norm_sub_le _ _)
    _ ≤ ε / 2 * ‖z - x‖ + ε / 2 * ‖y - x‖ :=
      (add_le_add (hm ⟨hz.1, hz.2.trans_lt (by linarith [hr.2])⟩)
        (hm ⟨hy.1, hy.2.trans_lt (by linarith [hr.2])⟩))
    _ ≤ ε / 2 * r + ε / 2 * r := by
      gcongr
      · rw [Real.norm_of_nonneg] <;> linarith [hz.1, hz.2]
      · rw [Real.norm_of_nonneg] <;> linarith [hy.1, hy.2]
    _ = ε * r := by ring
/-
**RightDerivMeasurableAux.norm_sub_le_of_mem_A** 是 Mathlib 中的一个定理，位于命名空间 `RightD
erivMeasurableAux`。
形式化陈述：norm_sub_le_of_mem_A {r x : Real} (hr : 0 < r) (ε : Real) {L₁ L₂ : F} (h₁ 
: x in A f L₁ r ε) (h₂ : x in A f L₂ r ε) : ‖L₁ - L₂‖ <= 4 * ε
参数：hr : 0 < r；ε : Real；h₁ : x in A f L₁ r ε；h₂ : x in A f L₂ r ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `RightDerivMeasurableAux.le_of_mem_A`：le_of_mem_A {r ε : Real} {L : F} {x
 : Real} (hx : x in A f L r ε) {y z : Real} (hy : y in Icc x (x + r / 2)) (hz : 
z in Icc x (x + r / 2)) :…
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 64 条，此处仅展示前 30 条）
-/
theorem norm_sub_le_of_mem_A {r x : ℝ} (hr : 0 < r) (ε : ℝ) {L₁ L₂ : F} (h₁ : x ∈ A f L₁ r ε)
    (h₂ : x ∈ A f L₂ r ε) : ‖L₁ - L₂‖ ≤ 4 * ε := by
  suffices H : ‖(r / 2) • (L₁ - L₂)‖ ≤ r / 2 * (4 * ε) by
    rwa [norm_smul, Real.norm_of_nonneg (half_pos hr).le, mul_le_mul_iff_right₀ (half_pos hr)] at H
  calc
    ‖(r / 2) • (L₁ - L₂)‖ =
        ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₂ -
            (f (x + r / 2) - f x - (x + r / 2 - x) • L₁)‖ := by
      simp [smul_sub]
    _ ≤ ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₂‖ +
          ‖f (x + r / 2) - f x - (x + r / 2 - x) • L₁‖ :=
      norm_sub_le _ _
    _ ≤ ε * r + ε * r := by
      apply add_le_add
      · apply le_of_mem_A h₂ <;> simp [(half_pos hr).le]
      · apply le_of_mem_A h₁ <;> simp [(half_pos hr).le]
    _ = r / 2 * (4 * ε) := by ring

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
/-
**RightDerivMeasurableAux.differentiable_set_subset_D** 是 Mathlib 中的一个定理，位于命名空间 
`RightDerivMeasurableAux`。
形式化陈述：differentiable_set_subset_D : { x | DifferentiableWithinAt Real f (Ici x) 
x ∧ derivWithin f (Ici x) x in K } subseteq D f K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RightDerivMeasurableAux.D.eq_1`：∀ {F : Type u_1} [inst : NormedAddCommGr
oup F] [inst_1 : NormedSpace ℝ F] (f : ℝ → F) (K : Set F),   RightDerivMeasurabl
eAux.D f K =     ⋂ e…
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `RightDerivMeasurableAux.mem_A_of_differentiable`：mem_A_of_differentiable
 {ε : Real} (hε : 0 < ε) {x : Real} (hx : DifferentiableWithinAt Real f (Ici x) 
x) : exists R > 0, forall r in Ioo (0…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Easy inclusion: a differentiability point with derivative in `K` belongs to `D f
 K`.
-/
theorem differentiable_set_subset_D :
    { x | DifferentiableWithinAt ℝ f (Ici x) x ∧ derivWithin f (Ici x) x ∈ K } ⊆ D f K := by
  intro x hx
  rw [D, mem_iInter]
  intro e
  have : (0 : ℝ) < (1 / 2) ^ e := pow_pos (by norm_num) _
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : ℝ) / 2 < 1)
  simp only [mem_iUnion, mem_iInter, B, mem_inter_iff]
  refine ⟨n, fun p hp q hq => ⟨derivWithin f (Ici x) x, hx.2, ⟨?_, ?_⟩⟩⟩ <;>
    · refine hR _ ⟨pow_pos (by norm_num) _, lt_of_le_of_lt ?_ hn⟩
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption)

/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
/-
**RightDerivMeasurableAux.D_subset_differentiable_set** 是 Mathlib 中的一个定理，位于命名空间 
`RightDerivMeasurableAux`。
形式化陈述：D_subset_differentiable_set {K : Set F} (hK : IsComplete K) : D f K subset
eq { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x) x in K 
}
参数：hK : IsComplete K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop`：∀ {b a : Prop}, (∃ (_ : a), b) ↔ a ∧ b
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `RightDerivMeasurableAux.norm_sub_le_of_mem_A`：norm_sub_le_of_mem_A {r x 
: Real} (hr : 0 < r) (ε : Real) {L₁ L₂ : F} (h₁ : x in A f L₁ r ε) (h₂ : x in A 
f L₂ r ε) : ‖L₁ - L₂‖ <= 4 * ε
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
（共 199 条，此处仅展示前 30 条）

--- 原说明 ---
Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `
K`.
-/
theorem D_subset_differentiable_set {K : Set F} (hK : IsComplete K) :
    D f K ⊆ { x | DifferentiableWithinAt ℝ f (Ici x) x ∧ derivWithin f (Ici x) x ∈ K } := by
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1 / 2) ^ n := fun {n} => pow_pos (by norm_num) n
  intro x hx
  have :
    ∀ e : ℕ, ∃ n : ℕ, ∀ p q, n ≤ p → n ≤ q →
      ∃ L ∈ K, x ∈ A f L ((1 / 2) ^ p) ((1 / 2) ^ e) ∩ A f L ((1 / 2) ^ q) ((1 / 2) ^ e) := by
    intro e
    have := mem_iInter.1 hx e
    rcases mem_iUnion.1 this with ⟨n, hn⟩
    refine ⟨n, fun p q hp hq => ?_⟩
    simp only [mem_iInter] at hn
    rcases mem_iUnion.1 (hn p hp q hq) with ⟨L, hL⟩
    exact ⟨L, exists_prop.mp <| mem_iUnion.1 hL⟩
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
    such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
    `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
      that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
      scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
      `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
      `2 ^ (- p')`. -/
  have M :
    ∀ e p q e' p' q',
      n e ≤ p →
        n e ≤ q → n e' ≤ p' → n e' ≤ q' → e ≤ e' → ‖L e p q - L e' p' q'‖ ≤ 12 * (1 / 2) ^ e := by
    intro e p q e' p' q' hp hq hp' hq' he'
    let r := max (n e) (n e')
    have I : ((1 : ℝ) / 2) ^ e' ≤ (1 / 2) ^ e :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he'
    have J1 : ‖L e p q - L e p r‖ ≤ 4 * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e p q) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p q hp hq).2.1
      have I2 : x ∈ A f (L e p r) ((1 / 2) ^ p) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.1
      exact norm_sub_le_of_mem_A P _ I1 I2
    have J2 : ‖L e p r - L e' p' r‖ ≤ 4 * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e p r) ((1 / 2) ^ r) ((1 / 2) ^ e) := (hn e p r hp (le_max_left _ _)).2.2
      have I2 : x ∈ A f (L e' p' r) ((1 / 2) ^ r) ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2
      exact norm_sub_le_of_mem_A P _ I1 (A_mono _ _ I I2)
    have J3 : ‖L e' p' r - L e' p' q'‖ ≤ 4 * (1 / 2) ^ e := by
      have I1 : x ∈ A f (L e' p' r) ((1 / 2) ^ p') ((1 / 2) ^ e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1
      have I2 : x ∈ A f (L e' p' q') ((1 / 2) ^ p') ((1 / 2) ^ e') := (hn e' p' q' hp' hq').2.1
      exact norm_sub_le_of_mem_A P _ (A_mono _ _ I I1) (A_mono _ _ I I2)
    calc
      ‖L e p q - L e' p' q'‖ =
          ‖L e p q - L e p r + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')‖ := by
        congr 1; abel
      _ ≤ ‖L e p q - L e p r‖ + ‖L e p r - L e' p' r‖ + ‖L e' p' r - L e' p' q'‖ := by
        grw [norm_add_le, norm_add_le]
      _ ≤ 4 * (1 / 2) ^ e + 4 * (1 / 2) ^ e + 4 * (1 / 2) ^ e := by gcongr
      _ = 12 * (1 / 2) ^ e := by ring
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
    is a Cauchy sequence. -/
  let L0 : ℕ → F := fun e => L e (n e) (n e)
  have : CauchySeq L0 := by
    rw [Metric.cauchySeq_iff']
    intro ε εpos
    obtain ⟨e, he⟩ : ∃ e : ℕ, (1 / 2) ^ e < ε / 12 :=
      exists_pow_lt_of_lt_one (div_pos εpos (by norm_num)) (by norm_num)
    refine ⟨e, fun e' he' => ?_⟩
    rw [dist_comm, dist_eq_norm]
    calc
      ‖L0 e - L0 e'‖ ≤ 12 * (1 / 2) ^ e := M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he'
      _ < 12 * (ε / 12) := mul_lt_mul' le_rfl he (le_of_lt P) (by norm_num)
      _ = ε := by ring
  -- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.
  obtain ⟨f', f'K, hf'⟩ : ∃ f' ∈ K, Tendsto L0 atTop (𝓝 f') :=
    cauchySeq_tendsto_of_isComplete hK (fun e => (hn e (n e) (n e) le_rfl le_rfl).1) this
  have Lf' : ∀ e p, n e ≤ p → ‖L e (n e) p - f'‖ ≤ 12 * (1 / 2) ^ e := by
    intro e p hp
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm
    rw [eventually_atTop]
    exact ⟨e, fun e' he' => M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩
  -- Let us show that `f` has right derivative `f'` at `x`.
  have : HasDerivWithinAt f f' (Ici x) x := by
    simp only [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
      some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
      this makes it possible to cover all scales, and thus to obtain a good linear approximation in
      the whole interval of length `(1/2)^(n e)`. -/
    intro ε εpos
    obtain ⟨e, he⟩ : ∃ e : ℕ, (1 / 2) ^ e < ε / 16 :=
      exists_pow_lt_of_lt_one (div_pos εpos (by norm_num)) (by norm_num)
    filter_upwards [Icc_mem_nhdsGE <| show x < x + (1 / 2) ^ (n e + 1) by simp] with y hy
    -- We need to show that `f y - f x - f' (y - x)` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `‖y - x‖ ∼ 2 ^ (-k)`.
    rcases eq_or_lt_of_le hy.1 with (rfl | xy)
    · simp only [sub_self, zero_smul, norm_zero, mul_zero, le_rfl]
    have yzero : 0 < y - x := sub_pos.2 xy
    have y_le : y - x ≤ (1 / 2) ^ (n e + 1) := by linarith [hy.2]
    have yone : y - x ≤ 1 := le_trans y_le (pow_le_one₀ (by norm_num) (by norm_num))
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ k : ℕ, (1 / 2) ^ (k + 1) < y - x ∧ y - x ≤ (1 / 2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)
    -- the scale is large enough (as `y - x` is small enough)
    have k_gt : n e < k := by
      have : ((1 : ℝ) / 2) ^ (k + 1) < (1 / 2) ^ (n e + 1) := lt_of_lt_of_le hk y_le
      rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)] at this
      lia
    set m := k - 1
    have m_ge : n e ≤ m := Nat.le_sub_one_of_lt k_gt
    have km : k = m + 1 := (Nat.succ_pred_eq_of_pos k_gt.pos).symm
    rw [km] at hk h'k
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J : ‖f y - f x - (y - x) • L e (n e) m‖ ≤ 4 * (1 / 2) ^ e * ‖y - x‖ :=
      calc
        ‖f y - f x - (y - x) • L e (n e) m‖ ≤ (1 / 2) ^ e * (1 / 2) ^ m := by
          apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2
          · simp only [one_div, inv_pow, left_mem_Icc, le_add_iff_nonneg_right]
            positivity
          · simp only [pow_add, tsub_le_iff_left] at h'k
            simpa only [hy.1, mem_Icc, true_and, one_div, pow_one] using! h'k
        _ = 4 * (1 / 2) ^ e * (1 / 2) ^ (m + 2) := by ring
        _ ≤ 4 * (1 / 2) ^ e * (y - x) := by gcongr
        _ = 4 * (1 / 2) ^ e * ‖y - x‖ := by rw [Real.norm_of_nonneg yzero.le]
    calc
      ‖f y - f x - (y - x) • f'‖ =
          ‖f y - f x - (y - x) • L e (n e) m + (y - x) • (L e (n e) m - f')‖ := by
        simp only [smul_sub, sub_add_sub_cancel]
      _ ≤ 4 * (1 / 2) ^ e * ‖y - x‖ + ‖y - x‖ * (12 * (1 / 2) ^ e) :=
        norm_add_le_of_le J <| by rw [norm_smul]; gcongr; exact Lf' _ _ m_ge
      _ = 16 * ‖y - x‖ * (1 / 2) ^ e := by ring
      _ ≤ 16 * ‖y - x‖ * (ε / 16) := by gcongr
      _ = ε * ‖y - x‖ := by ring
  -- Conclusion of the proof
  rw [← this.derivWithin (uniqueDiffOn_Ici x x Set.self_mem_Ici)] at f'K
  exact ⟨this.differentiableWithinAt, f'K⟩
/-
**RightDerivMeasurableAux.differentiable_set_eq_D** 是 Mathlib 中的一个定理，位于命名空间 `Rig
htDerivMeasurableAux`。
形式化陈述：differentiable_set_eq_D (hK : IsComplete K) : { x | DifferentiableWithinAt
 Real f (Ici x) x ∧ derivWithin f (Ici x) x in K } = D f K
参数：hK : IsComplete K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `RightDerivMeasurableAux.differentiable_set_subset_D`：differentiable_set_
subset_D : { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWithin f (Ici x)
 x in K } subseteq D f K
· 使用定理 `RightDerivMeasurableAux.D_subset_differentiable_set`：D_subset_differenti
able_set {K : Set F} (hK : IsComplete K) : D f K subseteq { x | DifferentiableWi
thinAt Real f (Ici x) x ∧ derivWithin f (…
-/
theorem differentiable_set_eq_D (hK : IsComplete K) :
    { x | DifferentiableWithinAt ℝ f (Ici x) x ∧ derivWithin f (Ici x) x ∈ K } = D f K :=
  Subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end RightDerivMeasurableAux

open RightDerivMeasurableAux

variable (f)

/-- The set of right differentiability points of a function, with derivative in a given complete
set, is Borel-measurable. -/
/-
**measurableSet_of_differentiableWithinAt_Ici_of_isComplete** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：measurableSet_of_differentiableWithinAt_Ici_of_isComplete {K : Set F} (hK 
: IsComplete K) : MeasurableSet { x | DifferentiableWithinAt Real f (Ici x) x ∧ 
derivWithin f (Ici x) x in K }
参数：hK : IsComplete K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RightDerivMeasurableAux.differentiable_set_eq_D`：differentiable_set_eq_D
 (hK : IsComplete K) : { x | DifferentiableWithinAt Real f (Ici x) x ∧ derivWith
in f (Ici x) x in K } = D f K
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `RightDerivMeasurableAux.measurableSet_B`：measurableSet_B {K : Set F} {r 
s ε : Real} : MeasurableSet (B f K r s ε)

--- 原说明 ---
The set of right differentiability points of a function, with derivative in a gi
ven complete
set, is Borel-measurable.
-/
theorem measurableSet_of_differentiableWithinAt_Ici_of_isComplete {K : Set F} (hK : IsComplete K) :
    MeasurableSet { x | DifferentiableWithinAt ℝ f (Ici x) x ∧ derivWithin f (Ici x) x ∈ K } := by
  -- simp [differentiable_set_eq_d K hK, D, measurableSet_b, MeasurableSet.iInter,
  --   MeasurableSet.iUnion]
  simp only [differentiable_set_eq_D K hK, D]
  repeat apply_rules [MeasurableSet.iUnion, MeasurableSet.iInter] <;> intro
  exact measurableSet_B

variable [CompleteSpace F]

/-- The set of right differentiability points of a function taking values in a complete space is
Borel-measurable. -/
/-
**measurableSet_of_differentiableWithinAt_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_of_differentiableWithinAt_Ici : MeasurableSet { x | Differen
tiableWithinAt Real f (Ici x) x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isComplete_univ`：isComplete_univ {α : Type u} [UniformSpace α] [Complete
Space α] : IsComplete (univ : Set α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `measurableSet_of_differentiableWithinAt_Ici_of_isComplete`：measurableSet
_of_differentiableWithinAt_Ici_of_isComplete {K : Set F} (hK : IsComplete K) : M
easurableSet { x | DifferentiableWithinAt Real …

--- 原说明 ---
The set of right differentiability points of a function taking values in a compl
ete space is
Borel-measurable.
-/
theorem measurableSet_of_differentiableWithinAt_Ici :
    MeasurableSet { x | DifferentiableWithinAt ℝ f (Ici x) x } := by
  have : IsComplete (univ : Set F) := isComplete_univ
  convert! measurableSet_of_differentiableWithinAt_Ici_of_isComplete f this
  simp

@[fun_prop]
/-
**measurable_derivWithin_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_derivWithin_Ici [MeasurableSpace F] [BorelSpace F] : Measurable
 fun x => derivWithin f (Ici x) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_isClosed`：measurable_of_isClosed {f : δ -> γ} (hf : forall
 s, IsClosed s -> MeasurableSet (f ⁻¹' s)) : Measurable f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `derivWithin_mem_iff`：derivWithin_mem_iff {f : 𝕜 -> F} {t : Set 𝕜} {s : S
et F} {x : 𝕜} : derivWithin f t x in s ↔ DifferentiableWithinAt 𝕜 f t x ∧ derivW
ithin f t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `measurableSet_of_differentiableWithinAt_Ici_of_isComplete`：measurableSet
_of_differentiableWithinAt_Ici_of_isComplete {K : Set F} (hK : IsComplete K) : M
easurableSet { x | DifferentiableWithinAt Real …
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `measurableSet_of_differentiableWithinAt_Ici`：measurableSet_of_differenti
ableWithinAt_Ici : MeasurableSet { x | DifferentiableWithinAt Real f (Ici x) x }
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
-/
theorem measurable_derivWithin_Ici [MeasurableSpace F] [BorelSpace F] :
    Measurable fun x => derivWithin f (Ici x) x := by
  refine measurable_of_isClosed fun s hs => ?_
  have :
    (fun x => derivWithin f (Ici x) x) ⁻¹' s =
      { x | DifferentiableWithinAt ℝ f (Ici x) x ∧ derivWithin f (Ici x) x ∈ s } ∪
        { x | ¬DifferentiableWithinAt ℝ f (Ici x) x } ∩ { _x | (0 : F) ∈ s } :=
    Set.ext fun x => mem_preimage.trans derivWithin_mem_iff
  rw [this]
  exact
    (measurableSet_of_differentiableWithinAt_Ici_of_isComplete _ hs.isComplete).union
      ((measurableSet_of_differentiableWithinAt_Ici _).compl.inter (MeasurableSet.const _))
/-
**stronglyMeasurable_derivWithin_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurable_derivWithin_Ici : StronglyMeasurable (fun x => derivWit
hin f (Ici x) x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable_separable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `measurable_derivWithin_Ici`：measurable_derivWithin_Ici [MeasurableSpace 
F] [BorelSpace F] : Measurable fun x => derivWithin f (Ici x) x
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `range_derivWithin_subset_closure_span_image`：range_derivWithin_subset_cl
osure_span_image (f : 𝕜 -> F) {s t : Set 𝕜} (h : s subseteq closure (s inter t))
 : range (derivWithin f s) subset…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsOpen.closure_inter`：IsOpen.closure_inter (h : IsOpen t) : closure s in
ter t subseteq closure (s inter t)
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
（共 42 条，此处仅展示前 30 条）
-/
theorem stronglyMeasurable_derivWithin_Ici :
    StronglyMeasurable (fun x ↦ derivWithin f (Ici x) x) := by
  borelize F
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_derivWithin_Ici f, ?_⟩
  obtain ⟨t, t_count, ht⟩ : ∃ t : Set ℝ, t.Countable ∧ Dense t := exists_countable_dense ℝ
  suffices H : range (fun x ↦ derivWithin f (Ici x) x) ⊆ closure (Submodule.span ℝ (f '' t)) from
    IsSeparable.mono (t_count.image f).isSeparable.span.closure H
  rintro - ⟨x, rfl⟩
  suffices H' : range (fun y ↦ derivWithin f (Ici x) y) ⊆ closure (Submodule.span ℝ (f '' t)) from
    H' (mem_range_self _)
  apply range_derivWithin_subset_closure_span_image
  calc Ici x
    = closure (Ioi x ∩ closure t) := by simp [dense_iff_closure_eq.1 ht]
  _ ⊆ closure (closure (Ioi x ∩ t)) := by
      apply closure_mono
      simpa [inter_comm] using (isOpen_Ioi (a := x)).closure_inter (s := t)
  _ ⊆ closure (Ici x ∩ t) := by
      rw [closure_closure]
      exact closure_mono (inter_subset_inter_left _ Ioi_subset_Ici_self)
/-
**aemeasurable_derivWithin_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_derivWithin_Ici [MeasurableSpace F] [BorelSpace F] (μ : Measu
re Real) : AEMeasurable (fun x => derivWithin f (Ici x) x) μ
参数：μ : Measure Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_derivWithin_Ici`：measurable_derivWithin_Ici [MeasurableSpace 
F] [BorelSpace F] : Measurable fun x => derivWithin f (Ici x) x
-/
theorem aemeasurable_derivWithin_Ici [MeasurableSpace F] [BorelSpace F] (μ : Measure ℝ) :
    AEMeasurable (fun x => derivWithin f (Ici x) x) μ :=
  (measurable_derivWithin_Ici f).aemeasurable
/-
**aestronglyMeasurable_derivWithin_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_derivWithin_Ici (μ : Measure Real) : AEStronglyMeasur
able (fun x => derivWithin f (Ici x) x) μ
参数：μ : Measure Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `stronglyMeasurable_derivWithin_Ici`：stronglyMeasurable_derivWithin_Ici :
 StronglyMeasurable (fun x => derivWithin f (Ici x) x)
-/
theorem aestronglyMeasurable_derivWithin_Ici (μ : Measure ℝ) :
    AEStronglyMeasurable (fun x => derivWithin f (Ici x) x) μ :=
  (stronglyMeasurable_derivWithin_Ici f).aestronglyMeasurable

/-- The set of right differentiability points of a function taking values in a complete space is
Borel-measurable. -/
/-
**measurableSet_of_differentiableWithinAt_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_of_differentiableWithinAt_Ioi : MeasurableSet { x | Differen
tiableWithinAt Real f (Ioi x) x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `measurableSet_of_differentiableWithinAt_Ici`：measurableSet_of_differenti
ableWithinAt_Ici : MeasurableSet { x | DifferentiableWithinAt Real f (Ici x) x }

--- 原说明 ---
The set of right differentiability points of a function taking values in a compl
ete space is
Borel-measurable.
-/
theorem measurableSet_of_differentiableWithinAt_Ioi :
    MeasurableSet { x | DifferentiableWithinAt ℝ f (Ioi x) x } := by
  simpa [differentiableWithinAt_Ioi_iff_Ici] using measurableSet_of_differentiableWithinAt_Ici f

@[fun_prop]
/-
**measurable_derivWithin_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_derivWithin_Ioi [MeasurableSpace F] [BorelSpace F] : Measurable
 fun x => derivWithin f (Ioi x) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `derivWithin_Ioi_eq_Ici`：derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCom
mGroup E] [NormedSpace Real E] (f : Real -> E) (x : Real) : derivWithin f (Ioi x
) x = derivW…
· 使用定理 `measurable_derivWithin_Ici`：measurable_derivWithin_Ici [MeasurableSpace 
F] [BorelSpace F] : Measurable fun x => derivWithin f (Ici x) x
-/
theorem measurable_derivWithin_Ioi [MeasurableSpace F] [BorelSpace F] :
    Measurable fun x => derivWithin f (Ioi x) x := by
  simpa [derivWithin_Ioi_eq_Ici] using measurable_derivWithin_Ici f
/-
**stronglyMeasurable_derivWithin_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurable_derivWithin_Ioi : StronglyMeasurable (fun x => derivWit
hin f (Ioi x) x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `derivWithin_Ioi_eq_Ici`：derivWithin_Ioi_eq_Ici {E : Type*} [NormedAddCom
mGroup E] [NormedSpace Real E] (f : Real -> E) (x : Real) : derivWithin f (Ioi x
) x = derivW…
· 使用定理 `stronglyMeasurable_derivWithin_Ici`：stronglyMeasurable_derivWithin_Ici :
 StronglyMeasurable (fun x => derivWithin f (Ici x) x)
-/
theorem stronglyMeasurable_derivWithin_Ioi :
    StronglyMeasurable (fun x ↦ derivWithin f (Ioi x) x) := by
  simpa [derivWithin_Ioi_eq_Ici] using stronglyMeasurable_derivWithin_Ici f
/-
**aemeasurable_derivWithin_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_derivWithin_Ioi [MeasurableSpace F] [BorelSpace F] (μ : Measu
re Real) : AEMeasurable (fun x => derivWithin f (Ioi x) x) μ
参数：μ : Measure Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_derivWithin_Ioi`：measurable_derivWithin_Ioi [MeasurableSpace 
F] [BorelSpace F] : Measurable fun x => derivWithin f (Ioi x) x
-/
theorem aemeasurable_derivWithin_Ioi [MeasurableSpace F] [BorelSpace F] (μ : Measure ℝ) :
    AEMeasurable (fun x => derivWithin f (Ioi x) x) μ :=
  (measurable_derivWithin_Ioi f).aemeasurable
/-
**aestronglyMeasurable_derivWithin_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_derivWithin_Ioi (μ : Measure Real) : AEStronglyMeasur
able (fun x => derivWithin f (Ioi x) x) μ
参数：μ : Measure Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `stronglyMeasurable_derivWithin_Ioi`：stronglyMeasurable_derivWithin_Ioi :
 StronglyMeasurable (fun x => derivWithin f (Ioi x) x)
-/
theorem aestronglyMeasurable_derivWithin_Ioi (μ : Measure ℝ) :
    AEStronglyMeasurable (fun x => derivWithin f (Ioi x) x) μ :=
  (stronglyMeasurable_derivWithin_Ioi f).aestronglyMeasurable

end RightDeriv

section WithParam

/- In this section, we prove the measurability of the derivative in a context with parameters:
given `f : α → E → F`, we want to show that `p ↦ fderiv 𝕜 (f p.1) p.2` is measurable. Contrary
to the previous sections, some assumptions are needed for this: if `f p.1` depends arbitrarily on
`p.1`, this is obviously false. We require that `f` is continuous and `E` is locally compact --
then the proofs in the previous sections adapt readily, as the set `A` defined above is open, so
that the differentiability set `D` is measurable. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} [TopologicalSpace α]
  {f : α → E → F}

namespace FDerivMeasurableAux

open Uniformity

/-
**FDerivMeasurableAux.isOpen_A_with_param** 是 Mathlib 中的一个引理，位于命名空间 `FDerivMeasu
rableAux`。
形式化陈述：isOpen_A_with_param {r s : Real} (hf : Continuous f.uncurry) (L : E ->L[𝕜]
 F) : IsOpen {p : α × E | p.2 in A (f p.1) L r s}
参数：hf : Continuous f.uncurry；L : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProperSpace.of_locallyCompactSpace`：ProperSpace.of_locallyCompactSpace (
𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [N
ormedSpace 𝕜 E] [Locally…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 137 条，此处仅展示前 30 条）
-/
lemma isOpen_A_with_param {r s : ℝ} (hf : Continuous f.uncurry) (L : E →L[𝕜] F) :
    IsOpen {p : α × E | p.2 ∈ A (f p.1) L r s} := by
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  simp only [A, mem_Ioc, mem_ball, map_sub, mem_ofPred_eq]
  apply isOpen_iff_mem_nhds.2
  rintro ⟨a, x⟩ ⟨r', ⟨Irr', Ir'r⟩, hr⟩
  rcases exists_between Irr' with ⟨t, hrt, htr'⟩
  rcases exists_between hrt with ⟨t', hrt', ht't⟩
  obtain ⟨b, b_lt, hb⟩ : ∃ b, b < s * r ∧ ∀ y ∈ closedBall x t, ∀ z ∈ closedBall x t,
      ‖f a z - f a y - (L z - L y)‖ ≤ b := by
    have B : Continuous (fun (p : E × E) ↦ ‖f a p.2 - f a p.1 - (L p.2 - L p.1)‖) := by fun_prop
    have C : (closedBall x t ×ˢ closedBall x t).Nonempty := by simp; linarith
    rcases ((isCompact_closedBall x t).prod (isCompact_closedBall x t)).exists_isMaxOn
      C B.continuousOn with ⟨p, pt, hp⟩
    simp only [mem_prod, mem_closedBall] at pt
    refine ⟨‖f a p.2 - f a p.1 - (L p.2 - L p.1)‖,
      hr p.1 (pt.1.trans_lt htr') p.2 (pt.2.trans_lt htr'), fun y hy z hz ↦ ?_⟩
    have D : (y, z) ∈ closedBall x t ×ˢ closedBall x t := mem_prod.2 ⟨hy, hz⟩
    exact hp D
  obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ b + 2 * ε < s * r :=
    ⟨(s * r - b) / 3, by linarith, by linarith⟩
  obtain ⟨u, u_open, au, hu⟩ : ∃ u, IsOpen u ∧ a ∈ u ∧ ∀ (p : α × E),
      p.1 ∈ u → p.2 ∈ closedBall x t → dist (f.uncurry p) (f.uncurry (a, p.2)) < ε := by
    have C : Continuous (fun (p : α × E) ↦ f a p.2) := by fun_prop
    have D : ({a} ×ˢ closedBall x t).EqOn f.uncurry (fun p ↦ f a p.2) := by
      rintro ⟨b, y⟩ ⟨hb, -⟩
      simp only [mem_singleton_iff] at hb
      simp [hb]
    obtain ⟨v, v_open, sub_v, hv⟩ : ∃ v, IsOpen v ∧ {a} ×ˢ closedBall x t ⊆ v ∧
        ∀ p ∈ v, dist (Function.uncurry f p) (f a p.2) < ε :=
      Uniform.exists_is_open_mem_uniformity_of_forall_mem_eq (s := {a} ×ˢ closedBall x t)
        (fun p _ ↦ hf.continuousAt) (fun p _ ↦ C.continuousAt) D (dist_mem_uniformity εpos)
    obtain ⟨w, w', w_open, -, sub_w, sub_w', hww'⟩ : ∃ (w : Set α) (w' : Set E),
        IsOpen w ∧ IsOpen w' ∧ {a} ⊆ w ∧ closedBall x t ⊆ w' ∧ w ×ˢ w' ⊆ v :=
      generalized_tube_lemma isCompact_singleton (isCompact_closedBall x t) v_open sub_v
    refine ⟨w, w_open, sub_w rfl, ?_⟩
    rintro ⟨b, y⟩ h hby
    exact hv _ (hww' ⟨h, sub_w' hby⟩)
  have : u ×ˢ ball x (t - t') ∈ 𝓝 (a, x) :=
    prod_mem_nhds (u_open.mem_nhds au) (ball_mem_nhds _ (sub_pos.2 ht't))
  filter_upwards [this]
  rintro ⟨a', x'⟩ ha'x'
  simp only [mem_prod, mem_ball] at ha'x'
  refine ⟨t', ⟨hrt', ht't.le.trans (htr'.le.trans Ir'r)⟩, fun y hy z hz ↦ ?_⟩
  have dyx : dist y x ≤ t := by linarith [dist_triangle y x' x]
  have dzx : dist z x ≤ t := by linarith [dist_triangle z x' x]
  calc
  ‖f a' z - f a' y - (L z - L y)‖ =
    ‖(f a' z - f a z) + (f a y - f a' y) + (f a z - f a y - (L z - L y))‖ := by congr; abel
  _ ≤ ‖f a' z - f a z‖ + ‖f a y - f a' y‖ + ‖f a z - f a y - (L z - L y)‖ := norm_add₃_le
  _ ≤ ε + ε + b := by
      gcongr
      · rw [← dist_eq_norm]
        change dist (f.uncurry (a', z)) (f.uncurry (a, z)) ≤ ε
        apply (hu _ _ _).le
        · exact ha'x'.1
        · simp [dzx]
      · rw [← dist_eq_norm']
        change dist (f.uncurry (a', y)) (f.uncurry (a, y)) ≤ ε
        apply (hu _ _ _).le
        · exact ha'x'.1
        · simp [dyx]
      · simp [hb, dyx, dzx]
  _ < s * r := by linarith
/-
**FDerivMeasurableAux.isOpen_B_with_param** 是 Mathlib 中的一个引理，位于命名空间 `FDerivMeasu
rableAux`。
形式化陈述：isOpen_B_with_param {r s t : Real} (hf : Continuous f.uncurry) (K : Set (E
 ->L[𝕜] F)) : IsOpen {p : α × E | p.2 in B (f p.1) K r s t}
参数：hf : Continuous f.uncurry；K : Set (E ->L[𝕜] F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用引理 `FDerivMeasurableAux.isOpen_A_with_param`：isOpen_A_with_param {r s : Real
} (hf : Continuous f.uncurry) (L : E ->L[𝕜] F) : IsOpen {p : α × E | p.2 in A (f
 p.1) L r s}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isOpen_B_with_param {r s t : ℝ} (hf : Continuous f.uncurry) (K : Set (E →L[𝕜] F)) :
    IsOpen {p : α × E | p.2 ∈ B (f p.1) K r s t} := by
  suffices H : IsOpen (⋃ L ∈ K,
      {p : α × E | p.2 ∈ A (f p.1) L r t ∧ p.2 ∈ A (f p.1) L s t}) by
    convert! H; ext p; simp [B]
  refine isOpen_biUnion (fun L _ ↦ ?_)
  exact (isOpen_A_with_param hf L).inter (isOpen_A_with_param hf L)

end FDerivMeasurableAux

open FDerivMeasurableAux

variable [MeasurableSpace α] [OpensMeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E]

/-
**measurableSet_of_differentiableAt_of_isComplete_with_param** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：measurableSet_of_differentiableAt_of_isComplete_with_param (hf : Continuou
s f.uncurry) {K : Set (E ->L[𝕜] F)} (hK : IsComplete K) : MeasurableSet {p : α ×
 E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 in K}
参数：hf : Continuous f.uncurry；E ->L[𝕜] F；hK : IsComplete K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FDerivMeasurableAux.differentiable_set_eq_D`：differentiable_set_eq_D (hK
 : IsComplete K) : { x | DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in K } = D f K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用引理 `ProperSpace.of_locallyCompactSpace`：ProperSpace.of_locallyCompactSpace (
𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [N
ormedSpace 𝕜 E] [Locally…
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用引理 `FDerivMeasurableAux.isOpen_B_with_param`：isOpen_B_with_param {r s t : Re
al} (hf : Continuous f.uncurry) (K : Set (E ->L[𝕜] F)) : IsOpen {p : α × E | p.2
 in B (f p.1) K r s t}
-/
theorem measurableSet_of_differentiableAt_of_isComplete_with_param
    (hf : Continuous f.uncurry) {K : Set (E →L[𝕜] F)} (hK : IsComplete K) :
    MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 ∈ K} := by
  have : {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 ∈ K}
          = {p : α × E | p.2 ∈ D (f p.1) K} := by simp [← differentiable_set_eq_D K hK]
  rw [this]
  simp only [D, mem_iInter, mem_iUnion]
  simp only [ofPred_forall, ofPred_exists]
  refine MeasurableSet.iInter (fun _ ↦ ?_)
  refine MeasurableSet.iUnion (fun _ ↦ ?_)
  refine MeasurableSet.iInter (fun _ ↦ ?_)
  refine MeasurableSet.iInter (fun _ ↦ ?_)
  refine MeasurableSet.iInter (fun _ ↦ ?_)
  refine MeasurableSet.iInter (fun _ ↦ ?_)
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  exact (isOpen_B_with_param hf K).measurableSet

variable (𝕜)
variable [CompleteSpace F]

/-- The set of differentiability points of a continuous function depending on a parameter taking
values in a complete space is Borel-measurable. -/
/-
**measurableSet_of_differentiableAt_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_of_differentiableAt_with_param (hf : Continuous f.uncurry) :
 MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2}
参数：hf : Continuous f.uncurry。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `isComplete_univ`：isComplete_univ {α : Type u} [UniformSpace α] [Complete
Space α] : IsComplete (univ : Set α)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `measurableSet_of_differentiableAt_of_isComplete_with_param`：measurableSe
t_of_differentiableAt_of_isComplete_with_param (hf : Continuous f.uncurry) {K : 
Set (E ->L[𝕜] F)} (hK : IsComplete K) : Measurab…

--- 原说明 ---
The set of differentiability points of a continuous function depending on a para
meter taking
values in a complete space is Borel-measurable.
-/
theorem measurableSet_of_differentiableAt_with_param (hf : Continuous f.uncurry) :
    MeasurableSet {p : α × E | DifferentiableAt 𝕜 (f p.1) p.2} := by
  have : IsComplete (univ : Set (E →L[𝕜] F)) := isComplete_univ
  convert! measurableSet_of_differentiableAt_of_isComplete_with_param hf this
  simp
/-
**measurable_fderiv_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fderiv_with_param (hf : Continuous f.uncurry) : Measurable (fun
 (p : α × E) => fderiv 𝕜 (f p.1) p.2)
参数：hf : Continuous f.uncurry。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_isClosed`：measurable_of_isClosed {f : δ -> γ} (hf : forall
 s, IsClosed s -> MeasurableSet (f ⁻¹' s)) : Measurable f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `fderiv_mem_iff`：fderiv_mem_iff {f : E -> F} {s : Set (E ->L[𝕜] F)} {x : 
E} : fderiv 𝕜 f x in s ↔ DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x in s ∨ ¬Different
iabl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `measurableSet_of_differentiableAt_of_isComplete_with_param`：measurableSe
t_of_differentiableAt_of_isComplete_with_param (hf : Continuous f.uncurry) {K : 
Set (E ->L[𝕜] F)} (hK : IsComplete K) : Measurab…
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `measurableSet_of_differentiableAt_with_param`：measurableSet_of_different
iableAt_with_param (hf : Continuous f.uncurry) : MeasurableSet {p : α × E | Diff
erentiableAt 𝕜 (f p.1) p.2}
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
-/
theorem measurable_fderiv_with_param (hf : Continuous f.uncurry) :
    Measurable (fun (p : α × E) ↦ fderiv 𝕜 (f p.1) p.2) := by
  refine measurable_of_isClosed (fun s hs ↦ ?_)
  have :
    (fun (p : α × E) ↦ fderiv 𝕜 (f p.1) p.2) ⁻¹' s =
      {p | DifferentiableAt 𝕜 (f p.1) p.2 ∧ fderiv 𝕜 (f p.1) p.2 ∈ s } ∪
        { p | ¬DifferentiableAt 𝕜 (f p.1) p.2} ∩ { _p | (0 : E →L[𝕜] F) ∈ s} :=
    Set.ext (fun x ↦ mem_preimage.trans fderiv_mem_iff)
  rw [this]
  exact
    (measurableSet_of_differentiableAt_of_isComplete_with_param hf hs.isComplete).union
      ((measurableSet_of_differentiableAt_with_param _ hf).compl.inter (MeasurableSet.const _))
/-
**measurable_fderiv_apply_const_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fderiv_apply_const_with_param [MeasurableSpace F] [BorelSpace F
] (hf : Continuous f.uncurry) (y : E) : Measurable (fun (p : α × E) => fderiv 𝕜 
(f p.1) p.2 y)
参数：hf : Continuous f.uncurry；y : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `ContinuousLinearMap.measurable_apply`：measurable_apply [MeasurableSpace 
F] [BorelSpace F] (x : E) : Measurable fun f : E ->L[𝕜] F => f x
· 使用定理 `measurable_fderiv_with_param`：measurable_fderiv_with_param (hf : Continu
ous f.uncurry) : Measurable (fun (p : α × E) => fderiv 𝕜 (f p.1) p.2)
-/
theorem measurable_fderiv_apply_const_with_param [MeasurableSpace F] [BorelSpace F]
    (hf : Continuous f.uncurry) (y : E) :
    Measurable (fun (p : α × E) ↦ fderiv 𝕜 (f p.1) p.2 y) :=
  (ContinuousLinearMap.measurable_apply y).comp (measurable_fderiv_with_param 𝕜 hf)

variable {𝕜}
/-
**measurable_deriv_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [O
pensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] {f : α -> 𝕜 -> F} (hf 
: Continuous f.uncurry) : Measurable (fun (p : α × 𝕜) => deriv (f p.1) p.2)
参数：hf : Continuous f.uncurry。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fderiv_apply_const_with_param`：measurable_fderiv_apply_const_
with_param [MeasurableSpace F] [BorelSpace F] (hf : Continuous f.uncurry) (y : E
) : Measurable (fun (p : α × E…
-/
theorem measurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] {f : α → 𝕜 → F} (hf : Continuous f.uncurry) :
    Measurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2) := by
  simpa only [fderiv_apply_one_eq_deriv] using measurable_fderiv_apply_const_with_param 𝕜 hf 1
/-
**stronglyMeasurable_deriv_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stronglyMeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpa
ce 𝕜] [OpensMeasurableSpace 𝕜] [h : SecondCountableTopologyEither α F] {f : α ->
 𝕜 -> F} (hf : Continuous f.uncurry) : StronglyMeasurable (fun (p : α × 𝕜) => de
riv (f p.1) p.2)
参数：hf : Continuous f.uncurry。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SecondCountableTopologyEither.out`：∀ {α : Type u_6} {β : Type u_7} {inst
 : TopologicalSpace α} {inst_1 : TopologicalSpace β}   [self : SecondCountableTo
pologyEither α β], Seco…
· 使用引理 `ProperSpace.of_locallyCompactSpace`：ProperSpace.of_locallyCompactSpace (
𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [N
ormedSpace 𝕜 E] [Locally…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable_separable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `measurable_deriv_with_param`：measurable_deriv_with_param [LocallyCompact
Space 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [Borel
Space F] {f : α -…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `range_deriv_subset_closure_span_image`：range_deriv_subset_closure_span_i
mage (f : 𝕜 -> F) {t : Set 𝕜} (h : Dense t) : range (deriv f) subseteq closure (
Submodule.span 𝕜 (f '' t))
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `TopologicalSpace.IsSeparable.mono`：∀ {α : Type u} [t : TopologicalSpace 
α] {s u : Set α},   TopologicalSpace.IsSeparable s → u ⊆ s → TopologicalSpace.Is
Separable u
· 使用定理 `TopologicalSpace.IsSeparable.closure`：∀ {α : Type u} [t : TopologicalSpa
ce α] {s : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le (closure s)
· 使用引理 `TopologicalSpace.IsSeparable.span`：TopologicalSpace.IsSeparable.span {R 
M : Type*} [AddCommMonoid M] [Semiring R] [Module R M] [TopologicalSpace M] [Top
ologicalSpace R] [Separ…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.isSeparable_range`：isSeparable_range [TopologicalSpace 
β] [SeparableSpace α] {f : α -> β} (hf : Continuous f) : IsSeparable (range f)
· 使用定理 `TopologicalSpace.instSeparableSpaceProd`：∀ {α : Type u} {β : Type u_1} [
t : TopologicalSpace α] [inst : TopologicalSpace β] [TopologicalSpace.SeparableS
pace α]   [TopologicalSpace.S…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem stronglyMeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [h : SecondCountableTopologyEither α F]
    {f : α → 𝕜 → F} (hf : Continuous f.uncurry) :
    StronglyMeasurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2) := by
  borelize F
  rcases h.out with hα | hF
  · have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
    apply stronglyMeasurable_iff_measurable_separable.2 ⟨measurable_deriv_with_param hf, ?_⟩
    have : range (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2)
        ⊆ closure (Submodule.span 𝕜 (range f.uncurry)) := by
      rintro - ⟨p, rfl⟩
      have A : deriv (f p.1) p.2 ∈ closure (Submodule.span 𝕜 (range (f p.1))) := by
        rw [← image_univ]
        apply range_deriv_subset_closure_span_image _ dense_univ (mem_range_self _)
      have B : range (f p.1) ⊆ range (f.uncurry) := by
        rintro - ⟨x, rfl⟩
        exact mem_range_self (p.1, x)
      exact closure_mono (Submodule.span_mono B) A
    exact (isSeparable_range hf).span.closure.mono this
  · exact (measurable_deriv_with_param hf).stronglyMeasurable
/-
**aemeasurable_deriv_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] 
[OpensMeasurableSpace 𝕜] [MeasurableSpace F] [BorelSpace F] {f : α -> 𝕜 -> F} (h
f : Continuous f.uncurry) (μ : Measure (α × 𝕜)) : AEMeasurable (fun (p : α × 𝕜) 
=> deriv (f p.1) p.2) μ
参数：hf : Continuous f.uncurry；μ : Measure (α × 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_deriv_with_param`：measurable_deriv_with_param [LocallyCompact
Space 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [MeasurableSpace F] [Borel
Space F] {f : α -…
-/
theorem aemeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [MeasurableSpace F]
    [BorelSpace F] {f : α → 𝕜 → F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜)) :
    AEMeasurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2) μ :=
  (measurable_deriv_with_param hf).aemeasurable
/-
**aestronglyMeasurable_deriv_with_param** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableS
pace 𝕜] [OpensMeasurableSpace 𝕜] [SecondCountableTopologyEither α F] {f : α -> 𝕜
 -> F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜)) : AEStronglyMeasurable 
(fun (p : α × 𝕜) => deriv (f p.1) p.2) μ
参数：hf : Continuous f.uncurry；μ : Measure (α × 𝕜)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `stronglyMeasurable_deriv_with_param`：stronglyMeasurable_deriv_with_param
 [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [h : Secon
dCountableTopologyEither …
-/
theorem aestronglyMeasurable_deriv_with_param [LocallyCompactSpace 𝕜] [MeasurableSpace 𝕜]
    [OpensMeasurableSpace 𝕜] [SecondCountableTopologyEither α F]
    {f : α → 𝕜 → F} (hf : Continuous f.uncurry) (μ : Measure (α × 𝕜)) :
    AEStronglyMeasurable (fun (p : α × 𝕜) ↦ deriv (f p.1) p.2) μ :=
  (stronglyMeasurable_deriv_with_param hf).aestronglyMeasurable

end WithParam

