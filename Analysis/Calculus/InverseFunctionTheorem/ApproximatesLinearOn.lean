/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Non-linear maps close to affine maps

In this file we study a map `f` such that `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `ApproximatesLinearOn.toOpenPartialHomeomorph`
to be an `OpenPartialHomeomorph` with `toFun = f`, `source = s`, and `target = f '' s`.
between `s` and `f '' s`. More precisely, we define `ApproximatesLinearOn.toOpenPartialHomeomorph`
to be an `OpenPartialHomeomorph` with `toFun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `ApproximatesLinearOn.toOpenPartialHomeomorph` will imply that the locally inverse function
and `ApproximatesLinearOn.toOpenPartialHomeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.

## Notation

We introduce some `local notation` to make formulas shorter:

* by `N` we denote `‖f'⁻¹‖`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.
-/

@[expose] public section

open Function Set Filter Metric

open scoped Topology NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ε : ℝ}

open Filter Metric Set

open ContinuousLinearMap (id)

/-- We say that `f` approximates a continuous linear map `f'` on `s` with constant `c`,
if `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function theorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
/-
**ApproximatesLinearOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ApproximatesLinearOn (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (c : Real>
=0) : Prop
参数：f : E -> F；f' : E ->L[𝕜] F；s : Set E；c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `f` approximates a continuous linear map `f'` on `s` with constant `
c`,
if `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function th
eorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse func
tion is defined
on a specific set.
-/
def ApproximatesLinearOn (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (c : ℝ≥0) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖

@[simp]
/-
**approximatesLinearOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：approximatesLinearOn_empty (f : E -> F) (f' : E ->L[𝕜] F) (c : Real>=0) : 
ApproximatesLinearOn f f' ∅ c
参数：f : E -> F；f' : E ->L[𝕜] F；c : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem approximatesLinearOn_empty (f : E → F) (f' : E →L[𝕜] F) (c : ℝ≥0) :
    ApproximatesLinearOn f f' ∅ c := by simp [ApproximatesLinearOn]

namespace ApproximatesLinearOn

variable {f : E → F}

/-! First we prove some properties of a function that `ApproximatesLinearOn` a (not necessarily
invertible) continuous linear map. -/


section

variable {f' : E →L[𝕜] F} {s t : Set E} {c c' : ℝ≥0}

/-
**ApproximatesLinearOn.mono_num** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearOn`
。
形式化陈述：mono_num (hc : c <= c') (hf : ApproximatesLinearOn f f' s c) : Approximate
sLinearOn f f' s c'
参数：hc : c <= c'；hf : ApproximatesLinearOn f f' s c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem mono_num (hc : c ≤ c') (hf : ApproximatesLinearOn f f' s c) :
    ApproximatesLinearOn f f' s c' :=
  fun x hx y hy ↦ le_trans (hf x hx y hy) (by gcongr)
/-
**ApproximatesLinearOn.mono_set** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearOn`
。
形式化陈述：mono_set (hst : s subseteq t) (hf : ApproximatesLinearOn f f' t c) : Appro
ximatesLinearOn f f' s c
参数：hst : s subseteq t；hf : ApproximatesLinearOn f f' t c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono_set (hst : s ⊆ t) (hf : ApproximatesLinearOn f f' t c) :
    ApproximatesLinearOn f f' s c := fun x hx y hy ↦ hf x (hst hx) y (hst hy)
/-
**ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith** 是 Mathlib 中的一个
定理，位于命名空间 `ApproximatesLinearOn`。
形式化陈述：approximatesLinearOn_iff_lipschitzOnWith {f : E -> F} {f' : E ->L[𝕜] F} {s
 : Set E} {c : Real>=0} : ApproximatesLinearOn f f' s c ↔ LipschitzOnWith c (f -
 ⇑f') s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `_private.Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLi
nearOn.0.ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith._abel_1_1
`：∀ {𝕜 : Type u_3} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : N
ormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem approximatesLinearOn_iff_lipschitzOnWith {f : E → F} {f' : E →L[𝕜] F} {s : Set E}
    {c : ℝ≥0} : ApproximatesLinearOn f f' s c ↔ LipschitzOnWith c (f - ⇑f') s := by
  have : ∀ x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y := fun x y ↦ by
    simp only [map_sub, Pi.sub_apply]; abel
  simp only [this, lipschitzOnWith_iff_norm_sub_le, ApproximatesLinearOn]

alias ⟨lipschitzOnWith, _root_.LipschitzOnWith.approximatesLinearOn⟩ :=
  approximatesLinearOn_iff_lipschitzOnWith
/-
**ApproximatesLinearOn.lipschitz_sub** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLine
arOn`。
形式化陈述：lipschitz_sub (hf : ApproximatesLinearOn f f' s c) : LipschitzWith c fun x
 : s => f x - f' x
参数：hf : ApproximatesLinearOn f f' s c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.to_restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : α
 → β}, LipschitzO…
· 使用定理 `ApproximatesLinearOn.lipschitzOnWith`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
theorem lipschitz_sub (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith c fun x : s => f x - f' x :=
  hf.lipschitzOnWith.to_restrict
/-
**ApproximatesLinearOn.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearOn
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E →L[𝕜] F} {
s : Set E} {c : NNReal}, ApproximatesLinearOn f f' s c → LipschitzWith (‖f'‖₊ + 
c) (s.domRestrict f)
参数：‖f'‖₊ + c；s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `LipschitzWith.add`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] [inst_1 : PseudoEMetricSpace α] {Kf Kg : NNReal}   {f g : α → E}, L
ipschit…
· 使用定理 `LipschitzWith.restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzW
ith K f → ∀ …
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `ApproximatesLinearOn.lipschitz_sub`：lipschitz_sub (hf : ApproximatesLine
arOn f f' s c) : LipschitzWith c fun x : s => f x - f' x
-/
protected theorem lipschitz (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith (‖f'‖₊ + c) (s.domRestrict f) := by
  simpa only [domRestrict_apply, add_sub_cancel] using!
    (f'.lipschitz.restrict s).add hf.lipschitz_sub
/-
**ApproximatesLinearOn.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearO
n`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E →L[𝕜] F} {
s : Set E} {c : NNReal}, ApproximatesLinearOn f f' s c → Continuous (s.domRestri
ct f)
参数：s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `ApproximatesLinearOn.lipschitz`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem continuous (hf : ApproximatesLinearOn f f' s c) : Continuous (s.domRestrict f) :=
  hf.lipschitz.continuous
/-
**ApproximatesLinearOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinea
rOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E →L[𝕜] F} {
s : Set E} {c : NNReal}, ApproximatesLinearOn f f' s c → ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `ApproximatesLinearOn.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type u_…
-/
protected theorem continuousOn (hf : ApproximatesLinearOn f f' s c) : ContinuousOn f s :=
  continuousOn_iff_continuous_domRestrict.2 hf.continuous

end

section LocallyOnto

/-!
We prove that a function which is linearly approximated by a continuous linear map with a nonlinear
right inverse is locally onto. This will apply to the case where the approximating map is a linear
equivalence, for the local inverse theorem, but also whenever the approximating map is onto,
by Banach's open mapping theorem. -/


variable [CompleteSpace E] {s : Set E} {c : ℝ≥0} {f' : E →L[𝕜] F}

/-- If a function is linearly approximated by a continuous linear map with a (possibly nonlinear)
right inverse, then it is locally onto: a ball of an explicit radius is included in the image
of the map. -/
/-
**ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse** 是 Mathlib 中的
一个定理，位于命名空间 `ApproximatesLinearOn`。
形式化陈述：surjOn_closedBall_of_nonlinearRightInverse (hf : ApproximatesLinearOn f f'
 s c) (f'symm : f'.NonlinearRightInverse) {ε : Real} {b : E} (ε0 : 0 <= ε) (hε :
 closedBall b ε subseteq s) : SurjOn f (closedBall b ε) (closedBall (f b) (((f's
ymm.nnnorm : Real)⁻¹ - c) * ε))
参数：hf : ApproximatesLinearOn f f' s c；f'symm : f'.NonlinearRightInverse；ε0 : 0 <
= ε；hε : closedBall b ε subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 184 条，此处仅展示前 30 条）

--- 原说明 ---
If a function is linearly approximated by a continuous linear map with a (possib
ly nonlinear)
right inverse, then it is locally onto: a ball of an explicit radius is included
 in the image
of the map.
-/
theorem surjOn_closedBall_of_nonlinearRightInverse
    (hf : ApproximatesLinearOn f f' s c)
    (f'symm : f'.NonlinearRightInverse) {ε : ℝ} {b : E} (ε0 : 0 ≤ ε) (hε : closedBall b ε ⊆ s) :
    SurjOn f (closedBall b ε) (closedBall (f b) (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε)) := by
  intro y hy
  rcases le_or_gt (f'symm.nnnorm : ℝ)⁻¹ c with hc | hc
  · refine ⟨b, by simp [ε0], ?_⟩
    have : dist y (f b) ≤ 0 :=
      (mem_closedBall.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0)
    simp only [dist_le_zero] at this
    rw [this]
  have If' : (0 : ℝ) < f'symm.nnnorm := by rw [← inv_pos]; exact (NNReal.coe_nonneg _).trans_lt hc
  have Icf' : (c : ℝ) * f'symm.nnnorm < 1 := by rwa [inv_eq_one_div, lt_div_iff₀ If'] at hc
  have Jcf' : (1 : ℝ) - c * f'symm.nnnorm ≠ 0 := by apply ne_of_gt; linarith
  /- We have to show that `y` can be written as `f x` for some `x ∈ closedBall b ε`.
    The idea of the proof is to apply the Banach contraction principle to the map
    `g : x ↦ x + f'symm (y - f x)`, as a fixed point of this map satisfies `f x = y`.
    When `f'symm` is a genuine linear inverse, `g` is a contracting map. In our case, since `f'symm`
    is nonlinear, this map is not contracting (it is not even continuous), but still the proof of
    the contraction theorem holds: `uₙ = gⁿ b` is a Cauchy sequence, converging exponentially fast
    to the desired point `x`. Instead of appealing to general results, we check this by hand.

    The main point is that `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentially small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` stays in the ball on which one has a
    control. Therefore, the bound can be checked at the next step, and so on inductively.
    -/
  set g := fun x => x + f'symm (y - f x) with hg
  set u := fun n : ℕ => g^[n] b with hu
  have usucc : ∀ n, u (n + 1) = g (u n) := by simp [hu, ← iterate_succ_apply' g _ b]
  -- First bound: if `f z` is close to `y`, then `g z` is close to `z` (i.e., almost a fixed point).
  have A : ∀ z, dist (g z) z ≤ f'symm.nnnorm * dist (f z) y := by
    intro z
    rw [dist_eq_norm, hg, add_sub_cancel_left, dist_eq_norm']
    exact f'symm.bound _
  -- Second bound: if `z` and `g z` are in the set with good control, then `f (g z)` becomes closer
  -- to `y` than `f z` was (this uses the linear approximation property, and is the reason for the
  -- choice of the formula for `g`).
  have B :
    ∀ z ∈ closedBall b ε,
      g z ∈ closedBall b ε → dist (f (g z)) y ≤ c * f'symm.nnnorm * dist (f z) y := by
    intro z hz hgz
    set v := f'symm (y - f z)
    calc
      dist (f (g z)) y = ‖f (z + v) - y‖ := by rw [dist_eq_norm]
      _ = ‖f (z + v) - f z - f' v + f' v - (y - f z)‖ := by congr 1; abel
      _ = ‖f (z + v) - f z - f' (z + v - z)‖ := by
        simp only [v, ContinuousLinearMap.NonlinearRightInverse.right_inv, add_sub_cancel_left,
          sub_add_cancel]
      _ ≤ c * ‖z + v - z‖ := hf _ (hε hgz) _ (hε hz)
      _ ≤ c * (f'symm.nnnorm * dist (f z) y) := by
        gcongr
        simpa [dist_eq_norm'] using f'symm.bound (y - f z)
      _ = c * f'symm.nnnorm * dist (f z) y := by ring
  -- Third bound: a complicated bound on `dist w b` (that will show up in the induction) is enough
  -- to check that `w` is in the ball on which one has controls. Will be used to check that `u n`
  -- belongs to this ball for all `n`.
  have C : ∀ (n : ℕ) (w : E), dist w b ≤ f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) /
      (1 - c * f'symm.nnnorm) * dist (f b) y → w ∈ closedBall b ε := fun n w hw ↦ by
    apply hw.trans
    rw [div_mul_eq_mul_div, div_le_iff₀]; swap; · linarith
    calc
      (f'symm.nnnorm : ℝ) * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) * dist (f b) y =
          f'symm.nnnorm * dist (f b) y * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) := by
        ring
      _ ≤ f'symm.nnnorm * dist (f b) y * 1 := by
        gcongr
        rw [sub_le_self_iff]
        positivity
      _ ≤ f'symm.nnnorm * (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε) := by
        rw [mul_one]
        gcongr
        exact mem_closedBall'.1 hy
      _ = ε * (1 - c * f'symm.nnnorm) := by field
  /- Main inductive control: `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentially small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` remains in the ball on which we
    have estimates. -/
  have D : ∀ n : ℕ, dist (f (u n)) y ≤ ((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y ∧
      dist (u n) b ≤ f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) /
        (1 - (c : ℝ) * f'symm.nnnorm) * dist (f b) y := fun n ↦ by
    induction n with
    | zero => simp [hu]
    | succ n IH => ?_
    rw [usucc]
    have Ign : dist (g (u n)) b ≤ f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n.succ) /
        (1 - c * f'symm.nnnorm) * dist (f b) y :=
      calc
        dist (g (u n)) b ≤ dist (g (u n)) (u n) + dist (u n) b := dist_triangle _ _ _
        _ ≤ f'symm.nnnorm * dist (f (u n)) y + dist (u n) b := add_le_add (A _) le_rfl
        _ ≤ f'symm.nnnorm * (((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y) +
              f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) *
                dist (f b) y := by
                  gcongr
                  · exact IH.1
                  · exact IH.2
        _ = f'symm.nnnorm * (1 - ((c : ℝ) * f'symm.nnnorm) ^ n.succ) /
              (1 - (c : ℝ) * f'symm.nnnorm) * dist (f b) y := by
          replace Jcf' : (1 : ℝ) - f'symm.nnnorm * c ≠ 0 := by convert! Jcf' using 1; ring
          simp [field, pow_succ, -mul_eq_mul_left_iff]
          ring
    refine ⟨?_, Ign⟩
    calc
      dist (f (g (u n))) y ≤ c * f'symm.nnnorm * dist (f (u n)) y :=
        B _ (C n _ IH.2) (C n.succ _ Ign)
      _ ≤ (c : ℝ) * f'symm.nnnorm * (((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y) := by
        gcongr
        apply IH.1
      _ = ((c : ℝ) * f'symm.nnnorm) ^ n.succ * dist (f b) y := by simp only [pow_succ']; ring
  -- Deduce from the inductive bound that `uₙ` is a Cauchy sequence, therefore converging.
  have : CauchySeq u := by
    refine cauchySeq_of_le_geometric _ (↑f'symm.nnnorm * dist (f b) y) Icf' fun n ↦ ?_
    calc
      dist (u n) (u (n + 1)) = dist (g (u n)) (u n) := by rw [usucc, dist_comm]
      _ ≤ f'symm.nnnorm * dist (f (u n)) y := A _
      _ ≤ f'symm.nnnorm * (((c : ℝ) * f'symm.nnnorm) ^ n * dist (f b) y) := by
        gcongr
        exact (D n).1
      _ = f'symm.nnnorm * dist (f b) y * ((c : ℝ) * f'symm.nnnorm) ^ n := by ring
  obtain ⟨x, hx⟩ : ∃ x, Tendsto u atTop (𝓝 x) := cauchySeq_tendsto_of_complete this
  -- As all the `uₙ` belong to the ball `closedBall b ε`, so does their limit `x`.
  have xmem : x ∈ closedBall b ε :=
    isClosed_closedBall.mem_of_tendsto hx (Eventually.of_forall fun n => C n _ (D n).2)
  refine ⟨x, xmem, ?_⟩
  -- It remains to check that `f x = y`. This follows from continuity of `f` on `closedBall b ε`
  -- and from the fact that `f uₙ` is converging to `y` by construction.
  have hx' : Tendsto u atTop (𝓝[closedBall b ε] x) := by
    simp only [nhdsWithin, tendsto_inf, hx, true_and, tendsto_principal]
    exact Eventually.of_forall fun n => C n _ (D n).2
  have T1 : Tendsto (f ∘ u) atTop (𝓝 (f x)) :=
    (hf.continuousOn.mono hε x xmem).tendsto.comp hx'
  have T2 : Tendsto (f ∘ u) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => (D n).1) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) Icf').mul tendsto_const_nhds
  exact tendsto_nhds_unique T1 T2
/-
**ApproximatesLinearOn.open_image** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearO
n`。
形式化陈述：open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRigh
tInverse) (hs : IsOpen s) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (
f '' s)
参数：hf : ApproximatesLinearOn f f' s c；f'symm : f'.NonlinearRightInverse；hs : IsO
pen s；hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`：surjOn_
closedBall_of_nonlinearRightInverse (hf : ApproximatesLinearOn f f' s c) (f'symm
 : f'.NonlinearRightInverse) {ε : Real} {b : E} (ε0 :…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    (hs : IsOpen s) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (f '' s) := by
  rcases hc with hE | hc
  · exact isOpen_discrete _
  simp only [isOpen_iff_mem_nhds, nhds_basis_closedBall.mem_iff, forall_mem_image] at hs ⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, ?_⟩
  exact (hf.surjOn_closedBall_of_nonlinearRightInverse f'symm (le_of_lt ε0) hε).mono hε Subset.rfl
/-
**ApproximatesLinearOn.image_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLin
earOn`。
形式化陈述：image_mem_nhds (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.Nonlinear
RightInverse) {x : E} (hs : s in 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹
) : f '' s in 𝓝 (f x)
参数：hf : ApproximatesLinearOn f f' s c；f'symm : f'.NonlinearRightInverse；hs : s i
n 𝓝 x；hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `ApproximatesLinearOn.open_image`：open_image (hf : ApproximatesLinearOn f
 f' s c) (f'symm : f'.NonlinearRightInverse) (hs : IsOpen s) (hc : Subsingleton 
F ∨ c < f'symm.nnnorm…
· 使用定理 `ApproximatesLinearOn.mono_set`：mono_set (hst : s subseteq t) (hf : Appro
ximatesLinearOn f f' t c) : ApproximatesLinearOn f f' s c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem image_mem_nhds (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    {x : E} (hs : s ∈ 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : f '' s ∈ 𝓝 (f x) := by
  obtain ⟨t, hts, ht, xt⟩ : ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := _root_.mem_nhds_iff.1 hs
  grw [← hts]
  exact IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)
/-
**ApproximatesLinearOn.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinear
On`。
形式化陈述：map_nhds_eq (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRig
htInverse) {x : E} (hs : s in 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) :
 map f (𝓝 x) = 𝓝 (f x)
参数：hf : ApproximatesLinearOn f f' s c；f'symm : f'.NonlinearRightInverse；hs : s i
n 𝓝 x；hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `ApproximatesLinearOn.continuousOn`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Filter.le_map`：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : fo
rall s in f, m '' s in g) : g <= f.map m
· 使用定理 `ApproximatesLinearOn.image_mem_nhds`：image_mem_nhds (hf : ApproximatesLi
nearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E} (hs : s in 𝓝 x) (hc
 : Subsingleton F ∨ c < f…
· 使用定理 `ApproximatesLinearOn.mono_set`：mono_set (hst : s subseteq t) (hf : Appro
ximatesLinearOn f f' t c) : ApproximatesLinearOn f f' s c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem map_nhds_eq (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E}
    (hs : s ∈ 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : map f (𝓝 x) = 𝓝 (f x) := by
  refine
    le_antisymm ((hf.continuousOn x (mem_of_mem_nhds hs)).continuousAt hs) (le_map fun t ht => ?_)
  have : f '' (s ∩ t) ∈ 𝓝 (f x) :=
    (hf.mono_set inter_subset_left).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_mono inter_subset_right)

end LocallyOnto

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ‖f'⁻¹‖⁻¹`. We use `N` as an abbreviation for `‖f'⁻¹‖`.
-/


variable {f' : E ≃L[𝕜] F} {s : Set E} {c : ℝ≥0}

local notation "N" => ‖(f'.symm : F →L[𝕜] E)‖₊

/-
**ApproximatesLinearOn.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLine
arOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E ≃L[𝕜] F} {
s : Set E} {c : NNReal},   ApproximatesLinearOn f (↑f') s c →     Subsingleton E
 ∨ c < ‖↑f'.symm‖₊⁻¹ → AntilipschitzWith (‖↑f'.symm‖₊⁻¹ - c)⁻¹ (s.domRestrict f)
参数：↑f'；‖↑f'.symm‖₊⁻¹ - c；s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.of_subsingleton`：of_subsingleton [Subsingleton α] {K :
 Real>=0} : AntilipschitzWith K f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AntilipschitzWith.add_lipschitzWith`：∀ {α : Type u_4} {E : Type u_5} [in
st : SeminormedAddCommGroup E] [inst_1 : PseudoEMetricSpace α] {Kf Kg : NNReal} 
  {f g : α → E},   Antili…
· 使用定理 `AntilipschitzWith.domRestrict`：domRestrict (hf : AntilipschitzWith K f) 
(s : Set α) : AntilipschitzWith K (s.domRestrict f)
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…
· 使用定理 `ApproximatesLinearOn.lipschitz_sub`：lipschitz_sub (hf : ApproximatesLine
arOn f f' s c) : LipschitzWith c fun x : s => f x - f' x
-/
protected theorem antilipschitz (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : AntilipschitzWith (N⁻¹ - c)⁻¹ (s.domRestrict f) := by
  rcases hc with hE | hc
  · exact AntilipschitzWith.of_subsingleton
  convert! (f'.antilipschitz.domRestrict s).add_lipschitzWith hf.lipschitz_sub hc
  simp [domRestrict]
/-
**ApproximatesLinearOn.injective** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearOn
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E ≃L[𝕜] F} {
s : Set E} {c : NNReal},   ApproximatesLinearOn f (↑f') s c → Subsingleton E ∨ c
 < ‖↑f'.symm‖₊⁻¹ → Function.Injective (s.domRestrict f)
参数：↑f'；s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …
· 使用定理 `ApproximatesLinearOn.antilipschitz`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Type u_…
-/
protected theorem injective (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Injective (s.domRestrict f) :=
  (hf.antilipschitz hc).injective
/-
**ApproximatesLinearOn.injOn** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E ≃L[𝕜] F} {
s : Set E} {c : NNReal},   ApproximatesLinearOn f (↑f') s c → Subsingleton E ∨ c
 < ‖↑f'.symm‖₊⁻¹ → Set.InjOn f s
参数：↑f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `ApproximatesLinearOn.injective`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
-/
protected theorem injOn (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : InjOn f s :=
  injOn_iff_injective.2 <| hf.injective hc
/-
**ApproximatesLinearOn.surjective** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearO
n`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {f' : E ≃L[𝕜] F} {
c : NNReal} [CompleteSpace E],   ApproximatesLinearOn f (↑f') Set.univ c → Subsi
ngleton E ∨ c < ‖↑f'.symm‖₊⁻¹ → Function.Surjective f
参数：↑f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Function.surjective_to_subsingleton`：surjective_to_subsingleton [na : No
nempty α] [Subsingleton β] (f : α -> β) : Surjective f
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Metric.forall_of_forall_mem_closedBall`：forall_of_forall_mem_closedBall 
(p : α -> Prop) (x : α) (H : existsᶠ R : Real in atTop, forall y in closedBall x
 R, p y) (y : α) : p y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`：surjOn_
closedBall_of_nonlinearRightInverse (hf : ApproximatesLinearOn f f' s c) (f'symm
 : f'.NonlinearRightInverse) {ε : Real} {b : E} (ε0 :…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
protected theorem surjective [CompleteSpace E] (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Surjective f := by
  rcases hc with hE | hc
  · have : Subsingleton F := (Equiv.subsingleton_congr f'.toEquiv).1 hE
    exact surjective_to_subsingleton _
  · apply forall_of_forall_mem_closedBall (fun y : F => ∃ a, f a = y) (f 0) _
    have hc' : (0 : ℝ) < N⁻¹ - c := by rw [sub_pos]; exact hc
    let p : ℝ → Prop := fun R => closedBall (f 0) R ⊆ Set.range f
    have hp : ∀ᶠ r : ℝ in atTop, p ((N⁻¹ - c) * r) := by
      have hr : ∀ᶠ r : ℝ in atTop, 0 ≤ r := eventually_ge_atTop 0
      refine hr.mono fun r hr => Subset.trans ?_ (image_subset_range f (closedBall 0 r))
      refine hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse hr ?_
      exact subset_univ _
    refine ((tendsto_id.const_mul_atTop hc').frequently hp.frequently).mono ?_
    exact fun R h y hy => h hy

/-- A map approximating a linear equivalence on a set defines a partial equivalence on this set.
Should not be used outside of this file, because it is superseded by `toOpenPartialHomeomorph`
below.

This is a first step towards the inverse function. -/
/-
**ApproximatesLinearOn.toPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ApproximatesLin
earOn`。
形式化陈述：toPartialEquiv (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c) (hc : S
ubsingleton E ∨ c < N⁻¹) : PartialEquiv E F
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ApproximatesLinearOn.injOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…

--- 原说明 ---
A map approximating a linear equivalence on a set defines a partial equivalence 
on this set.
Should not be used outside of this file, because it is superseded by `toOpenPart
ialHomeomorph`
below.

This is a first step towards the inverse function.
-/
def toPartialEquiv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : PartialEquiv E F :=
  (hf.injOn hc).toPartialEquiv _ _

/-- The inverse function is continuous on `f '' s`.
Use properties of `OpenPartialHomeomorph` instead. -/
/-
**ApproximatesLinearOn.inverse_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Approxima
tesLinearOn`。
形式化陈述：inverse_continuousOn (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c) (
hc : Subsingleton E ∨ c < N⁻¹) : ContinuousOn (hf.toPartialEquiv hc).symm (f '' 
s)
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `AntilipschitzWith.to_rightInvOn'`：to_rightInvOn' {s : Set α} (hf : Antil
ipschitzWith K (s.domRestrict f)) {g : β -> α} {t : Set β} (g_maps : MapsTo g t 
s) (g_inv : RightInvOn…
· 使用定理 `ApproximatesLinearOn.antilipschitz`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Type u_…
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `PartialEquiv.right_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : Partial
Equiv α β) ⦃x : β⦄, x ∈ self.target → ↑self (self.invFun x) = x

--- 原说明 ---
The inverse function is continuous on `f '' s`.
Use properties of `OpenPartialHomeomorph` instead.
-/
theorem inverse_continuousOn (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : ContinuousOn (hf.toPartialEquiv hc).symm (f '' s) := by
  apply continuousOn_iff_continuous_domRestrict.2
  refine ((hf.antilipschitz hc).to_rightInvOn' ?_ (hf.toPartialEquiv hc).right_inv').continuous
  exact fun x hx => (hf.toPartialEquiv hc).map_target hx

/-- The inverse function is approximated linearly on `f '' s` by `f'.symm`. -/
/-
**ApproximatesLinearOn.to_inv** 是 Mathlib 中的一个定理，位于命名空间 `ApproximatesLinearOn`。
形式化陈述：to_inv (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c) (hc : Subsingle
ton E ∨ c < N⁻¹) : ApproximatesLinearOn (hf.toPartialEquiv hc).symm (f'.symm : F
 ->L[𝕜] E) (f '' s) (N * (N⁻¹ - c)⁻¹ * c)
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `ContinuousLinearMap.bound_of_antilipschitz`：bound_of_antilipschitz (f : 
E ->SL[σ] F) {K : Real>=0} (h : AntilipschitzWith K f) (x) : ‖x‖ <= K * ‖f x‖
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `_private.Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLi
nearOn.0.ApproximatesLinearOn.to_inv._abel_1_1`：∀ {𝕜 : Type u_3} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `AntilipschitzWith.le_mul_dist`：∀ {α : Type u_1} {β : Type u_2} [inst : P
seudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   A
ntilipschitzWith K …
· 使用定理 `ApproximatesLinearOn.antilipschitz`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The inverse function is approximated linearly on `f '' s` by `f'.symm`.
-/
theorem to_inv (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    ApproximatesLinearOn (hf.toPartialEquiv hc).symm (f'.symm : F →L[𝕜] E) (f '' s)
      (N * (N⁻¹ - c)⁻¹ * c) := fun x hx y hy ↦ by
  set A := hf.toPartialEquiv hc
  have Af : ∀ z, A z = f z := fun z => rfl
  rcases (mem_image _ _ _).1 hx with ⟨x', x's, rfl⟩
  rcases (mem_image _ _ _).1 hy with ⟨y', y's, rfl⟩
  rw [← Af x', ← Af y', A.left_inv x's, A.left_inv y's]
  calc
    ‖x' - y' - f'.symm (A x' - A y')‖ ≤ N * ‖f' (x' - y' - f'.symm (A x' - A y'))‖ :=
      (f' : E →L[𝕜] F).bound_of_antilipschitz f'.antilipschitz _
    _ = N * ‖A y' - A x' - f' (y' - x')‖ := by
      congr 2
      simp only [ContinuousLinearEquiv.apply_symm_apply, map_sub]
      abel
    _ ≤ N * (c * ‖y' - x'‖) := by gcongr; exact hf _ y's _ x's
    _ ≤ N * (c * (((N⁻¹ - c)⁻¹ : ℝ≥0) * ‖A y' - A x'‖)) := by
      gcongr
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact (hf.antilipschitz hc).le_mul_dist ⟨y', y's⟩ ⟨x', x's⟩
    _ = (N * (N⁻¹ - c)⁻¹ * c : ℝ≥0) * ‖A x' - A y'‖ := by
      simp only [norm_sub_rev, NNReal.coe_mul]; ring

variable [CompleteSpace E]

section

variable (f s)

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns an open partial homeomorphism with `toFun = f` and `source = s`. -/
/-
**ApproximatesLinearOn.toOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Approx
imatesLinearOn`。
形式化陈述：toOpenPartialHomeomorph (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c
) (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : OpenPartialHomeomorph E F wh
ere toPartialEquiv
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹；hs : IsOpen s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ApproximatesLinearOn.inverse_continuousOn`：inverse_continuousOn (hf : Ap
proximatesLinearOn f (f' : E ->L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) : Co
ntinuousOn (hf.toPartialEquiv h…

--- 原说明 ---
Given a function `f` that approximates a linear equivalence on an open set `s`,
returns an open partial homeomorphism with `toFun = f` and `source = s`.
-/
def toOpenPartialHomeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : OpenPartialHomeomorph E F where
  toPartialEquiv := hf.toPartialEquiv hc
  open_source := hs
  open_target := hf.open_image f'.toNonlinearRightInverse hs <| by
    rwa [f'.toEquiv.subsingleton_congr] at hc
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hf.inverse_continuousOn hc

@[simp]
/-
**ApproximatesLinearOn.toOpenPartialHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ap
proximatesLinearOn`。
形式化陈述：toOpenPartialHomeomorph_coe (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F)
 s c) (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : (hf.toOpenPartialHomeomo
rph f s hc hs : E -> F) = f
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_coe (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toOpenPartialHomeomorph f s hc hs : E → F) = f :=
  rfl

@[simp]
/-
**ApproximatesLinearOn.toOpenPartialHomeomorph_source** 是 Mathlib 中的一个定理，位于命名空间 
`ApproximatesLinearOn`。
形式化陈述：toOpenPartialHomeomorph_source (hf : ApproximatesLinearOn f (f' : E ->L[𝕜]
 F) s c) (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : (hf.toOpenPartialHome
omorph f s hc hs).source = s
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_source (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toOpenPartialHomeomorph f s hc hs).source = s :=
  rfl

@[simp]
/-
**ApproximatesLinearOn.toOpenPartialHomeomorph_target** 是 Mathlib 中的一个定理，位于命名空间 
`ApproximatesLinearOn`。
形式化陈述：toOpenPartialHomeomorph_target (hf : ApproximatesLinearOn f (f' : E ->L[𝕜]
 F) s c) (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : (hf.toOpenPartialHome
omorph f s hc hs).target = f '' s
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹；hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toOpenPartialHomeomorph f s hc hs).target = f '' s :=
  rfl

/-- A function `f` that approximates a linear equivalence on the whole space is a homeomorphism. -/
/-
**ApproximatesLinearOn.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ApproximatesLinea
rOn`。
形式化陈述：toHomeomorph (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c) (hc : 
Subsingleton E ∨ c < N⁻¹) : E ≃ₜ F
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c；hc : Subsingleton E ∨ c 
< N⁻¹。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` that approximates a linear equivalence on the whole space is a ho
meomorphism.
-/
def toHomeomorph (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : E ≃ₜ F := by
  refine
    (hf.toOpenPartialHomeomorph _ _ hc isOpen_univ).toHomeomorphOfSourceEqUnivTargetEqUniv rfl ?_
  rw [toOpenPartialHomeomorph_target, image_univ, range_eq_univ]
  exact hf.surjective hc

end

/-
**ApproximatesLinearOn.closedBall_subset_target** 是 Mathlib 中的一个定理，位于命名空间 `Appro
ximatesLinearOn`。
形式化陈述：closedBall_subset_target (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s 
c) (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) {b : E} (ε0 : 0 <= ε) (hε : c
losedBall b ε subseteq s) : closedBall (f b) ((N⁻¹ - c) * ε) subseteq (hf.toOpen
PartialHomeomorph f s hc hs).target
参数：hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c；hc : Subsingleton E ∨ c < N
⁻¹；hs : IsOpen s；ε0 : 0 <= ε；hε : closedBall b ε subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`：surjOn_
closedBall_of_nonlinearRightInverse (hf : ApproximatesLinearOn f f' s c) (f'symm
 : f'.NonlinearRightInverse) {ε : Real} {b : E} (ε0 :…
-/
theorem closedBall_subset_target (hf : ApproximatesLinearOn f (f' : E →L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) {b : E} (ε0 : 0 ≤ ε) (hε : closedBall b ε ⊆ s) :
    closedBall (f b) ((N⁻¹ - c) * ε) ⊆ (hf.toOpenPartialHomeomorph f s hc hs).target :=
  (hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse ε0 hε).mono hε
    Subset.rfl

end ApproximatesLinearOn

