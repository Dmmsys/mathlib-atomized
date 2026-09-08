/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The Mellin transform

We define the Mellin transform of a locally integrable function on `Ioi 0`, and show it is
differentiable in a suitable vertical strip.

## Main statements

- `mellin` : the Mellin transform `∫ (t : ℝ) in Ioi 0, t ^ (s - 1) • f t`,
  where `s` is a complex number.
- `HasMellin`: shorthand asserting that the Mellin transform exists and has a given value
  (analogous to `HasSum`).
- `mellin_differentiableAt_of_isBigO_rpow` : if `f` is `O(x ^ (-a))` at infinity, and
  `O(x ^ (-b))` at 0, then `mellin f` is holomorphic on the domain `b < re s < a`.

-/

@[expose] public section

open MeasureTheory Set Filter Asymptotics TopologicalSpace

open Real

open Complex hiding exp log

open scoped Topology

noncomputable section

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Predicate on `f` and `s` asserting that the Mellin integral is well-defined. -/
/-
**MellinConvergent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MellinConvergent (f : Real -> E) (s : Complex) : Prop
参数：f : Real -> E；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate on `f` and `s` asserting that the Mellin integral is well-defined.
-/
def MellinConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Ioi 0)
/-
**MellinConvergent.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MellinConvergent.const_smul {f : Real -> E} {s : Complex} (hf : MellinConv
ergent f s) {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E] [IsBoundedSMu
l 𝕜 E] [SMulCommClass Complex 𝕜 E] (c : 𝕜) : MellinConvergent (fun t => c • f t)
 s
参数：hf : MellinConvergent f s；c : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
theorem MellinConvergent.const_smul {f : ℝ → E} {s : ℂ} (hf : MellinConvergent f s) {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    MellinConvergent (fun t => c • f t) s := by
  simpa only [MellinConvergent, smul_comm] using! hf.smul c
/-
**MellinConvergent.cpow_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MellinConvergent.cpow_smul {f : Real -> E} {s a : Complex} : MellinConverg
ent (fun t => (t : Complex) ^ a • f t) s ↔ MellinConvergent f (s + a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem MellinConvergent.cpow_smul {f : ℝ → E} {s a : ℂ} :
    MellinConvergent (fun t => (t : ℂ) ^ a • f t) s ↔ MellinConvergent f (s + a) := by
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

nonrec theorem MellinConvergent.div_const {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) (a : ℂ) :
    MellinConvergent (fun t => f t / a) s := by
  simpa only [MellinConvergent, smul_eq_mul, ← mul_div_assoc] using! hf.div_const a
/-
**MellinConvergent.comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MellinConvergent.comp_mul_left {f : Real -> E} {s : Complex} {a : Real} (h
a : 0 < a) : MellinConvergent (fun t => f (a * t)) s ↔ MellinConvergent f s
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_Ioi_comp_mul_left_iff`：integrableOn_Ioi_comp_
mul_left_iff (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a) : IntegrableOn (
fun x => f (a * x)) (Ioi c) ↔ Integrab…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.mul_cpow_ofReal_nonneg`：mul_cpow_ofReal_nonneg {a b : Real} (ha 
: 0 <= a) (hb : 0 <= b) (r : Complex) : ((a : Complex) * (b : Complex)) ^ r = (a
 : Complex) ^ r * (b…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Complex.cpow_eq_zero_iff`：cpow_eq_zero_iff (x y : Complex) : x ^ y = 0 ↔
 x = 0 ∧ y != 0
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Complex.ofReal_eq_zero`：ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ 
z = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MellinConvergent.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℂ E] (f : ℝ → E) (s : ℂ),   MellinConvergent f s = MeasureTh
eory.Integr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_smul_iff`：integrable_smul_iff [NormedDivisionRi
ng 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -
> β) : Integrable (c • …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem MellinConvergent.comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    MellinConvergent (fun t => f (a * t)) s ↔ MellinConvergent f s := by
  have := integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) 0 ha
  rw [mul_zero] at this
  have h1 : EqOn (fun t : ℝ => (↑(a * t) : ℂ) ^ (s - 1) • f (a * t))
      ((a : ℂ) ^ (s - 1) • fun t : ℝ => (t : ℂ) ^ (s - 1) • f (a * t)) (Ioi 0) := fun t ht ↦ by
    simp only [ofReal_mul, mul_cpow_ofReal_nonneg ha.le (le_of_lt ht), mul_smul, Pi.smul_apply]
  have h2 : (a : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or, ofReal_eq_zero]
    exact Or.inl ha.ne'
  rw [MellinConvergent, MellinConvergent, ← this, integrableOn_congr_fun h1 measurableSet_Ioi,
    IntegrableOn, IntegrableOn, integrable_smul_iff h2]
/-
**MellinConvergent.comp_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MellinConvergent.comp_rpow {f : Real -> E} {s : Complex} {a : Real} (ha : 
a != 0) : MellinConvergent (fun t => f (t ^ a)) s ↔ MellinConvergent f (s / a)
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MellinConvergent.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℂ E] (f : ℝ → E) (s : ℂ),   MellinConvergent f s = MeasureTh
eory.Integr…
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.coe_smul`：Complex.coe_smul {E : Type*} [AddCommGroup E] [Module 
Complex E] (x : Real) (y : E) : (x : Complex) • y = x • y
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Complex.cpow_mul_ofReal_nonneg`：cpow_mul_ofReal_nonneg {x : Real} (hx : 
0 <= x) (y : Real) (z : Complex) : (x : Complex) ^ (↑y * z) = (↑(x ^ y) : Comple
x) ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integrableOn_Ioi_comp_rpow_iff'`：integrableOn_Ioi_comp_rpo
w_iff' [NormedSpace Real E] (f : Real -> E) {p : Real} (hp : p != 0) : Integrabl
eOn (fun x => x ^ (p - 1) • f (x ^ …
-/
theorem MellinConvergent.comp_rpow {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : a ≠ 0) :
    MellinConvergent (fun t => f (t ^ a)) s ↔ MellinConvergent f (s / a) := by
  refine Iff.trans ?_ (integrableOn_Ioi_comp_rpow_iff' _ ha)
  rw [MellinConvergent]
  refine integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi
  rw [← Complex.coe_smul (t ^ (a - 1)), ← mul_smul, ← cpow_mul_ofReal_nonneg (le_of_lt ht),
    ofReal_cpow (le_of_lt ht), ← cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht)), ofReal_sub,
    ofReal_one, mul_sub, mul_div_cancel₀ _ (ofReal_ne_zero.mpr ha), mul_one, add_comm, ←
    add_sub_assoc, sub_add_cancel]

/-- A function `f` is `VerticalIntegrable` at `σ` if `y ↦ f(σ + yi)` is integrable. -/
/-
**Complex.VerticalIntegrable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Complex.VerticalIntegrable (f : Complex -> E) (σ : Real) (μ : Measure Real
参数：f : Complex -> E；σ : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is `VerticalIntegrable` at `σ` if `y ↦ f(σ + yi)` is integrable.
-/
def Complex.VerticalIntegrable (f : ℂ → E) (σ : ℝ) (μ : Measure ℝ := by volume_tac) : Prop :=
  Integrable (fun (y : ℝ) ↦ f (σ + y * I)) μ

/-- The Mellin transform of a function `f` (for a complex exponent `s`), defined as the integral of
`t ^ (s - 1) • f` over `Ioi 0`. -/
/-
**mellin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mellin (f : Real -> E) (s : Complex) : E
参数：f : Real -> E；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mellin transform of a function `f` (for a complex exponent `s`), defined as 
the integral of
`t ^ (s - 1) • f` over `Ioi 0`.
-/
def mellin (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) • f t

/-- The Mellin inverse transform of a function `f`, defined as `1 / (2π)` times
the integral of `y ↦ x ^ -(σ + yi) • f (σ + yi)`. -/
/-
**mellinInv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mellinInv (σ : Real) (f : Complex -> E) (x : Real) : E
参数：σ : Real；f : Complex -> E；x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mellin inverse transform of a function `f`, defined as `1 / (2π)` times
the integral of `y ↦ x ^ -(σ + yi) • f (σ + yi)`.
-/
def mellinInv (σ : ℝ) (f : ℂ → E) (x : ℝ) : E :=
  (1 / (2 * π)) • ∫ y : ℝ, (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)

-- next few lemmas don't require convergence of the Mellin transform (they are just 0 = 0 otherwise)
/-
**mellin_cpow_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_cpow_smul (f : Real -> E) (s a : Complex) : mellin (fun t => (t : C
omplex) ^ a • f t) s = mellin f (s + a)
参数：f : Real -> E；s a : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mellin_cpow_smul (f : ℝ → E) (s a : ℂ) :
    mellin (fun t => (t : ℂ) ^ a • f t) s = mellin f (s + a) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp_rw [← sub_add_eq_add_sub, cpow_add _ _ (ofReal_ne_zero.2 <| ne_of_gt ht), mul_smul]

/-- Compatibility with scalar multiplication by a normed field. For scalar multiplication by more
general rings assuming *a priori* that the Mellin transform is defined, see
`hasMellin_const_smul`. -/
/-
**mellin_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_const_smul (f : Real -> E) (s : Complex) {𝕜 : Type*} [NormedField 𝕜
] [NormedSpace 𝕜 E] [SMulCommClass Complex 𝕜 E] (c : 𝕜) : mellin (fun t => c • f
 t) s = c • mellin f s
参数：f : Real -> E；s : Complex；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Compatibility with scalar multiplication by a normed field. For scalar multiplic
ation by more
general rings assuming *a priori* that the Mellin transform is defined, see
`hasMellin_const_smul`.
-/
theorem mellin_const_smul (f : ℝ → E) (s : ℂ) {𝕜 : Type*}
    [NormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    mellin (fun t => c • f t) s = c • mellin f s := by
  simp only [mellin, smul_comm, integral_smul]
/-
**mellin_div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_div_const (f : Real -> Complex) (s a : Complex) : mellin (fun t => 
f t / a) s = mellin f s / a
参数：f : Real -> Complex；s a : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_div`：integral_div {L : Type*} [RCLike L] (r : L) 
(f : α -> L) : ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mellin_div_const (f : ℝ → ℂ) (s a : ℂ) : mellin (fun t => f t / a) s = mellin f s / a := by
  simp_rw [mellin, smul_eq_mul, ← mul_div_assoc, integral_div]
/-
**mellin_comp_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_comp_rpow (f : Real -> E) (s : Complex) (a : Real) : mellin (fun t 
=> f (t ^ a)) s = |a|⁻¹ • mellin f (s / a)
参数：f : Real -> E；s : Complex；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `setIntegral_Ioi_zero_cpow`：setIntegral_Ioi_zero_cpow (s : Complex) : ∫ x
 in Ioi (0 : Real), (x : Complex) ^ s = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_comp_rpow_Ioi`：integral_comp_rpow_Ioi (g : Real -
> E) {p : Real} (hp : p != 0) : ∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = 
∫ y in Ioi 0, g y
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
（共 56 条，此处仅展示前 30 条）
-/
theorem mellin_comp_rpow (f : ℝ → E) (s : ℂ) (a : ℝ) :
    mellin (fun t => f (t ^ a)) s = |a|⁻¹ • mellin f (s / a) := by
  /- This is true for `a = 0` as all sides are undefined but turn out to vanish thanks to our
  convention. The interesting case is `a ≠ 0` -/
  rcases eq_or_ne a 0 with rfl | ha
  · by_cases hE : CompleteSpace E
    · simp [integral_smul_const, mellin, setIntegral_Ioi_zero_cpow]
    · simp [integral, mellin, hE]
  simp_rw [mellin]
  conv_rhs => rw [← integral_comp_rpow_Ioi _ ha, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [← mul_smul, ← mul_assoc, inv_mul_cancel₀ (mt abs_eq_zero.1 ha), one_mul, ← smul_assoc,
    real_smul]
  rw [ofReal_cpow (le_of_lt ht), ← cpow_mul_ofReal_nonneg (le_of_lt ht), ←
    cpow_add _ _ (ofReal_ne_zero.mpr <| ne_of_gt ht), ofReal_sub, ofReal_one, mul_sub,
    mul_div_cancel₀ _ (ofReal_ne_zero.mpr ha), add_comm, ← add_sub_assoc, mul_one, sub_add_cancel]
/-
**mellin_comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_comp_mul_left (f : Real -> E) (s : Complex) {a : Real} (ha : 0 < a)
 : mellin (fun t => f (a * t)) s = (a : Complex) ^ (-s) • mellin f s
参数：f : Real -> E；s : Complex；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.mul_cpow_ofReal_nonneg`：mul_cpow_ofReal_nonneg {a b : Real} (ha 
: 0 <= a) (hb : 0 <= b) (r : Complex) : ((a : Complex) * (b : Complex)) ^ r = (a
 : Complex) ^ r * (b…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Complex.cpow_neg`：cpow_neg (x y : Complex) : x ^ (-y) = (x ^ y)⁻¹
（共 57 条，此处仅展示前 30 条）
-/
theorem mellin_comp_mul_left (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun t => f (a * t)) s = (a : ℂ) ^ (-s) • mellin f s := by
  simp_rw [mellin]
  have : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f (a * t))
      (fun t : ℝ => (a : ℂ) ^ (1 - s) • (fun u : ℝ => (u : ℂ) ^ (s - 1) • f u) (a * t))
        (Ioi 0) := fun t ht ↦ by
    dsimp only
    rw [ofReal_mul, mul_cpow_ofReal_nonneg ha.le (le_of_lt ht), ← mul_smul,
      (by ring : 1 - s = -(s - 1)), cpow_neg, inv_mul_cancel_left₀]
    rw [Ne, cpow_eq_zero_iff, ofReal_eq_zero, not_and_or]
    exact Or.inl ha.ne'
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_smul,
    integral_comp_mul_left_Ioi (fun u ↦ (u : ℂ) ^ (s - 1) • f u) _ ha,
    mul_zero, ← Complex.coe_smul, ← mul_smul, sub_eq_add_neg,
    cpow_add _ _ (ofReal_ne_zero.mpr ha.ne'), cpow_one, ofReal_inv,
    mul_assoc, mul_comm, inv_mul_cancel_right₀ (ofReal_ne_zero.mpr ha.ne')]
/-
**mellin_comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_comp_mul_right (f : Real -> E) (s : Complex) {a : Real} (ha : 0 < a
) : mellin (fun t => f (t * a)) s = (a : Complex) ^ (-s) • mellin f s
参数：f : Real -> E；s : Complex；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mellin_comp_mul_left`：mellin_comp_mul_left (f : Real -> E) (s : Complex)
 {a : Real} (ha : 0 < a) : mellin (fun t => f (a * t)) s = (a : Complex) ^ (-s) 
• mellin f…
-/
theorem mellin_comp_mul_right (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun t => f (t * a)) s = (a : ℂ) ^ (-s) • mellin f s := by
  simpa only [mul_comm] using mellin_comp_mul_left f s ha
/-
**mellin_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_comp_inv (f : Real -> E) (s : Complex) : mellin (fun t => f t⁻¹) s 
= mellin f (-s)
参数：f : Real -> E；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mellin_comp_rpow`：mellin_comp_rpow (f : Real -> E) (s : Complex) (a : Re
al) : mellin (fun t => f (t ^ a)) s = |a|⁻¹ • mellin f (s / a)
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用引理 `div_neg`：div_neg (a : R) : a / -b = -(a / b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mellin_comp_inv (f : ℝ → E) (s : ℂ) : mellin (fun t => f t⁻¹) s = mellin f (-s) := by
  simp_rw [← rpow_neg_one, mellin_comp_rpow _ _ _, abs_neg, abs_one,
    inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one]

/-- Predicate standing for "the Mellin transform of `f` is defined at `s` and equal to `m`". This
shortens some arguments. -/
/-
**HasMellin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasMellin (f : Real -> E) (s : Complex) (m : E) : Prop
参数：f : Real -> E；s : Complex；m : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate standing for "the Mellin transform of `f` is defined at `s` and equal 
to `m`". This
shortens some arguments.
-/
def HasMellin (f : ℝ → E) (s : ℂ) (m : E) : Prop :=
  MellinConvergent f s ∧ mellin f s = m
/-
**hasMellin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMellin_add {f g : Real -> E} {s : Complex} (hf : MellinConvergent f s) 
(hg : MellinConvergent g s) : HasMellin (fun t => f t + g t) s (mellin f s + mel
lin g s)
参数：hf : MellinConvergent f s；hg : MellinConvergent g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.IntegrableOn.add`：∀ {α : Type u_1} {ε' : Type u_4} {mα : M
easurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topologica
lSpace ε'] [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
-/
theorem hasMellin_add {f g : ℝ → E} {s : ℂ} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : HasMellin (fun t => f t + g t) s (mellin f s + mellin g s) :=
  ⟨by simpa only [MellinConvergent, smul_add] using! hf.add hg, by
    simpa only [mellin, smul_add] using! integral_add hf hg⟩
/-
**hasMellin_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMellin_sub {f g : Real -> E} {s : Complex} (hf : MellinConvergent f s) 
(hg : MellinConvergent g s) : HasMellin (fun t => f t - g t) s (mellin f s - mel
lin g s)
参数：hf : MellinConvergent f s；hg : MellinConvergent g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
-/
theorem hasMellin_sub {f g : ℝ → E} {s : ℂ} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : HasMellin (fun t => f t - g t) s (mellin f s - mellin g s) :=
  ⟨by simpa only [MellinConvergent, smul_sub] using! hf.sub hg, by
    simpa only [mellin, smul_sub] using! integral_sub hf hg⟩
/-
**hasMellin_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMellin_const_smul {f : Real -> E} {s : Complex} (hf : MellinConvergent 
f s) {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass 
Complex R E] (c : R) : HasMellin (fun t => c • f t) s (c • mellin f s)
参数：hf : MellinConvergent f s；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MellinConvergent.const_smul`：MellinConvergent.const_smul {f : Real -> E}
 {s : Complex} (hf : MellinConvergent f s) {𝕜 : Type*} [NormedAddCommGroup 𝕜] [S
MulZeroClass 𝕜 E]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `MeasureTheory.Integrable.integral_smul`：∀ {α : Type u_1} {G : Type u_5} 
[inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}
   {μ : MeasureTheory.Measur…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hasMellin_const_smul {f : ℝ → E} {s : ℂ} (hf : MellinConvergent f s)
    {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass ℂ R E] (c : R) :
    HasMellin (fun t => c • f t) s (c • mellin f s) :=
  ⟨hf.const_smul c, by simp [mellin, smul_comm, hf.integral_smul]⟩

end Defs

variable {E : Type*} [NormedAddCommGroup E]

section MellinConvergent

/-! ## Convergence of Mellin transform integrals -/

/-- Auxiliary lemma to reduce convergence statements from vector-valued functions to real
scalar-valued functions. -/
/-
**mellin_convergent_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_convergent_iff_norm [NormedSpace Complex E] {f : Real -> E} {T : Se
t Real} (hT : T subseteq Ioi 0) (hT' : MeasurableSet T) (hfc : AEStronglyMeasura
ble f <| volume.restrict <| Ioi 0) {s : Complex} : IntegrableOn (fun t : Real =>
 (t : Complex) ^ (s - 1) • f t) T ↔ IntegrableOn (fun t : Real => t ^ (s.re - 1)
 * ‖f t‖) T
参数：hT : T subseteq Ioi 0；hT' : MeasurableSet T；hfc : AEStronglyMeasurable f <| v
olume.restrict <| Ioi 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Complex.continuousAt_ofReal_cpow_const`：continuousAt_ofReal_cpow_const (
x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) : ContinuousAt (fun a => (a : Co
mplex) ^ y : Real -> Complex…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_set`：mono_set {s t} (h : s subse
teq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) : AEStronglyMeasurable[m]
 f (μ.restrict s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Auxiliary lemma to reduce convergence statements from vector-valued functions to
 real
scalar-valued functions.
-/
theorem mellin_convergent_iff_norm [NormedSpace ℂ E] {f : ℝ → E} {T : Set ℝ} (hT : T ⊆ Ioi 0)
    (hT' : MeasurableSet T) (hfc : AEStronglyMeasurable f <| volume.restrict <| Ioi 0) {s : ℂ} :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) T ↔
      IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖f t‖) T := by
  have : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (volume.restrict T) := by
    refine ((continuousOn_of_forall_continuousAt ?_).aestronglyMeasurable hT').smul
      (hfc.mono_set hT)
    exact fun t ht => continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt (hT ht))
  rw [IntegrableOn, ← integrable_norm_iff this, ← IntegrableOn]
  refine integrableOn_congr_fun (fun t ht => ?_) hT'
  simp_rw [norm_smul, norm_cpow_eq_rpow_re_of_pos (hT ht), sub_re, one_re]

/-- If `f` is a locally integrable real-valued function which is `O(x ^ (-a))` at `∞`, then for any
`s < a`, its Mellin transform converges on some neighbourhood of `+∞`. -/
/-
**mellin_convergent_top_of_isBigO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_convergent_top_of_isBigO {f : Real -> Real} (hfc : AEStronglyMeasur
able f <| volume.restrict (Ioi 0)) {a s : Real} (hf : f =O[atTop] (· ^ (-a))) (h
s : s < a) : exists c : Real, 0 < c ∧ IntegrableOn (fun t : Real => t ^ (s - 1) 
* f t) (Ioi c)
参数：hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0)；hf : f =O[atTop] (· ^
 (-a))；hs : s < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Real.continuousAt_rpow_const`：continuousAt_rpow_const (x : Real) (q : Re
al) (h : x != 0 ∨ 0 <= q) : ContinuousAt (fun x : Real => x ^ q) x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_set`：mono_set {s t} (h : s subse
teq t) (ht : AEStronglyMeasurable[m] f (μ.restrict t)) : AEStronglyMeasurable[m]
 f (μ.restrict s)
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a locally integrable real-valued function which is `O(x ^ (-a))` at `∞
`, then for any
`s < a`, its Mellin transform converges on some neighbourhood of `+∞`.
-/
theorem mellin_convergent_top_of_isBigO {f : ℝ → ℝ}
    (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0)) {a s : ℝ}
    (hf : f =O[atTop] (· ^ (-a))) (hs : s < a) :
    ∃ c : ℝ, 0 < c ∧ IntegrableOn (fun t : ℝ => t ^ (s - 1) * f t) (Ioi c) := by
  obtain ⟨d, hd'⟩ := hf.isBigOWith
  simp_rw [IsBigOWith, eventually_atTop] at hd'
  obtain ⟨e, he⟩ := hd'
  have he' : 0 < max e 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨max e 1, he', ?_, ?_⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set (Ioi_subset_Ioi he'.le))
    refine (continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact continuousAt_rpow_const _ _ (Or.inl <| (he'.trans ht).ne')
  · have : ∀ᵐ t : ℝ ∂volume.restrict (Ioi <| max e 1),
        ‖t ^ (s - 1) * f t‖ ≤ t ^ (s - 1 + -a) * d := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht' : 0 < t := he'.trans ht
      rw [norm_mul, rpow_add ht', ← norm_of_nonneg (rpow_nonneg ht'.le (-a)), mul_assoc,
        mul_comm _ d, norm_of_nonneg (rpow_nonneg ht'.le _)]
      gcongr
      exact he t ((le_max_left e 1).trans_lt ht).le
    refine (HasFiniteIntegral.mul_const ?_ _).mono' this
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) he').hasFiniteIntegral

/-- If `f` is a locally integrable real-valued function which is `O(x ^ (-b))` at `0`, then for any
`b < s`, its Mellin transform converges on some right neighbourhood of `0`. -/
/-
**mellin_convergent_zero_of_isBigO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_convergent_zero_of_isBigO {b : Real} {f : Real -> Real} (hfc : AESt
ronglyMeasurable f <| volume.restrict (Ioi 0)) (hf : f =O[𝓝[>] 0] (· ^ (-b))) {s
 : Real} (hs : b < s) : exists c : Real, 0 < c ∧ IntegrableOn (fun t : Real => t
 ^ (s - 1) * f t) (Ioc 0 c)
参数：hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0)；hf : f =O[𝓝[>] 0] (· 
^ (-b))；hs : b < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `integrableOn_Ioc_iff_integrableOn_Ioo`：integrableOn_Ioc_iff_integrableOn
_Ioo (hb : ‖f b‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Real.continuousAt_rpow_const`：continuousAt_rpow_const (x : Real) (q : Re
al) (h : x != 0 ∨ 0 <= q) : ContinuousAt (fun x : Real => x ^ q) x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a locally integrable real-valued function which is `O(x ^ (-b))` at `0
`, then for any
`b < s`, its Mellin transform converges on some right neighbourhood of `0`.
-/
theorem mellin_convergent_zero_of_isBigO {b : ℝ} {f : ℝ → ℝ}
    (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0))
    (hf : f =O[𝓝[>] 0] (· ^ (-b))) {s : ℝ} (hs : b < s) :
    ∃ c : ℝ, 0 < c ∧ IntegrableOn (fun t : ℝ => t ^ (s - 1) * f t) (Ioc 0 c) := by
  obtain ⟨d, _, hd'⟩ := hf.exists_pos
  simp_rw [IsBigOWith, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, gt_iff_lt] at hd'
  obtain ⟨ε, hε, hε'⟩ := hd'
  refine ⟨ε, hε, Iff.mpr integrableOn_Ioc_iff_integrableOn_Ioo ⟨?_, ?_⟩⟩
  · refine AEStronglyMeasurable.mul ?_ (hfc.mono_set Ioo_subset_Ioi_self)
    refine (continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
      measurableSet_Ioo
    exact continuousAt_rpow_const _ _ (Or.inl ht.1.ne')
  · apply HasFiniteIntegral.mono' (g := fun t => d * t ^ (s - b - 1))
    · refine (Integrable.hasFiniteIntegral ?_).const_mul _
      rw [← IntegrableOn, ← integrableOn_Ioc_iff_integrableOn_Ioo, ←
        intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
      rw [mul_comm, norm_mul]
      specialize hε' _ ht.1
      · rw [dist_eq_norm, sub_zero, norm_of_nonneg ht.1.le]
        exact ht.2
      · calc _ ≤ d * ‖t ^ (-b)‖ * ‖t ^ (s - 1)‖ := by gcongr
          _ = d * t ^ (s - b - 1) := ?_
        simp_rw [norm_of_nonneg (rpow_nonneg ht.1.le _), mul_assoc]
        rw [← rpow_add ht.1]
        congr 2
        abel

/-- If `f` is a locally integrable real-valued function on `Ioi 0` which is `O(x ^ (-a))` at `∞`
and `O(x ^ (-b))` at `0`, then its Mellin transform integral converges for `b < s < a`. -/
/-
**mellin_convergent_of_isBigO_scalar** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_convergent_of_isBigO_scalar {a b : Real} {f : Real -> Real} {s : Re
al} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] (· ^ (-a))) (hs
_top : s < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s) : IntegrableOn
 (fun t : Real => t ^ (s - 1) * f t) (Ioi 0)
参数：hfc : LocallyIntegrableOn f <| Ioi 0；hf_top : f =O[atTop] (· ^ (-a))；hs_top :
 s < a；hf_bot : f =O[𝓝[>] 0] (· ^ (-b))；hs_bot : b < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mellin_convergent_top_of_isBigO`：mellin_convergent_top_of_isBigO {f : Re
al -> Real} (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0)) {a s : Rea
l} (hf : f =O[atTop] …
· 使用定理 `MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `mellin_convergent_zero_of_isBigO`：mellin_convergent_zero_of_isBigO {b : 
Real} {f : Real -> Real} (hfc : AEStronglyMeasurable f <| volume.restrict (Ioi 0
)) (hf : f =O[𝓝[>] 0] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
· 使用定理 `Set.Ioc_union_Ioi`：Ioc_union_Ioi (h : c <= max a b) : Ioc a b union Ioi 
c = Ioi (min a c)
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc`：integrableOn_Icc_iff_integrableOn
_Ioc (ha : ‖f a‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.LocallyIntegrableOn.integrableOn_compact_subset`：∀ {X : Ty
pe u_1} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] 
[inst_2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.LocallyIntegrableOn.continuousOn_mul`：continuousOn_mul [Lo
callyCompactSpace X] [T2Space X] [NormedRing R] [SecondCountableTopologyEither X
 R] {f g : X -> R} {s : Set X} (hf : Loc…
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a locally integrable real-valued function on `Ioi 0` which is `O(x ^ (
-a))` at `∞`
and `O(x ^ (-b))` at `0`, then its Mellin transform integral converges for `b < 
s < a`.
-/
theorem mellin_convergent_of_isBigO_scalar {a b : ℝ} {f : ℝ → ℝ} {s : ℝ}
    (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1) * f t) (Ioi 0) := by
  obtain ⟨c1, hc1, hc1'⟩ := mellin_convergent_top_of_isBigO hfc.aestronglyMeasurable hf_top hs_top
  obtain ⟨c2, hc2, hc2'⟩ :=
    mellin_convergent_zero_of_isBigO hfc.aestronglyMeasurable hf_bot hs_bot
  have : Ioi 0 = Ioc 0 c2 ∪ Ioc c2 c1 ∪ Ioi c1 := by
    rw [union_assoc, Ioc_union_Ioi (le_max_right _ _),
      Ioc_union_Ioi ((min_le_left _ _).trans (le_max_right _ _)), min_eq_left (lt_min hc2 hc1).le]
  rw [this, integrableOn_union, integrableOn_union]
  refine ⟨⟨hc2', Iff.mp integrableOn_Icc_iff_integrableOn_Ioc ?_⟩, hc1'⟩
  refine
    (hfc.continuousOn_mul ?_ isOpen_Ioi.isLocallyClosed).integrableOn_compact_subset
      (fun t ht => (hc2.trans_le ht.1 : 0 < t)) isCompact_Icc
  exact continuousOn_of_forall_continuousAt
    fun t ht ↦ continuousAt_rpow_const _ _ <| Or.inl <| ne_of_gt ht
/-
**mellinConvergent_of_isBigO_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellinConvergent_of_isBigO_rpow [NormedSpace Complex E] {a b : Real} {f : 
Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[a
tTop] (· ^ (-a))) (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot
 : b < s.re) : MellinConvergent f s
参数：hfc : LocallyIntegrableOn f <| Ioi 0；hf_top : f =O[atTop] (· ^ (-a))；hs_top :
 s.re < a；hf_bot : f =O[𝓝[>] 0] (· ^ (-b))；hs_bot : b < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MellinConvergent.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℂ E] (f : ℝ → E) (s : ℂ),   MellinConvergent f s = MeasureTh
eory.Integr…
· 使用定理 `mellin_convergent_iff_norm`：mellin_convergent_iff_norm [NormedSpace Comp
lex E] {f : Real -> E} {T : Set Real} (hT : T subseteq Ioi 0) (hT' : MeasurableS
et T) (hfc : AES…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `mellin_convergent_of_isBigO_scalar`：mellin_convergent_of_isBigO_scalar {
a b : Real} {f : Real -> Real} {s : Real} (hfc : LocallyIntegrableOn f <| Ioi 0)
 (hf_top : f =O[atTop] (…
· 使用定理 `MeasureTheory.LocallyIntegrableOn.norm`：∀ {X : Type u_1} {E : Type u_6} 
[inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedAddComm
Group E]   {μ : MeasureTheor…
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
-/
theorem mellinConvergent_of_isBigO_rpow [NormedSpace ℂ E] {a b : ℝ} {f : ℝ → E} {s : ℂ}
    (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    MellinConvergent f s := by
  rw [MellinConvergent,
    mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hfc.aestronglyMeasurable]
  exact mellin_convergent_of_isBigO_scalar hfc.norm hf_top.norm_left hs_top hf_bot.norm_left hs_bot

end MellinConvergent

section MellinDiff

/-- If `f` is `O(x ^ (-a))` as `x → +∞`, then `log • f` is `O(x ^ (-b))` for every `b < a`. -/
/-
**isBigO_rpow_top_log_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_rpow_top_log_smul [NormedSpace Real E] {a b : Real} {f : Real -> E}
 (hab : b < a) (hf : f =O[atTop] (· ^ (-a))) : (fun t : Real => log t • f t) =O[
atTop] (· ^ (-b))
参数：hab : b < a；hf : f =O[atTop] (· ^ (-a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.smul`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7
} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E']   [inst_1 
: SeminormedA…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `isLittleO_log_rpow_atTop`：isLittleO_log_rpow_atTop {r : Real} (hr : 0 < 
r) : log =o[atTop] fun x => x ^ r
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
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b

--- 原说明 ---
If `f` is `O(x ^ (-a))` as `x → +∞`, then `log • f` is `O(x ^ (-b))` for every `
b < a`.
-/
theorem isBigO_rpow_top_log_smul [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} (hab : b < a)
    (hf : f =O[atTop] (· ^ (-a))) :
    (fun t : ℝ => log t • f t) =O[atTop] (· ^ (-b)) := by
  refine
    ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).isBigO.smul hf).congr'
      (Eventually.of_forall fun t => by rfl)
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun t ht => ?_))
  simp only
  rw [smul_eq_mul, ← rpow_add ht, ← sub_eq_add_neg, sub_eq_add_neg a, add_sub_cancel_left]

/-- If `f` is `O(x ^ (-a))` as `x → 0`, then `log • f` is `O(x ^ (-b))` for every `a < b`. -/
/-
**isBigO_rpow_zero_log_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_rpow_zero_log_smul [NormedSpace Real E] {a b : Real} {f : Real -> E
} (hab : a < b) (hf : f =O[𝓝[>] 0] (· ^ (-a))) : (fun t : Real => log t • f t) =
O[𝓝[>] 0] (· ^ (-b))
参数：hab : a < b；hf : f =O[𝓝[>] 0] (· ^ (-a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
· 使用定理 `isLittleO_log_rpow_atTop`：isLittleO_log_rpow_atTop {r : Real} (hr : 0 < 
r) : log =o[atTop] fun x => x ^ r
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
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Real.inv_rpow`：inv_rpow (hx : 0 <= x) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is `O(x ^ (-a))` as `x → 0`, then `log • f` is `O(x ^ (-b))` for every `a
 < b`.
-/
theorem isBigO_rpow_zero_log_smul [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} (hab : a < b)
    (hf : f =O[𝓝[>] 0] (· ^ (-a))) :
    (fun t : ℝ => log t • f t) =O[𝓝[>] 0] (· ^ (-b)) := by
  have : log =o[𝓝[>] 0] fun t : ℝ => t ^ (a - b) := by
    refine ((isLittleO_log_rpow_atTop (sub_pos.mpr hab)).neg_left.comp_tendsto
          tendsto_inv_nhdsGT_zero).congr'
      (.of_forall fun t => ?_)
      (eventually_mem_nhdsWithin.mono fun t ht => ?_)
    · simp
    · simp_rw [Function.comp_apply, inv_rpow (le_of_lt ht), ← rpow_neg (le_of_lt ht), neg_sub]
  refine (this.isBigO.smul hf).congr' (Eventually.of_forall fun t => by rfl)
      (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ?_))
  simp_rw [smul_eq_mul, ← rpow_add ht]
  congr 1
  abel

/-- Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the domain `b < re s < a`,
with derivative equal to the Mellin transform of `log • f`. -/
/-
**mellin_hasDerivAt_of_isBigO_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_hasDerivAt_of_isBigO_rpow [NormedSpace Complex E] {a b : Real} {f :
 Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f (Ioi 0)) (hf_top : f =O[a
tTop] (· ^ (-a))) (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot
 : b < s.re) : MellinConvergent (fun t => log t • f t) s ∧ HasDerivAt (mellin f)
 (mellin (fun t => log t • f t) s) s
参数：hfc : LocallyIntegrableOn f (Ioi 0)；hf_top : f =O[atTop] (· ^ (-a))；hs_top : 
s.re < a；hf_bot : f =O[𝓝[>] 0] (· ^ (-b))；hs_bot : b < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
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
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Complex.continuousAt_ofReal_cpow_const`：continuousAt_ofReal_cpow_const (
x : Real) (y : Complex) (h : 0 < y.re ∨ x != 0) : ContinuousAt (fun a => (a : Co
mplex) ^ y : Real -> Complex…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 181 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and 
is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the dom
ain `b < re s < a`,
with derivative equal to the Mellin transform of `log • f`.
-/
theorem mellin_hasDerivAt_of_isBigO_rpow [NormedSpace ℂ E] {a b : ℝ}
    {f : ℝ → E} {s : ℂ} (hfc : LocallyIntegrableOn f (Ioi 0)) (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    MellinConvergent (fun t => log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t => log t • f t) s) s := by
  set F : ℂ → ℝ → E := fun (z : ℂ) (t : ℝ) => (t : ℂ) ^ (z - 1) • f t
  set F' : ℂ → ℝ → E := fun (z : ℂ) (t : ℝ) => ((t : ℂ) ^ (z - 1) * log t) • f t
  -- A convenient radius of ball within which we can uniformly bound the derivative.
  obtain ⟨v, hv0, hv1, hv2⟩ : ∃ v : ℝ, 0 < v ∧ v < s.re - b ∧ v < a - s.re := by
    obtain ⟨w, hw1, hw2⟩ := exists_between (sub_pos.mpr hs_top)
    obtain ⟨w', hw1', hw2'⟩ := exists_between (sub_pos.mpr hs_bot)
    exact
      ⟨min w w', lt_min hw1 hw1', (min_le_right _ _).trans_lt hw2', (min_le_left _ _).trans_lt hw2⟩
  let bound : ℝ → ℝ := fun t : ℝ => (t ^ (s.re + v - 1) + t ^ (s.re - v - 1)) * |log t| * ‖f t‖
  have h1 : ∀ᶠ z : ℂ in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict <| Ioi 0) := by
    refine Eventually.of_forall fun z => AEStronglyMeasurable.smul ?_ hfc.aestronglyMeasurable
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
  have h2 : IntegrableOn (F s) (Ioi (0 : ℝ)) := by
    exact mellinConvergent_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot
  have h3 : AEStronglyMeasurable (F' s) (volume.restrict <| Ioi 0) := by
    apply LocallyIntegrableOn.aestronglyMeasurable
    refine hfc.continuousOn_smul isOpen_Ioi.isLocallyClosed
      ((continuousOn_of_forall_continuousAt fun t ht => ?_).mul ?_)
    · exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
    · refine continuous_ofReal.comp_continuousOn ?_
      exact continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi)
  have h4 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ z : ℂ, z ∈ Metric.ball s v → ‖F' z t‖ ≤ bound t := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    simp_rw [F', bound, norm_smul, norm_mul, norm_real, mul_assoc, norm_eq_abs]
    gcongr
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    rcases le_or_gt 1 t with h | h
    · refine le_add_of_le_of_nonneg (rpow_le_rpow_of_exponent_le h ?_)
        (by positivity)
      rw [sub_re, one_re, sub_le_sub_iff_right]
      rw [mem_ball_iff_norm] at hz
      have hz' := (re_le_norm _).trans hz.le
      rwa [sub_re, sub_le_iff_le_add'] at hz'
    · refine
        le_add_of_nonneg_of_le (rpow_pos_of_pos ht _).le (rpow_le_rpow_of_exponent_ge ht h.le ?_)
      rw [sub_re, one_re, sub_le_iff_le_add, sub_add_cancel]
      rw [mem_ball_iff_norm'] at hz
      have hz' := (re_le_norm _).trans hz.le
      rwa [sub_re, sub_le_iff_le_add, ← sub_le_iff_le_add'] at hz'
  have h5 : IntegrableOn bound (Ioi 0) := by
    simp_rw [bound, add_mul, mul_assoc]
    suffices ∀ {j : ℝ}, b < j → j < a →
        IntegrableOn (fun t : ℝ => t ^ (j - 1) * (|log t| * ‖f t‖)) (Ioi 0) volume by
      refine Integrable.add (this ?_ ?_) (this ?_ ?_)
      all_goals linarith
    · intro j hj hj'
      obtain ⟨w, hw1, hw2⟩ := exists_between hj
      obtain ⟨w', hw1', hw2'⟩ := exists_between hj'
      refine mellin_convergent_of_isBigO_scalar ?_ ?_ hw1' ?_ hw2
      · simp_rw [mul_comm]
        refine hfc.norm.mul_continuousOn ?_ isOpen_Ioi.isLocallyClosed
        refine Continuous.comp_continuousOn _root_.continuous_abs (continuousOn_log.mono ?_)
        exact subset_compl_singleton_iff.mpr self_notMem_Ioi
      · refine (isBigO_rpow_top_log_smul hw2' hf_top).norm_left.congr_left fun t ↦ ?_
        simp only [norm_smul, Real.norm_eq_abs]
      · refine (isBigO_rpow_zero_log_smul hw1 hf_bot).norm_left.congr_left fun t ↦ ?_
        simp only [norm_smul, Real.norm_eq_abs]
  have h6 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ y : ℂ, y ∈ Metric.ball s v → HasDerivAt (fun z : ℂ => F z t) (F' y t) y := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht y _ => ?_
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have u1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (z - 1)) (t ^ (y - 1) * log t) y := by
      convert! ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [ofReal_log (le_of_lt ht)]
      ring
    exact u1.smul_const (f t)
  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hv0) h1 h2 h3 h4 h5 h6
  simpa only [F', mul_smul] using! main

/-- Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the domain `b < re s < a`.
-/
/-
**mellin_differentiableAt_of_isBigO_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_differentiableAt_of_isBigO_rpow [NormedSpace Complex E] {a b : Real
} {f : Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top :
 f =O[atTop] (· ^ (-a))) (hs_top : s.re < a) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) 
(hs_bot : b < s.re) : DifferentiableAt Complex (mellin f) s
参数：hfc : LocallyIntegrableOn f <| Ioi 0；hf_top : f =O[atTop] (· ^ (-a))；hs_top :
 s.re < a；hf_bot : f =O[𝓝[>] 0] (· ^ (-b))；hs_bot : b < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `mellin_hasDerivAt_of_isBigO_rpow`：mellin_hasDerivAt_of_isBigO_rpow [Norm
edSpace Complex E] {a b : Real} {f : Real -> E} {s : Complex} (hfc : LocallyInte
grableOn f (Ioi 0)) (h…

--- 原说明 ---
Suppose `f` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` as `x → ∞`, and 
is
`O(x ^ (-b))` as `x → 0`. Then its Mellin transform is differentiable on the dom
ain `b < re s < a`.
-/
theorem mellin_differentiableAt_of_isBigO_rpow [NormedSpace ℂ E] {a b : ℝ}
    {f : ℝ → E} {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0)
    (hf_top : f =O[atTop] (· ^ (-a))) (hs_top : s.re < a)
    (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) :
    DifferentiableAt ℂ (mellin f) s :=
  (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot).2.differentiableAt

end MellinDiff

section ExpDecay

/-- If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-b))` at 0, then
its Mellin transform converges for `b < s.re`. -/
/-
**mellinConvergent_of_isBigO_rpow_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellinConvergent_of_isBigO_rpow_exp [NormedSpace Complex E] {a b : Real} (
ha : 0 < a) {f : Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f <| Ioi 0)
 (hf_top : f =O[atTop] fun t => exp (-a * t)) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b)))
 (hs_bot : b < s.re) : MellinConvergent f s
参数：ha : 0 < a；hfc : LocallyIntegrableOn f <| Ioi 0；hf_top : f =O[atTop] fun t =>
 exp (-a * t)；hf_bot : f =O[𝓝[>] 0] (· ^ (-b))；hs_bot : b < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mellinConvergent_of_isBigO_rpow`：mellinConvergent_of_isBigO_rpow [Normed
Space Complex E] {a b : Real} {f : Real -> E} {s : Complex} (hfc : LocallyIntegr
ableOn f <| Ioi 0) (h…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `isLittleO_exp_neg_mul_rpow_atTop`：isLittleO_exp_neg_mul_rpow_atTop {a : 
Real} (ha : 0 < a) (b : Real) : IsLittleO atTop (fun x : Real => exp (-a * x)) f
un x : Real => x ^ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-
b))` at 0, then
its Mellin transform converges for `b < s.re`.
-/
theorem mellinConvergent_of_isBigO_rpow_exp [NormedSpace ℂ E] {a b : ℝ} (ha : 0 < a) {f : ℝ → E}
    {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0) (hf_top : f =O[atTop] fun t => exp (-a * t))
    (hf_bot : f =O[𝓝[>] 0] (· ^ (-b))) (hs_bot : b < s.re) : MellinConvergent f s :=
  mellinConvergent_of_isBigO_rpow hfc (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO)
    (lt_add_one _) hf_bot hs_bot

/-- If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-b))` at 0, then
its Mellin transform is holomorphic on `b < s.re`. -/
/-
**mellin_differentiableAt_of_isBigO_rpow_exp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mellin_differentiableAt_of_isBigO_rpow_exp [NormedSpace Complex E] {a b : 
Real} (ha : 0 < a) {f : Real -> E} {s : Complex} (hfc : LocallyIntegrableOn f <|
 Ioi 0) (hf_top : f =O[atTop] fun t => exp (-a * t)) (hf_bot : f =O[𝓝[>] 0] (· ^
 (-b))) (hs_bot : b < s.re) : DifferentiableAt Complex (mellin f) s
参数：ha : 0 < a；hfc : LocallyIntegrableOn f <| Ioi 0；hf_top : f =O[atTop] fun t =>
 exp (-a * t)；hf_bot : f =O[𝓝[>] 0] (· ^ (-b))；hs_bot : b < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mellin_differentiableAt_of_isBigO_rpow`：mellin_differentiableAt_of_isBig
O_rpow [NormedSpace Complex E] {a b : Real} {f : Real -> E} {s : Complex} (hfc :
 LocallyIntegrableOn f <| Io…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `isLittleO_exp_neg_mul_rpow_atTop`：isLittleO_exp_neg_mul_rpow_atTop {a : 
Real} (ha : 0 < a) (b : Real) : IsLittleO atTop (fun x : Real => exp (-a * x)) f
un x : Real => x ^ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
If `f` is locally integrable, decays exponentially at infinity, and is `O(x ^ (-
b))` at 0, then
its Mellin transform is holomorphic on `b < s.re`.
-/
theorem mellin_differentiableAt_of_isBigO_rpow_exp [NormedSpace ℂ E] {a b : ℝ}
    (ha : 0 < a) {f : ℝ → E} {s : ℂ} (hfc : LocallyIntegrableOn f <| Ioi 0)
    (hf_top : f =O[atTop] fun t => exp (-a * t)) (hf_bot : f =O[𝓝[>] 0] (· ^ (-b)))
    (hs_bot : b < s.re) : DifferentiableAt ℂ (mellin f) s :=
  mellin_differentiableAt_of_isBigO_rpow hfc
    (hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop ha _).isBigO) (lt_add_one _) hf_bot hs_bot

end ExpDecay

section MellinIoc

/-!
## Mellin transforms of functions on `Ioc 0 1`
-/

/-- The Mellin transform of the indicator function of `Ioc 0 1`. -/
/-
**hasMellin_one_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMellin_one_Ioc {s : Complex} (hs : 0 < re s) : HasMellin (indicator (Io
c 0 1) (fun _ => 1 : Real -> Complex)) s (1 / s)
参数：hs : 0 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
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
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Complex.zero_re`：zero_re : (0 : Complex).re = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.Measure.restrict_restrict_of_subset`：restrict_restrict_of_
subset (h : s subseteq t) : (μ.restrict t).restrict s = μ.restrict s
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The Mellin transform of the indicator function of `Ioc 0 1`.
-/
theorem hasMellin_one_Ioc {s : ℂ} (hs : 0 < re s) :
    HasMellin (indicator (Ioc 0 1) (fun _ => 1 : ℝ → ℂ)) s (1 / s) := by
  have aux1 : -1 < (s - 1).re := by
    simpa only [sub_re, one_re, sub_eq_add_neg] using! lt_add_of_pos_left _ hs
  have aux2 : s ≠ 0 := by contrapose! hs; rw [hs, zero_re]
  have aux3 : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
  simp_rw [HasMellin, mellin, MellinConvergent, ← indicator_smul, IntegrableOn,
    integrable_indicator_iff aux3, smul_eq_mul, integral_indicator aux3, mul_one, IntegrableOn,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine ⟨intervalIntegral.intervalIntegrable_cpow' aux1, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl aux1), sub_add_cancel,
    ofReal_zero, ofReal_one, one_cpow, zero_cpow aux2, sub_zero]

/-- The Mellin transform of a power function restricted to `Ioc 0 1`. -/
/-
**hasMellin_cpow_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMellin_cpow_Ioc (a : Complex) {s : Complex} (hs : 0 < re s + re a) : Ha
sMellin (indicator (Ioc 0 1) (fun t => ↑t ^ a : Real -> Complex)) s (1 / (s + a)
)
参数：a : Complex；hs : 0 < re s + re a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasMellin_one_Ioc`：hasMellin_one_Ioc {s : Complex} (hs : 0 < re s) : Has
Mellin (indicator (Ioc 0 1) (fun _ => 1 : Real -> Complex)) s (1 / s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.add_re`：add_re (z w : Complex) : (z + w).re = z.re + w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The Mellin transform of a power function restricted to `Ioc 0 1`.
-/
theorem hasMellin_cpow_Ioc (a : ℂ) {s : ℂ} (hs : 0 < re s + re a) :
    HasMellin (indicator (Ioc 0 1) (fun t => ↑t ^ a : ℝ → ℂ)) s (1 / (s + a)) := by
  have := hasMellin_one_Ioc (by rwa [add_re] : 0 < (s + a).re)
  simp_rw [HasMellin, ← MellinConvergent.cpow_smul, ← mellin_cpow_smul, ← indicator_smul,
    smul_eq_mul, mul_one] at this
  exact this

end MellinIoc

