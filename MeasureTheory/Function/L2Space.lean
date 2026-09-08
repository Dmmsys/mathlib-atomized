/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ`
(defined in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
is also an inner product space, with inner product defined as `inner f g := ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `fun x ↦ ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product
  `fun x ↦ ⟪f x, g x⟫` is integrable.
* `L2.innerProductSpace` : `Lp E 2 μ` is an inner product space.
-/

@[expose] public section

noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter

open scoped NNReal ENNReal MeasureTheory InnerProductSpace

namespace MeasureTheory

section

variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

/-
**MeasureTheory.MemLp.integrable_sq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mem
Lp`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.MemLp f 2 μ → MeasureTheory.Integrable (fun x => f x ^
 2) μ
参数：fun x => f x ^ 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `MeasureTheory.MemLp.norm_rpow`：∀ {α : Type u_1} {E : Type u_4} {m : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] {f : α →…
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
-/
theorem MemLp.integrable_sq {f : α → ℝ} (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← memLp_one_iff_integrable] using h.norm_rpow two_ne_zero ENNReal.ofNat_ne_top
/-
**MeasureTheory.memLp_two_iff_integrable_sq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：memLp_two_iff_integrable_sq_norm {f : α -> F} (hf : AEStronglyMeasurable f
 μ) : MemLp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.memLp_norm_rpow_iff`：memLp_norm_rpow_iff {q : Real>=0∞} {f
 : α -> E} (hf : AEStronglyMeasurable f μ) (q_zero : q != 0) (q_top : q != ∞) : 
MemLp (fun x : α => ‖f …
-/
theorem memLp_two_iff_integrable_sq_norm {f : α → F} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => ‖f x‖ ^ 2) μ := by
  rw [← memLp_one_iff_integrable]
  convert! (memLp_norm_rpow_iff hf two_ne_zero ENNReal.ofNat_ne_top).symm
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
/-
**MeasureTheory.memLp_two_iff_integrable_sq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：memLp_two_iff_integrable_sq {f : α -> Real} (hf : AEStronglyMeasurable f μ
) : MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.memLp_two_iff_integrable_sq_norm`：memLp_two_iff_integrable
_sq_norm {f : α -> F} (hf : AEStronglyMeasurable f μ) : MemLp f 2 μ ↔ Integrable
 (fun x => ‖f x‖ ^ 2) μ
-/
theorem memLp_two_iff_integrable_sq {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ := by
  convert! memLp_two_iff_integrable_sq_norm hf using 3
  simp

end

section InnerProductSpace

variable {α : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
**MeasureTheory.MemLp.const_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {E : Type u_2} {𝕜 : Type u_3}   [inst : RCLike 𝕜] [inst_1 : NormedAdd
CommGroup E] [inst_2 : InnerProductSpace 𝕜 E] (c : E) {f : α → E},   MeasureTheo
ry.MemLp f p μ → MeasureTheory.MemLp (fun a => inner 𝕜 c (f a)) p μ
参数：c : E；fun a => inner 𝕜 c (f a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inner`：∀ {α : Type u_1} {𝕜 : Type u_2
} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : I
nnerProductSpace 𝕜 E] {m x : M…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
-/
theorem MemLp.const_inner (c : E) {f : α → E} (hf : MemLp f p μ) : MemLp (fun a => ⟪c, f a⟫) p μ :=
  hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.1)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)
/-
**MeasureTheory.MemLp.inner_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp
`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {E : Type u_2} {𝕜 : Type u_3}   [inst : RCLike 𝕜] [inst_1 : NormedAdd
CommGroup E] [inst_2 : InnerProductSpace 𝕜 E] {f : α → E},   MeasureTheory.MemLp
 f p μ → ∀ (c : E), MeasureTheory.MemLp (fun a => inner 𝕜 (f a) c) p μ
参数：c : E；fun a => inner 𝕜 (f a) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.of_le_mul`：∀ {α : Type u_1} {E : Type u_2} {F : Type
 u_3} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [ins
t : NormedAddCommGr…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inner`：∀ {α : Type u_1} {𝕜 : Type u_2
} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : I
nnerProductSpace 𝕜 E] {m x : M…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
-/
theorem MemLp.inner_const {f : α → E} (hf : MemLp f p μ) (c : E) : MemLp (fun a => ⟪f a, c⟫) p μ :=
  hf.of_le_mul (c := ‖c‖) (AEStronglyMeasurable.inner hf.1 aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

variable {f : α → E}

@[fun_prop]
/-
**MeasureTheory.Integrable.const_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {E 
: Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [
inst_2 : InnerProductSpace 𝕜 E] {f : α → E} (c : E),   MeasureTheory.Integrable 
f μ → MeasureTheory.Integrable (fun x => inner 𝕜 c (f x)) μ
参数：c : E；fun x => inner 𝕜 c (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.const_inner`：∀ {α : Type u_1} {m : MeasurableSpace α
} {p : ENNReal} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3}   [i
nst : RCLike 𝕜] [inst…
-/
theorem Integrable.const_inner (c : E) (hf : Integrable f μ) :
    Integrable (fun x => ⟪c, f x⟫) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.const_inner c

@[fun_prop]
/-
**MeasureTheory.Integrable.inner_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Integrable`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {E 
: Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜]   [inst_1 : NormedAddCommGroup E] [
inst_2 : InnerProductSpace 𝕜 E] {f : α → E},   MeasureTheory.Integrable f μ → ∀ 
(c : E), MeasureTheory.Integrable (fun x => inner 𝕜 (f x) c) μ
参数：c : E；fun x => inner 𝕜 (f x) c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.MemLp.inner_const`：∀ {α : Type u_1} {m : MeasurableSpace α
} {p : ENNReal} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3}   [i
nst : RCLike 𝕜] [inst…
-/
theorem Integrable.inner_const (hf : Integrable f μ) (c : E) :
    Integrable (fun x => ⟪f x, c⟫) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢; exact hf.inner_const c

variable [CompleteSpace E] [NormedSpace ℝ E]
/-
**MeasureTheory._root_.integral_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.integral_inner {f : α → E} (hf : Integrable f μ) (c : E) :
    ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
  ((innerSL 𝕜 c).restrictScalars ℝ).integral_comp_comm hf

variable (𝕜)
/-
**MeasureTheory._root_.integral_eq_zero_of_forall_integral_inner_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.integral_eq_zero_of_forall_integral_inner_eq_zero (f : α → E) (hf : Integrable f μ)
    (hf_int : ∀ c : E, ∫ x, ⟪c, f x⟫ ∂μ = 0) : ∫ x, f x ∂μ = 0 := by
  specialize hf_int (∫ x, f x ∂μ); rwa [integral_inner hf, inner_self_eq_zero] at hf_int

end InnerProductSpace

namespace L2

variable {α E F 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
**MeasureTheory.L2.eLpNorm_rpow_two_norm_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L2`。
形式化陈述：eLpNorm_rpow_two_norm_lt_top (f : Lp F 2 μ) : eLpNorm (fun x => ‖f x‖ ^ (2
 : Real)) 1 μ < ∞
参数：f : Lp F 2 μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_norm_rpow`：eLpNorm_norm_rpow (f : α -> F) (hq_pos 
: 0 < q) : eLpNorm (fun x => ‖f x‖ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ
 ^ q
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
-/
theorem eLpNorm_rpow_two_norm_lt_top (f : Lp F 2 μ) :
    eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) 1 μ < ∞ := by
  have h_two : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  rw [eLpNorm_norm_rpow f zero_lt_two, one_mul, h_two]
  exact ENNReal.rpow_lt_top_of_nonneg zero_le_two (Lp.eLpNorm_ne_top f)
/-
**MeasureTheory.L2.eLpNorm_inner_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.L2`。
形式化陈述：eLpNorm_inner_lt_top (f g : α ->₂[μ] E) : eLpNorm (fun x : α => ⟪f x, g x⟫
) 1 μ < ∞
参数：f g : α ->₂[μ] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `norm_inner_le_norm`：norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ <= ‖x‖ * ‖y‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `two_mul_le_add_sq`：two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono
 R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) : 2 * a * b <= a ^ 2 + b ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.eLpNorm_mono_ae`：eLpNorm_mono_ae {f : α -> F} {g : α -> G}
 (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
（共 38 条，此处仅展示前 30 条）
-/
theorem eLpNorm_inner_lt_top (f g : α →₂[μ] E) : eLpNorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞ := by
  have h : ∀ x, ‖⟪f x, g x⟫‖ ≤ ‖‖f x‖ ^ (2 : ℝ) + ‖g x‖ ^ (2 : ℝ)‖ := by
    intro x
    rw [← @Nat.cast_two ℝ, Real.rpow_natCast, Real.rpow_natCast]
    calc
      ‖⟪f x, g x⟫‖ ≤ ‖f x‖ * ‖g x‖ := norm_inner_le_norm _ _
      _ ≤ 2 * ‖f x‖ * ‖g x‖ := by
        gcongr
        exact le_mul_of_one_le_left (norm_nonneg _) one_le_two
      -- TODO(kmill): the type ascription is getting around an elaboration error
      _ ≤ ‖(‖f x‖ ^ 2 + ‖g x‖ ^ 2 : ℝ)‖ := (two_mul_le_add_sq _ _).trans (le_abs_self _)
  refine (eLpNorm_mono_ae (ae_of_all _ h)).trans_lt ((eLpNorm_add_le ?_ ?_ le_rfl).trans_lt ?_)
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  · exact ((Lp.aestronglyMeasurable g).norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [ENNReal.add_lt_top]
  exact ⟨eLpNorm_rpow_two_norm_lt_top f, eLpNorm_rpow_two_norm_lt_top g⟩

section InnerProductSpace

open scoped ComplexConjugate

/-
**MeasureTheory.L2.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.L2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inner 𝕜 (α →₂[μ] E) :=
  ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩
/-
**MeasureTheory.L2.inner_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L2`。
形式化陈述：inner_def (f g : α ->₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ
参数：f g : α ->₂[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ :=
  rfl
/-
**MeasureTheory.L2.integral_inner_eq_sq_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.L2`。
形式化陈述：integral_inner_eq_sq_eLpNorm (f : α ->₂[μ] E) : ∫ a, ⟪f a, f a⟫ ∂μ = ENNRe
al.toReal (∫⁻ a, (‖f a‖₊ : Real>=0∞) ^ (2 : Real) ∂μ)
参数：f : α ->₂[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
（共 42 条，此处仅展示前 30 条）
-/
theorem integral_inner_eq_sq_eLpNorm (f : α →₂[μ] E) :
    ∫ a, ⟪f a, f a⟫ ∂μ = ENNReal.toReal (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) := by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _
  · exact ((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const _).aestronglyMeasurable
  congr
  ext1 x
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ) := by simp
  rw [← Real.rpow_natCast _ 2, ← h_two, ←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, ofReal_norm]
  norm_cast
/-
**MeasureTheory.L2.norm_sq_eq_re_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
L2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_sq_eq_re_inner (f : α →₂[μ] E) : ‖f‖ ^ 2 = RCLike.re ⟪f, f⟫ := by
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [inner_def, integral_inner_eq_sq_eLpNorm, norm_def, ← ENNReal.toReal_pow, RCLike.ofReal_re,
    ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top (Lp.eLpNorm_ne_top f)) _]
  · rw [← ENNReal.rpow_natCast, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top, eLpNorm', ←
      ENNReal.rpow_mul, one_div, h_two]
    simp [enorm_eq_nnnorm]
  · refine (lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top zero_lt_two (ε := E) ?_).ne
    rw [← h_two, ← eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
    finiteness
/-
**MeasureTheory.L2.mem_L1_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L2`。
形式化陈述：mem_L1_inner (f g : α ->₂[μ] E) : AEEqFun.mk (fun x => ⟪f x, g x⟫) ((Lp.ae
stronglyMeasurable f).inner (Lp.aestronglyMeasurable g)) in Lp 𝕜 1 μ
参数：f g : α ->₂[μ] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inner`：∀ {α : Type u_1} {𝕜 : Type u_2
} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : I
nnerProductSpace 𝕜 E] {m x : M…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_aeeqFun`：eLpNorm_aeeqFun {α E : Type*} [Measurable
Space α] {μ : Measure α} [NormedAddCommGroup E] {p : Real>=0∞} {f : α -> E} (hf 
: AEStronglyMeasura…
· 使用定理 `MeasureTheory.L2.eLpNorm_inner_lt_top`：eLpNorm_inner_lt_top (f g : α ->₂
[μ] E) : eLpNorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞
-/
theorem mem_L1_inner (f g : α →₂[μ] E) :
    AEEqFun.mk (fun x => ⟪f x, g x⟫)
        ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)) ∈
      Lp 𝕜 1 μ := by
  simp_rw [mem_Lp_iff_eLpNorm_lt_top, eLpNorm_aeeqFun]; exact eLpNorm_inner_lt_top f g
/-
**MeasureTheory.L2.integrable_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L2`
。
形式化陈述：integrable_inner (f g : α ->₂[μ] E) : Integrable (fun x : α => ⟪f x, g x⟫)
 μ
参数：f g : α ->₂[μ] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.inner`：∀ {α : Type u_1} {𝕜 : Type u_2
} {E : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : I
nnerProductSpace 𝕜 E] {m x : M…
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.AEEqFun.integrable_iff_mem_L1`：integrable_iff_mem_L1 {f : 
α ->ₘ[μ] β} : Integrable f ↔ f in (α ->₁[μ] β)
· 使用定理 `MeasureTheory.L2.mem_L1_inner`：mem_L1_inner (f g : α ->₂[μ] E) : AEEqFun
.mk (fun x => ⟪f x, g x⟫) ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasu
rable g)) in Lp 𝕜 1…
-/
theorem integrable_inner (f g : α →₂[μ] E) : Integrable (fun x : α => ⟪f x, g x⟫) μ :=
  (integrable_congr
        (AEEqFun.coeFn_mk (fun x => ⟪f x, g x⟫)
          ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g)))).mp
    (AEEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))
/-
**MeasureTheory.L2.add_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_left' (f f' g : α →₂[μ] E) : ⟪f + f', g⟫ = ⟪f, g⟫ + ⟪f', g⟫ := by
  simp_rw [inner_def, ← integral_add (integrable_inner (𝕜 := 𝕜) f g) (integrable_inner f' g),
    ← inner_add_left]
  refine integral_congr_ae ((coeFn_add f f').mono fun x hx => ?_)
  simp only [hx, Pi.add_apply]
/-
**MeasureTheory.L2.smul_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.L2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem smul_left' (f g : α →₂[μ] E) (r : 𝕜) : ⟪r • f, g⟫ = conj r * ⟪f, g⟫ := by
  rw [inner_def, inner_def, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae ((coeFn_smul r f).mono fun x hx => ?_)
  simp only
  rw [smul_eq_mul, ← inner_smul_left, hx, Pi.smul_apply]
/-
**MeasureTheory.L2.innerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.L2
`。
形式化陈述：innerProductSpace : InnerProductSpace 𝕜 (α ->₂[μ] E) where norm_sq_eq_re_i
nner
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance innerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E) where
  norm_sq_eq_re_inner := private norm_sq_eq_re_inner
  conj_inner_symm _ _ := by simp_rw [inner_def, ← integral_conj, inner_conj_symm]
  add_left := private add_left'
  smul_left := private smul_left'

end InnerProductSpace

section IndicatorConstLp

variable (𝕜) {s t : Set α}

/-- The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs c` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
/-
**MeasureTheory.L2.inner_indicatorConstLp_eq_setIntegral_inner** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.L2`。
形式化陈述：inner_indicatorConstLp_eq_setIntegral_inner (f : Lp E 2 μ) (hs : Measurabl
eSet s) (c : E) (hμs : μ s != ∞) : (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ∫ x 
in s, ⟪c, f x⟫ ∂μ
参数：f : Lp E 2 μ；hs : MeasurableSet s；c : E；hμs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L2.inner_def`：inner_def (f g : α ->₂[μ] E) : ⟪f, g⟫ = ∫ a 
: α, ⟪f a, g a⟫ ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0

--- 原说明 ---
The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs c
` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`.
-/
theorem inner_indicatorConstLp_eq_setIntegral_inner (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E)
    (hμs : μ s ≠ ∞) : (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ∫ x in s, ⟪c, f x⟫ ∂μ := by
  rw [inner_def, ← integral_indicator hs]
  refine integral_congr_ae ((@indicatorConstLp_coeFn _ _ _ 2 μ _ s hs hμs c).mono fun x hx ↦ ?_)
  have : ⟪indicatorConstLp 2 hs hμs c x, f x⟫ = s.indicator (fun x ↦ ⟪c, f x⟫) x := by
    by_cases hxs : x ∈ s <;> simp [hx, hxs]
  simpa

/-- The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs c` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
/-
**MeasureTheory.L2.inner_indicatorConstLp_eq_inner_setIntegral** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.L2`。
形式化陈述：inner_indicatorConstLp_eq_inner_setIntegral [CompleteSpace E] [NormedSpace
 Real E] (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) (f : Lp E 2 μ) : (⟪indi
catorConstLp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : E；f : Lp E 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_inner`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} {E : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜]   [inst_1 : Norme
dAdd…
· 使用定理 `MeasureTheory.integrableOn_Lp_of_measure_ne_top`：integrableOn_Lp_of_meas
ure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α} (f : Lp E p μ) 
(hp : 1 <= p) (hμs : μ s != ∞) : Inte…
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.L2.inner_indicatorConstLp_eq_setIntegral_inner`：inner_indi
catorConstLp_eq_setIntegral_inner (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E) 
(hμs : μ s != ∞) : (⟪indicatorConstLp 2 hs hμs c, …

--- 原说明 ---
The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs c
` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`.
-/
theorem inner_indicatorConstLp_eq_inner_setIntegral [CompleteSpace E] [NormedSpace ℝ E]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) (f : Lp E 2 μ) :
    (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫ := by
  rw [← integral_inner (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
    L2.inner_indicatorConstLp_eq_setIntegral_inner]

variable {𝕜}

/-- The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs (1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`. -/
/-
**MeasureTheory.L2.inner_indicatorConstLp_one** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.L2`。
形式化陈述：inner_indicatorConstLp_one (hs : MeasurableSet s) (hμs : μ s != ∞) (f : Lp
 𝕜 2 μ) : ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hμs : μ s != ∞；f : Lp 𝕜 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L2.inner_indicatorConstLp_eq_inner_setIntegral`：inner_indi
catorConstLp_eq_inner_setIntegral [CompleteSpace E] [NormedSpace Real E] (hs : M
easurableSet s) (hμs : μ s != ∞) (c : E) (f : Lp E…
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product in `L2` of the indicator of a set `indicatorConstLp 2 hs hμs (
1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`.
-/
theorem inner_indicatorConstLp_one (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp 𝕜 2 μ) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ := by
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral 𝕜 hs hμs (1 : 𝕜) f]; simp

/-- The inner product in `L2` of two `indicatorConstLp`s, i.e. functions which are constant `a : E`
and `b : E` on measurable `s t : Set α` with finite measure, respectively, is `⟪a, b⟫` times the
measure of `s ∩ t`. -/
/-
**MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.L2`。
形式化陈述：inner_indicatorConstLp_indicatorConstLp [CompleteSpace E] (hs : Measurable
Set s) (ht : MeasurableSet t) (hμs : μ s != ∞
参数：hs : MeasurableSet s；ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.L2.inner_indicatorConstLp_eq_inner_setIntegral`：inner_indi
catorConstLp_eq_inner_setIntegral [CompleteSpace E] [NormedSpace Real E] (hs : M
easurableSet s) (hμs : μ s != ∞) (c : E) (f : Lp E…
· 使用定理 `MeasureTheory.setIntegral_indicatorConstLp`：setIntegral_indicatorConstLp
 [CompleteSpace E] {p : Real>=0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) 
(hμt : μ t != ∞) (e : E) : ∫ x i…
· 使用引理 `inner_smul_right_eq_smul`：inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪
x, r • y⟫ = r • ⟪x, y⟫
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
The inner product in `L2` of two `indicatorConstLp`s, i.e. functions which are c
onstant `a : E`
and `b : E` on measurable `s t : Set α` with finite measure, respectively, is `⟪
a, b⟫` times the
measure of `s ∩ t`.
-/
lemma inner_indicatorConstLp_indicatorConstLp [CompleteSpace E]
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞ := by finiteness)
    (hμt : μ t ≠ ∞ := by finiteness) (a b : E) :
    ⟪indicatorConstLp 2 hs hμs a, indicatorConstLp 2 ht hμt b⟫ = μ.real (s ∩ t) • ⟪a, b⟫ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  rw [inner_indicatorConstLp_eq_inner_setIntegral, setIntegral_indicatorConstLp hs,
    inner_smul_right_eq_smul, Set.inter_comm]

/-- The inner product in `L2` of indicators of two sets with finite measure
is the measure of the intersection. -/
/-
**MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.L2`。
形式化陈述：inner_indicatorConstLp_one_indicatorConstLp_one (hs : MeasurableSet s) (ht
 : MeasurableSet t) (hμs : μ s != ∞
参数：hs : MeasurableSet s；ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp`：inner_indicato
rConstLp_indicatorConstLp [CompleteSpace E] (hs : MeasurableSet s) (ht : Measura
bleSet t) (hμs : μ s != ∞
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `RCLike.ofReal_alg`：ofReal_alg (x : Real) : (x : K) = x • (1 : K)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product in `L2` of indicators of two sets with finite measure
is the measure of the intersection.
-/
lemma inner_indicatorConstLp_one_indicatorConstLp_one
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞ := by finiteness) (hμt : μ t ≠ ∞ := by finiteness) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), indicatorConstLp 2 ht hμt (1 : 𝕜)⟫ = μ.real (s ∩ t) := by
  simp [inner_indicatorConstLp_indicatorConstLp, RCLike.ofReal_alg]
/-
**MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.L2`。
形式化陈述：real_inner_indicatorConstLp_one_indicatorConstLp_one (hs : MeasurableSet s
) (ht : MeasurableSet t) (hμs : μ s != ∞
参数：hs : MeasurableSet s；ht : MeasurableSet t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp`：inner_indicato
rConstLp_indicatorConstLp [CompleteSpace E] (hs : MeasurableSet s) (ht : Measura
bleSet t) (hμs : μ s != ∞
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma real_inner_indicatorConstLp_one_indicatorConstLp_one
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞ := by finiteness) (hμt : μ t ≠ ∞ := by finiteness) :
    ⟪indicatorConstLp 2 hs hμs (1 : ℝ), indicatorConstLp 2 ht hμt (1 : ℝ)⟫_ℝ = μ.real (s ∩ t) := by
  simp [inner_indicatorConstLp_indicatorConstLp]
/-
**MeasureTheory.L2._root_.MeasureTheory.posSemidef_matrix_measure_inter** 是 Math
lib 中的一个引理，位于命名空间 `MeasureTheory.L2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.posSemidef_matrix_measure_inter {ι : Type*} [Finite ι] {s : ι → (Set α)}
    (mv : ∀ j, MeasurableSet (s j)) (hv : ∀ j, μ (s j) ≠ ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι ↦ μ.real (s i ∩ s j)) := by
  simp only [mv, ne_eq, hv, not_false_eq_true,
    ← real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram _ _

end IndicatorConstLp

end L2

section InnerContinuous

variable {α 𝕜 : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [RCLike 𝕜]
variable (μ : Measure α) [IsFiniteMeasure μ]

open scoped BoundedContinuousFunction ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
/-
**MeasureTheory.BoundedContinuousFunction.inner_toLp** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.BoundedContinuousFunction`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : TopologicalSpace α] [inst_1 : Meas
urableSpace α] [inst_2 : BorelSpace α]   [inst_3 : RCLike 𝕜] (μ : MeasureTheory.
Measure α) [inst_4 : MeasureTheory.IsFiniteMeasure μ]   (f g : BoundedContinuous
Function α 𝕜),   inner 𝕜 ((BoundedContinuousFunction.toLp 2 μ 𝕜) f) ((BoundedCon
tinuousFunction.toLp 2 μ 𝕜) g) =     ∫ (x : α), g x * (starRingEnd 𝕜) (f x) ∂μ
参数：μ : MeasureTheory.Measure α；f g : BoundedContinuousFunction α 𝕜；(BoundedConti
nuousFunction.toLp 2 μ 𝕜) f；(BoundedContinuousFunction.toLp 2 μ 𝕜) g；x : α；starR
ingEnd 𝕜；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `BoundedContinuousFunction.coeFn_toLp`：coeFn_toLp (f : α ->ᵇ E) : toLp (E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For bounded continuous functions `f`, `g` on a finite-measure topological space 
`α`, the L^2
inner product is the integral of their pointwise inner product.
-/
theorem BoundedContinuousFunction.inner_toLp (f g : α →ᵇ 𝕜) :
    ⟪BoundedContinuousFunction.toLp 2 μ 𝕜 f, BoundedContinuousFunction.toLp 2 μ 𝕜 g⟫ =
      ∫ x, g x * conj (f x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ 𝕜
  have hg_ae := g.coeFn_toLp 2 μ 𝕜
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]
  simp

variable [CompactSpace α]

/-- For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
/-
**MeasureTheory.ContinuousMap.inner_toLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.ContinuousMap`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : TopologicalSpace α] [inst_1 : Meas
urableSpace α] [inst_2 : BorelSpace α]   [inst_3 : RCLike 𝕜] (μ : MeasureTheory.
Measure α) [inst_4 : MeasureTheory.IsFiniteMeasure μ] [inst_5 : CompactSpace α] 
  (f g : C(α, 𝕜)),   inner 𝕜 ((ContinuousMap.toLp 2 μ 𝕜) f) ((ContinuousMap.toLp
 2 μ 𝕜) g) = ∫ (x : α), g x * (starRingEnd 𝕜) (f x) ∂μ
参数：μ : MeasureTheory.Measure α；f g : C(α, 𝕜)；(ContinuousMap.toLp 2 μ 𝕜) f；(Conti
nuousMap.toLp 2 μ 𝕜) g；x : α；starRingEnd 𝕜；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousMap.coeFn_toLp`：coeFn_toLp (f : C(α, E)) : toLp (E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For continuous functions `f`, `g` on a compact, finite-measure topological space
 `α`, the L^2
inner product is the integral of their pointwise inner product.
-/
theorem ContinuousMap.inner_toLp (f g : C(α, 𝕜)) :
    ⟪ContinuousMap.toLp 2 μ 𝕜 f, ContinuousMap.toLp 2 μ 𝕜 g⟫ =
      ∫ x, g x * conj (f x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  have hg_ae := g.coeFn_toLp (p := 2) (𝕜 := 𝕜) μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]
  simp

end InnerContinuous

end MeasureTheory

