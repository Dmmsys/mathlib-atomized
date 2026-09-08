/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Derivatives of Schwartz functions

In this file we define the various notions of derivatives of Schwartz functions.

## Main definitions

* `SchwartzMap.fderivCLM`: The differential as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`
* `SchwartzMap.derivCLM`: The one-dimensional derivative as a continuous linear map
  `𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`
* `SchwartzMap.instLineDeriv`: The directional derivative with notation `∂_{m} f`
* `SchwartzMap.instLaplacian`: The Laplacian for `𝓢(E, F)` as an instance of the notation type-class
  `Laplacian`.

## Main statements

* `SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv`: the iterated directional derivative is given
  by the applied Fréchet derivative of a Schwartz function.
* `SchwartzMap.laplacian_eq_sum`: the Laplacian is given by the sum of second derivatives in any
  orthonormal basis.
* `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`: Integration by parts using the
  directional derivative `∂_{m}`
* `SchwartzMap.integral_bilinear_laplacian_right_eq_left`: Integration by parts for the Laplacian

-/

@[expose] public noncomputable section

variable {ι 𝕜 𝕜' D E F V F F₁ F₂ F₃ : Type*}

namespace SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Derivatives

/-! ### Derivatives of Schwartz functions -/

variable [NormedSpace ℝ E]

variable (𝕜)
variable [RCLike 𝕜] [NormedSpace 𝕜 F]

variable (F) in
/-- The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map. -/
/-
**SchwartzMap.derivCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：derivCLM : 𝓢(Real, F) ->L[𝕜] 𝓢(Real, F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-dimensional derivative on Schwartz space as a continuous `𝕜`-linear map.
-/
def derivCLM : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F) :=
  mkCLM (deriv ·) (fun f g _ => deriv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => deriv_const_smul a f.differentiableAt)
    (fun f => (contDiff_succ_iff_deriv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [Real.norm_eq_abs, Finset.sup_singleton, schwartzSeminormFamily_apply, one_mul,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ'] using
        f.le_seminorm' 𝕜 k (n + 1) x⟩

@[simp]
/-
**SchwartzMap.derivCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：derivCLM_apply (f : 𝓢(Real, F)) (x : Real) : derivCLM 𝕜 F f x = deriv f x
参数：f : 𝓢(Real, F)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
-/
theorem derivCLM_apply (f : 𝓢(ℝ, F)) (x : ℝ) : derivCLM 𝕜 F f x = deriv f x :=
  rfl
/-
**SchwartzMap.hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：hasDerivAt (f : 𝓢(Real, F)) (x : Real) : HasDerivAt f (deriv f x) x
参数：f : 𝓢(Real, F)；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `SchwartzMap.differentiableAt`：∀ {E : Type u_5} {F : Type u_6} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]  
 [inst_3 : NormedS…
-/
theorem hasDerivAt (f : 𝓢(ℝ, F)) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  f.differentiableAt.hasDerivAt

open LineDeriv

section fderiv

variable [SMulCommClass ℝ 𝕜 F]

variable (E F) in
/-- The Fréchet derivative on Schwartz space as a continuous `𝕜`-linear map. -/
/-
**SchwartzMap.fderivCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：fderivCLM : 𝓢(E, F) ->L[𝕜] 𝓢(E, E ->L[Real] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fréchet derivative on Schwartz space as a continuous `𝕜`-linear map.
-/
def fderivCLM : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F) :=
  mkCLM (fderiv ℝ ·) (fun f g _ => fderiv_add f.differentiableAt g.differentiableAt)
    (fun a f _ => fderiv_const_smul f.differentiableAt a)
    (fun f => (contDiff_succ_iff_fderiv.mp (f.smooth ⊤)).2.2) fun ⟨k, n⟩ =>
    ⟨{⟨k, n + 1⟩}, 1, zero_le_one, fun f x => by
      simpa only [schwartzSeminormFamily_apply, Seminorm.comp_apply, Finset.sup_singleton,
        one_smul, norm_iteratedFDeriv_fderiv, one_mul] using f.le_seminorm 𝕜 k (n + 1) x⟩

@[simp]
/-
**SchwartzMap.fderivCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fderivCLM_apply (f : 𝓢(E, F)) (x : E) : fderivCLM 𝕜 E F f x = fderiv Real 
f x
参数：f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fderivCLM_apply (f : 𝓢(E, F)) (x : E) : fderivCLM 𝕜 E F f x = fderiv ℝ f x :=
  rfl
/-
**SchwartzMap.hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：hasFDerivAt (f : 𝓢(E, F)) (x : E) : HasFDerivAt f (fderiv Real f x) x
参数：f : 𝓢(E, F)；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `SchwartzMap.differentiableAt`：∀ {E : Type u_5} {F : Type u_6} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]  
 [inst_3 : NormedS…
-/
theorem hasFDerivAt (f : 𝓢(E, F)) (x : E) : HasFDerivAt f (fderiv ℝ f x) x :=
  f.differentiableAt.hasFDerivAt

/-- The partial derivative (or directional derivative) in the direction `m : E` as a
continuous linear map on Schwartz space. -/
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial derivative (or directional derivative) in the direction `m : E` as a
continuous linear map on Schwartz space.
-/
instance : LineDeriv E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp m f := (SchwartzMap.evalCLM ℝ E F m ∘L fderivCLM ℝ E F) f
/-
**SchwartzMap.lineDerivOp_apply_eq_fderiv** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap
`。
形式化陈述：lineDerivOp_apply_eq_fderiv (m : E) (f : 𝓢(E, F)) (x : E) : ∂_{m} f x = fd
eriv Real f x m
参数：m : E；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lineDerivOp_apply_eq_fderiv (m : E) (f : 𝓢(E, F)) (x : E) :
    ∂_{m} f x = fderiv ℝ f x m := rfl
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivAdd E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_add m := ((SchwartzMap.evalCLM ℝ E F m).comp (fderivCLM ℝ E F)).map_add
  lineDerivOp_left_add v w f := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivSMul 𝕜 E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_smul m := (SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F).map_smul
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LineDerivLeftSMul ℝ E 𝓢(E, F) 𝓢(E, F) where
  lineDerivOp_left_smul r y f := by
    ext x
    simp [lineDerivOp_apply_eq_fderiv]
/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousLineDeriv E 𝓢(E, F) 𝓢(E, F) where
  continuous_lineDerivOp m := (SchwartzMap.evalCLM ℝ E F m ∘L fderivCLM ℝ E F).continuous

open LineDeriv
/-
**SchwartzMap.lineDerivOpCLM_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：lineDerivOpCLM_eq (m : E) : lineDerivOpCLM 𝕜 𝓢(E, F) m = SchwartzMap.evalC
LM 𝕜 E F m ∘L fderivCLM 𝕜 E F
参数：m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.instLineDerivAdd`：∀ {E : Type u_5} {F : Type u_8} [inst : No
rmedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F]  
 [inst_3 : NormedS…
· 使用定理 `SchwartzMap.instLineDerivSMul`：∀ (𝕜 : Type u_2) {E : Type u_5} {F : Type
 u_8} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : 
NormedSpace ℝ F] [i…
· 使用定理 `SchwartzMap.instContinuousLineDeriv`：∀ {E : Type u_5} {F : Type u_8} [in
st : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace
 ℝ F]   [inst_3 : NormedS…
-/
theorem lineDerivOpCLM_eq (m : E) :
    lineDerivOpCLM 𝕜 𝓢(E, F) m = SchwartzMap.evalCLM 𝕜 E F m ∘L fderivCLM 𝕜 E F := rfl
/-
**SchwartzMap.lineDerivOp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：lineDerivOp_apply (m : E) (f : 𝓢(E, F)) (x : E) : ∂_{m} f x = lineDeriv Re
al f x m
参数：m : E；f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DifferentiableAt.lineDeriv_eq_fderiv`：DifferentiableAt.lineDeriv_eq_fder
iv (hf : DifferentiableAt 𝕜 f x) : lineDeriv 𝕜 f x v = fderiv 𝕜 f x v
· 使用定理 `SchwartzMap.differentiableAt`：∀ {E : Type u_5} {F : Type u_6} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]  
 [inst_3 : NormedS…
-/
theorem lineDerivOp_apply (m : E) (f : 𝓢(E, F)) (x : E) : ∂_{m} f x = lineDeriv ℝ f x m :=
  f.differentiableAt.lineDeriv_eq_fderiv.symm
/-
**SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `S
chwartzMap`。
形式化陈述：iteratedLineDerivOp_eq_iteratedFDeriv {n : Nat} {m : Fin n -> E} {f : 𝓢(E,
 F)} {x : E} : ∂^{m} f x = iteratedFDeriv Real n f x m
参数：E, F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LineDeriv.iteratedLineDerivOp_succ_left`：iteratedLineDerivOp_succ_left {
n : Nat} (m : Fin (n + 1) -> V) (f : E) : ∂^{m} f = ∂_{m 0} (∂^{tail m} f)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `iteratedFDeriv_succ_apply_left`：iteratedFDeriv_succ_apply_left {n : Nat}
 (m : Fin (n + 1) -> E) : (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) -> E) -> 
F) m = (fderiv 𝕜 (it…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderiv_continuousMultilinear_apply_const_apply`：fderiv_continuousMultili
near_apply_const_apply (hc : DifferentiableAt 𝕜 c x) (u : forall i, M i) (m : E)
 : (fderiv 𝕜 (fun y => (c y) u) x) m…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ContDiff.differentiable_iteratedFDeriv`：ContDiff.differentiable_iterated
FDeriv {m : Nat} (hm : m < n) (hf : ContDiff 𝕜 n f) : Differentiable 𝕜 fun x => 
iteratedFDeriv 𝕜 m f x
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
· 使用定理 `SchwartzMap.smooth`：smooth (f : 𝓢(E, F)) (n : Nat∞) : ContDiff Real n f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iteratedLineDerivOp_eq_iteratedFDeriv {n : ℕ} {m : Fin n → E} {f : 𝓢(E, F)} {x : E} :
    ∂^{m} f x = iteratedFDeriv ℝ n f x m := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedFDeriv_succ_apply_left,
      ← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_eq_fderiv, ← ih]
    · exact (f.smooth ⊤).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n) x

end fderiv

variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-
**SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名
空间 `SchwartzMap`。
形式化陈述：lineDerivOp_compCLMOfContinuousLinearEquiv (m : D) (g : D ≃L[Real] E) (f :
 𝓢(E, F)) : ∂_{m} (compCLMOfContinuousLinearEquiv 𝕜 g f) = compCLMOfContinuousLi
nearEquiv 𝕜 g (∂_{g m} f)
参数：m : D；g : D ≃L[Real] E；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.comp_right_fderiv`：comp_right_fderiv {f : F -> G} 
{x : E} : fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E ->L[𝕜] F)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineDerivOp_compCLMOfContinuousLinearEquiv (m : D) (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    ∂_{m} (compCLMOfContinuousLinearEquiv 𝕜 g f) =
    compCLMOfContinuousLinearEquiv 𝕜 g (∂_{g m} f) := by
  ext x
  simp [lineDerivOp_apply_eq_fderiv, ContinuousLinearEquiv.comp_right_fderiv]

end Derivatives

section support

variable (𝕜)
variable [RCLike 𝕜] [NormedSpace 𝕜 F]

/-
**SchwartzMap.tsupport_derivCLM_subset** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：tsupport_derivCLM_subset (f : 𝓢(Real, F)) : tsupport (derivCLM 𝕜 F f) subs
eteq tsupport f
参数：f : 𝓢(Real, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `tsupport_fderiv_apply_subset`：tsupport_fderiv_apply_subset (v : E) : tsu
pport (fderiv 𝕜 f · v) subseteq tsupport f
-/
theorem tsupport_derivCLM_subset (f : 𝓢(ℝ, F)) : tsupport (derivCLM 𝕜 F f) ⊆ tsupport f := by
  change tsupport (deriv f ·) ⊆ _
  simp_rw [← fderiv_apply_one_eq_deriv]
  exact tsupport_fderiv_apply_subset ℝ 1

variable [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 F]
/-
**SchwartzMap.tsupport_fderivCLM_subset** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：tsupport_fderivCLM_subset (f : 𝓢(E, F)) : tsupport (fderivCLM 𝕜 E F f) sub
seteq tsupport f
参数：f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsupport_fderiv_subset`：tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) s
ubseteq tsupport f
-/
theorem tsupport_fderivCLM_subset (f : 𝓢(E, F)) : tsupport (fderivCLM 𝕜 E F f) ⊆ tsupport f :=
  tsupport_fderiv_subset ℝ

open LineDeriv
/-
**SchwartzMap.tsupport_lineDerivOp_subset** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap
`。
形式化陈述：tsupport_lineDerivOp_subset (m : E) (f : 𝓢(E, F)) : tsupport (∂_{m} f : 𝓢(
E, F)) subseteq tsupport f
参数：m : E；f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsupport_fderiv_apply_subset`：tsupport_fderiv_apply_subset (v : E) : tsu
pport (fderiv 𝕜 f · v) subseteq tsupport f
-/
theorem tsupport_lineDerivOp_subset (m : E) (f : 𝓢(E, F)) :
    tsupport (∂_{m} f : 𝓢(E, F)) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ m
/-
**SchwartzMap.tsupport_iteratedLineDerivOp_subset** 是 Mathlib 中的一个定理，位于命名空间 `Sch
wartzMap`。
形式化陈述：tsupport_iteratedLineDerivOp_subset {n : Nat} (m : Fin n -> E) (f : 𝓢(E, F
)) : tsupport (∂^{m} f : 𝓢(E, F)) subseteq tsupport f
参数：m : Fin n -> E；f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LineDeriv.iteratedLineDerivOp_succ_left`：iteratedLineDerivOp_succ_left {
n : Nat} (m : Fin (n + 1) -> V) (f : E) : ∂^{m} f = ∂_{m 0} (∂^{tail m} f)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SchwartzMap.tsupport_lineDerivOp_subset`：tsupport_lineDerivOp_subset (m 
: E) (f : 𝓢(E, F)) : tsupport (∂_{m} f : 𝓢(E, F)) subseteq tsupport f
-/
theorem tsupport_iteratedLineDerivOp_subset {n : ℕ} (m : Fin n → E) (f : 𝓢(E, F)) :
    tsupport (∂^{m} f : 𝓢(E, F)) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left]
    exact (tsupport_lineDerivOp_subset (m 0) _).trans (IH <| Fin.tail m)

end support

section Laplacian

/-! ## Laplacian on `𝓢(E, F)` -/

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Laplacian LineDeriv

/-
**SchwartzMap.** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Laplacian 𝓢(E, F) 𝓢(E, F) where
  laplacian := laplacianCLM ℝ E 𝓢(E, F)
/-
**SchwartzMap.laplacianCLM_eq'** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：laplacianCLM_eq' (f : 𝓢(E, F)) : laplacianCLM Real E 𝓢(E, F) f = Δ f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.instLineDerivAdd`：∀ {E : Type u_5} {F : Type u_8} [inst : No
rmedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F]  
 [inst_3 : NormedS…
· 使用定理 `SchwartzMap.instLineDerivSMul`：∀ (𝕜 : Type u_2) {E : Type u_5} {F : Type
 u_8} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : 
NormedSpace ℝ F] [i…
· 使用定理 `SchwartzMap.instContinuousLineDeriv`：∀ {E : Type u_5} {F : Type u_8} [in
st : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace
 ℝ F]   [inst_3 : NormedS…
-/
theorem laplacianCLM_eq' (f : 𝓢(E, F)) : laplacianCLM ℝ E 𝓢(E, F) f = Δ f := rfl
/-
**SchwartzMap.laplacian_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι Real E) (f : 𝓢(E, F))
 : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
参数：b : OrthonormalBasis ι Real E；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LineDeriv.laplacianCLM_eq_sum`：laplacianCLM_eq_sum [Fintype ι] (v : Orth
onormalBasis ι Real E) (f : V₁) : laplacianCLM Real E V₁ f = ∑ i, ∂_{v i} (∂_{v 
i} f)
· 使用定理 `SchwartzMap.instLineDerivAdd`：∀ {E : Type u_5} {F : Type u_8} [inst : No
rmedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F]  
 [inst_3 : NormedS…
· 使用定理 `SchwartzMap.instLineDerivSMul`：∀ (𝕜 : Type u_2) {E : Type u_5} {F : Type
 u_8} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : 
NormedSpace ℝ F] [i…
· 使用定理 `SchwartzMap.instContinuousLineDeriv`：∀ {E : Type u_5} {F : Type u_8} [in
st : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace
 ℝ F]   [inst_3 : NormedS…
· 使用定理 `SchwartzMap.instLineDerivLeftSMulReal`：∀ {E : Type u_5} {F : Type u_8} [
inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpa
ce ℝ F]   [inst_3 : NormedS…
-/
theorem laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    Δ f = ∑ i, ∂_{b i} (∂_{b i} f) :=
  LineDeriv.laplacianCLM_eq_sum b f

variable (𝕜) in
@[simp]
/-
**SchwartzMap.laplacianCLM_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：laplacianCLM_eq [RCLike 𝕜] [NormedSpace 𝕜 F] (f : 𝓢(E, F)) : laplacianCLM 
𝕜 E 𝓢(E, F) f = Δ f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `SchwartzMap.instLineDerivAdd`：∀ {E : Type u_5} {F : Type u_8} [inst : No
rmedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F]  
 [inst_3 : NormedS…
· 使用定理 `SchwartzMap.instLineDerivSMul`：∀ (𝕜 : Type u_2) {E : Type u_5} {F : Type
 u_8} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [inst_2 : 
NormedSpace ℝ F] [i…
· 使用定理 `SchwartzMap.instContinuousLineDeriv`：∀ {E : Type u_5} {F : Type u_8} [in
st : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace
 ℝ F]   [inst_3 : NormedS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `SchwartzMap.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b : Orthonor
malBasis ι Real E) (f : 𝓢(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laplacianCLM_eq [RCLike 𝕜] [NormedSpace 𝕜 F] (f : 𝓢(E, F)) :
    laplacianCLM 𝕜 E 𝓢(E, F) f = Δ f := by
  simp [laplacianCLM, laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
/-
**SchwartzMap.laplacian_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：laplacian_apply (f : 𝓢(E, F)) (x : E) : Δ f x = Δ (f : E -> F) x
参数：f : 𝓢(E, F)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b : Orthonor
malBasis ι Real E) (f : 𝓢(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `SchwartzMap.instIsZeroApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   
[inst_3 : NormedS…
· 使用定理 `SchwartzMap.instIsAddApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`：laplacia
n_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι] (v : OrthonormalBas
is ι Real E) : Δ f = fun x => ∑ i, iteratedFDeriv Re…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laplacian_apply (f : 𝓢(E, F)) (x : E) : Δ f x = Δ (f : E → F) x := by
  rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E),
    sum_apply, ← iteratedLineDerivOp_eq_iteratedFDeriv, iteratedLineDerivOp_succ_left]

end Laplacian

section integration_by_parts

variable [NormedSpace ℝ E]

open ENNReal MeasureTheory

section one_dim

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a general bilinear map. -/
/-
**SchwartzMap.integral_bilinear_deriv_right_eq_neg_left** 是 Mathlib 中的一个定理，位于命名空
间 `SchwartzMap`。
形式化陈述：integral_bilinear_deriv_right_eq_neg_left (f : 𝓢(Real, E)) (g : 𝓢(Real, F)
) (L : E ->L[Real] F ->L[Real] V) : ∫ (x : Real), L (f x) (deriv g x) = -∫ (x : 
Real), L (deriv f x) (g x)
参数：f : 𝓢(Real, E)；g : 𝓢(Real, F)；L : E ->L[Real] F ->L[Real] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrab
le`：integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (hu : forall x 
in tsupport v, HasDerivAt u (u' x) x) (hv : forall x in tsupport…
· 使用定理 `SchwartzMap.hasDerivAt`：hasDerivAt (f : 𝓢(Real, F)) (x : Real) : HasDeri
vAt f (deriv f x) x
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a general bilinear map.
-/
theorem integral_bilinear_deriv_right_eq_neg_left (f : 𝓢(ℝ, E)) (g : 𝓢(ℝ, F))
    (L : E →L[ℝ] F →L[ℝ] V) :
    ∫ (x : ℝ), L (f x) (deriv g x) = -∫ (x : ℝ), L (deriv f x) (g x) :=
  MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (fun x _ ↦ f.hasDerivAt x) (fun x _ ↦ g.hasDerivAt x) (pairing L f (derivCLM ℝ F g)).integrable
    (pairing L (derivCLM ℝ E f) g).integrable (pairing L f g).integrable

variable [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 𝕜] [SMulCommClass ℝ 𝕜 𝕜] in
/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for multiplication of scalar-valued Schwartz functions. -/
/-
**SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Sch
wartzMap`。
形式化陈述：integral_mul_deriv_eq_neg_deriv_mul (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, 𝕜)) : ∫ 
(x : Real), f x * (deriv g x) = -∫ (x : Real), deriv f x * (g x)
参数：f : 𝓢(Real, 𝕜)；g : 𝓢(Real, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilinear_deriv_right_eq_neg_left`：integral_bilinear
_deriv_right_eq_neg_left (f : 𝓢(Real, E)) (g : 𝓢(Real, F)) (L : E ->L[Real] F ->
L[Real] V) : ∫ (x : Real), L (f x) (deriv g…

--- 原说明 ---
Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for multiplication of scalar-valued Schwartz functions.
-/
theorem integral_mul_deriv_eq_neg_deriv_mul (f : 𝓢(ℝ, 𝕜)) (g : 𝓢(ℝ, 𝕜)) :
    ∫ (x : ℝ), f x * (deriv g x) = -∫ (x : ℝ), deriv f x * (g x) :=
  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.mul ℝ 𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a Schwartz function with values in continuous linear maps. -/
/-
**SchwartzMap.integral_smul_deriv_right_eq_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `S
chwartzMap`。
形式化陈述：integral_smul_deriv_right_eq_neg_left (f : 𝓢(Real, 𝕜)) (g : 𝓢(Real, F)) : 
∫ (x : Real), f x • deriv g x = -∫ (x : Real), deriv f x • g x
参数：f : 𝓢(Real, 𝕜)；g : 𝓢(Real, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilinear_deriv_right_eq_neg_left`：integral_bilinear
_deriv_right_eq_neg_left (f : 𝓢(Real, E)) (g : 𝓢(Real, F)) (L : E ->L[Real] F ->
L[Real] V) : ∫ (x : Real), L (f x) (deriv g…
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

--- 原说明 ---
Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a Schwartz function with values in continuous linear maps.
-/
theorem integral_smul_deriv_right_eq_neg_left (f : 𝓢(ℝ, 𝕜)) (g : 𝓢(ℝ, F)) :
    ∫ (x : ℝ), f x • deriv g x = -∫ (x : ℝ), deriv f x • g x :=
  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.lsmul ℝ 𝕜)

/-- Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a Schwartz function with values in continuous linear maps. -/
/-
**SchwartzMap.integral_clm_comp_deriv_right_eq_neg_left** 是 Mathlib 中的一个定理，位于命名空
间 `SchwartzMap`。
形式化陈述：integral_clm_comp_deriv_right_eq_neg_left (f : 𝓢(Real, F ->L[𝕜] V)) (g : 𝓢
(Real, F)) : ∫ (x : Real), f x (deriv g x) = -∫ (x : Real), deriv f x (g x)
参数：f : 𝓢(Real, F ->L[𝕜] V)；g : 𝓢(Real, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `SchwartzMap.integral_bilinear_deriv_right_eq_neg_left`：integral_bilinear
_deriv_right_eq_neg_left (f : 𝓢(Real, E)) (g : 𝓢(Real, F)) (L : E ->L[Real] F ->
L[Real] V) : ∫ (x : Real), L (f x) (deriv g…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
Integration by parts of Schwartz functions for the 1-dimensional derivative.

Version for a Schwartz function with values in continuous linear maps.
-/
theorem integral_clm_comp_deriv_right_eq_neg_left (f : 𝓢(ℝ, F →L[𝕜] V)) (g : 𝓢(ℝ, F)) :
    ∫ (x : ℝ), f x (deriv g x) = -∫ (x : ℝ), deriv f x (g x) :=
  integral_bilinear_deriv_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars ℝ)

end one_dim

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [MeasurableSpace D] {μ : Measure D} [BorelSpace D] [FiniteDimensional ℝ D] [μ.IsAddHaarMeasure]

open scoped LineDeriv

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for a general bilinear map. -/
/-
**SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left** 是 Mathlib 中的一个定理
，位于命名空间 `SchwartzMap`。
形式化陈述：integral_bilinear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F)
) (L : E ->L[Real] F ->L[Real] V) (v : D) : ∫ (x : D), L (f x) (∂_{v} g x) ∂μ = 
-∫ (x : D), L (∂_{v} f x) (g x) ∂μ
参数：f : 𝓢(D, E)；g : 𝓢(D, F)；L : E ->L[Real] F ->L[Real] V；v : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`：integr
al_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable {f f' : E -> F} {g g'
 : E -> G} {v : E} {B : F ->L[Real] G ->L[Real] W} (hf…
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `SchwartzMap.hasTemperateGrowth`：hasTemperateGrowth (f : 𝓢(E, F)) : Funct
ion.HasTemperateGrowth f
· 使用引理 `HasFDerivAt.hasLineDerivAt`：HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt
 f L x) (v : E) : HasLineDerivAt 𝕜 f (L v) x v
· 使用定理 `SchwartzMap.hasFDerivAt`：hasFDerivAt (f : 𝓢(E, F)) (x : E) : HasFDerivAt
 f (fderiv Real f x) x

--- 原说明 ---
Integration by parts of Schwartz functions for directional derivatives.

Version for a general bilinear map.
-/
theorem integral_bilinear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F))
    (L : E →L[ℝ] F →L[ℝ] V) (v : D) :
    ∫ (x : D), L (f x) (∂_{v} g x) ∂μ = -∫ (x : D), L (∂_{v} f x) (g x) ∂μ := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (v := v)
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
    (bilinLeftCLM L (∂_{v} g).hasTemperateGrowth _).integrable
    (bilinLeftCLM L g.hasTemperateGrowth _).integrable
  all_goals exact fun x _ ↦ (hasFDerivAt _ x).hasLineDerivAt v

variable [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 𝕜] [SMulCommClass ℝ 𝕜 𝕜] in
/-- Integration by parts of Schwartz functions for directional derivatives.

Version for multiplication of scalar-valued Schwartz functions. -/
/-
**SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left** 是 Mathlib 中的一个定理，位于命名
空间 `SchwartzMap`。
形式化陈述：integral_mul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, 𝕜)) (v 
: D) : ∫ (x : D), f x * ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x * g x ∂μ
参数：f : 𝓢(D, 𝕜)；g : 𝓢(D, 𝕜)；v : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`：integral_bi
linear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F)) (L : E ->L[Real
] F ->L[Real] V) (v : D) : ∫ (x : D), L (f x) (∂_…

--- 原说明 ---
Integration by parts of Schwartz functions for directional derivatives.

Version for multiplication of scalar-valued Schwartz functions.
-/
theorem integral_mul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, 𝕜)) (v : D) :
    ∫ (x : D), f x * ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x * g x ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.mul ℝ 𝕜) v

variable [RCLike 𝕜] [NormedSpace 𝕜 F] [NormedSpace 𝕜 V]

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for scalar multiplication. -/
/-
**SchwartzMap.integral_smul_lineDerivOp_right_eq_neg_left** 是 Mathlib 中的一个定理，位于命
名空间 `SchwartzMap`。
形式化陈述：integral_smul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v
 : D) : ∫ (x : D), f x • ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x • g x ∂μ
参数：f : 𝓢(D, 𝕜)；g : 𝓢(D, F)；v : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`：integral_bi
linear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F)) (L : E ->L[Real
] F ->L[Real] V) (v : D) : ∫ (x : D), L (f x) (∂_…
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

--- 原说明 ---
Integration by parts of Schwartz functions for directional derivatives.

Version for scalar multiplication.
-/
theorem integral_smul_lineDerivOp_right_eq_neg_left (f : 𝓢(D, 𝕜)) (g : 𝓢(D, F)) (v : D) :
    ∫ (x : D), f x • ∂_{v} g x ∂μ = -∫ (x : D), ∂_{v} f x • g x ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.lsmul ℝ 𝕜) v

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for a Schwartz function with values in continuous linear maps. -/
/-
**SchwartzMap.integral_clm_comp_lineDerivOp_right_eq_neg_left** 是 Mathlib 中的一个定理
，位于命名空间 `SchwartzMap`。
形式化陈述：integral_clm_comp_lineDerivOp_right_eq_neg_left (f : 𝓢(D, F ->L[𝕜] V)) (g 
: 𝓢(D, F)) (v : D) : ∫ (x : D), f x (∂_{v} g x) ∂μ = -∫ (x : D), ∂_{v} f x (g x)
 ∂μ
参数：f : 𝓢(D, F ->L[𝕜] V)；g : 𝓢(D, F)；v : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`：integral_bi
linear_lineDerivOp_right_eq_neg_left (f : 𝓢(D, E)) (g : 𝓢(D, F)) (L : E ->L[Real
] F ->L[Real] V) (v : D) : ∫ (x : D), L (f x) (∂_…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
Integration by parts of Schwartz functions for directional derivatives.

Version for a Schwartz function with values in continuous linear maps.
-/
theorem integral_clm_comp_lineDerivOp_right_eq_neg_left (f : 𝓢(D, F →L[𝕜] V)) (g : 𝓢(D, F))
    (v : D) : ∫ (x : D), f x (∂_{v} g x) ∂μ = -∫ (x : D), ∂_{v} f x (g x) ∂μ :=
  integral_bilinear_lineDerivOp_right_eq_neg_left f g
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] V)).bilinearRestrictScalars ℝ) v

end integration_by_parts

section laplacian_integration_by_parts

open MeasureTheory Laplacian LineDeriv

/-! ### Integration by parts -/

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [MeasurableSpace E] {μ : Measure E} [BorelSpace E] [μ.IsAddHaarMeasure]

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for a general bilinear map. -/
/-
**SchwartzMap.integral_bilinear_laplacian_right_eq_left** 是 Mathlib 中的一个定理，位于命名空
间 `SchwartzMap`。
形式化陈述：integral_bilinear_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (L
 : F₁ ->L[Real] F₂ ->L[Real] F₃) : ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, L (Δ f x) (g x
) ∂μ
参数：f : 𝓢(E, F₁)；g : 𝓢(E, F₂)；L : F₁ ->L[Real] F₂ ->L[Real] F₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b : Orthonor
malBasis ι Real E) (f : 𝓢(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `SchwartzMap.instIsZeroApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Nor
medAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   
[inst_3 : NormedS…
· 使用定理 `SchwartzMap.instIsAddApply`：∀ {E : Type u_5} {F : Type u_6} [inst : Norm
edAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [
inst_3 : NormedS…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Integration by parts of Schwartz functions for the Laplacian.

Version for a general bilinear map.
-/
theorem integral_bilinear_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
    (L : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, L (Δ f x) (g x) ∂μ := by
  simp_rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E), sum_apply, map_sum,
    _root_.sum_apply]
  rw [MeasureTheory.integral_finsetSum, MeasureTheory.integral_finsetSum]
  · simp [integral_bilinear_lineDerivOp_right_eq_neg_left]
  · exact fun _ _ ↦ (pairing L (∂_{_} <| ∂_{_} f) g).integrable
  · exact fun _ _ ↦ (pairing L f (∂_{_} <| ∂_{_} g)).integrable

variable [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 𝕜] [SMulCommClass ℝ 𝕜 𝕜] in
/-- Integration by parts of Schwartz functions for the Laplacian.

Version for multiplication of scalar-valued Schwartz functions. -/
/-
**SchwartzMap.integral_mul_laplacian_right_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Sc
hwartzMap`。
形式化陈述：integral_mul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, 𝕜)) : ∫ x, f 
x * Δ g x ∂μ = ∫ x, Δ f x * g x ∂μ
参数：f : 𝓢(E, 𝕜)；g : 𝓢(E, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilinear_laplacian_right_eq_left`：integral_bilinear
_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (L : F₁ ->L[Real] F₂ ->L[
Real] F₃) : ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, …

--- 原说明 ---
Integration by parts of Schwartz functions for the Laplacian.

Version for multiplication of scalar-valued Schwartz functions.
-/
theorem integral_mul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, 𝕜)) :
    ∫ x, f x * Δ g x ∂μ = ∫ x, Δ f x * g x ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.mul ℝ 𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for scalar multiplication. -/
/-
**SchwartzMap.integral_smul_laplacian_right_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `S
chwartzMap`。
形式化陈述：integral_smul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F)) : ∫ x, f
 x • Δ g x ∂μ = ∫ x, Δ f x • g x ∂μ
参数：f : 𝓢(E, 𝕜)；g : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilinear_laplacian_right_eq_left`：integral_bilinear
_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (L : F₁ ->L[Real] F₂ ->L[
Real] F₃) : ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, …
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

--- 原说明 ---
Integration by parts of Schwartz functions for the Laplacian.

Version for scalar multiplication.
-/
theorem integral_smul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F)) :
    ∫ x, f x • Δ g x ∂μ = ∫ x, Δ f x • g x ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.lsmul ℝ 𝕜)

variable [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂]

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for a Schwartz function with values in continuous linear maps. -/
/-
**SchwartzMap.integral_clm_comp_laplacian_right_eq_left** 是 Mathlib 中的一个定理，位于命名空
间 `SchwartzMap`。
形式化陈述：integral_clm_comp_laplacian_right_eq_left (f : 𝓢(E, F₁ ->L[𝕜] F₂)) (g : 𝓢(
E, F₁)) : ∫ x, f x (Δ g x) ∂μ = ∫ x, Δ f x (g x) ∂μ
参数：f : 𝓢(E, F₁ ->L[𝕜] F₂)；g : 𝓢(E, F₁)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `SchwartzMap.integral_bilinear_laplacian_right_eq_left`：integral_bilinear
_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (L : F₁ ->L[Real] F₂ ->L[
Real] F₃) : ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
Integration by parts of Schwartz functions for the Laplacian.

Version for a Schwartz function with values in continuous linear maps.
-/
theorem integral_clm_comp_laplacian_right_eq_left (f : 𝓢(E, F₁ →L[𝕜] F₂)) (g : 𝓢(E, F₁)) :
    ∫ x, f x (Δ g x) ∂μ = ∫ x, Δ f x (g x) ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g
    ((ContinuousLinearMap.id 𝕜 (F₁ →L[𝕜] F₂)).bilinearRestrictScalars ℝ)

end laplacian_integration_by_parts

end SchwartzMap

