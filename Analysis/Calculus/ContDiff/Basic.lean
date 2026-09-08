/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Basic properties of continuously-differentiable functions

This file continues the development of the API for `ContDiff`, `ContDiffAt`, etc, covering
constants, products, composition with linear maps, etc.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Fin Filter Function

open scoped Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s t : Set E} {f : E → F} {x : E} {b : E × F → G} {m n : ℕ∞ω}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Constants -/
section constants

/-
**iteratedFDerivWithin_succ_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_succ_const (n : Nat) (c : F) : iteratedFDerivWithin 𝕜
 (n + 1) (fun _ : E => c) s = 0
参数：n : Nat；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `fderivWithin_fun_const`：fderivWithin_fun_const (c : F) : fderivWithin 𝕜 
(fun _ => c) s = 0
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
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedFDerivWithin_succ_eq_comp_left`：iteratedFDerivWithin_succ_eq_com
p_left {n : Nat} : iteratedFDerivWithin 𝕜 (n + 1) f s = (continuousMultilinearCu
rryLeftEquiv 𝕜 (fun _ : Fin …
-/
theorem iteratedFDerivWithin_succ_const (n : ℕ) (c : F) :
    iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E ↦ c) s = 0 := by
  induction n with
  | zero =>
    ext1
    simp [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, comp_def]
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left, IH]
    simp only [Pi.zero_def, comp_def, fderivWithin_fun_const, map_zero]

@[simp]
/-
**iteratedFDerivWithin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_zero {i : Nat} : iteratedFDerivWithin 𝕜 i (0 : E -> F
) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_succ_const`：iteratedFDerivWithin_succ_const (n : Na
t) (c : F) : iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E => c) s = 0
-/
theorem iteratedFDerivWithin_zero {i : ℕ} :
    iteratedFDerivWithin 𝕜 i (0 : E → F) s = 0 := by
  cases i with
  | zero => ext; simp
  | succ i => apply iteratedFDerivWithin_succ_const

@[simp]
/-
**iteratedFDerivWithin_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_fun_zero {i : Nat} : iteratedFDerivWithin 𝕜 i (fun (_
 : E) => (0 : F)) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedFDerivWithin_zero`：iteratedFDerivWithin_zero {i : Nat} : iterate
dFDerivWithin 𝕜 i (0 : E -> F) s = 0
-/
theorem iteratedFDerivWithin_fun_zero {i : ℕ} :
    iteratedFDerivWithin 𝕜 i (fun (_ : E) ↦ (0 : F)) s = 0 := by
  apply iteratedFDerivWithin_zero

@[deprecated (since := "2026-03-18")]
alias iteratedFDerivWithin_zero_fun := iteratedFDerivWithin_fun_zero

@[simp]
/-
**ftaylorSeriesWithin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ftaylorSeriesWithin_zero : ftaylorSeriesWithin 𝕜 (0 : E -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
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
· 使用定理 `iteratedFDerivWithin_zero`：iteratedFDerivWithin_zero {i : Nat} : iterate
dFDerivWithin 𝕜 i (0 : E -> F) s = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ftaylorSeriesWithin_zero :
    ftaylorSeriesWithin 𝕜 (0 : E → F) = 0 := by
  ext
  simp [ftaylorSeriesWithin]

@[simp]
/-
**ftaylorSeriesWithin_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ftaylorSeriesWithin_fun_zero : ftaylorSeriesWithin 𝕜 (fun (_ : E) => (0 : 
F)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ftaylorSeriesWithin_zero`：ftaylorSeriesWithin_zero : ftaylorSeriesWithin
 𝕜 (0 : E -> F) = 0
-/
theorem ftaylorSeriesWithin_fun_zero :
    ftaylorSeriesWithin 𝕜 (fun (_ : E) ↦ (0 : F)) = 0 := by
  apply ftaylorSeriesWithin_zero

@[simp]
/-
**iteratedFDeriv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_zero {n : Nat} : iteratedFDeriv 𝕜 n (0 : E -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_zero`：iteratedFDerivWithin_zero {i : Nat} : iterate
dFDerivWithin 𝕜 i (0 : E -> F) s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedFDeriv_zero {n : ℕ} :
    iteratedFDeriv 𝕜 n (0 : E → F) = 0 :=
  funext fun x ↦ by simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_zero]

@[simp]
/-
**iteratedFDeriv_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_fun_zero {n : Nat} : iteratedFDeriv 𝕜 n (fun (_ : E) => (0 
: F)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedFDeriv_zero`：iteratedFDeriv_zero {n : Nat} : iteratedFDeriv 𝕜 n 
(0 : E -> F) = 0
-/
theorem iteratedFDeriv_fun_zero {n : ℕ} :
    iteratedFDeriv 𝕜 n (fun (_ : E) ↦ (0 : F)) = 0 := by
  apply iteratedFDeriv_zero

@[deprecated (since := "2026-03-18")] alias iteratedFDeriv_zero_fun := iteratedFDeriv_fun_zero

@[simp]
/-
**ftaylorSeries_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ftaylorSeries_zero : ftaylorSeries 𝕜 (0 : E -> F) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
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
· 使用定理 `iteratedFDeriv_zero`：iteratedFDeriv_zero {n : Nat} : iteratedFDeriv 𝕜 n 
(0 : E -> F) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ftaylorSeries_zero :
    ftaylorSeries 𝕜 (0 : E → F) = 0 := by
  ext
  simp [ftaylorSeries]

@[simp]
/-
**ftaylorSeries_fun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ftaylorSeries_fun_zero : ftaylorSeries 𝕜 (fun (_ : E) => (0 : F)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
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
· 使用定理 `iteratedFDeriv_fun_zero`：iteratedFDeriv_fun_zero {n : Nat} : iteratedFDe
riv 𝕜 n (fun (_ : E) => (0 : F)) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ftaylorSeries_fun_zero :
    ftaylorSeries 𝕜 (fun (_ : E) ↦ (0 : F)) = 0 := by
  ext
  simp [ftaylorSeries]
/-
**contDiff_zero_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_zero_fun : ContDiff 𝕜 n fun _ : E => (0 : F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s
-/
theorem contDiff_zero_fun : ContDiff 𝕜 n fun _ : E => (0 : F) :=
  analyticOnNhd_const.contDiff

/-- Constants are `C^∞`. -/
@[fun_prop]
/-
**contDiff_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s

--- 原说明 ---
Constants are `C^∞`.
-/
theorem contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c :=
  analyticOnNhd_const.contDiff

@[fun_prop]
/-
**contDiffOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun _ : E => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun _ : E => c) s :=
  contDiff_const.contDiffOn

@[fun_prop]
/-
**contDiffAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x :=
  contDiff_const.contDiffAt

@[fun_prop]
/-
**contDiffWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_const {c : F} : ContDiffWithinAt 𝕜 n (fun _ : E => c) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
-/
theorem contDiffWithinAt_const {c : F} : ContDiffWithinAt 𝕜 n (fun _ : E => c) s x :=
  contDiffAt_const.contDiffWithinAt

@[nontriviality]
/-
**contDiff_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_of_subsingleton [Subsingleton F] : ContDiff 𝕜 n f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem contDiff_of_subsingleton [Subsingleton F] : ContDiff 𝕜 n f := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiff_const

@[nontriviality]
/-
**contDiffAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_of_subsingleton [Subsingleton F] : ContDiffAt 𝕜 n f x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
-/
theorem contDiffAt_of_subsingleton [Subsingleton F] : ContDiffAt 𝕜 n f x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const

@[nontriviality]
/-
**contDiffWithinAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_of_subsingleton [Subsingleton F] : ContDiffWithinAt 𝕜 n f
 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
-/
theorem contDiffWithinAt_of_subsingleton [Subsingleton F] : ContDiffWithinAt 𝕜 n f s x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffWithinAt_const

@[nontriviality]
/-
**contDiffOn_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_subsingleton [Subsingleton F] : ContDiffOn 𝕜 n f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `contDiffOn_const`：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n 
(fun _ : E => c) s
-/
theorem contDiffOn_of_subsingleton [Subsingleton F] : ContDiffOn 𝕜 n f s := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffOn_const
/-
**iteratedFDerivWithin_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_const_of_ne {n : Nat} (hn : n != 0) (c : F) (s : Set 
E) : iteratedFDerivWithin 𝕜 n (fun _ : E => c) s = 0
参数：hn : n != 0；c : F；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_succ_const`：iteratedFDerivWithin_succ_const (n : Na
t) (c : F) : iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E => c) s = 0
-/
theorem iteratedFDerivWithin_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F) (s : Set E) :
    iteratedFDerivWithin 𝕜 n (fun _ : E ↦ c) s = 0 := by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const n c
/-
**iteratedFDeriv_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_const_of_ne {n : Nat} (hn : n != 0) (c : F) : (iteratedFDer
iv 𝕜 n fun _ : E => c) = 0
参数：hn : n != 0；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_const_of_ne`：iteratedFDerivWithin_const_of_ne {n : 
Nat} (hn : n != 0) (c : F) (s : Set E) : iteratedFDerivWithin 𝕜 n (fun _ : E => 
c) s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedFDeriv_const_of_ne {n : ℕ} (hn : n ≠ 0) (c : F) :
    (iteratedFDeriv 𝕜 n fun _ : E ↦ c) = 0 := by
  simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_const_of_ne hn]
/-
**iteratedFDeriv_succ_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_succ_const (n : Nat) (c : F) : (iteratedFDeriv 𝕜 (n + 1) fu
n _ : E => c) = 0
参数：n : Nat；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iteratedFDeriv_const_of_ne`：iteratedFDeriv_const_of_ne {n : Nat} (hn : n
 != 0) (c : F) : (iteratedFDeriv 𝕜 n fun _ : E => c) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem iteratedFDeriv_succ_const (n : ℕ) (c : F) :
    (iteratedFDeriv 𝕜 (n + 1) fun _ : E ↦ c) = 0 :=
  iteratedFDeriv_const_of_ne (by simp) _
/-
**contDiffWithinAt_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_singleton : ContDiffWithinAt 𝕜 n f {x} x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.congr`：ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n
 f s x) (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 
n f₁ s x
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem contDiffWithinAt_singleton : ContDiffWithinAt 𝕜 n f {x} x :=
  (contDiffWithinAt_const (c := f x)).congr (by simp) rfl

end constants

/-! ### Smoothness of linear functions -/
section linear

/-- Unbundled bounded linear functions are `C^n`. -/
/-
**IsBoundedLinearMap.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedLinearMap.contDiff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f
参数：hf : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
· 使用定理 `ContinuousLinearMap.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…

--- 原说明 ---
Unbundled bounded linear functions are `C^n`.
-/
theorem IsBoundedLinearMap.contDiff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f :=
  (ContinuousLinearMap.analyticOnNhd hf.toContinuousLinearMap univ).contDiff

@[fun_prop]
/-
**ContinuousLinearMap.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.contDiff (f : E ->L[𝕜] F) : ContDiff 𝕜 n f
参数：f : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.contDiff`：IsBoundedLinearMap.contDiff (hf : IsBounded
LinearMap 𝕜 f) : ContDiff 𝕜 n f
· 使用定理 `ContinuousLinearMap.isBoundedLinearMap`：ContinuousLinearMap.isBoundedLin
earMap (f : E ->L[𝕜] F) : IsBoundedLinearMap 𝕜 f
-/
theorem ContinuousLinearMap.contDiff (f : E →L[𝕜] F) : ContDiff 𝕜 n f :=
  f.isBoundedLinearMap.contDiff

@[fun_prop]
/-
**ContinuousLinearEquiv.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.contDiff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f
参数：f : E ≃L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
-/
theorem ContinuousLinearEquiv.contDiff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff

@[fun_prop]
/-
**LinearIsometry.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.contDiff (f : E ->ₗᵢ[𝕜] F) : ContDiff 𝕜 n f
参数：f : E ->ₗᵢ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
-/
theorem LinearIsometry.contDiff (f : E →ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousLinearMap.contDiff

@[fun_prop]
/-
**LinearIsometryEquiv.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f
参数：f : E ≃ₗᵢ[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
-/
theorem LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E →L[𝕜] F).contDiff

/-- The identity is `C^n`. -/
@[to_fun (attr := fun_prop) contDiff_fun_id]
/-
**contDiff_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_id : ContDiff 𝕜 n (id : E -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.contDiff`：IsBoundedLinearMap.contDiff (hf : IsBounded
LinearMap 𝕜 f) : ContDiff 𝕜 n f
· 使用定理 `IsBoundedLinearMap.id`：id : IsBoundedLinearMap 𝕜 fun x : E => x

--- 原说明 ---
The identity is `C^n`.
-/
theorem contDiff_id : ContDiff 𝕜 n (id : E → E) :=
  IsBoundedLinearMap.id.contDiff

@[to_fun (attr := fun_prop) contDiffWithinAt_fun_id]
/-
**contDiffWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (id : E -> E) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (id : E → E) s x :=
  contDiff_id.contDiffWithinAt

@[to_fun (attr := fun_prop) contDiffAt_fun_id]
/-
**contDiffAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E → E) x :=
  contDiff_id.contDiffAt

@[to_fun (attr := fun_prop) contDiffOn_fun_id]
/-
**contDiffOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
theorem contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E → E) s :=
  contDiff_id.contDiffOn

/-- Bilinear functions are `C^n`. -/
/-
**IsBoundedBilinearMap.contDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.contDiff (hb : IsBoundedBilinearMap 𝕜 b) : ContDiff 𝕜
 n b
参数：hb : IsBoundedBilinearMap 𝕜 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.contDiff`：AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f u
niv) : ContDiff 𝕜 n f
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
· 使用定理 `ContinuousLinearMap.analyticOnNhd_bilinear`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {F : Type u_…

--- 原说明 ---
Bilinear functions are `C^n`.
-/
theorem IsBoundedBilinearMap.contDiff (hb : IsBoundedBilinearMap 𝕜 b) : ContDiff 𝕜 n b :=
  (hb.toContinuousLinearMap.analyticOnNhd_bilinear _).contDiff

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
/-
**HasFTaylorSeriesUpToOn.continuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] 
G) (hf : HasFTaylorSeriesUpToOn n f p s) : HasFTaylorSeriesUpToOn n (g ∘ f) (fun
 x k => g.compContinuousMultilinearMap (p x k)) s where zero_eq x hx
参数：g : F ->L[𝕜] G；hf : HasFTaylorSeriesUpToOn n f p s。
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […

--- 原说明 ---
If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` 
admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`.
-/
theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp {n : ℕ∞ω} (g : F →L[𝕜] G)
    (hf : HasFTaylorSeriesUpToOn n f p s) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x k => g.compContinuousMultilinearMap (p x k)) s where
  zero_eq x hx := congr_arg g (hf.zero_eq x hx)
  fderivWithin m hm x hx := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
  cont m hm := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).continuous.comp_continuousOn (hf.cont m hm)

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
/-
**ContDiffWithinAt.continuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.continuousLinearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffW
ithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x
参数：g : F ->L[𝕜] G；hf : ContDiffWithinAt 𝕜 n f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`：HasFTaylorSeriesUpToOn.
continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] G) (hf : HasFTaylorSeriesUpTo
On n f p s) : HasFTaylorSeriesUpToOn …
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
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
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousLinearMap.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
Composition by continuous linear maps on the left preserves `C^n` functions in a
 domain
at a point.
-/
theorem ContDiffWithinAt.continuousLinearMap_comp (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨u, hu, _, hp.continuousLinearMap_comp g, fun i ↦ ?_⟩
    change AnalyticOn 𝕜
      (fun x ↦ (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
      (fun _ : Fin i ↦ E) F G g) (p x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (h'p i) (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    exact ⟨u, hu, _, hp.continuousLinearMap_comp g⟩

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
/-
**ContDiffAt.continuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.continuousLinearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n 
f x) : ContDiffAt 𝕜 n (g ∘ f) x
参数：g : F ->L[𝕜] G；hf : ContDiffAt 𝕜 n f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousLinearMap_comp`：ContDiffWithinAt.continuousLi
nearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithin
At 𝕜 n (g ∘ f) s x

--- 原说明 ---
Composition by continuous linear maps on the left preserves `C^n` functions in a
 domain
at a point.
-/
theorem ContDiffAt.continuousLinearMap_comp (g : F →L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  ContDiffWithinAt.continuousLinearMap_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
/-
**ContDiffOn.continuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousLinearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffOn 𝕜 n 
f s) : ContDiffOn 𝕜 n (g ∘ f) s
参数：g : F ->L[𝕜] G；hf : ContDiffOn 𝕜 n f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.continuousLinearMap_comp`：ContDiffWithinAt.continuousLi
nearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithin
At 𝕜 n (g ∘ f) s x

--- 原说明 ---
Composition by continuous linear maps on the left preserves `C^n` functions on d
omains.
-/
theorem ContDiffOn.continuousLinearMap_comp (g : F →L[𝕜] G) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (g ∘ f) s := fun x hx => (hf x hx).continuousLinearMap_comp g

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
/-
**ContDiff.continuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuousLinearMap_comp {f : E -> F} (g : F ->L[𝕜] G) (hf : Cont
Diff 𝕜 n f) : ContDiff 𝕜 n fun x => g (f x)
参数：g : F ->L[𝕜] G；hf : ContDiff 𝕜 n f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.continuousLinearMap_comp`：ContDiffOn.continuousLinearMap_comp
 (g : F ->L[𝕜] G) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Composition by continuous linear maps on the left preserves `C^n` functions.
-/
theorem ContDiff.continuousLinearMap_comp {f : E → F} (g : F →L[𝕜] G) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun x => g (f x) :=
  contDiffOn_univ.1 <| ContDiffOn.continuousLinearMap_comp _ (contDiffOn_univ.2 hf)

/-- The iterated derivative within a set of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
/-
**ContinuousLinearMap.iteratedFDerivWithin_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ContinuousLinearMap.iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L
[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {
i : Nat} (hi : i <= n) : iteratedFDerivWithin 𝕜 i (g ∘ f) s x = g.compContinuous
MultilinearMap (iteratedFDerivWithin 𝕜 i f s x)
参数：g : F ->L[𝕜] G；hf : ContDiffWithinAt 𝕜 n f s x；hs : UniqueDiffOn 𝕜 s；hx : x i
n s；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.contDiffOn'`：ContDiffWithinAt.contDiffOn' (hm : m <= n)
 (h' : m = ∞ -> n = ω) (h : ContDiffWithinAt 𝕜 n f s x) : exists u, IsOpen u ∧ x
 in u ∧ ContDiffOn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_inter_open`：iteratedFDerivWithin_inter_open {n : Na
t} (hu : IsOpen u) (hx : x in u) : iteratedFDerivWithin 𝕜 n f (s inter u) x = it
eratedFDerivWithin 𝕜 …
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`：HasFTaylorSeriesUpToOn.
continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] G) (hf : HasFTaylorSeriesUpTo
On n f p s) : HasFTaylorSeriesUpToOn …
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `UniqueDiffOn.inter`：UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsO
pen t) : UniqueDiffOn 𝕜 (s inter t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The iterated derivative within a set of the composition with a linear map on the
 left is
obtained by applying the linear map to the iterated derivative.
-/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, hxU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU hxU, ← iteratedFDerivWithin_inter_open (f := f) hU hxU]
  rw [insert_eq_of_mem hx] at hfU
  exact .symm <| (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
    |>.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨hx, hxU⟩

/-- The iterated derivative of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative. -/
/-
**ContinuousLinearMap.iteratedFDeriv_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.iteratedFDeriv_comp_left {f : E -> F} (g : F ->L[𝕜] G)
 (hf : ContDiffAt 𝕜 n f x) {i : Nat} (hi : i <= n) : iteratedFDeriv 𝕜 i (g ∘ f) 
x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x)
参数：g : F ->L[𝕜] G；hf : ContDiffAt 𝕜 n f x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`：ContinuousLinearMap.
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffWithi
nAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The iterated derivative of the composition with a linear map on the left is
obtained by applying the linear map to the iterated derivative.
-/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left {f : E → F} (g : F →L[𝕜] G)
    (hf : ContDiffAt 𝕜 n f x) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

/-- The iterated derivative within a set of the composition with a linear equiv on the left is
obtained by applying the linear equiv to the iterated derivative. This is true without
differentiability assumptions. -/
/-
**ContinuousLinearEquiv.iteratedFDerivWithin_comp_left** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : 
E -> F) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (i : Nat) : iteratedFDerivWithin 𝕜
 i (g ∘ f) s x = (g : F ->L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWi
thin 𝕜 i f s x)
参数：g : F ≃L[𝕜] G；f : E -> F；hs : UniqueDiffOn 𝕜 s；hx : x in s；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iteratedFDerivWithin_succ_apply_left`：iteratedFDerivWithin_succ_apply_le
ft {n : Nat} (m : Fin (n + 1) -> E) : (iteratedFDerivWithin 𝕜 (n + 1) f s x : (F
in (n + 1) -> E) -> F) m =…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_congr'`：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s
) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} 
{s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) 
s x = (iso : E ->L[𝕜] F).comp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The iterated derivative within a set of the composition with a linear equiv on t
he left is
obtained by applying the linear equiv to the iterated derivative. This is true w
ithout
differentiability assumptions.
-/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe]
  | succ i IH =>
    rw [iteratedFDerivWithin_succ_apply_left]
    have Z : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (g ∘ f) s) s x =
        fderivWithin 𝕜 (g.continuousMultilinearMapCongrRight (fun _ : Fin i => E) ∘
          iteratedFDerivWithin 𝕜 i f s) s x :=
      fderivWithin_congr' (@IH) hx
    simp_rw [Z]
    rw [(g.continuousMultilinearMapCongrRight fun _ : Fin i => E).comp_fderivWithin (hs x hx)]
    simp [iteratedFDerivWithin_succ_apply_left]

/-- Iterated derivatives commute with left composition by continuous linear equivalences. -/
/-
**ContinuousLinearEquiv.iteratedFDeriv_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.iteratedFDeriv_comp_left {f : E -> F} {x : E} (g : F
 ≃L[𝕜] G) {i : Nat} : iteratedFDeriv 𝕜 i (g ∘ f) x = g.toContinuousLinearMap.com
pContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x)
参数：g : F ≃L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`：ContinuousLinearEq
uiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E -> F) (hs : UniqueDiff
On 𝕜 s) (hx : x in s) (i : Nat) : iterated…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `trivial`：True

--- 原说明 ---
Iterated derivatives commute with left composition by continuous linear equivale
nces.
-/
theorem ContinuousLinearEquiv.iteratedFDeriv_comp_left {f : E → F} {x : E} (g : F ≃L[𝕜] G) {i : ℕ} :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.iteratedFDerivWithin_comp_left f uniqueDiffOn_univ trivial

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative within a set. -/
/-
**LinearIsometry.norm_iteratedFDerivWithin_comp_left** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：LinearIsometry.norm_iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->ₗ
ᵢ[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) 
{i : Nat} (hi : i <= n) : ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDer
ivWithin 𝕜 i f s x‖
参数：g : F ->ₗᵢ[𝕜] G；hf : ContDiffWithinAt 𝕜 n f s x；hs : UniqueDiffOn 𝕜 s；hx : x 
in s；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`：ContinuousLinearMap.
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffWithi
nAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometry.norm_compContinuousMultilinearMap`：LinearIsometry.norm_co
mpContinuousMultilinearMap (g : G ->ₗᵢ[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E 
G) : ‖g.toContinuousLinearMap.compCont…

--- 原说明 ---
Composition with a linear isometry on the left preserves the norm of the iterate
d
derivative within a set.
-/
theorem LinearIsometry.norm_iteratedFDerivWithin_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearMap.iteratedFDerivWithin_comp_left hf hs hx hi
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap

/-- Composition with a linear isometry on the left preserves the norm of the iterated
derivative. -/
/-
**LinearIsometry.norm_iteratedFDeriv_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.norm_iteratedFDeriv_comp_left {f : E -> F} (g : F ->ₗᵢ[𝕜] G
) (hf : ContDiffAt 𝕜 n f x) {i : Nat} (hi : i <= n) : ‖iteratedFDeriv 𝕜 i (g ∘ f
) x‖ = ‖iteratedFDeriv 𝕜 i f x‖
参数：g : F ->ₗᵢ[𝕜] G；hf : ContDiffAt 𝕜 n f x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearIsometry.norm_iteratedFDerivWithin_comp_left`：LinearIsometry.norm_
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->ₗᵢ[𝕜] G) (hf : ContDiffWith
inAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) …
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Composition with a linear isometry on the left preserves the norm of the iterate
d
derivative.
-/
theorem LinearIsometry.norm_iteratedFDeriv_comp_left {f : E → F} (g : F →ₗᵢ[𝕜] G)
    (hf : ContDiffAt 𝕜 n f x) {i : ℕ} (hi : i ≤ n) :
    ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative within a set. -/
/-
**LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (
f : E -> F) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (i : Nat) : ‖iteratedFDerivWit
hin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖
参数：g : F ≃ₗᵢ[𝕜] G；f : E -> F；hs : UniqueDiffOn 𝕜 s；hx : x in s；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`：ContinuousLinearEq
uiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E -> F) (hs : UniqueDiff
On 𝕜 s) (hx : x in s) (i : Nat) : iterated…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometry.norm_compContinuousMultilinearMap`：LinearIsometry.norm_co
mpContinuousMultilinearMap (g : G ->ₗᵢ[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E 
G) : ‖g.toContinuousLinearMap.compCont…

--- 原说明 ---
Composition with a linear isometry equiv on the left preserves the norm of the i
terated
derivative within a set.
-/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (i : ℕ) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F →L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_left f hs hx i
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap g.toLinearIsometry

/-- Composition with a linear isometry equiv on the left preserves the norm of the iterated
derivative. -/
/-
**LinearIsometryEquiv.norm_iteratedFDeriv_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E 
-> F) (x : E) (i : Nat) : ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f
 x‖
参数：g : F ≃ₗᵢ[𝕜] G；f : E -> F；x : E；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
· 使用定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left`：LinearIsometryE
quiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E -> F) (hs : Uni
queDiffOn 𝕜 s) (hx : x in s) (i : Nat) : ‖ite…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Composition with a linear isometry equiv on the left preserves the norm of the i
terated
derivative.
-/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E → F) (x : E)
    (i : ℕ) : ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_left f uniqueDiffOn_univ (mem_univ x) i

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point in a domain. -/
/-
**ContinuousLinearEquiv.comp_contDiffWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.comp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) : ContDiff
WithinAt 𝕜 n (e ∘ f) s x ↔ ContDiffWithinAt 𝕜 n f s x
参数：e : F ≃L[𝕜] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `ContDiffWithinAt.continuousLinearMap_comp`：ContDiffWithinAt.continuousLi
nearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithin
At 𝕜 n (g ∘ f) s x

--- 原说明 ---
Composition by continuous linear equivs on the left respects higher differentiab
ility at a
point in a domain.
-/
theorem ContinuousLinearEquiv.comp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) :
    ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => by
    simpa only [Function.comp_def, e.symm.coe_coe, e.symm_apply_apply] using
      H.continuousLinearMap_comp (e.symm : G →L[𝕜] F),
    fun H => H.continuousLinearMap_comp (e : F →L[𝕜] G)⟩

/-- Composition by continuous linear equivs on the left respects higher differentiability at a
point. -/
/-
**ContinuousLinearEquiv.comp_contDiffAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.comp_contDiffAt_iff (e : F ≃L[𝕜] G) : ContDiffAt 𝕜 n
 (e ∘ f) x ↔ ContDiffAt 𝕜 n f x
参数：e : F ≃L[𝕜] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.comp_contDiffWithinAt_iff`：ContinuousLinearEquiv.c
omp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) : ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ Co
ntDiffWithinAt 𝕜 n f s x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Composition by continuous linear equivs on the left respects higher differentiab
ility at a
point.
-/
theorem ContinuousLinearEquiv.comp_contDiffAt_iff (e : F ≃L[𝕜] G) :
    ContDiffAt 𝕜 n (e ∘ f) x ↔ ContDiffAt 𝕜 n f x := by
  simp only [← contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff]

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
/-
**ContinuousLinearEquiv.comp_contDiffOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.comp_contDiffOn_iff (e : F ≃L[𝕜] G) : ContDiffOn 𝕜 n
 (e ∘ f) s ↔ ContDiffOn 𝕜 n f s
参数：e : F ≃L[𝕜] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ContinuousLinearEquiv.comp_contDiffWithinAt_iff`：ContinuousLinearEquiv.c
omp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) : ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ Co
ntDiffWithinAt 𝕜 n f s x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Composition by continuous linear equivs on the left respects higher differentiab
ility on
domains.
-/
theorem ContinuousLinearEquiv.comp_contDiffOn_iff (e : F ≃L[𝕜] G) :
    ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s := by
  simp [ContDiffOn, e.comp_contDiffWithinAt_iff]

/-- Composition by continuous linear equivs on the left respects higher differentiability. -/
/-
**ContinuousLinearEquiv.comp_contDiff_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.comp_contDiff_iff (e : F ≃L[𝕜] G) : ContDiff 𝕜 n (e 
∘ f) ↔ ContDiff 𝕜 n f
参数：e : F ≃L[𝕜] G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.comp_contDiffOn_iff`：ContinuousLinearEquiv.comp_co
ntDiffOn_iff (e : F ≃L[𝕜] G) : ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Composition by continuous linear equivs on the left respects higher differentiab
ility.
-/
theorem ContinuousLinearEquiv.comp_contDiff_iff (e : F ≃L[𝕜] G) :
    ContDiff 𝕜 n (e ∘ f) ↔ ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, e.comp_contDiffOn_iff]

set_option backward.isDefEq.respectTransparency false in
/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is affine, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term at `x` is given
by `p (g x) k (g.contLinear v₁, ..., g.contLinear vₖ)` . -/
/-
**HasFTaylorSeriesUpToOn.comp_continuousAffineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.comp_continuousAffineMap (hf : HasFTaylorSeriesUpTo
On n f p s) (g : G ->ᴬ[𝕜] E) : HasFTaylorSeriesUpToOn n (f ∘ g) (fun x k => (p (
g x) k).compContinuousLinearMap fun _ => g.contLinear) (g ⁻¹' s)
参数：hf : HasFTaylorSeriesUpToOn n f p s；g : G ->ᴬ[𝕜] E。
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
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `isBoundedLinearMap_continuousMultilinearMap_comp_linear`：isBoundedLinear
Map_continuousMultilinearMap_comp_linear (g : G ->L[𝕜] E) : IsBoundedLinearMap 𝕜
 fun f : ContinuousMultilinearMap 𝕜 (fun _ : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `Fin.comp_cons`：comp_cons {α : Sort*} {β : Sort*} (g : α -> β) (y : α) (q
 : Fin n -> α) : g ∘ cons y q = cons (g y) (g ∘ q)
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `IsBoundedLinearMap.hasFDerivAt`：hasFDerivAt (h : IsBoundedLinearMap 𝕜 f)
 : HasFDerivAt f h.toContinuousLinearMap x
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `ContinuousAffineMap.hasFDerivWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `IsBoundedLinearMap.continuous`：continuous (hf : IsBoundedLinearMap 𝕜 f) 
: Continuous f
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` admits a Taylor series `p` in a set `s`, and `g` is affine, then `f ∘ g` 
admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term at `x` is given
by `p (g x) k (g.contLinear v₁, ..., g.contLinear vₖ)` .
-/
theorem HasFTaylorSeriesUpToOn.comp_continuousAffineMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G →ᴬ[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g)
      (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g.contLinear) (g ⁻¹' s) := by
  let A : ∀ m : ℕ, (E [×m]→L[𝕜] F) → G [×m]→L[𝕜] F :=
    fun m h ↦ h.compContinuousLinearMap fun _ ↦ g.contLinear
  have hA : ∀ m, IsBoundedLinearMap 𝕜 (A m) := fun m =>
    isBoundedLinearMap_continuousMultilinearMap_comp_linear g.contLinear
  constructor
  · intro x hx
    simp only [(hf.zero_eq (g x) hx).symm, Function.comp_apply]
    change (p (g x) 0 fun _ : Fin 0 => g.contLinear 0) = p (g x) 0 0
    rw [map_zero]
    rfl
  · intro m hm x hx
    convert!
      (hA m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g.contLinear ∘ cons y v)
      = p (g x) m.succ (cons (g.contLinear y) (g.contLinear ∘ v))
    rw [comp_cons]
  · intro m hm
    exact (hA m).continuous.comp_continuousOn <| (hf.cont m hm).comp g.continuous.continuousOn <|
      Subset.refl _

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term at `x` is given by `p (g x) k (g v₁, ..., g vₖ)` . -/
/-
**HasFTaylorSeriesUpToOn.compContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.compContinuousLinearMap (hf : HasFTaylorSeriesUpToO
n n f p s) (g : G ->L[𝕜] E) : HasFTaylorSeriesUpToOn n (f ∘ g) (fun x k => (p (g
 x) k).compContinuousLinearMap fun _ => g) (g ⁻¹' s)
参数：hf : HasFTaylorSeriesUpToOn n f p s；g : G ->L[𝕜] E。
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
· 使用定理 `HasFTaylorSeriesUpToOn.comp_continuousAffineMap`：HasFTaylorSeriesUpToOn.
comp_continuousAffineMap (hf : HasFTaylorSeriesUpToOn n f p s) (g : G ->ᴬ[𝕜] E) 
: HasFTaylorSeriesUpToOn n (f ∘ g) (f…

--- 原说明 ---
If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` 
admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term at `x` is given by `p (g x) k (g v₁, ...,
 g vₖ)` .
-/
theorem HasFTaylorSeriesUpToOn.compContinuousLinearMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G →L[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g)
      (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g) (g ⁻¹' s) :=
  hf.comp_continuousAffineMap g.toContinuousAffineMap

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
/-
**ContDiffWithinAt.comp_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.comp_continuousLinearMap {x : G} (g : G ->L[𝕜] E) (hf : C
ontDiffWithinAt 𝕜 n f s (g x)) : ContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x
参数：g : G ->L[𝕜] E；hf : ContDiffWithinAt 𝕜 n f s (g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Set.MapsTo.union_union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∪ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_singleton`：mapsTo_singleton {x : α} : MapsTo f {x} t ↔ f x in
 t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `HasFTaylorSeriesUpToOn.compContinuousLinearMap`：HasFTaylorSeriesUpToOn.c
ompContinuousLinearMap (hf : HasFTaylorSeriesUpToOn n f p s) (g : G ->L[𝕜] E) : 
HasFTaylorSeriesUpToOn n (f ∘ g) (fu…
· 使用引理 `AnalyticOn.comp`：AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F} {
t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s
) : A…
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
· 使用定理 `ContinuousLinearMap.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
Composition by continuous linear maps on the right preserves `C^n` functions at 
a point on
a domain.
-/
theorem ContDiffWithinAt.comp_continuousLinearMap {x : G} (g : G →L[𝕜] E)
    (hf : ContDiffWithinAt 𝕜 n f s (g x)) : ContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g, ?_⟩
    · refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
      exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)
    · intro i
      change AnalyticOn 𝕜 (fun x ↦
        ContinuousMultilinearMap.compContinuousLinearMapL (fun _ ↦ g) (p (g x) i)) (⇑g ⁻¹' u)
      apply AnalyticOn.comp _ _ (Set.mapsTo_univ _ _)
      · exact ContinuousLinearMap.analyticOn _ _
      · exact (h'p i).comp (g.analyticOn _) (mapsTo_preimage _ _)
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g⟩
    refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
    exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
/-
**ContDiffOn.comp_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.comp_continuousLinearMap (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜
] E) : ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s)
参数：hf : ContDiffOn 𝕜 n f s；g : G ->L[𝕜] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.comp_continuousLinearMap`：ContDiffWithinAt.comp_continu
ousLinearMap {x : G} (g : G ->L[𝕜] E) (hf : ContDiffWithinAt 𝕜 n f s (g x)) : Co
ntDiffWithinAt 𝕜 n (f ∘ g) (g ⁻…

--- 原说明 ---
Composition by continuous linear maps on the right preserves `C^n` functions on 
domains.
-/
theorem ContDiffOn.comp_continuousLinearMap (hf : ContDiffOn 𝕜 n f s) (g : G →L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s) := fun x hx => (hf (g x) hx).comp_continuousLinearMap g

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
/-
**ContDiff.comp_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.comp_continuousLinearMap {f : E -> F} {g : G ->L[𝕜] E} (hf : Cont
Diff 𝕜 n f) : ContDiff 𝕜 n (f ∘ g)
参数：hf : ContDiff 𝕜 n f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.comp_continuousLinearMap`：ContDiffOn.comp_continuousLinearMap
 (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E) : ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Composition by continuous linear maps on the right preserves `C^n` functions.
-/
theorem ContDiff.comp_continuousLinearMap {f : E → F} {g : G →L[𝕜] E} (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (f ∘ g) :=
  contDiffOn_univ.1 <| ContDiffOn.comp_continuousLinearMap (contDiffOn_univ.2 hf) _

/-- The iterated derivative within a set of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
/-
**ContinuousLinearMap.iteratedFDerivWithin_comp_right** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：ContinuousLinearMap.iteratedFDerivWithin_comp_right {f : E -> F} (g : G ->
L[𝕜] E) (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (h's : UniqueDiffOn 𝕜 
(g ⁻¹' s)) {x : G} (hx : g x in s) {i : Nat} (hi : i <= n) : iteratedFDerivWithi
n 𝕜 i (f ∘ g) (g ⁻¹' s) x = (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousL
inearMap fun _ => g
参数：g : G ->L[𝕜] E；hf : ContDiffOn 𝕜 n f s；hs : UniqueDiffOn 𝕜 s；h's : UniqueDiff
On 𝕜 (g ⁻¹' s)；hx : g x in s；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`：HasFTayl
orSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn (h : HasFTaylorSeriesUpTo
On n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDif…
· 使用定理 `HasFTaylorSeriesUpToOn.compContinuousLinearMap`：HasFTaylorSeriesUpToOn.c
ompContinuousLinearMap (hf : HasFTaylorSeriesUpToOn n f p s) (g : G ->L[𝕜] E) : 
HasFTaylorSeriesUpToOn n (f ∘ g) (fu…
· 使用定理 `ContDiffOn.ftaylorSeriesWithin`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `ContDiffOn.of_le`：ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= 
n) : ContDiffOn 𝕜 m f s
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The iterated derivative within a set of the composition with a linear map on the
 right is
obtained by composing the iterated derivative with the linear map.
-/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_right {f : E → F} (g : G →L[𝕜] E)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (h's : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G}
    (hx : g x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
  ((((hf.of_le hi).ftaylorSeriesWithin hs).compContinuousLinearMap
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl h's hx).symm

/-- The iterated derivative within a set of the composition with a linear equiv on the right is
obtained by composing the iterated derivative with the linear equiv. -/
/-
**ContinuousLinearEquiv.iteratedFDerivWithin_comp_right** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (g : G ≃L[𝕜] E) (f :
 E -> F) (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : Nat) : iteratedFDe
rivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x = (iteratedFDerivWithin 𝕜 i f s (g x)).compCon
tinuousLinearMap fun _ => g
参数：g : G ≃L[𝕜] E；f : E -> F；hs : UniqueDiffOn 𝕜 s；hx : g x in s；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_congr'`：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s
) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} 
{s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) 
s x = (iso : E ->L[𝕜] F).comp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.uniqueDiffOn_preimage_iff`：ContinuousLinearEquiv.u
niqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) : UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiff
On 𝕜 s
· 使用定理 `ContinuousLinearEquiv.comp_right_fderivWithin`：comp_right_fderivWithin {
f : F -> G} {s : Set F} {x : E} (hxs : UniqueDiffWithinAt 𝕜 (iso ⁻¹' s) x) : fde
rivWithin 𝕜 (f ∘ iso) (iso ⁻¹' s) x…
· 使用定理 `ContinuousLinearMap.comp_apply`：comp_apply (g : M₂ ->SL[σ₂₃] M₃) (f : M₁
 ->SL[σ₁₂] M₂) (x : M₁) : (g ∘SL f) x = g (f x)
· 使用定理 `ContinuousLinearEquiv.coe_coe`：coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ -
>SL[σ₁₂] M₂) = e
· 使用定理 `Fin.tail_def`：tail_def {n : Nat} {α : Fin (n + 1) -> Sort*} {q : forall 
i, α i} : (tail fun k : Fin (n + 1) => q k) = fun k : Fin n => q k.succ

--- 原说明 ---
The iterated derivative within a set of the composition with a linear equiv on t
he right is
obtained by composing the iterated derivative with the linear equiv.
-/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (g : G ≃L[𝕜] E) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g := by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  | succ i IH =>
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, iteratedFDerivWithin_succ_apply_left]
    have : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s)) (g ⁻¹' s) x =
        fderivWithin 𝕜
          (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _ (fun _x : Fin i => g) ∘
            (iteratedFDerivWithin 𝕜 i f s ∘ g)) (g ⁻¹' s) x :=
      fderivWithin_congr' (@IH) hx
    rw [this, ContinuousLinearEquiv.comp_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousLinearEquiv.comp_right_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx),
      ContinuousLinearMap.comp_apply, coe_coe, tail_def, tail_def]

/-- The iterated derivative of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map. -/
/-
**ContinuousLinearMap.iteratedFDeriv_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.iteratedFDeriv_comp_right (g : G ->L[𝕜] E) {f : E -> F
} (hf : ContDiff 𝕜 n f) (x : G) {i : Nat} (hi : i <= n) : iteratedFDeriv 𝕜 i (f 
∘ g) x = (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g
参数：g : G ->L[𝕜] E；hf : ContDiff 𝕜 n f；x : G；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_right`：ContinuousLinearMap
.iteratedFDerivWithin_comp_right {f : E -> F} (g : G ->L[𝕜] E) (hf : ContDiffOn 
𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (h's : U…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The iterated derivative of the composition with a linear map on the right is
obtained by composing the iterated derivative with the linear map.
-/
theorem ContinuousLinearMap.iteratedFDeriv_comp_right (g : G →L[𝕜] E) {f : E → F}
    (hf : ContDiff 𝕜 n f) (x : G) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (f ∘ g) x =
      (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ uniqueDiffOn_univ
      (mem_univ _) hi

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
/-
**LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) 
(f : E -> F) (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : Nat) : ‖iterat
edFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ = ‖iteratedFDerivWithin 𝕜 i f s (g x)‖
参数：g : G ≃ₗᵢ[𝕜] E；f : E -> F；hs : UniqueDiffOn 𝕜 s；hx : g x in s；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`：ContinuousLinearE
quiv.iteratedFDerivWithin_comp_right (g : G ≃L[𝕜] E) (f : E -> F) (hs : UniqueDi
ffOn 𝕜 s) {x : G} (hx : g x in s) (i : Nat)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv`：norm_c
ompContinuous_linearIsometryEquiv (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : for
all i, E i ≃ₗᵢ[𝕜] E₁ i) : ‖g.compContinuousLinearMap f…

--- 原说明 ---
Composition with a linear isometry on the right preserves the norm of the iterat
ed derivative
within a set.
-/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E → F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x ∈ s) (i : ℕ) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ = ‖iteratedFDerivWithin 𝕜 i f s (g x)‖ := by
  have : iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f hs hx i
  rw [this, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

/-- Composition with a linear isometry on the right preserves the norm of the iterated derivative
within a set. -/
/-
**LinearIsometryEquiv.norm_iteratedFDeriv_comp_right** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E
 -> F) (x : G) (i : Nat) : ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ = ‖iteratedFDeriv 𝕜 i 
f (g x)‖
参数：g : G ≃ₗᵢ[𝕜] E；f : E -> F；x : G；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right`：LinearIsometry
Equiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E -> F) (hs : U
niqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : …
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Composition with a linear isometry on the right preserves the norm of the iterat
ed derivative
within a set.
-/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E → F) (x : G)
    (i : ℕ) : ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ = ‖iteratedFDeriv 𝕜 i f (g x)‖ := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
/-
**ContinuousLinearEquiv.contDiffWithinAt_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.contDiffWithinAt_comp_iff (e : G ≃L[𝕜] E) : ContDiff
WithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f s x
参数：e : G ≃L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `ContDiffWithinAt.comp_continuousLinearMap`：ContDiffWithinAt.comp_continu
ousLinearMap {x : G} (g : G ->L[𝕜] E) (hf : ContDiffWithinAt 𝕜 n f s (g x)) : Co
ntDiffWithinAt 𝕜 n (f ∘ g) (g ⁻…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.coe_coe`：coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ -
>SL[σ₁₂] M₂) = e

--- 原说明 ---
Composition by continuous linear equivs on the right respects higher differentia
bility at a
point in a domain.
-/
theorem ContinuousLinearEquiv.contDiffWithinAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f s x := by
  constructor
  · intro H
    simpa [← preimage_comp, Function.comp_def] using H.comp_continuousLinearMap (e.symm : E →L[𝕜] G)
  · intro H
    rw [← e.apply_symm_apply x, ← e.coe_coe] at H
    exact H.comp_continuousLinearMap _

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point. -/
/-
**ContinuousLinearEquiv.contDiffAt_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.contDiffAt_comp_iff (e : G ≃L[𝕜] E) : ContDiffAt 𝕜 n
 (f ∘ e) (e.symm x) ↔ ContDiffAt 𝕜 n f x
参数：e : G ≃L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `ContinuousLinearEquiv.contDiffWithinAt_comp_iff`：ContinuousLinearEquiv.c
ontDiffWithinAt_comp_iff (e : G ≃L[𝕜] E) : ContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s
) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f…

--- 原说明 ---
Composition by continuous linear equivs on the right respects higher differentia
bility at a
point.
-/
theorem ContinuousLinearEquiv.contDiffAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffAt 𝕜 n (f ∘ e) (e.symm x) ↔ ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ, ← contDiffWithinAt_univ, ← preimage_univ]
  exact e.contDiffWithinAt_comp_iff

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
/-
**ContinuousLinearEquiv.contDiffOn_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.contDiffOn_comp_iff (e : G ≃L[𝕜] E) : ContDiffOn 𝕜 n
 (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n f s
参数：e : G ≃L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `ContinuousLinearEquiv.symm_preimage_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `ContDiffOn.comp_continuousLinearMap`：ContDiffOn.comp_continuousLinearMap
 (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E) : ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s)

--- 原说明 ---
Composition by continuous linear equivs on the right respects higher differentia
bility on
domains.
-/
theorem ContinuousLinearEquiv.contDiffOn_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => by simpa [Function.comp_def] using H.comp_continuousLinearMap (e.symm : E →L[𝕜] G),
    fun H => H.comp_continuousLinearMap (e : G →L[𝕜] E)⟩

/-- Composition by continuous linear equivs on the right respects higher differentiability. -/
/-
**ContinuousLinearEquiv.contDiff_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.contDiff_comp_iff (e : G ≃L[𝕜] E) : ContDiff 𝕜 n (f 
∘ e) ↔ ContDiff 𝕜 n f
参数：e : G ≃L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `ContinuousLinearEquiv.contDiffOn_comp_iff`：ContinuousLinearEquiv.contDif
fOn_comp_iff (e : G ≃L[𝕜] E) : ContDiffOn 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n
 f s

--- 原说明 ---
Composition by continuous linear equivs on the right respects higher differentia
bility.
-/
theorem ContinuousLinearEquiv.contDiff_comp_iff (e : G ≃L[𝕜] E) :
    ContDiff 𝕜 n (f ∘ e) ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← contDiffOn_univ, ← preimage_univ]
  exact e.contDiffOn_comp_iff

end linear

/-! ### The Cartesian product of two C^n functions is C^n. -/
section prod

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the Cartesian
product of `f` and `g` admits the Cartesian product of `p` and `q` as a Taylor series. -/
/-
**HasFTaylorSeriesUpToOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.prodMk {n : Nat∞ω} (hf : HasFTaylorSeriesUpToOn n f
 p s) {g : E -> G} {q : E -> FormalMultilinearSeries 𝕜 E G} (hg : HasFTaylorSeri
esUpToOn n g q s) : HasFTaylorSeriesUpToOn n (fun y => (f y, g y)) (fun y k => (
p y k).prod (q y k)) s
参数：hf : HasFTaylorSeriesUpToOn n f p s；hg : HasFTaylorSeriesUpToOn n g q s。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type uF} […
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `LinearIsometryEquiv.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type u_…
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `LinearIsometryEquiv.continuous`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Ty
pe u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+
* R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `HasFTaylorSeriesUpToOn.cont`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type uF} […

--- 原说明 ---
If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then 
the Cartesian
product of `f` and `g` admits the Cartesian product of `p` and `q` as a Taylor s
eries.
-/
theorem HasFTaylorSeriesUpToOn.prodMk {n : ℕ∞ω}
    (hf : HasFTaylorSeriesUpToOn n f p s) {g : E → G}
    {q : E → FormalMultilinearSeries 𝕜 E G} (hg : HasFTaylorSeriesUpToOn n g q s) :
    HasFTaylorSeriesUpToOn n (fun y => (f y, g y)) (fun y k => (p y k).prod (q y k)) s := by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m => E) F G
  constructor
  · intro x hx; rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]; rfl
  · intro m hm x hx
    convert!
      (L m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm x hx).prodMk (hg.fderivWithin m hm x hx))
  · intro m hm
    exact (L m).continuous.comp_continuousOn ((hf.cont m hm).prodMk (hg.cont m hm))

/-- The Cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
@[fun_prop]
/-
**ContDiffWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F} {g : E -> G} (hf : ContDi
ffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) : ContDiffWithinAt 𝕜 n (
fun x : E => (f x, g x)) s x
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `HasFTaylorSeriesUpToOn.prodMk`：HasFTaylorSeriesUpToOn.prodMk {n : Nat∞ω}
 (hf : HasFTaylorSeriesUpToOn n f p s) {g : E -> G} {q : E -> FormalMultilinearS
eries 𝕜 E G} (hg : …
· 使用定理 `HasFTaylorSeriesUpToOn.mono`：HasFTaylorSeriesUpToOn.mono (h : HasFTaylor
SeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) : HasFTaylorSeriesUpToOn 
n f p t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用定理 `LinearIsometryEquiv.analyticOnNhd`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {F : Type u_…
· 使用引理 `AnalyticOn.prod`：AnalyticOn.prod {f : E -> F} {g : E -> G} {s : Set E} (
hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) : AnalyticOn 𝕜 (fun x => (f x, g 
x)) s
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
The Cartesian product of `C^n` functions at a point in a domain is `C^n`.
-/
theorem ContDiffWithinAt.prodMk {s : Set E} {f : E → F} {g : E → G}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x : E => (f x, g x)) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    refine ⟨u ∩ v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right), fun i ↦ ?_⟩
    change AnalyticOn 𝕜 (fun x ↦ ContinuousMultilinearMap.prodL _ _ _ _ (p x i, q x i)) (u ∩ v)
    apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn _ (Set.mapsTo_univ _ _)
    exact ((h'p i).mono inter_subset_left).prod ((h'q i).mono inter_subset_right)
  | (n : ℕ∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    exact ⟨u ∩ v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right)⟩

/-- The Cartesian product of `C^n` functions on domains is `C^n`. -/
@[fun_prop]
/-
**ContDiffOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> G} (hf : ContDiffOn 𝕜
 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s
参数：hf : ContDiffOn 𝕜 n f s；hg : ContDiffOn 𝕜 n g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…

--- 原说明 ---
The Cartesian product of `C^n` functions on domains is `C^n`.
-/
theorem ContDiffOn.prodMk {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

/-- The Cartesian product of `C^n` functions at a point is `C^n`. -/
@[fun_prop]
/-
**ContDiffAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x) (hg 
: ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x

--- 原说明 ---
The Cartesian product of `C^n` functions at a point is `C^n`.
-/
theorem ContDiffAt.prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x :=
  contDiffWithinAt_univ.1 <| hf.contDiffWithinAt.prodMk hg.contDiffWithinAt

/-- The Cartesian product of `C^n` functions is `C^n`. -/
@[fun_prop]
/-
**ContDiff.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDiff 𝕜 n f) (hg : Cont
Diff 𝕜 n g) : ContDiff 𝕜 n fun x : E => (f x, g x)
参数：hf : ContDiff 𝕜 n f；hg : ContDiff 𝕜 n g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用定理 `ContDiffOn.prodMk`：ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> 
G} (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x :
 E => (…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s

--- 原说明 ---
The Cartesian product of `C^n` functions is `C^n`.
-/
theorem ContDiff.prodMk {f : E → F} {g : E → G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x : E => (f x, g x) :=
  contDiffOn_univ.1 <| hf.contDiffOn.prodMk hg.contDiffOn
/-
**iteratedFDerivWithin_prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_prodMk {f : E -> F} {g : E -> G} (hf : ContDiffWithin
At 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) (hs : UniqueDiffOn 𝕜 s) (ha : x 
in s) {i : Nat} (hi : i <= n) : iteratedFDerivWithin 𝕜 i (fun x => (f x, g x)) s
 x = (iteratedFDerivWithin 𝕜 i f s x).prod (iteratedFDerivWithin 𝕜 i g s x)
参数：hf : ContDiffWithinAt 𝕜 n f s x；hg : ContDiffWithinAt 𝕜 n g s x；hs : UniqueDi
ffOn 𝕜 s；ha : x in s；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.prod_ext`：prod_ext {f g : ContinuousMultilinear
Map R M₁ (M₂ × M₃)} (h₁ : (ContinuousLinearMap.fst _ _ _).compContinuousMultilin
earMap f = (ContinuousL…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`：ContinuousLinearMap.
iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiffWithi
nAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (…
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousLinearMap.compContinuousMultilinearMap_coe`：∀ {R : Type u} {ι 
: Type v} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R]  
 [inst_1 : (i : ι) → AddCommMonoid (M₁ i)]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedFDerivWithin_prodMk {f : E → F} {g : E → G} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hs : UniqueDiffOn 𝕜 s) (ha : x ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (fun x ↦ (f x, g x)) s x =
      (iteratedFDerivWithin 𝕜 i f s x).prod (iteratedFDerivWithin 𝕜 i g s x) := by
  ext <;>
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]
/-
**iteratedFDeriv_prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_prodMk {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) {i : Nat} (hi : i <= n) : iteratedFDeriv 𝕜 i (fun x =>
 (f x, g x)) x = (iteratedFDeriv 𝕜 i f x).prod (iteratedFDeriv 𝕜 i g x)
参数：hf : ContDiffAt 𝕜 n f x；hg : ContDiffAt 𝕜 n g x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_prodMk`：iteratedFDerivWithin_prodMk {f : E -> F} {g
 : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) (
hs : UniqueDiffOn…
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem iteratedFDeriv_prodMk {f : E → F} {g : E → G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun x ↦ (f x, g x)) x =
      (iteratedFDeriv 𝕜 i f x).prod (iteratedFDeriv 𝕜 i g x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    (Set.mem_univ _) hi

end prod

/-! ### Being `C^k` on a union of open sets can be tested on each set -/
section contDiffOn_union

/-- If a function is `C^k` on two open sets, it is also `C^n` on their union. -/
/-
**ContDiffOn.union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiffOn.union_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hf' : ContDiffOn 𝕜 n
 f t) (hs : IsOpen s) (ht : IsOpen t) : ContDiffOn 𝕜 n f (s union t)
参数：hf : ContDiffOn 𝕜 n f s；hf' : ContDiffOn 𝕜 n f t；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiffWithinAt.contDiffAt`：ContDiffWithinAt.contDiffAt (h : ContDiffWi
thinAt 𝕜 n f s x) (hx : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is `C^k` on two open sets, it is also `C^n` on their union.
-/
lemma ContDiffOn.union_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    ContDiffOn 𝕜 n f (s ∪ t) := by
  rintro x (hx | hx)
  · exact (hf x hx).contDiffAt (hs.mem_nhds hx) |>.contDiffWithinAt
  · exact (hf' x hx).contDiffAt (ht.mem_nhds hx) |>.contDiffWithinAt

/-- A function is `C^k` on two open sets iff it is `C^k` on their union. -/
/-
**contDiffOn_union_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) : ContDiffO
n 𝕜 n f (s union t) ↔ ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 n f t
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `ContDiffOn.union_of_isOpen`：ContDiffOn.union_of_isOpen (hf : ContDiffOn 
𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t) (hs : IsOpen s) (ht : IsOpen t) : ContDiffOn
 𝕜 n f (s union …

--- 原说明 ---
A function is `C^k` on two open sets iff it is `C^k` on their union.
-/
lemma contDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    ContDiffOn 𝕜 n f (s ∪ t) ↔ ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 n f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ ↦ ContDiffOn.union_of_isOpen hfs hft hs ht⟩
/-
**contDiff_of_contDiffOn_union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiff_of_contDiffOn_union_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hf' : Co
ntDiffOn 𝕜 n f t) (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpen t) : Con
tDiff 𝕜 n f
参数：hf : ContDiffOn 𝕜 n f s；hf' : ContDiffOn 𝕜 n f t；hst : s union t = univ；hs : 
IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用引理 `ContDiffOn.union_of_isOpen`：ContDiffOn.union_of_isOpen (hf : ContDiffOn 
𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t) (hs : IsOpen s) (ht : IsOpen t) : ContDiffOn
 𝕜 n f (s union …
-/
lemma contDiff_of_contDiffOn_union_of_isOpen (hf : ContDiffOn 𝕜 n f s)
    (hf' : ContDiffOn 𝕜 n f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is `C^k` on open sets `s i`, it is `C^k` on their union -/
/-
**ContDiffOn.iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set E} (hf : forall i : 
ι, ContDiffOn 𝕜 n f (s i)) (hs : forall i, IsOpen (s i)) : ContDiffOn 𝕜 n f (⋃ i
, s i)
参数：hf : forall i : ι, ContDiffOn 𝕜 n f (s i)；hs : forall i, IsOpen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiffOn.contDiffAt`：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (h
x : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is `C^k` on open sets `s i`, it is `C^k` on their union
-/
lemma ContDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, ContDiffOn 𝕜 n f (s i)) (hs : ∀ i, IsOpen (s i)) :
    ContDiffOn 𝕜 n f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).contDiffAt ((hs i).mem_nhds hxsi) |>.contDiffWithinAt

/-- A function is `C^k` on a union of open sets `s i` iff it is `C^k` on each `s i`. -/
/-
**contDiffOn_iUnion_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set E} (hs : forall 
i, IsOpen (s i)) : ContDiffOn 𝕜 n f (⋃ i, s i) ↔ forall i : ι, ContDiffOn 𝕜 n f 
(s i)
参数：hs : forall i, IsOpen (s i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用引理 `ContDiffOn.iUnion_of_isOpen`：ContDiffOn.iUnion_of_isOpen {ι : Type*} {s 
: ι -> Set E} (hf : forall i : ι, ContDiffOn 𝕜 n f (s i)) (hs : forall i, IsOpen
 (s i)) : ContDif…

--- 原说明 ---
A function is `C^k` on a union of open sets `s i` iff it is `C^k` on each `s i`.
-/
lemma contDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set E}
    (hs : ∀ i, IsOpen (s i)) :
    ContDiffOn 𝕜 n f (⋃ i, s i) ↔ ∀ i : ι, ContDiffOn 𝕜 n f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ ContDiffOn.iUnion_of_isOpen h hs⟩
/-
**contDiff_of_contDiffOn_iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contDiff_of_contDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set E} (hf :
 forall i : ι, ContDiffOn 𝕜 n f (s i)) (hs : forall i, IsOpen (s i)) (hs' : ⋃ i,
 s i = univ) : ContDiff 𝕜 n f
参数：hf : forall i : ι, ContDiffOn 𝕜 n f (s i)；hs : forall i, IsOpen (s i)；hs' : ⋃
 i, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffOn_univ`：contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n 
f
· 使用引理 `ContDiffOn.iUnion_of_isOpen`：ContDiffOn.iUnion_of_isOpen {ι : Type*} {s 
: ι -> Set E} (hf : forall i : ι, ContDiffOn 𝕜 n f (s i)) (hs : forall i, IsOpen
 (s i)) : ContDif…
-/
lemma contDiff_of_contDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, ContDiffOn 𝕜 n f (s i)) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ, ← hs']
  exact ContDiffOn.iUnion_of_isOpen hf hs

end contDiffOn_union

/-- The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify your proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
/-
**contDiff_prodAssoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prodAssoc {n : Nat∞ω} : ContDiff 𝕜 n Equiv.prodAssoc E F G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f

--- 原说明 ---
The natural equivalence `(E × F) × G ≃ E × (F × G)` is smooth.

Warning: if you think you need this lemma, it is likely that you can simplify yo
ur proof by
reformulating the lemma that you're applying next using the tips in
Note [continuity lemma statement]
-/
theorem contDiff_prodAssoc {n : ℕ∞ω} : ContDiff 𝕜 n <| Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

/-- The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `contDiff_prodAssoc`
-/
/-
**contDiff_prodAssoc_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_prodAssoc_symm {n : Nat∞ω} : ContDiff 𝕜 n (Equiv.prodAssoc E F G)
.symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f

--- 原说明 ---
The natural equivalence `E × (F × G) ≃ (E × F) × G` is smooth.

Warning: see remarks attached to `contDiff_prodAssoc`
-/
theorem contDiff_prodAssoc_symm {n : ℕ∞ω} : ContDiff 𝕜 n <| (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff
