/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives of functions taking values in product types

In this file we prove lemmas about derivatives of functions `f : 𝕜 → E × F` and of functions
`f : 𝕜 → (Π i, E i)`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative
-/

public section

universe u v w

open Topology Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f₁ : 𝕜 → F} {f₁' : F} {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/


variable {G : Type w} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {f₂ : 𝕜 → G} {f₂' : G}

/-
**HasDerivAtFilter.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter f₁ f₁' L) (hf₂ : HasDerivA
tFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') L
参数：hf₁ : HasDerivAtFilter f₁ f₁' L；hf₂ : HasDerivAtFilter f₂ f₂' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasFDerivAtFilter.prodMk`：HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFil
ter f₁ f₁' L) (hf₂ : HasFDerivAtFilter f₂ f₂' L) : HasFDerivAtFilter (fun x => (
f₁ x, f₂ x)) (…
-/
theorem HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter f₁ f₁' L)
    (hf₂ : HasDerivAtFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁', f₂') L :=
  HasFDerivAtFilter.prodMk hf₁ hf₂
/-
**HasDerivWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.prodMk (hf₁ : HasDerivWithinAt f₁ f₁' s x) (hf₂ : HasDeri
vWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x
参数：hf₁ : HasDerivWithinAt f₁ f₁' s x；hf₂ : HasDerivWithinAt f₂ f₂' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.prodMk`：HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter
 f₁ f₁' L) (hf₂ : HasDerivAtFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x,
 f₂ x)) (f₁',…
-/
theorem HasDerivWithinAt.prodMk (hf₁ : HasDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasDerivWithinAt f₂ f₂' s x) : HasDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') s x :=
  HasDerivAtFilter.prodMk hf₁ hf₂
/-
**HasDerivAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) 
: HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x
参数：hf₁ : HasDerivAt f₁ f₁' x；hf₂ : HasDerivAt f₂ f₂' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.prodMk`：HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter
 f₁ f₁' L) (hf₂ : HasDerivAtFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x,
 f₂ x)) (f₁',…
-/
theorem HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
    HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  HasDerivAtFilter.prodMk hf₁ hf₂
/-
**HasStrictDerivAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt f₁ f₁' x) (hf₂ : HasStrict
DerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x
参数：hf₁ : HasStrictDerivAt f₁ f₁' x；hf₂ : HasStrictDerivAt f₂ f₂' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAtFilter.prodMk`：HasDerivAtFilter.prodMk (hf₁ : HasDerivAtFilter
 f₁ f₁' L) (hf₂ : HasDerivAtFilter f₂ f₂' L) : HasDerivAtFilter (fun x => (f₁ x,
 f₂ x)) (f₁',…
-/
theorem HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt f₁ f₁' x)
    (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x :=
  HasDerivAtFilter.prodMk hf₁ hf₂

end CartesianProduct

section Pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variable {ι : Type*} {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
  [∀ i, NormedSpace 𝕜 (E' i)] {φ : 𝕜 → ∀ i, E' i} {φ' : ∀ i, E' i}

@[simp]
/-
**hasDerivAtFilter_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_pi : HasDerivAtFilter φ φ' L ↔ forall i, HasDerivAtFilter
 (fun x => φ x i) (φ' i) L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_pi'`：hasFDerivAtFilter_pi' : HasFDerivAtFilter Φ Φ' L 
↔ forall i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') L
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_pi :
    HasDerivAtFilter φ φ' L ↔ ∀ i, HasDerivAtFilter (fun x => φ x i) (φ' i) L :=
  hasFDerivAtFilter_pi'

@[simp]
/-
**hasStrictDerivAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_pi : HasStrictDerivAt φ φ' x ↔ forall i, HasStrictDerivAt
 (fun x => φ x i) (φ' i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_pi`：hasDerivAtFilter_pi : HasDerivAtFilter φ φ' L ↔ for
all i, HasDerivAtFilter (fun x => φ x i) (φ' i) L
-/
theorem hasStrictDerivAt_pi :
    HasStrictDerivAt φ φ' x ↔ ∀ i, HasStrictDerivAt (fun x => φ x i) (φ' i) x :=
  hasDerivAtFilter_pi
/-
**hasDerivAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_pi : HasDerivAt φ φ' x ↔ forall i, HasDerivAt (fun x => φ x i) 
(φ' i) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_pi`：hasDerivAtFilter_pi : HasDerivAtFilter φ φ' L ↔ for
all i, HasDerivAtFilter (fun x => φ x i) (φ' i) L
-/
theorem hasDerivAt_pi : HasDerivAt φ φ' x ↔ ∀ i, HasDerivAt (fun x => φ x i) (φ' i) x :=
  hasDerivAtFilter_pi
/-
**hasDerivWithinAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_pi : HasDerivWithinAt φ φ' s x ↔ forall i, HasDerivWithin
At (fun x => φ x i) (φ' i) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasDerivAtFilter_pi`：hasDerivAtFilter_pi : HasDerivAtFilter φ φ' L ↔ for
all i, HasDerivAtFilter (fun x => φ x i) (φ' i) L
-/
theorem hasDerivWithinAt_pi :
    HasDerivWithinAt φ φ' s x ↔ ∀ i, HasDerivWithinAt (fun x => φ x i) (φ' i) s x :=
  hasDerivAtFilter_pi
/-
**derivWithin_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_pi (h : forall i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s 
x) : derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x
参数：h : forall i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin.eq_1`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F :
 Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 : Topo
logica…
· 使用定理 `fderivWithin_pi`：fderivWithin_pi (h : forall i, DifferentiableWithinAt 𝕜
 (φ i) s x) (hs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fun x i => φ i x) 
s x =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fderivWithin_zero_of_not_accPt`：fderivWithin_zero_of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : fderivWithin 𝕜 f s x = 0
· 使用定理 `uniqueDiffWithinAt_iff_accPt`：uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {
x : 𝕜} : UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s)
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem derivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (fun x => φ x i) s x) :
    derivWithin φ s x = fun i => derivWithin (fun x => φ x i) s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · rw [derivWithin, fderivWithin_pi h hsx]
    simp [derivWithin]
    -- TODO: restore exact (hasDerivWithinAt_pi.2 fun i => (h i).hasDerivWithinAt).derivWithin hsx
  · rw [uniqueDiffWithinAt_iff_accPt] at hsx
    simp [derivWithin, fderivWithin_zero_of_not_accPt hsx, Pi.zero_def]
    -- TODO: restore simp only [derivWithin_zero_of_not_uniqueDiffWithinAt hsx, Pi.zero_def]
/-
**deriv_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_pi (h : forall i, DifferentiableAt 𝕜 (fun x => φ x i) x) : deriv φ x
 = fun i => deriv (fun x => φ x i) x
参数：h : forall i, DifferentiableAt 𝕜 (fun x => φ x i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderiv_pi`：fderiv_pi (h : forall i, DifferentiableAt 𝕜 (φ i) x) : fderiv
 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `fderiv_eq_smul_deriv`：fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -
> F) y = y • deriv f x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_pi (h : ∀ i, DifferentiableAt 𝕜 (fun x => φ x i) x) :
    deriv φ x = fun i => deriv (fun x => φ x i) x := by
  -- TODO: restore (hasDerivAt_pi.2 fun i => (h i).hasDerivAt).deriv
  simp only [deriv, fderiv_pi h]
  simp

end Pi


/-!
### Derivatives of tuples `f : 𝕜 → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
-/
section PiFin

variable {n : Nat} {F' : Fin n.succ → Type*}
variable [∀ i, NormedAddCommGroup (F' i)] [∀ i, NormedSpace 𝕜 (F' i)]
variable {φ : 𝕜 → F' 0} {φs : 𝕜 → ∀ i, F' (Fin.succ i)}

/-
**hasStrictDerivAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_finCons {φ' : Π i, F' i} : HasStrictDerivAt (fun x => Fin
.cons (φ x) (φs x)) φ' x ↔ HasStrictDerivAt φ (φ' 0) x ∧ HasStrictDerivAt φs (fu
n i => φ' i.succ) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasStrictFDerivAt_finCons`：hasStrictFDerivAt_finCons {φ' : E ->L[𝕜] Π i,
 F' i} : HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔ HasStrictFDer
ivAt φ (.proj 0…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasStrictDerivAt_finCons {φ' : Π i, F' i} :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasStrictDerivAt φ (φ' 0) x ∧ HasStrictDerivAt φs (fun i => φ' i.succ) x :=
  hasStrictFDerivAt_finCons

/-- A variant of `hasStrictDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasStrictDerivAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} : HasSt
rictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔ HasStrictDeri
vAt φ φ' x ∧ HasStrictDerivAt φs φs' x
参数：Fin.succ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasStrictDerivAt_finCons`：hasStrictDerivAt_finCons {φ' : Π i, F' i} : Ha
sStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔ HasStrictDerivAt φ (φ' 0)
 x ∧ HasStrict…

--- 原说明 ---
A variant of `hasStrictDerivAt_finCons` where the derivative variables are free 
on the RHS
instead.
-/
theorem hasStrictDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔
      HasStrictDerivAt φ φ' x ∧ HasStrictDerivAt φs φs' x :=
  hasStrictDerivAt_finCons
/-
**HasStrictDerivAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} (h : Has
StrictDerivAt φ φ' x) (hs : HasStrictDerivAt φs φs' x) : HasStrictDerivAt (fun x
 => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x
参数：Fin.succ i；h : HasStrictDerivAt φ φ' x；hs : HasStrictDerivAt φs φs' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasStrictDerivAt_finCons'`：hasStrictDerivAt_finCons' {φ' : F' 0} {φs' : 
Π i, F' (Fin.succ i)} : HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.c
ons φ' φs') x ↔…
-/
theorem HasStrictDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasStrictDerivAt φ φ' x) (hs : HasStrictDerivAt φs φs' x) :
    HasStrictDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x :=
  hasStrictDerivAt_finCons'.mpr ⟨h, hs⟩
/-
**hasDerivAtFilter_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_finCons {φ' : Π i, F' i} {l : Filter (𝕜 × 𝕜)} : HasDerivA
tFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔ HasDerivAtFilter φ (φ' 0) l ∧ Ha
sDerivAtFilter φs (fun i => φ' i.succ) l
参数：𝕜 × 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasFDerivAtFilter_finCons`：hasFDerivAtFilter_finCons {φ' : E ->L[𝕜] Π i,
 F' i} {l : Filter (E × E)} : HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x))
 φ' l ↔ HasFDer…
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem hasDerivAtFilter_finCons {φ' : Π i, F' i} {l : Filter (𝕜 × 𝕜)} :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔
      HasDerivAtFilter φ (φ' 0) l ∧ HasDerivAtFilter φs (fun i => φ' i.succ) l :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasDerivAtFilter_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasDerivAtFilter_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAtFilter_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Fi
lter (𝕜 × 𝕜)} : HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φ
s') l ↔ HasDerivAtFilter φ φ' l ∧ HasDerivAtFilter φs φs' l
参数：Fin.succ i；𝕜 × 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivAtFilter_finCons`：hasDerivAtFilter_finCons {φ' : Π i, F' i} {l :
 Filter (𝕜 × 𝕜)} : HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔ HasD
erivAtFilter φ…

--- 原说明 ---
A variant of `hasDerivAtFilter_finCons` where the derivative variables are free 
on the RHS
instead.
-/
theorem hasDerivAtFilter_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)} :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') l ↔
      HasDerivAtFilter φ φ' l ∧ HasDerivAtFilter φs φs' l :=
  hasDerivAtFilter_finCons
/-
**HasDerivAtFilter.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAtFilter.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Fil
ter (𝕜 × 𝕜)} (h : HasDerivAtFilter φ φ' l) (hs : HasDerivAtFilter φs φs' l) : Ha
sDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') l
参数：Fin.succ i；𝕜 × 𝕜；h : HasDerivAtFilter φ φ' l；hs : HasDerivAtFilter φs φs' l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasDerivAtFilter_finCons'`：hasDerivAtFilter_finCons' {φ' : F' 0} {φs' : 
Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)} : HasDerivAtFilter (fun x => Fin.cons
 (φ x) (φs x)) …
-/
theorem HasDerivAtFilter.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} {l : Filter (𝕜 × 𝕜)}
    (h : HasDerivAtFilter φ φ' l) (hs : HasDerivAtFilter φs φs' l) :
    HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') l :=
  hasDerivAtFilter_finCons'.mpr ⟨h, hs⟩
/-
**hasDerivAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_finCons {φ' : Π i, F' i} : HasDerivAt (fun x => Fin.cons (φ x) 
(φs x)) φ' x ↔ HasDerivAt φ (φ' 0) x ∧ HasDerivAt φs (fun i => φ' i.succ) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivAtFilter_finCons`：hasDerivAtFilter_finCons {φ' : Π i, F' i} {l :
 Filter (𝕜 × 𝕜)} : HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔ HasD
erivAtFilter φ…
-/
theorem hasDerivAt_finCons {φ' : Π i, F' i} :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasDerivAt φ (φ' 0) x ∧ HasDerivAt φs (fun i => φ' i.succ) x :=
  hasDerivAtFilter_finCons

/-- A variant of `hasDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasDerivAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} : HasDerivAt 
(fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔ HasDerivAt φ φ' x ∧ HasDe
rivAt φs φs' x
参数：Fin.succ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivAt_finCons`：hasDerivAt_finCons {φ' : Π i, F' i} : HasDerivAt (fu
n x => Fin.cons (φ x) (φs x)) φ' x ↔ HasDerivAt φ (φ' 0) x ∧ HasDerivAt φs (fun 
i => φ' …

--- 原说明 ---
A variant of `hasDerivAt_finCons` where the derivative variables are free on the
 RHS
instead.
-/
theorem hasDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔
      HasDerivAt φ φ' x ∧ HasDerivAt φs φs' x :=
  hasDerivAt_finCons
/-
**HasDerivAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} (h : HasDerivA
t φ φ' x) (hs : HasDerivAt φs φs' x) : HasDerivAt (fun x => Fin.cons (φ x) (φs x
)) (Fin.cons φ' φs') x
参数：Fin.succ i；h : HasDerivAt φ φ' x；hs : HasDerivAt φs φs' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasDerivAt_finCons'`：hasDerivAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin
.succ i)} : HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x ↔ Ha
sDerivAt …
-/
theorem HasDerivAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasDerivAt φ φ' x) (hs : HasDerivAt φs φs' x) :
    HasDerivAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') x :=
  hasDerivAt_finCons'.mpr ⟨h, hs⟩
/-
**hasDerivWithinAt_finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_finCons {φ' : Π i, F' i} : HasDerivWithinAt (fun x => Fin
.cons (φ x) (φs x)) φ' s x ↔ HasDerivWithinAt φ (φ' 0) s x ∧ HasDerivWithinAt φs
 (fun i => φ' i.succ) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivAtFilter_finCons`：hasDerivAtFilter_finCons {φ' : Π i, F' i} {l :
 Filter (𝕜 × 𝕜)} : HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔ HasD
erivAtFilter φ…
-/
theorem hasDerivWithinAt_finCons {φ' : Π i, F' i} :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) φ' s x ↔
      HasDerivWithinAt φ (φ' 0) s x ∧ HasDerivWithinAt φs (fun i => φ' i.succ) s x :=
  hasDerivAtFilter_finCons

/-- A variant of `hasDerivWithinAt_finCons` where the derivative variables are free on the RHS
instead. -/
/-
**hasDerivWithinAt_finCons'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivWithinAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} : HasDe
rivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x ↔ HasDerivWit
hinAt φ φ' s x ∧ HasDerivWithinAt φs φs' s x
参数：Fin.succ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivAtFilter_finCons`：hasDerivAtFilter_finCons {φ' : Π i, F' i} {l :
 Filter (𝕜 × 𝕜)} : HasDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' l ↔ HasD
erivAtFilter φ…

--- 原说明 ---
A variant of `hasDerivWithinAt_finCons` where the derivative variables are free 
on the RHS
instead.
-/
theorem hasDerivWithinAt_finCons' {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x ↔
      HasDerivWithinAt φ φ' s x ∧ HasDerivWithinAt φs φs' s x :=
  hasDerivAtFilter_finCons
/-
**HasDerivWithinAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)} (h : Has
DerivWithinAt φ φ' s x) (hs : HasDerivWithinAt φs φs' s x) : HasDerivWithinAt (f
un x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x
参数：Fin.succ i；h : HasDerivWithinAt φ φ' s x；hs : HasDerivWithinAt φs φs' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasDerivWithinAt_finCons'`：hasDerivWithinAt_finCons' {φ' : F' 0} {φs' : 
Π i, F' (Fin.succ i)} : HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.c
ons φ' φs') s x…
-/
theorem HasDerivWithinAt.finCons {φ' : F' 0} {φs' : Π i, F' (Fin.succ i)}
    (h : HasDerivWithinAt φ φ' s x) (hs : HasDerivWithinAt φs φs' s x) :
    HasDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (Fin.cons φ' φs') s x :=
  hasDerivWithinAt_finCons'.mpr ⟨h, hs⟩

-- TODO: write the `Fin.cons` versions of `derivWithin_pi` and `deriv_pi`

end PiFin

