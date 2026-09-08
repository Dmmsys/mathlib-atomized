/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Additive operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
-/

public section


open Filter Asymptotics ContinuousLinearMap

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f g : E → F}
variable {f' g' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

section ConstSMul

variable {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-! ### Derivative of a function multiplied by a constant -/

@[to_fun]
/-
**HasFDerivAtFilter.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' L) (c : R) : HasF
DerivAtFilter (c • f) (c • f') L
参数：h : HasFDerivAtFilter f f' L；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
### Derivative of a function multiplied by a constant
-/
theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' L) (c : R) :
    HasFDerivAtFilter (c • f) (c • f') L :=
  (c • (1 : F →L[𝕜] F)).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) : HasS
trictFDerivAt (c • f) (c • f') x
参数：h : HasStrictFDerivAt f f' x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.const_smul`：HasFDerivAtFilter.const_smul (h : HasFDeri
vAtFilter f f' L) (c : R) : HasFDerivAtFilter (c • f) (c • f') L
-/
theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
    HasStrictFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) : Ha
sFDerivWithinAt (c • f) (c • f') s x
参数：h : HasFDerivWithinAt f f' s x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.const_smul`：HasFDerivAtFilter.const_smul (h : HasFDeri
vAtFilter f f' L) (c : R) : HasFDerivAtFilter (c • f) (c • f') L
-/
theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
    HasFDerivWithinAt (c • f) (c • f') s x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) : HasFDerivAt (c •
 f) (c • f') x
参数：h : HasFDerivAt f f' x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.const_smul`：HasFDerivAtFilter.const_smul (h : HasFDeri
vAtFilter f f' L) (c : R) : HasFDerivAtFilter (c • f) (c • f') L
-/
theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
    HasFDerivAt (c • f) (c • f') x :=
  HasFDerivAtFilter.const_smul h c

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c 
: R) : DifferentiableWithinAt 𝕜 (c • f) s x
参数：h : DifferentiableWithinAt 𝕜 f s x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.const_smul`：HasFDerivWithinAt.const_smul (h : HasFDeri
vWithinAt f f' s x) (c : R) : HasFDerivWithinAt (c • f) (c • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (c • f) s x :=
  (h.hasFDerivWithinAt.const_smul c).differentiableWithinAt

@[to_fun (attr := fun_prop)]
/-
**DifferentiableAt.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) : Differe
ntiableAt 𝕜 (c • f) x
参数：h : DifferentiableAt 𝕜 f x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.const_smul`：HasFDerivAt.const_smul (h : HasFDerivAt f f' x) 
(c : R) : HasFDerivAt (c • f) (c • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (c • f) x :=
  (h.hasFDerivAt.const_smul c).differentiableAt

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) : Differe
ntiableOn 𝕜 (c • f) s
参数：h : DifferentiableOn 𝕜 f s；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.const_smul`：DifferentiableWithinAt.const_smul (h 
: DifferentiableWithinAt 𝕜 f s x) (c : R) : DifferentiableWithinAt 𝕜 (c • f) s x
-/
theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (h x hx).const_smul c

@[to_fun (attr := fun_prop)]
/-
**Differentiable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) : Differentiabl
e 𝕜 (c • f)
参数：h : Differentiable 𝕜 f；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.const_smul`：DifferentiableAt.const_smul (h : Differenti
ableAt 𝕜 f x) (c : R) : DifferentiableAt 𝕜 (c • f) x
-/
theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 (c • f) := fun x => (h x).const_smul c
/-
**fderivWithin_fun_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (h : Differen
tiableWithinAt 𝕜 f s x) (c : R) : fderivWithin 𝕜 (fun y => c • f y) s x = c • fd
erivWithin 𝕜 f s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 f s x；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.const_smul`：HasFDerivWithinAt.const_smul (h : HasFDeri
vWithinAt f f' s x) (c : R) : HasFDerivWithinAt (c • f) (c • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_fun_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.hasFDerivWithinAt.const_smul c).fderivWithin hxs
/-
**fderivWithin_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (h : Differentiab
leWithinAt 𝕜 f s x) (c : R) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f 
s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : DifferentiableWithinAt 𝕜 f s x；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_fun_const_smul`：fderivWithin_fun_const_smul (hxs : UniqueDi
ffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f s x) (c : R) : fderivWithin 𝕜 
(fun y => c • f y…
-/
theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x :=
  fderivWithin_fun_const_smul hxs h c

/-- If `c` is invertible, `c • f` is differentiable at `x` within `s` if and only if `f` is. -/
/-
**differentiableWithinAt_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_smul_iff (c : R) [Invertible c] : DifferentiableWit
hinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 𝕜 f s x
参数：c : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.congr_of_eventuallyEq`：DifferentiableWithinAt.con
gr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : f₁ x = f x) : DifferentiableW…
· 使用定理 `DifferentiableWithinAt.const_smul`：DifferentiableWithinAt.const_smul (h 
: DifferentiableWithinAt 𝕜 f s x) (c : R) : DifferentiableWithinAt 𝕜 (c • f) s x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_smul_smul`：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst
_1 : MulAction α β] (c : α) (x : β) [inst_2 : Invertible c],   ⅟c • c • x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `c` is invertible, `c • f` is differentiable at `x` within `s` if and only if
 `f` is.
-/
lemma differentiableWithinAt_smul_iff (c : R) [Invertible c] :
    DifferentiableWithinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.const_smul c⟩
  apply (h.const_smul ⅟c).congr_of_eventuallyEq ?_ (by simp)
  filter_upwards with x using by simp

/-- A version of `fderivWithin_const_smul` without differentiability hypothesis:
in return, the constant `c` must be invertible, i.e. if `R` is a field. -/
/-
**fderivWithin_const_smul_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const_smul_of_invertible (c : R) [Invertible c] (hs : UniqueD
iffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x
参数：c : R；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.const_smul`：HasFDerivWithinAt.const_smul (h : HasFDeri
vWithinAt f f' s x) (c : R) : HasFDerivWithinAt (c • f) (c • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `differentiableWithinAt_smul_iff`：differentiableWithinAt_smul_iff (c : R)
 [Invertible c] : DifferentiableWithinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 
𝕜 f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `fderivWithin_const_smul` without differentiability hypothesis:
in return, the constant `c` must be invertible, i.e. if `R` is a field.
-/
theorem fderivWithin_const_smul_of_invertible (c : R) [Invertible c]
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact (h.hasFDerivWithinAt.const_smul c).fderivWithin hs
  · have : ¬DifferentiableWithinAt 𝕜 (c • f) s x := by
      contrapose h
      exact (differentiableWithinAt_smul_iff c).mp h
    simp [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this]
/-
**fderiv_fun_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) : fderiv 𝕜 (fun
 y => c • f y) x = c • fderiv 𝕜 f x
参数：h : DifferentiableAt 𝕜 f x；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.const_smul`：HasFDerivAt.const_smul (h : HasFDerivAt f f' x) 
(c : R) : HasFDerivAt (c • f) (c • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_fun_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv
/-
**fderiv_const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) : fderiv 𝕜 (c • f) 
x = c • fderiv 𝕜 f x
参数：h : DifferentiableAt 𝕜 f x；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.const_smul`：HasFDerivAt.const_smul (h : HasFDerivAt f f' x) 
(c : R) : HasFDerivAt (c • f) (c • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x :=
  (h.hasFDerivAt.const_smul c).fderiv

/-- If `c` is invertible, `c • f` is differentiable at `x` if and only if `f` is. -/
/-
**differentiableAt_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_smul_iff (c : R) [Invertible c] : DifferentiableAt 𝕜 (c •
 f) x ↔ DifferentiableAt 𝕜 f x
参数：c : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用引理 `differentiableWithinAt_smul_iff`：differentiableWithinAt_smul_iff (c : R)
 [Invertible c] : DifferentiableWithinAt 𝕜 (c • f) s x ↔ DifferentiableWithinAt 
𝕜 f s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `c` is invertible, `c • f` is differentiable at `x` if and only if `f` is.
-/
lemma differentiableAt_smul_iff (c : R) [Invertible c] :
    DifferentiableAt 𝕜 (c • f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, differentiableWithinAt_smul_iff, differentiableWithinAt_univ]

/-- A version of `fderiv_const_smul` without differentiability hypothesis: in return, the constant
`c` must be invertible, i.e. if `R` is a field. -/
/-
**fderiv_const_smul_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const_smul_of_invertible (c : R) [Invertible c] : fderiv 𝕜 (c • f) 
x = c • fderiv 𝕜 f x
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_const_smul_of_invertible`：fderivWithin_const_smul_of_invert
ible (c : R) [Invertible c] (hs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c 
• f) s x = c • fderivWithin…
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `fderiv_const_smul` without differentiability hypothesis: in return
, the constant
`c` must be invertible, i.e. if `R` is a field.
-/
theorem fderiv_const_smul_of_invertible (c : R) [Invertible c] :
    fderiv 𝕜 (c • f) x = c • fderiv 𝕜 f x := by
  simp [← fderivWithin_univ, fderivWithin_const_smul_of_invertible c uniqueDiffWithinAt_univ]

end ConstSMul

section ConstSMulDivisionRing

variable {R : Type*} [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F]
  [ContinuousConstSMul R F]

/-- Special case of `fderivWithin_const_smul_of_invertible` over a division semiring: any constant
is allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulActionWithZero`
typeclass. -/
/-
**fderivWithin_const_smul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_const_smul_field (c : R) (hs : UniqueDiffWithinAt 𝕜 s x) : fd
erivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x
参数：c : R；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_zero`：fderivWithin_zero : fderivWithin 𝕜 (0 : E -> F) s = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fderivWithin_const_smul_of_invertible`：fderivWithin_const_smul_of_invert
ible (c : R) [Invertible c] (hs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c 
• f) s x = c • fderivWithin…

--- 原说明 ---
Special case of `fderivWithin_const_smul_of_invertible` over a division semiring
: any constant
is allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulAc
tionWithZero`
typeclass.
-/
lemma fderivWithin_const_smul_field (c : R) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  obtain (rfl | ha) := eq_or_ne c 0
  · simp
  · have : Invertible c := invertibleOfNonzero ha
    simp [fderivWithin_const_smul_of_invertible c hs]
/-
**fderivWithin_const_smul_field'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_const_smul_field' {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜} (c : R) : 
fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `fderivWithin_const_smul_field`：fderivWithin_const_smul_field (c : R) (hs
 : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f
 s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_uniqueDiffWithinAt`：fderivWithin_zero_of_not_un
iqueDiffWithinAt {f : 𝕜 -> F} {x : 𝕜} {s : Set 𝕜} (h : ¬UniqueDiffWithinAt 𝕜 s x
) : fderivWithin 𝕜 f s x = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivWithin_const_smul_field' {s : Set 𝕜} {f : 𝕜 → F} {x : 𝕜} (c : R) :
    fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f s x := by
  by_cases hsx : UniqueDiffWithinAt 𝕜 s x
  · exact fderivWithin_const_smul_field c hsx
  · simp [fderivWithin_zero_of_not_uniqueDiffWithinAt hsx]

omit [DivisionSemiring R] [Module R F] [SMulCommClass 𝕜 R F] [ContinuousConstSMul R F] in
/-- Special case of `fderivWithin_neg` for functions `𝕜 → F`, i.e. when the domain `E` is the scalar
field `𝕜` itself. In this case no `UniqueDiffWithinAt 𝕜 s x` hypothesis is needed. -/
/-
**fderivWithin_neg'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderivWithin_neg' {s : Set 𝕜} {f : 𝕜 -> F} {x : 𝕜} : fderivWithin 𝕜 (-f) s
 x = -fderivWithin 𝕜 f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `fderivWithin_const_smul_field'`：fderivWithin_const_smul_field' {s : Set 
𝕜} {f : 𝕜 -> F} {x : 𝕜} (c : R) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 
𝕜 f s x

--- 原说明 ---
Special case of `fderivWithin_neg` for functions `𝕜 → F`, i.e. when the domain `
E` is the scalar
field `𝕜` itself. In this case no `UniqueDiffWithinAt 𝕜 s x` hypothesis is neede
d.
-/
lemma fderivWithin_neg' {s : Set 𝕜} {f : 𝕜 → F} {x : 𝕜} :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x := by
  simpa only [neg_smul, one_smul] using fderivWithin_const_smul_field' (f := f) (-1 : 𝕜)

@[deprecated (since := "2026-01-11")] alias fderivWithin_const_smul_of_field :=
  fderivWithin_const_smul_field

/-- Special case of `fderiv_const_smul_of_invertible` over a division semiring: any constant is
allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulActionWithZero`
typeclass. -/
/-
**fderiv_const_smul_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：fderiv_const_smul_field (c : R) : fderiv 𝕜 (c • f) = c • fderiv 𝕜 f
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `fderivWithin_const_smul_field`：fderivWithin_const_smul_field (c : R) (hs
 : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (c • f) s x = c • fderivWithin 𝕜 f
 s x
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Special case of `fderiv_const_smul_of_invertible` over a division semiring: any 
constant is
allowed.

TODO: This would work for scalars in a `GroupWithZero` if we had a `DistribMulAc
tionWithZero`
typeclass.
-/
lemma fderiv_const_smul_field (c : R) : fderiv 𝕜 (c • f) = c • fderiv 𝕜 f := by
  simp_rw [← fderivWithin_univ]
  ext x
  simp [fderivWithin_const_smul_field c uniqueDiffWithinAt_univ]

@[deprecated (since := "2026-01-11")] alias fderiv_const_smul_of_field := fderiv_const_smul_field

end ConstSMulDivisionRing

section Add

/-! ### Derivative of the sum of two functions -/

@[to_fun]
/-
**HasFDerivAtFilter.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFil
ter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L
参数：hf : HasFDerivAtFilter f f' L；hg : HasFDerivAtFilter g g' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `HasFDerivAtFilter.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…

--- 原说明 ---
### Derivative of the sum of two functions
-/
theorem HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f' L)
    (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L :=
  .of_isLittleO <| (hf.isLittleO.add hg.isLittleO).congr_left fun _ => by
    grind [Pi.add_apply]

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDeri
vAt g g' x) : HasStrictFDerivAt (f + g) (f' + g') x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.add`：HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L
-/
theorem HasStrictFDerivAt.add (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWit
hinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.add`：HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L
-/
theorem HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) : HasF
DerivAt (f + g) (f' + g') x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.add`：HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L
-/
theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f + g) (f' + g') x :=
  HasFDerivAtFilter.add hf hg

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x) (hg : Dif
ferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f + g) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.add`：HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f + g) s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 
𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.add`：HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDer
ivAt g g' x) : HasFDerivAt (f + g) (f' + g') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 
𝕜 g s) : DifferentiableOn 𝕜 (f + g) s
参数：hf : DifferentiableOn 𝕜 f s；hg : DifferentiableOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.add`：DifferentiableWithinAt.add (hf : Differentia
bleWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithi
nAt 𝕜 (f + g) s …
-/
theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s := fun x hx => (hf x hx).add (hg x hx)

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) : D
ifferentiable 𝕜 (f + g)
参数：hf : Differentiable 𝕜 f；hg : Differentiable 𝕜 g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.add`：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
-/
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) := fun x => (hf x).add (hg x)

-- TODO: `@[to_fun]` gives incorrect lemma name
/-
**fderivWithin_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWith
inAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderivWithin 𝕜 (f + g) s x
 = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hf : DifferentiableWithinAt 𝕜 f s x；hg : Diffe
rentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.add`：HasFDerivWithinAt.add (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f + g) (f' + g') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f + g) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.add hg.hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : Differentiable
WithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderivWithin 𝕜 (fun y 
=> f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hf : DifferentiableWithinAt 𝕜 f s x；hg : Diffe
rentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_add`：fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf 
: DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderiv
Within…
-/
theorem fderivWithin_fun_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  fderivWithin_add hxs hf hg

-- TODO: `@[to_fun]` gives incorrect lemma name
/-
**fderiv_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : f
deriv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.add`：HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDer
ivAt g g' x) : HasFDerivAt (f + g) (f' + g') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
/-
**fderiv_fun_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
 : fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_add`：fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : Differentiabl
eAt 𝕜 g x) : fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x
-/
theorem fderiv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  fderiv_add hf hg

@[simp]
/-
**hasFDerivAtFilter_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_add_const_iff (c : F) : HasFDerivAtFilter (f · + c) f' L
 ↔ HasFDerivAtFilter f f' L
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAtFilter_add_const_iff (c : F) :
    HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L := by
  simp [hasFDerivAtFilter_iff_isLittleOTVS]

alias ⟨_, HasFDerivAtFilter.add_const⟩ := hasFDerivAtFilter_add_const_iff

@[simp]
/-
**hasStrictFDerivAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_add_const_iff (c : F) : HasStrictFDerivAt (f · + c) f' x
 ↔ HasStrictFDerivAt f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasStrictFDerivAt_add_const_iff (c : F) :
    HasStrictFDerivAt (f · + c) f' x ↔ HasStrictFDerivAt f f' x := by
  simp [hasStrictFDerivAt_iff_isLittleO]

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.add_const⟩ := hasStrictFDerivAt_add_const_iff

@[simp]
/-
**hasFDerivWithinAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_add_const_iff (c : F) : HasFDerivWithinAt (f · + c) f' s
 x ↔ HasFDerivWithinAt f f' s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_add_const_iff`：hasFDerivAtFilter_add_const_iff (c : F)
 : HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivWithinAt_add_const_iff (c : F) :
    HasFDerivWithinAt (f · + c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.add_const⟩ := hasFDerivWithinAt_add_const_iff

@[simp]
/-
**hasFDerivAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_add_const_iff (c : F) : HasFDerivAt (f · + c) f' x ↔ HasFDeriv
At f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_add_const_iff`：hasFDerivAtFilter_add_const_iff (c : F)
 : HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivAt_add_const_iff (c : F) : HasFDerivAt (f · + c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_add_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.add_const⟩ := hasFDerivAt_add_const_iff

@[simp]
/-
**differentiableWithinAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_add_const_iff (c : F) : DifferentiableWithinAt 𝕜 (f
un y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivWithinAt_add_const_iff`：hasFDerivWithinAt_add_const_iff (c : F)
 : HasFDerivWithinAt (f · + c) f' s x ↔ HasFDerivWithinAt f f' s x
-/
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ ↦ hasFDerivWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.add_const⟩ := differentiableWithinAt_add_const_iff

@[simp]
/-
**differentiableAt_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_add_const_iff (c : F) : DifferentiableAt 𝕜 (fun y => f y 
+ c) x ↔ DifferentiableAt 𝕜 f x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivAt_add_const_iff`：hasFDerivAt_add_const_iff (c : F) : HasFDeriv
At (f · + c) f' x ↔ HasFDerivAt f f' x
-/
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ ↦ hasFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.add_const⟩ := differentiableAt_add_const_iff

@[simp]
/-
**differentiableOn_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_add_const_iff (c : F) : DifferentiableOn 𝕜 (fun y => f y 
+ c) s ↔ DifferentiableOn 𝕜 f s
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `differentiableWithinAt_add_const_iff`：differentiableWithinAt_add_const_i
ff (c : F) : DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWit
hinAt 𝕜 f s x
-/
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ ↦ differentiableWithinAt_add_const_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.add_const⟩ := differentiableOn_add_const_iff

@[simp]
/-
**differentiable_add_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_add_const_iff (c : F) : (Differentiable 𝕜 fun y => f y + c)
 ↔ Differentiable 𝕜 f
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `differentiableAt_add_const_iff`：differentiableAt_add_const_iff (c : F) :
 DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x
-/
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ ↦ differentiableAt_add_const_iff c

@[fun_prop]
alias ⟨_, Differentiable.add_const⟩ := differentiable_add_const_iff

@[simp]
/-
**fderivWithin_add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_add_const (c : F) : fderivWithin 𝕜 (fun y => f y + c) s x = f
derivWithin 𝕜 f s x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_add_const (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x := by
  classical simp [fderivWithin]

@[simp]
/-
**fderiv_add_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_add_const`：fderivWithin_add_const (c : F) : fderivWithin 𝕜 
(fun y => f y + c) s x = fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const]

@[simp]
/-
**hasFDerivAtFilter_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_const_add_iff (c : F) : HasFDerivAtFilter (c + f ·) f' L
 ↔ HasFDerivAtFilter f f' L
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `hasFDerivAtFilter_add_const_iff`：hasFDerivAtFilter_add_const_iff (c : F)
 : HasFDerivAtFilter (f · + c) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivAtFilter_const_add_iff (c : F) :
    HasFDerivAtFilter (c + f ·) f' L ↔ HasFDerivAtFilter f f' L := by
  simpa only [add_comm] using hasFDerivAtFilter_add_const_iff c

alias ⟨_, HasFDerivAtFilter.const_add⟩ := hasFDerivAtFilter_const_add_iff

@[simp]
/-
**hasStrictFDerivAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_const_add_iff (c : F) : HasStrictFDerivAt (c + f ·) f' x
 ↔ HasStrictFDerivAt f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `hasStrictFDerivAt_add_const_iff`：hasStrictFDerivAt_add_const_iff (c : F)
 : HasStrictFDerivAt (f · + c) f' x ↔ HasStrictFDerivAt f f' x
-/
theorem hasStrictFDerivAt_const_add_iff (c : F) :
    HasStrictFDerivAt (c + f ·) f' x ↔ HasStrictFDerivAt f f' x := by
  simpa only [add_comm] using hasStrictFDerivAt_add_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.const_add⟩ := hasStrictFDerivAt_const_add_iff

@[simp]
/-
**hasFDerivWithinAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_const_add_iff (c : F) : HasFDerivWithinAt (c + f ·) f' s
 x ↔ HasFDerivWithinAt f f' s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const_add_iff`：hasFDerivAtFilter_const_add_iff (c : F)
 : HasFDerivAtFilter (c + f ·) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivWithinAt_const_add_iff (c : F) :
    HasFDerivWithinAt (c + f ·) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.const_add⟩ := hasFDerivWithinAt_const_add_iff

@[simp]
/-
**hasFDerivAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDeriv
At f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_const_add_iff`：hasFDerivAtFilter_const_add_iff (c : F)
 : HasFDerivAtFilter (c + f ·) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_const_add_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.const_add⟩ := hasFDerivAt_const_add_iff

@[simp]
/-
**differentiableWithinAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_const_add_iff (c : F) : DifferentiableWithinAt 𝕜 (f
un y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivWithinAt_const_add_iff`：hasFDerivWithinAt_const_add_iff (c : F)
 : HasFDerivWithinAt (c + f ·) f' s x ↔ HasFDerivWithinAt f f' s x
-/
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  exists_congr fun _ ↦ hasFDerivWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableWithinAt.const_add⟩ := differentiableWithinAt_const_add_iff

@[simp]
/-
**differentiableAt_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_const_add_iff (c : F) : DifferentiableAt 𝕜 (fun y => c + 
f y) x ↔ DifferentiableAt 𝕜 f x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasFDerivAt_const_add_iff`：hasFDerivAt_const_add_iff (c : F) : HasFDeriv
At (c + f ·) f' x ↔ HasFDerivAt f f' x
-/
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  exists_congr fun _ ↦ hasFDerivAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableAt.const_add⟩ := differentiableAt_const_add_iff

@[simp]
/-
**differentiableOn_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_const_add_iff (c : F) : DifferentiableOn 𝕜 (fun y => c + 
f y) s ↔ DifferentiableOn 𝕜 f s
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `differentiableWithinAt_const_add_iff`：differentiableWithinAt_const_add_i
ff (c : F) : DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWit
hinAt 𝕜 f s x
-/
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  forall₂_congr fun _ _ ↦ differentiableWithinAt_const_add_iff c

@[fun_prop]
alias ⟨_, DifferentiableOn.const_add⟩ := differentiableOn_const_add_iff

@[simp]
/-
**differentiable_const_add_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_const_add_iff (c : F) : (Differentiable 𝕜 fun y => c + f y)
 ↔ Differentiable 𝕜 f
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `differentiableAt_const_add_iff`：differentiableAt_const_add_iff (c : F) :
 DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x
-/
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  forall_congr' fun _ ↦ differentiableAt_const_add_iff c

@[fun_prop]
alias ⟨_, Differentiable.const_add⟩ := differentiable_const_add_iff

@[simp]
/-
**fderivWithin_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const_add (c : F) : fderivWithin 𝕜 (fun y => c + f y) s x = f
derivWithin 𝕜 f s x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `fderivWithin_add_const`：fderivWithin_add_const (c : F) : fderivWithin 𝕜 
(fun y => f y + c) s x = fderivWithin 𝕜 f s x
-/
theorem fderivWithin_const_add (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const c

@[simp]
/-
**fderiv_const_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x
参数：c : F。
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
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `fderiv_add_const`：fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c)
 x = fderiv 𝕜 f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


variable {ι : Type*} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

@[fun_prop]
/-
**HasStrictFDerivAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.fun_sum (h : forall i in u, HasStrictFDerivAt (A i) (A' 
i) x) : HasStrictFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
参数：h : forall i in u, HasStrictFDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.sum`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u
_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F']   {g
' : α → F'} {l …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem HasStrictFDerivAt.fun_sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x := by
  simp only [hasStrictFDerivAt_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp [Finset.sum_sub_distrib]

@[fun_prop]
/-
**HasStrictFDerivAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.sum (h : forall i in u, HasStrictFDerivAt (A i) (A' i) x
) : HasStrictFDerivAt (∑ i in u, A i) (∑ i in u, A' i) x
参数：h : forall i in u, HasStrictFDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.fun_sum`：HasStrictFDerivAt.fun_sum (h : forall i in u,
 HasStrictFDerivAt (A i) (A' i) x) : HasStrictFDerivAt (fun y => ∑ i in u, A i y
) (∑ i in u, A'…
-/
theorem HasStrictFDerivAt.sum (h : ∀ i ∈ u, HasStrictFDerivAt (A i) (A' i) x) :
    HasStrictFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x := by
  convert! HasStrictFDerivAt.fun_sum h; simp
/-
**HasFDerivAtFilter.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.fun_sum (h : forall i in u, HasFDerivAtFilter (A i) (A' 
i) L) : HasFDerivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) L
参数：h : forall i in u, HasFDerivAtFilter (A i) (A' i) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.sum`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u
_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F']   {g
' : α → F'} {l …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem HasFDerivAtFilter.fun_sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) L := by
  simp only [hasFDerivAtFilter_iff_isLittleO] at *
  convert! IsLittleO.sum h
  simp
/-
**HasFDerivAtFilter.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.sum (h : forall i in u, HasFDerivAtFilter (A i) (A' i) L
) : HasFDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) L
参数：h : forall i in u, HasFDerivAtFilter (A i) (A' i) L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAtFilter.fun_sum`：HasFDerivAtFilter.fun_sum (h : forall i in u,
 HasFDerivAtFilter (A i) (A' i) L) : HasFDerivAtFilter (fun y => ∑ i in u, A i y
) (∑ i in u, A'…
-/
theorem HasFDerivAtFilter.sum (h : ∀ i ∈ u, HasFDerivAtFilter (A i) (A' i) L) :
    HasFDerivAtFilter (∑ i ∈ u, A i) (∑ i ∈ u, A' i) L := by
  convert! HasFDerivAtFilter.fun_sum h; simp

@[fun_prop]
/-
**HasFDerivWithinAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.fun_sum (h : forall i in u, HasFDerivWithinAt (A i) (A' 
i) s x) : HasFDerivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x
参数：h : forall i in u, HasFDerivWithinAt (A i) (A' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.fun_sum`：HasFDerivAtFilter.fun_sum (h : forall i in u,
 HasFDerivAtFilter (A i) (A' i) L) : HasFDerivAtFilter (fun y => ∑ i in u, A i y
) (∑ i in u, A'…
-/
theorem HasFDerivWithinAt.fun_sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) s x :=
  HasFDerivAtFilter.fun_sum h

@[fun_prop]
/-
**HasFDerivWithinAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.sum (h : forall i in u, HasFDerivWithinAt (A i) (A' i) s
 x) : HasFDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i) s x
参数：h : forall i in u, HasFDerivWithinAt (A i) (A' i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.sum`：HasFDerivAtFilter.sum (h : forall i in u, HasFDer
ivAtFilter (A i) (A' i) L) : HasFDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) 
L
-/
theorem HasFDerivWithinAt.sum (h : ∀ i ∈ u, HasFDerivWithinAt (A i) (A' i) s x) :
    HasFDerivWithinAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) s x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
/-
**HasFDerivAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.fun_sum (h : forall i in u, HasFDerivAt (A i) (A' i) x) : HasF
DerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
参数：h : forall i in u, HasFDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.fun_sum`：HasFDerivAtFilter.fun_sum (h : forall i in u,
 HasFDerivAtFilter (A i) (A' i) L) : HasFDerivAtFilter (fun y => ∑ i in u, A i y
) (∑ i in u, A'…
-/
theorem HasFDerivAt.fun_sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ u, A i y) (∑ i ∈ u, A' i) x :=
  HasFDerivAtFilter.fun_sum h

@[fun_prop]
/-
**HasFDerivAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.sum (h : forall i in u, HasFDerivAt (A i) (A' i) x) : HasFDeri
vAt (∑ i in u, A i) (∑ i in u, A' i) x
参数：h : forall i in u, HasFDerivAt (A i) (A' i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.sum`：HasFDerivAtFilter.sum (h : forall i in u, HasFDer
ivAtFilter (A i) (A' i) L) : HasFDerivAtFilter (∑ i in u, A i) (∑ i in u, A' i) 
L
-/
theorem HasFDerivAt.sum (h : ∀ i ∈ u, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (∑ i ∈ u, A i) (∑ i ∈ u, A' i) x :=
  HasFDerivAtFilter.sum h

@[fun_prop]
/-
**DifferentiableWithinAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.fun_sum (h : forall i in u, DifferentiableWithinAt 
𝕜 (A i) s x) : DifferentiableWithinAt 𝕜 (fun y => ∑ i in u, A i y) s x
参数：h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.fun_sum`：HasFDerivWithinAt.fun_sum (h : forall i in u,
 HasFDerivWithinAt (A i) (A' i) s x) : HasFDerivWithinAt (fun y => ∑ i in u, A i
 y) (∑ i in u, …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.fun_sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i ∈ u, A i y) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt

@[fun_prop]
/-
**DifferentiableWithinAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.sum (h : forall i in u, DifferentiableWithinAt 𝕜 (A
 i) s x) : DifferentiableWithinAt 𝕜 (∑ i in u, A i) s x
参数：h : forall i in u, DifferentiableWithinAt 𝕜 (A i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.sum`：HasFDerivWithinAt.sum (h : forall i in u, HasFDer
ivWithinAt (A i) (A' i) s x) : HasFDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i
) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (∑ i ∈ u, A i) s x :=
  HasFDerivWithinAt.differentiableWithinAt <|
    HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt

@[simp, fun_prop]
/-
**DifferentiableAt.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) :
 DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x
参数：h : forall i in u, DifferentiableAt 𝕜 (A i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.fun_sum`：HasFDerivAt.fun_sum (h : forall i in u, HasFDerivAt
 (A i) (A' i) x) : HasFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i ∈ u, A i y) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt

@[simp, fun_prop]
/-
**DifferentiableAt.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) : Dif
ferentiableAt 𝕜 (∑ i in u, A i) x
参数：h : forall i in u, DifferentiableAt 𝕜 (A i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.sum`：HasFDerivAt.sum (h : forall i in u, HasFDerivAt (A i) (
A' i) x) : HasFDerivAt (∑ i in u, A i) (∑ i in u, A' i) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (∑ i ∈ u, A i) x :=
  HasFDerivAt.differentiableAt <| HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt

@[fun_prop]
/-
**DifferentiableOn.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.fun_sum (h : forall i in u, DifferentiableOn 𝕜 (A i) s) :
 DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s
参数：h : forall i in u, DifferentiableOn 𝕜 (A i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.fun_sum`：DifferentiableWithinAt.fun_sum (h : fora
ll i in u, DifferentiableWithinAt 𝕜 (A i) s x) : DifferentiableWithinAt 𝕜 (fun y
 => ∑ i in u, A i y)…
-/
theorem DifferentiableOn.fun_sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i ∈ u, A i y) s := fun x hx =>
  DifferentiableWithinAt.fun_sum fun i hi => h i hi x hx

@[fun_prop]
/-
**DifferentiableOn.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sum (h : forall i in u, DifferentiableOn 𝕜 (A i) s) : Dif
ferentiableOn 𝕜 (∑ i in u, A i) s
参数：h : forall i in u, DifferentiableOn 𝕜 (A i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.sum`：DifferentiableWithinAt.sum (h : forall i in 
u, DifferentiableWithinAt 𝕜 (A i) s x) : DifferentiableWithinAt 𝕜 (∑ i in u, A i
) s x
-/
theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (∑ i ∈ u, A i) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx

@[simp, fun_prop]
/-
**Differentiable.fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.fun_sum (h : forall i in u, Differentiable 𝕜 (A i)) : Diffe
rentiable 𝕜 fun y => ∑ i in u, A i y
参数：h : forall i in u, Differentiable 𝕜 (A i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.fun_sum`：DifferentiableAt.fun_sum (h : forall i in u, D
ifferentiableAt 𝕜 (A i) x) : DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x
-/
theorem Differentiable.fun_sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i ∈ u, A i y :=
  fun x => DifferentiableAt.fun_sum fun i hi => h i hi x

@[simp, fun_prop]
/-
**Differentiable.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.sum (h : forall i in u, Differentiable 𝕜 (A i)) : Different
iable 𝕜 (∑ i in u, A i)
参数：h : forall i in u, Differentiable 𝕜 (A i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sum`：DifferentiableAt.sum (h : forall i in u, Different
iableAt 𝕜 (A i) x) : DifferentiableAt 𝕜 (∑ i in u, A i) x
-/
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 (∑ i ∈ u, A i) := fun x => DifferentiableAt.sum fun i hi => h i hi x
/-
**fderivWithin_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_sum (hxs : UniqueDiffWithinAt 𝕜 s x) (h : forall i in u, 
DifferentiableWithinAt 𝕜 (A i) s x) : fderivWithin 𝕜 (fun y => ∑ i in u, A i y) 
s x = ∑ i in u, fderivWithin 𝕜 (A i) s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : forall i in u, DifferentiableWithinAt 𝕜 (A
 i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.fun_sum`：HasFDerivWithinAt.fun_sum (h : forall i in u,
 HasFDerivWithinAt (A i) (A' i) s x) : HasFDerivWithinAt (fun y => ∑ i in u, A i
 y) (∑ i in u, …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_fun_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i ∈ u, A i y) s x = ∑ i ∈ u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.fun_sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x) (h : forall i in u, Diff
erentiableWithinAt 𝕜 (A i) s x) : fderivWithin 𝕜 (∑ i in u, A i) s x = ∑ i in u,
 fderivWithin 𝕜 (A i) s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；h : forall i in u, DifferentiableWithinAt 𝕜 (A
 i) s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.sum`：HasFDerivWithinAt.sum (h : forall i in u, HasFDer
ivWithinAt (A i) (A' i) s x) : HasFDerivWithinAt (∑ i in u, A i) (∑ i in u, A' i
) s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (∑ i ∈ u, A i) s x = ∑ i ∈ u, fderivWithin 𝕜 (A i) s x :=
  (HasFDerivWithinAt.sum fun i hi => (h i hi).hasFDerivWithinAt).fderivWithin hxs
/-
**fderiv_fun_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) : fderiv 𝕜 
(fun y => ∑ i in u, A i y) x = ∑ i in u, fderiv 𝕜 (A i) x
参数：h : forall i in u, DifferentiableAt 𝕜 (A i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.fun_sum`：HasFDerivAt.fun_sum (h : forall i in u, HasFDerivAt
 (A i) (A' i) x) : HasFDerivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_fun_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i ∈ u, A i y) x = ∑ i ∈ u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt).fderiv
/-
**fderiv_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_sum (h : forall i in u, DifferentiableAt 𝕜 (A i) x) : fderiv 𝕜 (∑ i
 in u, A i) x = ∑ i in u, fderiv 𝕜 (A i) x
参数：h : forall i in u, DifferentiableAt 𝕜 (A i) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.sum`：HasFDerivAt.sum (h : forall i in u, HasFDerivAt (A i) (
A' i) x) : HasFDerivAt (∑ i in u, A i) (∑ i in u, A' i) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (∑ i ∈ u, A i) x = ∑ i ∈ u, fderiv 𝕜 (A i) x :=
  (HasFDerivAt.sum fun i hi => (h i hi).hasFDerivAt).fderiv

end Sum

section Neg

/-! ### Derivative of the negative of a function -/


@[to_fun]
/-
**HasFDerivAtFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' L) : HasFDerivAtFilter (
-f) (-f') L
参数：h : HasFDerivAtFilter f f' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.comp`：HasFDerivAtFilter.comp {g : F -> G} {g' : F ->L[
𝕜] G} {L' : Filter (F × F)} (hg : HasFDerivAtFilter g g' L') (hf : HasFDerivAtFi
lter f f' L)…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.hasFDerivAtFilter`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)

--- 原说明 ---
### Derivative of the negative of a function
-/
theorem HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter (-f) (-f') L :=
  (-1 : F →L[𝕜] F).hasFDerivAtFilter.comp h tendsto_map

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) : HasStrictFDerivAt (
-f) (-f') x
参数：h : HasStrictFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.neg`：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f'
 L) : HasFDerivAtFilter (-f) (-f') L
-/
theorem HasStrictFDerivAt.neg (h : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (-f) (-f') x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) : HasFDerivWithinAt
 (-f) (-f') s x
参数：h : HasFDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.neg`：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f'
 L) : HasFDerivAtFilter (-f) (-f') L
-/
theorem HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (-f) (-f') s x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (-f) (-f') x
参数：h : HasFDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.neg`：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f'
 L) : HasFDerivAtFilter (-f) (-f') L
-/
theorem HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt (-f) (-f') x :=
  HasFDerivAtFilter.neg h

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) : Differen
tiableWithinAt 𝕜 (-f) s x
参数：h : DifferentiableWithinAt 𝕜 f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.neg`：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f'
 s x) : HasFDerivWithinAt (-f) (-f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (-f) s x :=
  h.hasFDerivWithinAt.neg.differentiableWithinAt

@[simp]
/-
**differentiableWithinAt_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_fun_neg_iff : DifferentiableWithinAt 𝕜 (fun y => -f
 y) s x ↔ DifferentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `DifferentiableWithinAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.neg`：DifferentiableWithinAt.neg (h : Differentiab
leWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (-f) s x
-/
theorem differentiableWithinAt_fun_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/-
**differentiableWithinAt_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_neg_iff : DifferentiableWithinAt 𝕜 (-f) s x ↔ Diffe
rentiableWithinAt 𝕜 f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `DifferentiableWithinAt.neg`：DifferentiableWithinAt.neg (h : Differentiab
leWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (-f) s x
-/
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (-f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
/-
**DifferentiableAt.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (-f
) x
参数：h : DifferentiableAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.neg`：HasFDerivAt.neg (h : HasFDerivAt f f' x) : HasFDerivAt 
(-f) (-f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (-f) x :=
  h.hasFDerivAt.neg.differentiableAt

@[simp]
/-
**differentiableAt_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_fun_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ Diff
erentiableAt 𝕜 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `DifferentiableAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableAt.neg`：DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) 
: DifferentiableAt 𝕜 (-f) x
-/
theorem differentiableAt_fun_neg_iff :
    DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/-
**differentiableAt_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_neg_iff : DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 
f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `DifferentiableAt.neg`：DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) 
: DifferentiableAt 𝕜 (-f) x
-/
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (-f) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (-f
) s
参数：h : DifferentiableOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.neg`：DifferentiableWithinAt.neg (h : Differentiab
leWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (-f) s x
-/
theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (-f) s :=
  fun x hx => (h x hx).neg

@[simp]
/-
**differentiableOn_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_fun_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ Diff
erentiableOn 𝕜 f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `DifferentiableOn.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableOn.neg`：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) 
: DifferentiableOn 𝕜 (-f) s
-/
theorem differentiableOn_fun_neg_iff :
    DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/-
**differentiableOn_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_neg_iff : DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 
f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `DifferentiableOn.neg`：DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) 
: DifferentiableOn 𝕜 (-f) s
-/
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (-f) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩

@[to_fun (attr := fun_prop)]
/-
**Differentiable.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 (-f)
参数：h : Differentiable 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.neg`：DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) 
: DifferentiableAt 𝕜 (-f) x
-/
theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 (-f) := fun x =>
  (h x).neg

@[simp]
/-
**differentiable_fun_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_fun_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differenti
able 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Differentiable.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `Differentiable.neg`：Differentiable.neg (h : Differentiable 𝕜 f) : Differ
entiable 𝕜 (-f)
-/
theorem differentiable_fun_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.fun_neg, fun h => h.neg⟩

@[simp]
/-
**differentiable_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiable_neg_iff : Differentiable 𝕜 (-f) ↔ Differentiable 𝕜 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Differentiable.neg`：Differentiable.neg (h : Differentiable 𝕜 f) : Differ
entiable 𝕜 (-f)
-/
theorem differentiable_neg_iff : Differentiable 𝕜 (-f) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
/-
**fderivWithin_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (fu
n y => -f y) s x = -fderivWithin 𝕜 f s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.neg`：HasFDerivWithinAt.neg (h : HasFDerivWithinAt f f'
 s x) : HasFDerivWithinAt (-f) (-f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_zero_of_not_differentiableWithinAt`：fderivWithin_zero_of_no
t_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 
f s x = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x := by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · exact h.hasFDerivWithinAt.neg.fderivWithin hxs
  · rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa

/-- Version of `fderivWithin_fun_neg` where the function is written `-f` instead of `fun y ↦ -f y`.
For the special case `E = 𝕜` without a `UniqueDiffWithinAt 𝕜 s x` hypothesis, see
`fderivWithin_neg'`. -/
/-
**fderivWithin_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (-f) s 
x = -fderivWithin 𝕜 f s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_fun_neg`：fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s
 x) : fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x

--- 原说明 ---
Version of `fderivWithin_fun_neg` where the function is written `-f` instead of 
`fun y ↦ -f y`.
For the special case `E = 𝕜` without a `UniqueDiffWithinAt 𝕜 s x` hypothesis, se
e
`fderivWithin_neg'`.
-/
theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (-f) s x = -fderivWithin 𝕜 f s x :=
  fderivWithin_fun_neg hxs

@[simp]
/-
**fderiv_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_fun_neg`：fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s
 x) : fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_fun_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_fun_neg uniqueDiffWithinAt_univ]

/-- Version of `fderiv_neg` where the function is written `-f` instead of `fun y ↦ - f y`. -/
/-
**fderiv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_neg : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_fun_neg`：fderiv_fun_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 
f x

--- 原说明 ---
Version of `fderiv_neg` where the function is written `-f` instead of `fun y ↦ -
 f y`.
-/
theorem fderiv_neg : fderiv 𝕜 (-f) x = -fderiv 𝕜 f x :=
  fderiv_fun_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


@[to_fun]
/-
**HasFDerivAtFilter.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFil
ter g g' L) : HasFDerivAtFilter (f - g) (f' - g') L
参数：hf : HasFDerivAtFilter f f' L；hg : HasFDerivAtFilter g g' L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFDerivAtFilter.add`：HasFDerivAtFilter.add (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f + g) (f' + g') L
· 使用定理 `HasFDerivAtFilter.neg`：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f'
 L) : HasFDerivAtFilter (-f) (-f') L

--- 原说明 ---
### Derivative of the difference of two functions
-/
theorem HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f' L) (hg : HasFDerivAtFilter g g' L) :
    HasFDerivAtFilter (f - g) (f' - g') L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]
/-
**HasStrictFDerivAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDeri
vAt g g' x) : HasStrictFDerivAt (f - g) (f' - g') x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.sub`：HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f - g) (f' - g') L
-/
theorem HasStrictFDerivAt.sub (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (f - g) (f' - g') x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
/-
**HasFDerivWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWit
hinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.sub`：HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f - g) (f' - g') L
-/
theorem HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
/-
**HasFDerivAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) : HasF
DerivAt (f - g) (f' - g') x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.sub`：HasFDerivAtFilter.sub (hf : HasFDerivAtFilter f f
' L) (hg : HasFDerivAtFilter g g' L) : HasFDerivAtFilter (f - g) (f' - g') L
-/
theorem HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (f - g) (f' - g') x :=
  HasFDerivAtFilter.sub hf hg

@[to_fun (attr := fun_prop)]
/-
**DifferentiableWithinAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x) (hg : Dif
ferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f - g) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hg : DifferentiableWithinAt 𝕜 g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.sub`：HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (f - g) s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
/-
**DifferentiableAt.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 
𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.sub`：HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDer
ivAt g g' x) : HasFDerivAt (f - g) (f' - g') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).differentiableAt

@[to_fun (attr := simp)]
/-
**DifferentiableAt.add_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.add_iff_left (hg : DifferentiableAt 𝕜 g x) : Differentiab
leAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 f x
参数：hg : DifferentiableAt 𝕜 g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用定理 `DifferentiableAt.add`：DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x
-/
lemma DifferentiableAt.add_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 f x := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
/-
**DifferentiableAt.add_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.add_iff_right (hg : DifferentiableAt 𝕜 f x) : Differentia
bleAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 g x
参数：hg : DifferentiableAt 𝕜 f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `DifferentiableAt.add_iff_left`：DifferentiableAt.add_iff_left (hg : Diffe
rentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DifferentiableAt.add_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f + g) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
/-
**DifferentiableAt.sub_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sub_iff_left (hg : DifferentiableAt 𝕜 g x) : Differentiab
leAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 f x
参数：hg : DifferentiableAt 𝕜 g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DifferentiableAt.sub_iff_left (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
/-
**DifferentiableAt.sub_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sub_iff_right (hg : DifferentiableAt 𝕜 f x) : Differentia
bleAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 g x
参数：hg : DifferentiableAt 𝕜 f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DifferentiableAt.sub_iff_right (hg : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 g x := by
  simp only [sub_eq_add_neg, hg, add_iff_right, differentiableAt_neg_iff]

@[to_fun (attr := fun_prop)]
/-
**DifferentiableOn.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 
𝕜 g s) : DifferentiableOn 𝕜 (f - g) s
参数：hf : DifferentiableOn 𝕜 f s；hg : DifferentiableOn 𝕜 g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.sub`：DifferentiableWithinAt.sub (hf : Differentia
bleWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithi
nAt 𝕜 (f - g) s …
-/
theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s := fun x hx => (hf x hx).sub (hg x hx)

@[to_fun (attr := simp)]
/-
**DifferentiableOn.add_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.add_iff_left (hg : DifferentiableOn 𝕜 g s) : Differentiab
leOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 f s
参数：hg : DifferentiableOn 𝕜 g s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `DifferentiableOn.sub`：DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f - g) s
· 使用定理 `DifferentiableOn.add`：DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s)
 (hg : DifferentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f + g) s
-/
lemma DifferentiableOn.add_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 f s := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
/-
**DifferentiableOn.add_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.add_iff_right (hg : DifferentiableOn 𝕜 f s) : Differentia
bleOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 g s
参数：hg : DifferentiableOn 𝕜 f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `DifferentiableOn.add_iff_left`：DifferentiableOn.add_iff_left (hg : Diffe
rentiableOn 𝕜 g s) : DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 f s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DifferentiableOn.add_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f + g) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
/-
**DifferentiableOn.sub_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sub_iff_left (hg : DifferentiableOn 𝕜 g s) : Differentiab
leOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 f s
参数：hg : DifferentiableOn 𝕜 g s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DifferentiableOn.sub_iff_left (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
/-
**DifferentiableOn.sub_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sub_iff_right (hg : DifferentiableOn 𝕜 f s) : Differentia
bleOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 g s
参数：hg : DifferentiableOn 𝕜 f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma DifferentiableOn.sub_iff_right (hg : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (f - g) s ↔ DifferentiableOn 𝕜 g s := by
  simp only [sub_eq_add_neg, differentiableOn_neg_iff, hg, add_iff_right]

@[to_fun (attr := simp, fun_prop)]
/-
**Differentiable.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) : D
ifferentiable 𝕜 (f - g)
参数：hf : Differentiable 𝕜 f；hg : Differentiable 𝕜 g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
-/
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) := fun x => (hf x).sub (hg x)

@[to_fun (attr := simp)]
/-
**Differentiable.add_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Differentiable.add_iff_left (hg : Differentiable 𝕜 g) : Differentiable 𝕜 (
f + g) ↔ Differentiable 𝕜 f
参数：hg : Differentiable 𝕜 g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Differentiable.sub`：Differentiable.sub (hf : Differentiable 𝕜 f) (hg : D
ifferentiable 𝕜 g) : Differentiable 𝕜 (f - g)
· 使用定理 `Differentiable.add`：Differentiable.add (hf : Differentiable 𝕜 f) (hg : D
ifferentiable 𝕜 g) : Differentiable 𝕜 (f + g)
-/
lemma Differentiable.add_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 f := by
  refine ⟨fun h ↦ ?_, fun hf ↦ hf.add hg⟩
  simpa only [add_sub_cancel_right] using h.sub hg

@[to_fun (attr := simp)]
/-
**Differentiable.add_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Differentiable.add_iff_right (hg : Differentiable 𝕜 f) : Differentiable 𝕜 
(f + g) ↔ Differentiable 𝕜 g
参数：hg : Differentiable 𝕜 f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Differentiable.add_iff_left`：Differentiable.add_iff_left (hg : Different
iable 𝕜 g) : Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Differentiable.add_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f + g) ↔ Differentiable 𝕜 g := by
  simp only [add_comm f, hg.add_iff_left]

@[to_fun (attr := simp)]
/-
**Differentiable.sub_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Differentiable.sub_iff_left (hg : Differentiable 𝕜 g) : Differentiable 𝕜 (
f - g) ↔ Differentiable 𝕜 f
参数：hg : Differentiable 𝕜 g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Differentiable.sub_iff_left (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_left]

@[to_fun (attr := simp)]
/-
**Differentiable.sub_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Differentiable.sub_iff_right (hg : Differentiable 𝕜 f) : Differentiable 𝕜 
(f - g) ↔ Differentiable 𝕜 g
参数：hg : Differentiable 𝕜 f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Differentiable.sub_iff_right (hg : Differentiable 𝕜 f) :
    Differentiable 𝕜 (f - g) ↔ Differentiable 𝕜 g := by
  simp only [sub_eq_add_neg, differentiable_neg_iff, hg, add_iff_right]
/-
**fderivWithin_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : Differentiable
WithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderivWithin 𝕜 (fun y 
=> f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hf : DifferentiableWithinAt 𝕜 f s x；hg : Diffe
rentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.sub`：HasFDerivWithinAt.sub (hf : HasFDerivWithinAt f f
' s x) (hg : HasFDerivWithinAt g g' s x) : HasFDerivWithinAt (f - g) (f' - g') s
 x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.hasFDerivWithinAt.sub hg.hasFDerivWithinAt).fderivWithin hxs
/-
**fderivWithin_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWith
inAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderivWithin 𝕜 (f - g) s x
 = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；hf : DifferentiableWithinAt 𝕜 f s x；hg : Diffe
rentiableWithinAt 𝕜 g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderivWithin_fun_sub`：fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s
 x) (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) 
: fderivWi…
-/
theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (f - g) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  fderivWithin_fun_sub hxs hf hg
/-
**fderiv_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x)
 : fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.sub`：HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDer
ivAt g g' x) : HasFDerivAt (f - g) (f' - g') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
/-
**fderiv_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) : f
deriv 𝕜 (f - g) x = fderiv 𝕜 f x - fderiv 𝕜 g x
参数：hf : DifferentiableAt 𝕜 f x；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fderiv_fun_sub`：fderiv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : Diffe
rentiableAt 𝕜 g x) : fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g
 x
-/
theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (f - g) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  fderiv_fun_sub hf hg

@[simp]
/-
**hasFDerivAtFilter_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAtFilter_sub_const_iff (c : F) : HasFDerivAtFilter (f · - c) f' L
 ↔ HasFDerivAtFilter f f' L
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAtFilter_sub_const_iff (c : F) :
    HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L := by
  simp only [sub_eq_add_neg, hasFDerivAtFilter_add_const_iff]

alias ⟨_, HasFDerivAtFilter.sub_const⟩ := hasFDerivAtFilter_sub_const_iff

@[simp]
/-
**hasStrictFDerivAt_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_sub_const_iff (c : F) : HasStrictFDerivAt (f · - c) f' x
 ↔ HasStrictFDerivAt f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_sub_const_iff`：hasFDerivAtFilter_sub_const_iff (c : F)
 : HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasStrictFDerivAt_sub_const_iff (c : F) :
    HasStrictFDerivAt (f · - c) f' x ↔ HasStrictFDerivAt f f' x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasStrictFDerivAt.sub_const⟩ := hasStrictFDerivAt_sub_const_iff

@[simp]
/-
**hasFDerivWithinAt_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_sub_const_iff (c : F) : HasFDerivWithinAt (f · - c) f' s
 x ↔ HasFDerivWithinAt f f' s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_sub_const_iff`：hasFDerivAtFilter_sub_const_iff (c : F)
 : HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivWithinAt_sub_const_iff (c : F) :
    HasFDerivWithinAt (f · - c) f' s x ↔ HasFDerivWithinAt f f' s x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivWithinAt.sub_const⟩ := hasFDerivWithinAt_sub_const_iff

@[simp]
/-
**hasFDerivAt_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_sub_const_iff (c : F) : HasFDerivAt (f · - c) f' x ↔ HasFDeriv
At f f' x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAtFilter_sub_const_iff`：hasFDerivAtFilter_sub_const_iff (c : F)
 : HasFDerivAtFilter (f · - c) f' L ↔ HasFDerivAtFilter f f' L
-/
theorem hasFDerivAt_sub_const_iff (c : F) : HasFDerivAt (f · - c) f' x ↔ HasFDerivAt f f' x :=
  hasFDerivAtFilter_sub_const_iff c

@[fun_prop]
alias ⟨_, HasFDerivAt.sub_const⟩ := hasFDerivAt_sub_const_iff

@[fun_prop]
/-
**hasStrictFDerivAt_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasStrictFDerivAt_sub_const {x : F} (c : F) : HasStrictFDerivAt (· - c) (.
id 𝕜 F) x
参数：c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.sub_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type u_…
· 使用定理 `hasStrictFDerivAt_id`：hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt i
d (.id 𝕜 E) x
-/
theorem hasStrictFDerivAt_sub_const {x : F} (c : F) : HasStrictFDerivAt (· - c) (.id 𝕜 F) x :=
  (hasStrictFDerivAt_id x).sub_const c

@[fun_prop]
/-
**hasFDerivAt_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_sub_const {x : F} (c : F) : HasFDerivAt (· - c) (.id 𝕜 F) x
参数：c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.sub_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
-/
theorem hasFDerivAt_sub_const {x : F} (c : F) : HasFDerivAt (· - c) (.id 𝕜 F) x :=
  (hasFDerivAt_id x).sub_const c

@[fun_prop]
/-
**DifferentiableWithinAt.sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c 
: F) : DifferentiableWithinAt 𝕜 (fun y => f y - c) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivWithinAt.sub_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.hasFDerivWithinAt.sub_const c).differentiableWithinAt

@[simp]
/-
**differentiableWithinAt_sub_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_sub_const_iff (c : F) : DifferentiableWithinAt 𝕜 (f
un y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_sub_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]

@[fun_prop]
/-
**DifferentiableAt.sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) : Differe
ntiableAt 𝕜 (fun y => f y - c) x
参数：hf : DifferentiableAt 𝕜 f x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `HasFDerivAt.sub_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.hasFDerivAt.sub_const c).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) : Differe
ntiableOn 𝕜 (fun y => f y - c) s
参数：hf : DifferentiableOn 𝕜 f s；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.sub_const`：DifferentiableWithinAt.sub_const (hf :
 DifferentiableWithinAt 𝕜 f s x) (c : F) : DifferentiableWithinAt 𝕜 (fun y => f 
y - c) s x
-/
theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c

@[fun_prop]
/-
**Differentiable.sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) : Differentiabl
e 𝕜 fun y => f y - c
参数：hf : Differentiable 𝕜 f；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
-/
theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c
/-
**fderivWithin_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_sub_const (c : F) : fderivWithin 𝕜 (fun y => f y - c) s x = f
derivWithin 𝕜 f s x
参数：c : F。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `fderivWithin_add_const`：fderivWithin_add_const (c : F) : fderivWithin 𝕜 
(fun y => f y + c) s x = fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_sub_const (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const]
/-
**fderiv_sub_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x
参数：c : F。
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `fderiv_add_const`：fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c)
 x = fderiv 𝕜 f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]
/-
**HasFDerivAtFilter.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' L) (c : F) : HasF
DerivAtFilter (fun x => c - f x) (-f') L
参数：hf : HasFDerivAtFilter f f' L；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `HasFDerivAtFilter.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {F : Type u_…
· 使用定理 `HasFDerivAtFilter.neg`：HasFDerivAtFilter.neg (h : HasFDerivAtFilter f f'
 L) : HasFDerivAtFilter (-f) (-f') L
-/
theorem HasFDerivAtFilter.const_sub (hf : HasFDerivAtFilter f f' L) (c : F) :
    HasFDerivAtFilter (fun x => c - f x) (-f') L := by
  simpa only [sub_eq_add_neg] using! hf.neg.const_add c

@[fun_prop]
/-
**HasStrictFDerivAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) : HasS
trictFDerivAt (fun x => c - f x) (-f') x
参数：hf : HasStrictFDerivAt f f' x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.const_sub`：HasFDerivAtFilter.const_sub (hf : HasFDeriv
AtFilter f f' L) (c : F) : HasFDerivAtFilter (fun x => c - f x) (-f') L
-/
theorem HasStrictFDerivAt.const_sub (hf : HasStrictFDerivAt f f' x) (c : F) :
    HasStrictFDerivAt (fun x => c - f x) (-f') x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
/-
**HasFDerivWithinAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.const_sub (hf : HasFDerivWithinAt f f' s x) (c : F) : Ha
sFDerivWithinAt (fun x => c - f x) (-f') s x
参数：hf : HasFDerivWithinAt f f' s x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.const_sub`：HasFDerivAtFilter.const_sub (hf : HasFDeriv
AtFilter f f' L) (c : F) : HasFDerivAtFilter (fun x => c - f x) (-f') L
-/
theorem HasFDerivWithinAt.const_sub (hf : HasFDerivWithinAt f f' s x) (c : F) :
    HasFDerivWithinAt (fun x => c - f x) (-f') s x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
/-
**HasFDerivAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (c : F) : HasFDerivAt (fun
 x => c - f x) (-f') x
参数：hf : HasFDerivAt f f' x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAtFilter.const_sub`：HasFDerivAtFilter.const_sub (hf : HasFDeriv
AtFilter f f' L) (c : F) : HasFDerivAtFilter (fun x => c - f x) (-f') L
-/
theorem HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (c : F) :
    HasFDerivAt (fun x => c - f x) (-f') x :=
  HasFDerivAtFilter.const_sub hf c

@[fun_prop]
/-
**DifferentiableWithinAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c 
: F) : DifferentiableWithinAt 𝕜 (fun y => c - f y) s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivWithinAt.const_sub`：HasFDerivWithinAt.const_sub (hf : HasFDeriv
WithinAt f f' s x) (c : F) : HasFDerivWithinAt (fun x => c - f x) (-f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.hasFDerivWithinAt.const_sub c).differentiableWithinAt

@[simp]
/-
**differentiableWithinAt_const_sub_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_const_sub_iff (c : F) : DifferentiableWithinAt 𝕜 (f
un y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x
参数：c : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_const_sub_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [sub_eq_add_neg]

@[fun_prop]
/-
**DifferentiableAt.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) : Differe
ntiableAt 𝕜 (fun y => c - f y) x
参数：hf : DifferentiableAt 𝕜 f x；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFDerivAt.const_sub`：HasFDerivAt.const_sub (hf : HasFDerivAt f f' x) (
c : F) : HasFDerivAt (fun x => c - f x) (-f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.hasFDerivAt.const_sub c).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) : Differe
ntiableOn 𝕜 (fun y => c - f y) s
参数：hf : DifferentiableOn 𝕜 f s；c : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.const_sub`：DifferentiableWithinAt.const_sub (hf :
 DifferentiableWithinAt 𝕜 f s x) (c : F) : DifferentiableWithinAt 𝕜 (fun y => c 
- f y) s x
-/
theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c

@[fun_prop]
/-
**Differentiable.const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) : Differentiabl
e 𝕜 fun y => c - f y
参数：hf : Differentiable 𝕜 f；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.const_sub`：DifferentiableAt.const_sub (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x
-/
theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c
/-
**fderivWithin_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) : fderivWi
thin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x
参数：hxs : UniqueDiffWithinAt 𝕜 s x；c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `fderivWithin_const_add`：fderivWithin_const_add (c : F) : fderivWithin 𝕜 
(fun y => c + f y) s x = fderivWithin 𝕜 f s x
· 使用定理 `fderivWithin_fun_neg`：fderivWithin_fun_neg (hxs : UniqueDiffWithinAt 𝕜 s
 x) : fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_fun_neg, hxs]
/-
**fderiv_const_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x
参数：c : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_const_sub`：fderivWithin_const_sub (hxs : UniqueDiffWithinAt
 𝕜 s x) (c : F) : fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAt_univ]

end Sub

section CompAdd

/-! ### Derivative of the composition with a translation -/

open scoped Pointwise Topology

/-
**hasFDerivWithinAt_comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_comp_add_left (a : E) : HasFDerivWithinAt (fun x => f (a
 + x)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (a + x)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_inf`：map_inf {f g : Filter α} {m : α -> β} (h : Injective m) 
: map m (f ⊓ g) = map m f ⊓ map m g
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add_left_nhds`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : 
AddGroup G] [IsTopologicalAddGroup G] (x y : G),   Filter.map (fun x_1 => x + x_
1) (nhd…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_sub_add_left_eq_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c + a - (c + b) = a - b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivWithinAt_comp_add_left (a : E) :
    HasFDerivWithinAt (fun x ↦ f (a + x)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (a + x) := by
  have : map (a + ·) (𝓝[s] x) = 𝓝[a +ᵥ s] (a + x) := by
    simp only [nhdsWithin, Filter.map_inf (add_right_injective a)]
    simp [← Set.image_vadd]
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, ← this, Function.comp_def]
/-
**differentiableWithinAt_comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_comp_add_left (a : E) : DifferentiableWithinAt 𝕜 (f
un x => f (a + x)) s x ↔ DifferentiableWithinAt 𝕜 f (a +ᵥ s) (a + x)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_comp_add_left (a : E) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f (a + x)) s x ↔
      DifferentiableWithinAt 𝕜 f (a +ᵥ s) (a + x) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_left]
/-
**fderivWithin_comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_add_left (a : E) : fderivWithin 𝕜 (fun x => f (a + x)) s
 x = fderivWithin 𝕜 f (a +ᵥ s) (a + x)
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_comp_add_left (a : E) :
    fderivWithin 𝕜 (fun x ↦ f (a + x)) s x = fderivWithin 𝕜 f (a +ᵥ s) (a + x) := by
  classical
  simp only [fderivWithin, hasFDerivWithinAt_comp_add_left, differentiableWithinAt_comp_add_left]
/-
**hasFDerivWithinAt_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_comp_add_right (a : E) : HasFDerivWithinAt (fun x => f (
x + a)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (x + a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `hasFDerivWithinAt_comp_add_left`：hasFDerivWithinAt_comp_add_left (a : E)
 : HasFDerivWithinAt (fun x => f (a + x)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ 
s) (a + x)
-/
theorem hasFDerivWithinAt_comp_add_right (a : E) :
    HasFDerivWithinAt (fun x ↦ f (x + a)) f' s x ↔ HasFDerivWithinAt f f' (a +ᵥ s) (x + a) := by
  simpa only [add_comm a] using hasFDerivWithinAt_comp_add_left a
/-
**differentiableWithinAt_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_comp_add_right (a : E) : DifferentiableWithinAt 𝕜 (
fun x => f (x + a)) s x ↔ DifferentiableWithinAt 𝕜 f (a +ᵥ s) (x + a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_comp_add_right (a : E) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f (x + a)) s x ↔
      DifferentiableWithinAt 𝕜 f (a +ᵥ s) (x + a) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_add_right]
/-
**fderivWithin_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_add_right (a : E) : fderivWithin 𝕜 (fun x => f (x + a)) 
s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a)
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `fderivWithin_comp_add_left`：fderivWithin_comp_add_left (a : E) : fderivW
ithin 𝕜 (fun x => f (a + x)) s x = fderivWithin 𝕜 f (a +ᵥ s) (a + x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderivWithin_comp_add_right (a : E) :
    fderivWithin 𝕜 (fun x ↦ f (x + a)) s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a) := by
  simp only [add_comm _ a, fderivWithin_comp_add_left]
/-
**hasFDerivAt_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_comp_add_right (a : E) : HasFDerivAt (fun x => f (x + a)) f' x
 ↔ HasFDerivAt f f' (x + a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.vadd_set_univ`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α] [
inst_1 : AddAction α β] {a : α}, a +ᵥ Set.univ = Set.univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAt_comp_add_right (a : E) :
    HasFDerivAt (fun x ↦ f (x + a)) f' x ↔ HasFDerivAt f f' (x + a) := by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_add_right]
/-
**differentiableAt_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_add_right (a : E) : DifferentiableAt 𝕜 (fun x => f (
x + a)) x ↔ DifferentiableAt 𝕜 f (x + a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableAt_comp_add_right (a : E) :
    DifferentiableAt 𝕜 (fun x ↦ f (x + a)) x ↔ DifferentiableAt 𝕜 f (x + a) := by
  simp [DifferentiableAt, hasFDerivAt_comp_add_right]
/-
**fderiv_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_add_right (a : E) : fderiv 𝕜 (fun x => f (x + a)) x = fderiv 𝕜
 f (x + a)
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_comp_add_right`：fderivWithin_comp_add_right (a : E) : fderi
vWithin 𝕜 (fun x => f (x + a)) s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.vadd_set_univ`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α] [
inst_1 : AddAction α β] {a : α}, a +ᵥ Set.univ = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_comp_add_right (a : E) :
    fderiv 𝕜 (fun x ↦ f (x + a)) x = fderiv 𝕜 f (x + a) := by
  simp [← fderivWithin_univ, fderivWithin_comp_add_right]
/-
**hasFDerivAt_comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_comp_add_left (a : E) : HasFDerivAt (fun x => f (a + x)) f' x 
↔ HasFDerivAt f f' (a + x)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `hasFDerivAt_comp_add_right`：hasFDerivAt_comp_add_right (a : E) : HasFDer
ivAt (fun x => f (x + a)) f' x ↔ HasFDerivAt f f' (x + a)
-/
theorem hasFDerivAt_comp_add_left (a : E) :
    HasFDerivAt (fun x ↦ f (a + x)) f' x ↔ HasFDerivAt f f' (a + x) := by
  simpa [add_comm a] using hasFDerivAt_comp_add_right a
/-
**differentiableAt_comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_add_left (a : E) : DifferentiableAt 𝕜 (fun x => f (a
 + x)) x ↔ DifferentiableAt 𝕜 f (a + x)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableAt_comp_add_left (a : E) :
    DifferentiableAt 𝕜 (fun x ↦ f (a + x)) x ↔ DifferentiableAt 𝕜 f (a + x) := by
  simp [DifferentiableAt, hasFDerivAt_comp_add_left]
/-
**fderiv_comp_add_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_add_left (a : E) : fderiv 𝕜 (fun x => f (a + x)) x = fderiv 𝕜 
f (a + x)
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `fderiv_comp_add_right`：fderiv_comp_add_right (a : E) : fderiv 𝕜 (fun x =
> f (x + a)) x = fderiv 𝕜 f (x + a)
-/
theorem fderiv_comp_add_left (a : E) :
    fderiv 𝕜 (fun x ↦ f (a + x)) x = fderiv 𝕜 f (a + x) := by
  simpa [add_comm a] using fderiv_comp_add_right a
/-
**hasFDerivWithinAt_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_comp_sub (a : E) : HasFDerivWithinAt (fun x => f (x - a)
) f' s x ↔ HasFDerivWithinAt f f' (-a +ᵥ s) (x - a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `hasFDerivWithinAt_comp_add_right`：hasFDerivWithinAt_comp_add_right (a : 
E) : HasFDerivWithinAt (fun x => f (x + a)) f' s x ↔ HasFDerivWithinAt f f' (a +
ᵥ s) (x + a)
-/
theorem hasFDerivWithinAt_comp_sub (a : E) :
    HasFDerivWithinAt (fun x ↦ f (x - a)) f' s x ↔ HasFDerivWithinAt f f' (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using hasFDerivWithinAt_comp_add_right (-a)
/-
**differentiableWithinAt_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_comp_sub (a : E) : DifferentiableWithinAt 𝕜 (fun x 
=> f (x - a)) s x ↔ DifferentiableWithinAt 𝕜 f (-a +ᵥ s) (x - a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableWithinAt_comp_sub (a : E) :
    DifferentiableWithinAt 𝕜 (fun x ↦ f (x - a)) s x ↔
      DifferentiableWithinAt 𝕜 f (-a +ᵥ s) (x - a) := by
  simp [DifferentiableWithinAt, hasFDerivWithinAt_comp_sub]
/-
**fderivWithin_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_comp_sub (a : E) : fderivWithin 𝕜 (fun x => f (x - a)) s x = 
fderivWithin 𝕜 f (-a +ᵥ s) (x - a)
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `fderivWithin_comp_add_right`：fderivWithin_comp_add_right (a : E) : fderi
vWithin 𝕜 (fun x => f (x + a)) s x = fderivWithin 𝕜 f (a +ᵥ s) (x + a)
-/
theorem fderivWithin_comp_sub (a : E) :
    fderivWithin 𝕜 (fun x ↦ f (x - a)) s x = fderivWithin 𝕜 f (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using fderivWithin_comp_add_right (-a)
/-
**hasFDerivAt_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_comp_sub (a : E) : HasFDerivAt (fun x => f (x - a)) f' x ↔ Has
FDerivAt f f' (x - a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.vadd_set_univ`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α] [
inst_1 : AddAction α β] {a : α}, a +ᵥ Set.univ = Set.univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasFDerivAt_comp_sub (a : E) :
    HasFDerivAt (fun x ↦ f (x - a)) f' x ↔ HasFDerivAt f f' (x - a) := by
  simp [← hasFDerivWithinAt_univ, hasFDerivWithinAt_comp_sub]
/-
**differentiableAt_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_comp_sub (a : E) : DifferentiableAt 𝕜 (fun x => f (x - a)
) x ↔ DifferentiableAt 𝕜 f (x - a)
参数：a : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableAt_comp_sub (a : E) :
    DifferentiableAt 𝕜 (fun x ↦ f (x - a)) x ↔ DifferentiableAt 𝕜 f (x - a) := by
  simp [DifferentiableAt, hasFDerivAt_comp_sub]
/-
**fderiv_comp_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_comp_sub (a : E) : fderiv 𝕜 (fun x => f (x - a)) x = fderiv 𝕜 f (x 
- a)
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_comp_sub`：fderivWithin_comp_sub (a : E) : fderivWithin 𝕜 (f
un x => f (x - a)) s x = fderivWithin 𝕜 f (-a +ᵥ s) (x - a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.vadd_set_univ`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup α] [
inst_1 : AddAction α β] {a : α}, a +ᵥ Set.univ = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fderiv_comp_sub (a : E) :
    fderiv 𝕜 (fun x ↦ f (x - a)) x = fderiv 𝕜 f (x - a) := by
  simp [← fderivWithin_univ, fderivWithin_comp_sub]

end CompAdd

end

