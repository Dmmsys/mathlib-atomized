/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Complex.Basic

/-! # Real differentiability of complex-differentiable functions

`HasDerivAt.real_of_complex` expresses that, if a function on `ℂ` is differentiable (over `ℂ`),
then its restriction to `ℝ` is differentiable over `ℝ`, with derivative the real part of the
complex derivative.
-/

public section

assert_not_exists IsConformalMap Conformal

section RealDerivOfComplex

/-! ### Differentiability of the restriction to `ℝ` of complex functions -/

open Complex

variable {e : ℂ → ℂ} {e' : ℂ} {z : ℝ}

/-- If a complex function is differentiable at a real point, then the induced real function is also
differentiable at this point, with a derivative equal to the real part of the complex derivative. -/
/-
**HasStrictDerivAt.real_of_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) : HasStrict
DerivAt (fun x : Real => (e x).re) e'.re z
参数：h : HasStrictDerivAt e e' z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousLinearMap.hasStrictFDerivAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.M
odule 𝕜 E] [inst_3 : Topolo…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasStrictFDerivAt.restrictScalars`：HasStrictFDerivAt.restrictScalars (h 
: HasStrictFDerivAt f f' x) : HasStrictFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasStrictFDerivAt.hasStrictDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…

--- 原说明 ---
If a complex function is differentiable at a real point, then the induced real f
unction is also
differentiable at this point, with a derivative equal to the real part of the co
mplex derivative.
-/
theorem HasStrictDerivAt.real_of_complex (h : HasStrictDerivAt e e' z) :
    HasStrictDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasStrictFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasStrictFDerivAt
  have B :
    HasStrictFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasStrictFDerivAt.restrictScalars ℝ
  have C : HasStrictFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasStrictFDerivAt
  simpa using (C.comp z (B.comp z A)).hasStrictDerivAt

/-- If a complex function `e` is differentiable at a real point, then the function `ℝ → ℝ` given by
the real part of `e` is also differentiable at this point, with a derivative equal to the real part
of the complex derivative. -/
/-
**HasDerivAt.real_of_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.real_of_complex (h : HasDerivAt e e' z) : HasDerivAt (fun x : R
eal => (e x).re) e'.re z
参数：h : HasDerivAt e e' z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x

--- 原说明 ---
If a complex function `e` is differentiable at a real point, then the function `
ℝ → ℝ` given by
the real part of `e` is also differentiable at this point, with a derivative equ
al to the real part
of the complex derivative.
-/
theorem HasDerivAt.real_of_complex (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).re) e'.re z := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
    HasFDerivAt e ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt re reCLM (e (ofRealCLM z)) := reCLM.hasFDerivAt
  simpa using! (C.comp z (B.comp z A)).hasDerivAt
/-
**ContDiffAt.real_of_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.real_of_complex {n : WithTop Nat∞} (h : ContDiffAt Complex n e 
z) : ContDiffAt Real n (fun x : Real => (e x).re) z
参数：h : ContDiffAt Complex n e z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `ContDiffAt.restrict_scalars`：ContDiffAt.restrict_scalars (h : ContDiffAt
 𝕜' n f x) : ContDiffAt 𝕜 n f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
-/
theorem ContDiffAt.real_of_complex {n : WithTop ℕ∞} (h : ContDiffAt ℂ n e z) :
    ContDiffAt ℝ n (fun x : ℝ => (e x).re) z := by
  have A : ContDiffAt ℝ n ((↑) : ℝ → ℂ) z := ofRealCLM.contDiff.contDiffAt
  have B : ContDiffAt ℝ n e z := h.restrict_scalars ℝ
  have C : ContDiffAt ℝ n re (e z) := reCLM.contDiff.contDiffAt
  exact C.comp z (B.comp z A)
/-
**ContDiff.real_of_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.real_of_complex {n : WithTop Nat∞} (h : ContDiff Complex n e) : C
ontDiff Real n fun x : Real => (e x).re
参数：h : ContDiff Complex n e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.real_of_complex`：ContDiffAt.real_of_complex {n : WithTop Nat∞
} (h : ContDiffAt Complex n e z) : ContDiffAt Real n (fun x : Real => (e x).re) 
z
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.real_of_complex {n : WithTop ℕ∞} (h : ContDiff ℂ n e) :
    ContDiff ℝ n fun x : ℝ => (e x).re :=
  contDiff_iff_contDiffAt.2 fun _ => h.contDiffAt.real_of_complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-
**HasStrictDerivAt.complexToReal_fderiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.complexToReal_fderiv' {f : Complex -> E} {x : Complex} {f
' : E} (h : HasStrictDerivAt f f' x) : HasStrictFDerivAt f (reCLM.smulRight f' +
 I • imCLM.smulRight f') x
参数：h : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
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
· 使用定理 `Complex.restrictScalars_toSpanSingleton'`：∀ {E : Type u_1} [inst : Semin
ormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] (x : E),   ContinuousLinearMap.r
estrictScalars ℝ (ContinuousLi…
· 使用定理 `HasStrictFDerivAt.restrictScalars`：HasStrictFDerivAt.restrictScalars (h 
: HasStrictFDerivAt f f' x) : HasStrictFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E}
    (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasStrictFDerivAt.restrictScalars ℝ
/-
**HasDerivAt.complexToReal_fderiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.complexToReal_fderiv' {f : Complex -> E} {x : Complex} {f' : E}
 (h : HasDerivAt f f' x) : HasFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRig
ht f') x
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
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
· 使用定理 `Complex.restrictScalars_toSpanSingleton'`：∀ {E : Type u_1} [inst : Semin
ormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] (x : E),   ContinuousLinearMap.r
estrictScalars ℝ (ContinuousLi…
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.complexToReal_fderiv' {f : ℂ → E} {x : ℂ} {f' : E} (h : HasDerivAt f f' x) :
    HasFDerivAt f (reCLM.smulRight f' + I • imCLM.smulRight f') x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivAt.restrictScalars ℝ
/-
**HasDerivWithinAt.complexToReal_fderiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.complexToReal_fderiv' {f : Complex -> E} {s : Set Complex
} {x : Complex} {f' : E} (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (
reCLM.smulRight f' + I • imCLM.smulRight f') s x
参数：h : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
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
· 使用定理 `Complex.restrictScalars_toSpanSingleton'`：∀ {E : Type u_1} [inst : Semin
ormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] (x : E),   ContinuousLinearMap.r
estrictScalars ℝ (ContinuousLi…
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.complexToReal_fderiv' {f : ℂ → E} {s : Set ℂ} {x : ℂ} {f' : E}
    (h : HasDerivWithinAt f f' s x) :
    HasFDerivWithinAt f (reCLM.smulRight f' + I • imCLM.smulRight f') s x := by
  simpa only [Complex.restrictScalars_toSpanSingleton'] using h.hasFDerivWithinAt.restrictScalars ℝ
/-
**HasStrictDerivAt.complexToReal_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.complexToReal_fderiv {f : Complex -> Complex} {f' x : Com
plex} (h : HasStrictDerivAt f f' x) : HasStrictFDerivAt f (f' • (1 : Complex ->L
[Real] Complex)) x
参数：h : HasStrictDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.restrictScalars_toSpanSingleton`：∀ (x : ℂ), ContinuousLinearMap.
restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ x) = x • 1
· 使用定理 `HasStrictFDerivAt.restrictScalars`：HasStrictFDerivAt.restrictScalars (h 
: HasStrictFDerivAt f f' x) : HasStrictFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasStrictDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasStrictDerivAt f f' x) :
    HasStrictFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasStrictFDerivAt.restrictScalars ℝ
/-
**HasDerivAt.complexToReal_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.complexToReal_fderiv {f : Complex -> Complex} {f' x : Complex} 
(h : HasDerivAt f f' x) : HasFDerivAt f (f' • (1 : Complex ->L[Real] Complex)) x
参数：h : HasDerivAt f f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.restrictScalars_toSpanSingleton`：∀ (x : ℂ), ContinuousLinearMap.
restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ x) = x • 1
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.complexToReal_fderiv {f : ℂ → ℂ} {f' x : ℂ} (h : HasDerivAt f f' x) :
    HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivAt.restrictScalars ℝ
/-
**HasDerivWithinAt.complexToReal_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.complexToReal_fderiv {f : Complex -> Complex} {s : Set Co
mplex} {f' x : Complex} (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f
' • (1 : Complex ->L[Real] Complex)) s x
参数：h : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.restrictScalars_toSpanSingleton`：∀ (x : ℂ), ContinuousLinearMap.
restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ x) = x • 1
· 使用定理 `HasFDerivWithinAt.restrictScalars`：HasFDerivWithinAt.restrictScalars (h 
: HasFDerivWithinAt f f' s x) : HasFDerivWithinAt f (f'.restrictScalars 𝕜) s x
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.complexToReal_fderiv {f : ℂ → ℂ} {s : Set ℂ} {f' x : ℂ}
    (h : HasDerivWithinAt f f' s x) : HasFDerivWithinAt f (f' • (1 : ℂ →L[ℝ] ℂ)) s x := by
  simpa only [Complex.restrictScalars_toSpanSingleton] using h.hasFDerivWithinAt.restrictScalars ℝ

/-- If a complex function `e` is differentiable at a real point, then its restriction to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative. -/
/-
**HasDerivAt.comp_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : Rea
l => e ↑y) e' z
参数：hf : HasDerivAt e e' ↑z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `ContinuousLinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜
 F] {x : 𝕜} (e : 𝕜 →…

--- 原说明 ---
If a complex function `e` is differentiable at a real point, then its restrictio
n to `ℝ` is
differentiable there as a function `ℝ → ℂ`, with the same derivative.
-/
theorem HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z) : HasDerivAt (fun y : ℝ => e ↑y) e' z := by
  simpa only [ofRealCLM_apply, ofReal_one, mul_one] using! hf.comp z ofRealCLM.hasDerivAt

/-- If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is also
differentiable as a function `ℝ → ℂ`. -/
/-
**HasDerivAt.ofReal_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.ofReal_comp {f : Real -> Real} {u : Real} (hf : HasDerivAt f u 
z) : HasDerivAt (fun y : Real => ↑(f y) : Real -> Complex) u z
参数：hf : HasDerivAt f u z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `ContinuousLinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNorme
dField 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜
 F] {x : 𝕜} (e : 𝕜 →…

--- 原说明 ---
If a function `f : ℝ → ℝ` is differentiable at a (real) point `x`, then it is al
so
differentiable as a function `ℝ → ℂ`.
-/
theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z := by
  simpa only [ofRealCLM_apply, ofReal_one, real_smul, mul_one] using!
    ofRealCLM.hasDerivAt.scomp z hf
/-
**HasDerivWithinAt.ofReal_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.ofReal_comp {f : Real -> Real} {s : Set Real} {u : Real} 
(hf : HasDerivWithinAt f u s z) : HasDerivWithinAt (fun y : Real => ↑(f y) : Rea
l -> Complex) u s z
参数：hf : HasDerivWithinAt f u s z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivAt.comp_hasDerivWithinAt`：HasFDerivAt.comp_hasDerivWithinAt (hl
 : HasFDerivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
l ∘ f) (l' f') s x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem HasDerivWithinAt.ofReal_comp {f : ℝ → ℝ} {s : Set ℝ} {u : ℝ}
    (hf : HasDerivWithinAt f u s z) : HasDerivWithinAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u s z := by
  simpa only [Function.comp_apply, ofRealCLM_apply] using!
    ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt z hf

@[fun_prop]
/-
**Complex.differentiable_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.differentiable_re : Differentiable Real Complex.re
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
lemma Complex.differentiable_re : Differentiable ℝ Complex.re := reCLM.differentiable

@[fun_prop]
/-
**Complex.differentiable_im** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.differentiable_im : Differentiable Real Complex.im
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
lemma Complex.differentiable_im : Differentiable ℝ Complex.im := imCLM.differentiable

@[fun_prop]
/-
**Complex.differentiable_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.differentiable_ofReal : Differentiable Real Complex.ofReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
-/
lemma Complex.differentiable_ofReal : Differentiable ℝ Complex.ofReal := ofRealCLM.differentiable

open ComplexConjugate in
@[fun_prop]
/-
**Complex.differentiable_conj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Complex.differentiable_conj : Differentiable Real (conj : Complex -> Compl
ex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.differentiable`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
lemma Complex.differentiable_conj : Differentiable ℝ (conj : ℂ → ℂ) := conjCLE.differentiable

variable {f : ℂ → E} {s : Set ℂ} {z : ℂ}

@[fun_prop]
/-
**Differentiable.real_of_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Differentiable.real_of_complex (hf : Differentiable Complex f) : Different
iable Real f
参数：hf : Differentiable Complex f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.restrictScalars`：Differentiable.restrictScalars (h : Diff
erentiable 𝕜' f) : Differentiable 𝕜 f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma Differentiable.real_of_complex (hf : Differentiable ℂ f) : Differentiable ℝ f :=
  hf.restrictScalars (𝕜 := ℝ)

@[fun_prop]
/-
**DifferentiableAt.real_of_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableAt.real_of_complex (hf : DifferentiableAt Complex f z) : Dif
ferentiableAt Real f z
参数：hf : DifferentiableAt Complex f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.restrictScalars`：DifferentiableAt.restrictScalars (h : 
DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma DifferentiableAt.real_of_complex (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℝ f z :=
  hf.restrictScalars (𝕜 := ℝ)

@[fun_prop]
/-
**DifferentiableWithinAt.real_of_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.real_of_complex (hf : DifferentiableWithinAt Comple
x f s z) : DifferentiableWithinAt Real f s z
参数：hf : DifferentiableWithinAt Complex f s z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.restrictScalars`：DifferentiableWithinAt.restrictS
calars (h : DifferentiableWithinAt 𝕜' f s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma DifferentiableWithinAt.real_of_complex (hf : DifferentiableWithinAt ℂ f s z) :
    DifferentiableWithinAt ℝ f s z :=
  hf.restrictScalars (𝕜 := ℝ)

@[fun_prop]
/-
**DifferentiableOn.real_of_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：DifferentiableOn.real_of_complex (hf : DifferentiableOn Complex f s) : Dif
ferentiableOn Real f s
参数：hf : DifferentiableOn Complex f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.restrictScalars`：DifferentiableOn.restrictScalars (h : 
DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma DifferentiableOn.real_of_complex (hf : DifferentiableOn ℂ f s) : DifferentiableOn ℝ f s :=
  hf.restrictScalars (𝕜 := ℝ)

end RealDerivOfComplex

