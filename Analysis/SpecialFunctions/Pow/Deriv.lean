/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/

public section


noncomputable section

open scoped Real Topology NNReal ENNReal
open Filter

namespace Complex

/-
**Complex.hasStrictFDerivAt_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictFDerivAt_cpow {p : Complex × Complex} (hp : p.1 in slitPlane) : H
asStrictFDerivAt (fun x : Complex × Complex => x.1 ^ x.2) ((p.2 * p.1 ^ (p.2 - 1
)) • ContinuousLinearMap.fst Complex Complex Complex + (p.1 ^ p.2 * log p.1) • C
ontinuousLinearMap.snd Complex Complex Complex) p
参数：hp : p.1 in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.slitPlane_ne_zero`：∀ {z : ℂ}, z ∈ Complex.slitPlane → z ≠ 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.cpow_sub`：cpow_sub {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `Complex.cpow_one`：cpow_one (x : Complex) : x ^ (1 : Complex) = x
· 使用定理 `mul_div_left_comm`：mul_div_left_comm : a * (b / c) = b * (a / c)
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `HasStrictFDerivAt.congr_of_eventuallyEq`：HasStrictFDerivAt.congr_of_even
tuallyEq (h : HasStrictFDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt 
f₁ f' x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
（共 37 条，此处仅展示前 30 条）
-/
theorem hasStrictFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
  have A : p.1 ≠ 0 := slitPlane_ne_zero hp
  have : (fun x : ℂ × ℂ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A, cpow_one, mul_div_left_comm, mul_smul, mul_smul]
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm, smul_add] using!
    ((hasStrictFDerivAt_fst.clog hp).mul hasStrictFDerivAt_snd).cexp
/-
**Complex.hasStrictFDerivAt_cpow'** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictFDerivAt_cpow' {x y : Complex} (hp : x in slitPlane) : HasStrictF
DerivAt (fun x : Complex × Complex => x.1 ^ x.2) ((y * x ^ (y - 1)) • Continuous
LinearMap.fst Complex Complex Complex + (x ^ y * log x) • ContinuousLinearMap.sn
d Complex Complex Complex) (x, y)
参数：hp : x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.hasStrictFDerivAt_cpow`：hasStrictFDerivAt_cpow {p : Complex × Co
mplex} (hp : p.1 in slitPlane) : HasStrictFDerivAt (fun x : Complex × Complex =>
 x.1 ^ x.2) ((p.2 * …
-/
theorem hasStrictFDerivAt_cpow' {x y : ℂ} (hp : x ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (x ^ y * log x) • ContinuousLinearMap.snd ℂ ℂ ℂ) (x, y) :=
  @hasStrictFDerivAt_cpow (x, y) hp
/-
**Complex.hasStrictDerivAt_const_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasStrictDerivAt_const_cpow {x y : Complex} (h : x != 0 ∨ y != 0) : HasStr
ictDerivAt (fun y => x ^ y) (x ^ y * log x) y
参数：h : x != 0 ∨ y != 0。
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
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Or.neg_resolve_left`：∀ {a b : Prop}, ¬a ∨ b → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `HasStrictDerivAt.congr_of_eventuallyEq`：HasStrictDerivAt.congr_of_eventu
allyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictDerivAt f₁ f
' x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.zero_cpow`：zero_cpow {x : Complex} (h : x != 0) : (0 : Complex) 
^ x = 0
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_def_of_ne_zero`：cpow_def_of_ne_zero {x : Complex} (hx : x !
= 0) (y : Complex) : x ^ y = exp (log x * y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasStrictDerivAt.cexp`：HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f'
 x) : HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x
· 使用定理 `HasStrictDerivAt.const_mul`：HasStrictDerivAt.const_mul (c : 𝔸) (hd : Has
StrictDerivAt d d' x) : HasStrictDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
-/
theorem hasStrictDerivAt_const_cpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
    HasStrictDerivAt (fun y => x ^ y) (x ^ y * log x) y := by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero, mul_zero]
    refine (hasStrictDerivAt_const y 0).congr_of_eventuallyEq ?_
    exact (isOpen_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  · simpa only [cpow_def_of_ne_zero hx, mul_one] using!
      ((hasStrictDerivAt_id y).const_mul (log x)).cexp
/-
**Complex.hasFDerivAt_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：hasFDerivAt_cpow {p : Complex × Complex} (hp : p.1 in slitPlane) : HasFDer
ivAt (fun x : Complex × Complex => x.1 ^ x.2) ((p.2 * p.1 ^ (p.2 - 1)) • Continu
ousLinearMap.fst Complex Complex Complex + (p.1 ^ p.2 * log p.1) • ContinuousLin
earMap.snd Complex Complex Complex) p
参数：hp : p.1 in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Complex.hasStrictFDerivAt_cpow`：hasStrictFDerivAt_cpow {p : Complex × Co
mplex} (hp : p.1 in slitPlane) : HasStrictFDerivAt (fun x : Complex × Complex =>
 x.1 ^ x.2) ((p.2 * …
-/
theorem hasFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
  (hasStrictFDerivAt_cpow hp).hasFDerivAt

end Complex

section fderiv

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {f' g' : StrongDual ℂ E}
  {x : E} {s : Set E} {c : ℂ}

/-
**HasStrictFDerivAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.cpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDer
ivAt g g' x) (h0 : f x in slitPlane) : HasStrictFDerivAt (fun x => f x ^ g x) ((
g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x；h0 : f x in slitP
lane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Complex.hasStrictFDerivAt_cpow`：hasStrictFDerivAt_cpow {p : Complex × Co
mplex} (hp : p.1 in slitPlane) : HasStrictFDerivAt (fun x : Complex × Complex =>
 x.1 ^ x.2) ((p.2 * …
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.cpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x :=
  (hasStrictFDerivAt_cpow (p := (f x, g x)) h0).comp x (hf.prodMk hg)
/-
**HasStrictFDerivAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.const_cpow (hf : HasStrictFDerivAt f f' x) (h0 : c != 0 
∨ f x != 0) : HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • 
f') x
参数：hf : HasStrictFDerivAt f f' x；h0 : c != 0 ∨ f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Complex.hasStrictDerivAt_const_cpow`：hasStrictDerivAt_const_cpow {x y : 
Complex} (h : x != 0 ∨ y != 0) : HasStrictDerivAt (fun y => x ^ y) (x ^ y * log 
x) y
-/
theorem HasStrictFDerivAt.const_cpow (hf : HasStrictFDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).comp_hasStrictFDerivAt x hf
/-
**HasFDerivAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h0 :
 f x in slitPlane) : HasFDerivAt (fun x => f x ^ g x) ((g x * f x ^ (g x - 1)) •
 f' + (f x ^ g x * Complex.log (f x)) • g') x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x；h0 : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `Complex.hasFDerivAt_cpow`：hasFDerivAt_cpow {p : Complex × Complex} (hp :
 p.1 in slitPlane) : HasFDerivAt (fun x : Complex × Complex => x.1 ^ x.2) ((p.2 
* p.1 ^ (p.2 -…
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert! (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prodMk hg)
/-
**HasFDerivAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.const_cpow (hf : HasFDerivAt f f' x) (h0 : c != 0 ∨ f x != 0) 
: HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x
参数：hf : HasFDerivAt f f' x；h0 : c != 0 ∨ f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_const_cpow`：hasStrictDerivAt_const_cpow {x y : 
Complex} (h : x != 0 ∨ y != 0) : HasStrictDerivAt (fun y => x ^ y) (x ^ y * log 
x) y
-/
theorem HasFDerivAt.const_cpow (hf : HasFDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivAt x hf
/-
**HasFDerivWithinAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWi
thinAt g g' s x) (h0 : f x in slitPlane) : HasFDerivWithinAt (fun x => f x ^ g x
) ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x；h0 : f x in s
litPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `Complex.hasFDerivAt_cpow`：hasFDerivAt_cpow {p : Complex × Complex} (hp :
 p.1 in slitPlane) : HasFDerivAt (fun x : Complex × Complex => x.1 ^ x.2) ((p.2 
* p.1 ^ (p.2 -…
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') s x := by
  convert!
    (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x (hf.prodMk hg)
/-
**HasFDerivWithinAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.const_cpow (hf : HasFDerivWithinAt f f' s x) (h0 : c != 
0 ∨ f x != 0) : HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) 
• f') s x
参数：hf : HasFDerivWithinAt f f' s x；h0 : c != 0 ∨ f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_const_cpow`：hasStrictDerivAt_const_cpow {x y : 
Complex} (h : x != 0 ∨ y != 0) : HasStrictDerivAt (fun y => x ^ y) (x ^ y * log 
x) y
-/
theorem HasFDerivWithinAt.const_cpow (hf : HasFDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivWithinAt x hf

@[fun_prop]
/-
**DifferentiableAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.cpow (hf : DifferentiableAt Complex f x) (hg : Differenti
ableAt Complex g x) (h0 : f x in slitPlane) : DifferentiableAt Complex (fun x =>
 f x ^ g x) x
参数：hf : DifferentiableAt Complex f x；hg : DifferentiableAt Complex g x；h0 : f x 
in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasFDerivAt.cpow`：HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFD
erivAt g g' x) (h0 : f x in slitPlane) : HasFDerivAt (fun x => f x ^ g x) ((g x 
* f x …
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (h0 : f x ∈ slitPlane) : DifferentiableAt ℂ (fun x => f x ^ g x) x :=
  (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

@[fun_prop]
/-
**DifferentiableAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.const_cpow (hf : DifferentiableAt Complex f x) (h0 : c !=
 0 ∨ f x != 0) : DifferentiableAt Complex (fun x => c ^ f x) x
参数：hf : DifferentiableAt Complex f x；h0 : c != 0 ∨ f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFDerivAt.const_cpow`：HasFDerivAt.const_cpow (hf : HasFDerivAt f f' x)
 (h0 : c != 0 ∨ f x != 0) : HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.l
og c) • f') …
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.const_cpow (hf : DifferentiableAt ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    DifferentiableAt ℂ (fun x => c ^ f x) x :=
  (hf.hasFDerivAt.const_cpow h0).differentiableAt

@[fun_prop]
/-
**DifferentiableAt.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.cpow_const (hf : DifferentiableAt Complex f x) (h0 : f x 
in slitPlane) : DifferentiableAt Complex (fun x => f x ^ c) x
参数：hf : DifferentiableAt Complex f x；h0 : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.cpow`：DifferentiableAt.cpow (hf : DifferentiableAt Comp
lex f x) (hg : DifferentiableAt Complex g x) (h0 : f x in slitPlane) : Different
iableAt Com…
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
-/
theorem DifferentiableAt.cpow_const (hf : DifferentiableAt ℂ f x) (h0 : f x ∈ slitPlane) :
    DifferentiableAt ℂ (fun x => f x ^ c) x :=
  hf.cpow (differentiableAt_const c) h0

@[fun_prop]
/-
**DifferentiableWithinAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt Complex f s x) (h
g : DifferentiableWithinAt Complex g s x) (h0 : f x in slitPlane) : Differentiab
leWithinAt Complex (fun x => f x ^ g x) s x
参数：hf : DifferentiableWithinAt Complex f s x；hg : DifferentiableWithinAt Complex
 g s x；h0 : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasFDerivWithinAt.cpow`：HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f
 f' s x) (hg : HasFDerivWithinAt g g' s x) (h0 : f x in slitPlane) : HasFDerivWi
thinAt (fun …
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x)
    (hg : DifferentiableWithinAt ℂ g s x) (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ g x) s x :=
  (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableWithinAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt Complex f s
 x) (h0 : c != 0 ∨ f x != 0) : DifferentiableWithinAt Complex (fun x => c ^ f x)
 s x
参数：hf : DifferentiableWithinAt Complex f s x；h0 : c != 0 ∨ f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFDerivWithinAt.const_cpow`：HasFDerivWithinAt.const_cpow (hf : HasFDer
ivWithinAt f f' s x) (h0 : c != 0 ∨ f x != 0) : HasFDerivWithinAt (fun x => c ^ 
f x) ((c ^ f x * C…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : c ≠ 0 ∨ f x ≠ 0) : DifferentiableWithinAt ℂ (fun x => c ^ f x) s x :=
  (hf.hasFDerivWithinAt.const_cpow h0).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableWithinAt.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.cpow_const (hf : DifferentiableWithinAt Complex f s
 x) (h0 : f x in slitPlane) : DifferentiableWithinAt Complex (fun x => f x ^ c) 
s x
参数：hf : DifferentiableWithinAt Complex f s x；h0 : f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.cpow`：DifferentiableWithinAt.cpow (hf : Different
iableWithinAt Complex f s x) (hg : DifferentiableWithinAt Complex g s x) (h0 : f
 x in slitPlane) …
· 使用定理 `differentiableWithinAt_const`：differentiableWithinAt_const (c : F) : Dif
ferentiableWithinAt 𝕜 (fun _ => c) s x
-/
theorem DifferentiableWithinAt.cpow_const (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ c) s x :=
  hf.cpow (differentiableWithinAt_const c) h0

@[fun_prop]
/-
**DifferentiableOn.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.cpow (hf : DifferentiableOn Complex f s) (hg : Differenti
ableOn Complex g s) (h0 : Set.MapsTo f s slitPlane) : DifferentiableOn Complex (
fun x => f x ^ g x) s
参数：hf : DifferentiableOn Complex f s；hg : DifferentiableOn Complex g s；h0 : Set.
MapsTo f s slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.cpow`：DifferentiableWithinAt.cpow (hf : Different
iableWithinAt Complex f s x) (hg : DifferentiableWithinAt Complex g s x) (h0 : f
 x in slitPlane) …
-/
theorem DifferentiableOn.cpow (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : Set.MapsTo f s slitPlane) : DifferentiableOn ℂ (fun x ↦ f x ^ g x) s :=
  fun x hx ↦ (hf x hx).cpow (hg x hx) (h0 hx)

@[fun_prop]
/-
**DifferentiableOn.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.const_cpow (hf : DifferentiableOn Complex f s) (h0 : c !=
 0 ∨ forall x in s, f x != 0) : DifferentiableOn Complex (fun x => c ^ f x) s
参数：hf : DifferentiableOn Complex f s；h0 : c != 0 ∨ forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.const_cpow`：DifferentiableWithinAt.const_cpow (hf
 : DifferentiableWithinAt Complex f s x) (h0 : c != 0 ∨ f x != 0) : Differentiab
leWithinAt Complex (fun…
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
-/
theorem DifferentiableOn.const_cpow (hf : DifferentiableOn ℂ f s)
    (h0 : c ≠ 0 ∨ ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℂ (fun x ↦ c ^ f x) s :=
  fun x hx ↦ (hf x hx).const_cpow (h0.imp_right fun h ↦ h x hx)

@[fun_prop]
/-
**DifferentiableOn.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.cpow_const (hf : DifferentiableOn Complex f s) (h0 : fora
ll x in s, f x in slitPlane) : DifferentiableOn Complex (fun x => f x ^ c) s
参数：hf : DifferentiableOn Complex f s；h0 : forall x in s, f x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.cpow`：DifferentiableOn.cpow (hf : DifferentiableOn Comp
lex f s) (hg : DifferentiableOn Complex g s) (h0 : Set.MapsTo f s slitPlane) : D
ifferentiab…
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
-/
theorem DifferentiableOn.cpow_const (hf : DifferentiableOn ℂ f s)
    (h0 : ∀ x ∈ s, f x ∈ slitPlane) :
    DifferentiableOn ℂ (fun x => f x ^ c) s :=
  hf.cpow (differentiableOn_const c) h0

@[fun_prop]
/-
**Differentiable.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.cpow (hf : Differentiable Complex f) (hg : Differentiable C
omplex g) (h0 : forall x, f x in slitPlane) : Differentiable Complex (fun x => f
 x ^ g x)
参数：hf : Differentiable Complex f；hg : Differentiable Complex g；h0 : forall x, f 
x in slitPlane。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.cpow`：DifferentiableAt.cpow (hf : DifferentiableAt Comp
lex f x) (hg : DifferentiableAt Complex g x) (h0 : f x in slitPlane) : Different
iableAt Com…
-/
theorem Differentiable.cpow (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h0 : ∀ x, f x ∈ slitPlane) : Differentiable ℂ (fun x ↦ f x ^ g x) :=
  fun x ↦ (hf x).cpow (hg x) (h0 x)

@[fun_prop]
/-
**Differentiable.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.const_cpow (hf : Differentiable Complex f) (h0 : c != 0 ∨ f
orall x, f x != 0) : Differentiable Complex (fun x => c ^ f x)
参数：hf : Differentiable Complex f；h0 : c != 0 ∨ forall x, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.const_cpow`：DifferentiableAt.const_cpow (hf : Different
iableAt Complex f x) (h0 : c != 0 ∨ f x != 0) : DifferentiableAt Complex (fun x 
=> c ^ f x) x
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
-/
theorem Differentiable.const_cpow (hf : Differentiable ℂ f)
    (h0 : c ≠ 0 ∨ ∀ x, f x ≠ 0) : Differentiable ℂ (fun x ↦ c ^ f x) :=
  fun x ↦ (hf x).const_cpow (h0.imp_right fun h ↦ h x)

@[fun_prop]
/-
**differentiable_const_cpow_of_neZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiable_const_cpow_of_neZero (z : Complex) [NeZero z] : Differentia
ble Complex fun s : Complex => z ^ s
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.const_cpow`：Differentiable.const_cpow (hf : Differentiabl
e Complex f) (h0 : c != 0 ∨ forall x, f x != 0) : Differentiable Complex (fun x 
=> c ^ f x)
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma differentiable_const_cpow_of_neZero (z : ℂ) [NeZero z] :
    Differentiable ℂ fun s : ℂ ↦ z ^ s :=
  differentiable_id.const_cpow (.inl <| NeZero.ne z)

@[fun_prop]
/-
**differentiableAt_const_cpow_of_neZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：differentiableAt_const_cpow_of_neZero (z : Complex) [NeZero z] (t : Comple
x) : DifferentiableAt Complex (fun s : Complex => z ^ s) t
参数：z : Complex；t : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.const_cpow`：DifferentiableAt.const_cpow (hf : Different
iableAt Complex f x) (h0 : c != 0 ∨ f x != 0) : DifferentiableAt Complex (fun x 
=> c ^ f x) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma differentiableAt_const_cpow_of_neZero (z : ℂ) [NeZero z] (t : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ ↦ z ^ s) t :=
  differentiableAt_id.const_cpow (.inl <| NeZero.ne z)

end fderiv

section deriv

open Complex

variable {f g : ℂ → ℂ} {s : Set ℂ} {f' g' x c : ℂ}

nonrec theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.hasStrictFDerivAt.cpow hg h0).hasStrictDerivAt

/-
**HasStrictDerivAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c != 0 ∨ f
 x != 0) : HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x
参数：hf : HasStrictDerivAt f f' x；h : c != 0 ∨ f x != 0。
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
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Complex.hasStrictDerivAt_const_cpow`：hasStrictDerivAt_const_cpow {x y : 
Complex} (h : x != 0 ∨ y != 0) : HasStrictDerivAt (fun y => x ^ y) (x ^ y * log 
x) y
-/
theorem HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h).comp x hf
/-
**Complex.hasStrictDerivAt_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.hasStrictDerivAt_cpow_const (h : x in slitPlane) : HasStrictDerivA
t (fun z : Complex => z ^ c) (c * x ^ (c - 1)) x
参数：h : x in slitPlane。
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
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `HasStrictDerivAt.cpow`：∀ {f g : ℂ → ℂ} {f' g' x : ℂ},   HasStrictDerivAt
 f f' x →     HasStrictDerivAt g g' x →       f x ∈ Complex.slitPlane →         
HasStrictDe…
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
-/
theorem Complex.hasStrictDerivAt_cpow_const (h : x ∈ slitPlane) :
    HasStrictDerivAt (fun z : ℂ => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using!
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h
/-
**HasStrictDerivAt.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x) (h0 : f x in sl
itPlane) : HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x
参数：hf : HasStrictDerivAt f f' x；h0 : f x in slitPlane。
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
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Complex.hasStrictDerivAt_cpow_const`：Complex.hasStrictDerivAt_cpow_const
 (h : x in slitPlane) : HasStrictDerivAt (fun z : Complex => z ^ c) (c * x ^ (c 
- 1)) x
-/
theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x)
    (h0 : f x ∈ slitPlane) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).comp x hf
/-
**HasDerivAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h0 : f 
x in slitPlane) : HasDerivAt (fun x => f x ^ g x) (g x * f x ^ (g x - 1) * f' + 
f x ^ g x * Complex.log (f x) * g') x
参数：hf : HasDerivAt f f' x；hg : HasDerivAt g g' x；h0 : f x in slitPlane。
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
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `HasFDerivAt.cpow`：HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFD
erivAt g g' x) (h0 : f x in slitPlane) : HasFDerivAt (fun x => f x ^ g x) ((g x 
* f x …
· 使用定理 `HasDerivAt.hasFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
-/
theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.hasFDerivAt.cpow hg h0).hasDerivAt
/-
**HasDerivAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c != 0 ∨ f x != 0) : 
HasDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x
参数：hf : HasDerivAt f f' x；h0 : c != 0 ∨ f x != 0。
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
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_const_cpow`：hasStrictDerivAt_const_cpow {x y : 
Complex} (h : x != 0 ∨ y != 0) : HasStrictDerivAt (fun y => x ^ y) (x ^ y * log 
x) y
-/
theorem HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp x hf
/-
**HasDerivAt.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : f x in slitPlane) : H
asDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x
参数：hf : HasDerivAt f f' x；h0 : f x in slitPlane。
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
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_cpow_const`：Complex.hasStrictDerivAt_cpow_const
 (h : x in slitPlane) : HasStrictDerivAt (fun z : Complex => z ^ c) (c * x ^ (c 
- 1)) x
-/
theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : f x ∈ slitPlane) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf
/-
**HasDerivWithinAt.cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithi
nAt g g' s x) (h0 : f x in slitPlane) : HasDerivWithinAt (fun x => f x ^ g x) (g
 x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') s x
参数：hf : HasDerivWithinAt f f' s x；hg : HasDerivWithinAt g g' s x；h0 : f x in sli
tPlane。
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
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasFDerivWithinAt.hasDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `HasFDerivWithinAt.cpow`：HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f
 f' s x) (hg : HasFDerivWithinAt g g' s x) (h0 : f x in slitPlane) : HasFDerivWi
thinAt (fun …
· 使用定理 `HasDerivWithinAt.hasFDerivWithinAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
-/
theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasDerivWithinAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') s x := by
  simpa using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt
/-
**HasDerivWithinAt.const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c != 0 
∨ f x != 0) : HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f')
 s x
参数：hf : HasDerivWithinAt f f' s x；h0 : c != 0 ∨ f x != 0。
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
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_const_cpow`：hasStrictDerivAt_const_cpow {x y : 
Complex} (h : x != 0 ∨ y != 0) : HasStrictDerivAt (fun y => x ^ y) (x ^ y * log 
x) y
-/
theorem HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasDerivWithinAt x hf
/-
**HasDerivWithinAt.cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x) (h0 : f x in 
slitPlane) : HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x
参数：hf : HasDerivWithinAt f f' s x；h0 : f x in slitPlane。
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
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_cpow_const`：Complex.hasStrictDerivAt_cpow_const
 (h : x in slitPlane) : HasStrictDerivAt (fun z : Complex => z ^ c) (c * x ^ (c 
- 1)) x
-/
theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x)
    (h0 : f x ∈ slitPlane) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf
/-
**Complex.derivWithin_const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.derivWithin_const_cpow (hf : DifferentiableWithinAt Complex f s x)
 (c : Complex) : derivWithin (fun x => c ^ f x) s x = log c * derivWithin f s x 
* c ^ f x
参数：hf : DifferentiableWithinAt Complex f s x；c : Complex。
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `derivWithin_zero_of_frequently_mem`：derivWithin_zero_of_frequently_mem (
t : Set F) (ht : ¬ AccPt (f x) (𝓟 t)) (h : existsᶠ y in 𝓝[s \ {x}] x, f y in t) 
: derivWithin f s x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用引理 `Set.Infinite.of_accPt`：Set.Infinite.of_accPt {S : Set X} {x : X} (h : Ac
cPt x (𝓟 S)) : S.Infinite
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `accPt_principal_iff_nhdsWithin`：accPt_principal_iff_nhdsWithin : AccPt x
 (𝓟 s) ↔ (𝓝[s \ {x}] x).NeBot
· 使用定理 `uniqueDiffWithinAt_iff_accPt`：uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {
x : 𝕜} : UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.const_cpow`：HasDerivWithinAt.const_cpow (hf : HasDerivW
ithinAt f f' s x) (h0 : c != 0 ∨ f x != 0) : HasDerivWithinAt (fun x => c ^ f x)
 (c ^ f x * Compl…
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
（共 31 条，此处仅展示前 30 条）
-/
theorem Complex.derivWithin_const_cpow (hf : DifferentiableWithinAt ℂ f s x) (c : ℂ) :
    derivWithin (fun x ↦ c ^ f x) s x = log c * derivWithin f s x * c ^ f x := by
  by_cases h : UniqueDiffWithinAt ℂ s x; swap
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt h,
      derivWithin_zero_of_not_uniqueDiffWithinAt h, mul_zero, zero_mul]
  by_cases hc : c = 0; swap
  · rw [mul_comm, ← mul_assoc]
    exact (hf.hasDerivWithinAt.const_cpow (Or.inl hc)).derivWithin h
  rw [uniqueDiffWithinAt_iff_accPt, accPt_principal_iff_nhdsWithin] at h
  simp only [hc, log_zero, zero_mul]
  apply derivWithin_zero_of_frequently_mem {0, 1} (mt Set.Infinite.of_accPt (by simp))
  simpa [zero_cpow_eq_iff, em']
/-
**Complex.deriv_const_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.deriv_const_cpow (hf : DifferentiableAt Complex f x) (c : Complex)
 : deriv (fun x => c ^ f x) x = log c * deriv f x * c ^ f x
参数：hf : DifferentiableAt Complex f x；c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `Complex.derivWithin_const_cpow`：Complex.derivWithin_const_cpow (hf : Dif
ferentiableWithinAt Complex f s x) (c : Complex) : derivWithin (fun x => c ^ f x
) s x = log c * deri…
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
-/
theorem Complex.deriv_const_cpow (hf : DifferentiableAt ℂ f x) (c : ℂ) :
    deriv (fun x ↦ c ^ f x) x = log c * deriv f x * c ^ f x := by
  rw [← derivWithin_univ, derivWithin_const_cpow, derivWithin_univ]
  rwa [differentiableWithinAt_univ]

/-- Although `fun x => x ^ r` for fixed `r` is *not* complex-differentiable along the negative real
line, it is still real-differentiable, and the derivative is what one would formally expect.
See `hasDerivAt_ofReal_cpow_const` for an alternate formulation. -/
/-
**hasDerivAt_ofReal_cpow_const'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_ofReal_cpow_const' {x : Real} (hx : x != 0) {r : Complex} (hr :
 r != -1) : HasDerivAt (fun y : Real => (y : Complex) ^ (r + 1) / (r + 1)) (x ^ 
r) x
参数：hx : x != 0；hr : r != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `HasDerivAt.comp_ofReal`：HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z)
 : HasDerivAt (fun y : Real => e ↑y) e' z
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `HasDerivAt.div_const`：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d :
 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.cpow_const`：HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h
0 : f x in slitPlane) : HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
Although `fun x => x ^ r` for fixed `r` is *not* complex-differentiable along th
e negative real
line, it is still real-differentiable, and the derivative is what one would form
ally expect.
See `hasDerivAt_ofReal_cpow_const` for an alternate formulation.
-/
theorem hasDerivAt_ofReal_cpow_const' {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ -1) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1) / (r + 1)) (x ^ r) x := by
  rw [Ne, ← add_eq_zero_iff_eq_neg, ← Ne] at hr
  rcases lt_or_gt_of_ne hx.symm with (hx | hx)
  · -- easy case : `0 < x`
    apply HasDerivAt.comp_ofReal (e := fun y => (y : ℂ) ^ (r + 1) / (r + 1))
    convert! HasDerivAt.div_const (𝕜 := ℂ) ?_ (r + 1) using 1
    · exact (mul_div_cancel_right₀ _ hr).symm
    · convert! HasDerivAt.cpow_const ?_ ?_ using 1
      · rw [add_sub_cancel_right, mul_comm]; exact (mul_one _).symm
      · exact hasDerivAt_id (x : ℂ)
      · simp [hx]
  · -- harder case : `x < 0`
    have : ∀ᶠ y : ℝ in 𝓝 x,
        (y : ℂ) ^ (r + 1) / (r + 1) = (-y : ℂ) ^ (r + 1) * exp (π * I * (r + 1)) / (r + 1) := by
      refine Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => ?_
      rw [ofReal_cpow_of_nonpos (le_of_lt hy)]
    refine HasDerivAt.congr_of_eventuallyEq ?_ this
    rw [ofReal_cpow_of_nonpos (le_of_lt hx)]
    suffices HasDerivAt (fun y : ℝ => (-↑y) ^ (r + 1) * exp (↑π * I * (r + 1)))
        ((r + 1) * (-↑x) ^ r * exp (↑π * I * r)) x by
      convert! this.div_const (r + 1) using 1
      conv_rhs => rw [mul_assoc, mul_comm, mul_div_cancel_right₀ _ hr]
    rw [mul_add ((π : ℂ) * _), mul_one, exp_add, exp_pi_mul_I, mul_comm (_ : ℂ) (-1 : ℂ),
      neg_one_mul]
    simp_rw [mul_neg, ← neg_mul, ← ofReal_neg]
    suffices HasDerivAt (fun y : ℝ => (↑(-y) : ℂ) ^ (r + 1)) (-(r + 1) * ↑(-x) ^ r) x by
      convert! this.neg.mul_const _ using 1; ring
    suffices HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) (-x) by
      convert! @HasDerivAt.scomp ℝ _ ℂ _ _ x ℝ _ _ _ _ _ _ _ _ this (hasDerivAt_neg x) using 1
      rw [real_smul, ofReal_neg 1, ofReal_one]; ring
    suffices HasDerivAt (fun y : ℂ => y ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) ↑(-x) by
      exact this.comp_ofReal
    conv in ↑_ ^ _ => rw [(by ring : r = r + 1 - 1)]
    convert! HasDerivAt.cpow_const ?_ ?_ using 1
    · rw [add_sub_cancel_right, add_sub_cancel_right]; exact (mul_one _).symm
    · exact hasDerivAt_id ((-x : ℝ) : ℂ)
    · simp [hx]

/-- An alternate formulation of `hasDerivAt_ofReal_cpow_const'`. -/
/-
**hasDerivAt_ofReal_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_ofReal_cpow_const {x : Real} (hx : x != 0) {r : Complex} (hr : 
r != 0) : HasDerivAt (fun y : Real => (y : Complex) ^ r) (r * x ^ (r - 1)) x
参数：hx : x != 0；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasDerivAt_ofReal_cpow_const'`：hasDerivAt_ofReal_cpow_const' {x : Real} 
(hx : x != 0) {r : Complex} (hr : r != -1) : HasDerivAt (fun y : Real => (y : Co
mplex) ^ (r + 1) / …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `sub_eq_neg_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b =
 -b ↔ a = 0
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a

--- 原说明 ---
An alternate formulation of `hasDerivAt_ofReal_cpow_const'`.
-/
theorem hasDerivAt_ofReal_cpow_const {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ r) (r * x ^ (r - 1)) x := by
  have := HasDerivAt.const_mul r <| hasDerivAt_ofReal_cpow_const' hx
    (by rwa [ne_eq, sub_eq_neg_self])
  simpa [sub_add_cancel, mul_div_cancel₀ _ hr] using this

/-- A version of `DifferentiableAt.cpow_const` for a real function. -/
/-
**DifferentiableAt.ofReal_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.ofReal_cpow_const {f : Real -> Real} {x : Real} (hf : Dif
ferentiableAt Real f x) (h0 : f x != 0) (h1 : c != 0) : DifferentiableAt Real (f
un (y : Real) => (f y : Complex) ^ c) x
参数：hf : DifferentiableAt Real f x；h0 : f x != 0；h1 : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasDerivAt_ofReal_cpow_const`：hasDerivAt_ofReal_cpow_const {x : Real} (h
x : x != 0) {r : Complex} (hr : r != 0) : HasDerivAt (fun y : Real => (y : Compl
ex) ^ r) (r * x ^ …

--- 原说明 ---
A version of `DifferentiableAt.cpow_const` for a real function.
-/
theorem DifferentiableAt.ofReal_cpow_const {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (h0 : f x ≠ 0) (h1 : c ≠ 0) :
    DifferentiableAt ℝ (fun (y : ℝ) => (f y : ℂ) ^ c) x :=
  (hasDerivAt_ofReal_cpow_const h0 h1).differentiableAt.comp x hf
/-
**Complex.deriv_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.deriv_cpow_const (hx : x in Complex.slitPlane) : deriv (fun (x : C
omplex) => x ^ c) x = c * x ^ (c - 1)
参数：hx : x in Complex.slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Complex.hasStrictDerivAt_cpow_const`：Complex.hasStrictDerivAt_cpow_const
 (h : x in slitPlane) : HasStrictDerivAt (fun z : Complex => z ^ c) (c * x ^ (c 
- 1)) x
-/
theorem Complex.deriv_cpow_const (hx : x ∈ Complex.slitPlane) :
    deriv (fun (x : ℂ) ↦ x ^ c) x = c * x ^ (c - 1) :=
  (hasStrictDerivAt_cpow_const hx).hasDerivAt.deriv

/-- A version of `Complex.deriv_cpow_const` for a real variable. -/
/-
**Complex.deriv_ofReal_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.deriv_ofReal_cpow_const {x : Real} (hx : x != 0) (hc : c != 0) : d
eriv (fun x : Real => (x : Complex) ^ c) x = c * x ^ (c - 1)
参数：hx : x != 0；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `hasDerivAt_ofReal_cpow_const`：hasDerivAt_ofReal_cpow_const {x : Real} (h
x : x != 0) {r : Complex} (hr : r != 0) : HasDerivAt (fun y : Real => (y : Compl
ex) ^ r) (r * x ^ …

--- 原说明 ---
A version of `Complex.deriv_cpow_const` for a real variable.
-/
theorem Complex.deriv_ofReal_cpow_const {x : ℝ} (hx : x ≠ 0) (hc : c ≠ 0) :
    deriv (fun x : ℝ ↦ (x : ℂ) ^ c) x = c * x ^ (c - 1) :=
  (hasDerivAt_ofReal_cpow_const hx hc).deriv
/-
**deriv_cpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_cpow_const (hf : DifferentiableAt Complex f x) (hx : f x in Complex.
slitPlane) : deriv (fun (x : Complex) => f x ^ c) x = c * f x ^ (c - 1) * deriv 
f x
参数：hf : DifferentiableAt Complex f x；hx : f x in Complex.slitPlane。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.cpow_const`：HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h
0 : f x in slitPlane) : HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_cpow_const (hf : DifferentiableAt ℂ f x) (hx : f x ∈ Complex.slitPlane) :
    deriv (fun (x : ℂ) ↦ f x ^ c) x = c * f x ^ (c - 1) * deriv f x :=
  (hf.hasDerivAt.cpow_const hx).deriv
/-
**isTheta_deriv_ofReal_cpow_const_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isTheta_deriv_ofReal_cpow_const_atTop {c : Complex} (hc : c != 0) : deriv 
(fun (x : Real) => (x : Complex) ^ c) =Θ[atTop] fun x => x ^ (c.re - 1)
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.deriv_ofReal_cpow_const`：Complex.deriv_ofReal_cpow_const {x : Re
al} (hx : x != 0) (hc : c != 0) : deriv (fun x : Real => (x : Complex) ^ c) x = 
c * x ^ (c - 1)
· 使用定理 `Asymptotics.IsTheta.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {𝕜 :
 Type u_14} [inst : Norm F] [inst_1 : NormedField 𝕜] {g : α → F} {l : Filter α} 
  {c : 𝕜} {f : α → 𝕜}, c…
· 使用定理 `Asymptotics.IsTheta.of_norm_eventuallyEq`：∀ {α : Type u_1} {E' : Type u_
6} [inst : SeminormedAddCommGroup E'] {f' : α → E'} {l : Filter α} {g : α → ℝ}, 
  (fun x => ‖f' x‖) =ᶠ[l] g → …
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `Complex.sub_re`：sub_re (z w : Complex) : (z - w).re = z.re - w.re
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
-/
theorem isTheta_deriv_ofReal_cpow_const_atTop {c : ℂ} (hc : c ≠ 0) :
    deriv (fun (x : ℝ) => (x : ℂ) ^ c) =Θ[atTop] fun x => x ^ (c.re - 1) := by
  calc
    _ =ᶠ[atTop] fun x : ℝ ↦ c * x ^ (c - 1) := by
      filter_upwards [eventually_ne_atTop 0] with x hx using by rw [deriv_ofReal_cpow_const hx hc]
    _ =Θ[atTop] fun x : ℝ ↦ ‖(x : ℂ) ^ (c - 1)‖ :=
      (Asymptotics.IsTheta.of_norm_eventuallyEq EventuallyEq.rfl).const_mul_left hc
    _ =ᶠ[atTop] fun x ↦ x ^ (c.re - 1) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
/-
**isBigO_deriv_ofReal_cpow_const_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_deriv_ofReal_cpow_const_atTop (c : Complex) : deriv (fun (x : Real)
 => (x : Complex) ^ c) =O[atTop] fun x => x ^ (c.re - 1)
参数：c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isTheta_deriv_ofReal_cpow_const_atTop`：isTheta_deriv_ofReal_cpow_const_a
tTop {c : Complex} (hc : c != 0) : deriv (fun (x : Real) => (x : Complex) ^ c) =
Θ[atTop] fun x => x ^ (c.re…
-/
theorem isBigO_deriv_ofReal_cpow_const_atTop (c : ℂ) :
    deriv (fun (x : ℝ) => (x : ℂ) ^ c) =O[atTop] fun x => x ^ (c.re - 1) := by
  obtain rfl | hc := eq_or_ne c 0
  · simp_rw [cpow_zero, deriv_const', Asymptotics.isBigO_zero]
  · exact (isTheta_deriv_ofReal_cpow_const_atTop hc).1

end deriv

namespace Real

variable {x y z : ℝ}

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`. -/
/-
**Real.hasStrictFDerivAt_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictFDerivAt_rpow_of_pos (p : Real × Real) (hp : 0 < p.1) : HasStrict
FDerivAt (fun x : Real × Real => x.1 ^ x.2) ((p.2 * p.1 ^ (p.2 - 1)) • Continuou
sLinearMap.fst Real Real Real + (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd 
Real Real Real) p
参数：p : Real × Real；hp : 0 < p.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `HasStrictFDerivAt.congr_of_eventuallyEq`：HasStrictFDerivAt.congr_of_even
tuallyEq (h : HasStrictFDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt 
f₁ f' x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_sub_one`：rpow_sub_one {x : Real} (hx : x != 0) (y : Real) : x 
^ (y - 1) = x ^ y / x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_div_left_comm`：mul_div_left_comm : a * (b / c) = b * (a / c)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `HasStrictFDerivAt.exp`：HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f
' x) : HasStrictFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x
· 使用定理 `HasStrictFDerivAt.fun_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {x : E} {𝔸' …
· 使用定理 `HasStrictFDerivAt.log`：HasStrictFDerivAt.log (hf : HasStrictFDerivAt f f
' x) (hx : f x != 0) : HasStrictFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x
· 使用定理 `hasStrictFDerivAt_fst`：hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.
fst E F) (fst 𝕜 E F) p
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `0 < p.fst`
.
-/
theorem hasStrictFDerivAt_rpow_of_pos (p : ℝ × ℝ) (hp : 0 < p.1) :
    HasStrictFDerivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    (continuousAt_fst.eventually (lt_mem_nhds hp)).mono fun p hp => rpow_def_of_pos hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert! ((hasStrictFDerivAt_fst.log hp.ne').fun_mul hasStrictFDerivAt_snd).exp using 1
  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
    div_eq_mul_inv, smul_smul, smul_smul, mul_assoc, add_comm]

/-- `(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`. -/
/-
**Real.hasStrictFDerivAt_rpow_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictFDerivAt_rpow_of_neg (p : Real × Real) (hp : p.1 < 0) : HasStrict
FDerivAt (fun x : Real × Real => x.1 ^ x.2) ((p.2 * p.1 ^ (p.2 - 1)) • Continuou
sLinearMap.fst Real Real Real + (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin
 (p.2 * π) * π) • ContinuousLinearMap.snd Real Real Real) p
参数：p : Real × Real；hp : p.1 < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.rpow_def_of_neg`：rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real)
 : x ^ y = exp (log x * y) * cos (y * π)
· 使用定理 `HasStrictFDerivAt.congr_of_eventuallyEq`：HasStrictFDerivAt.congr_of_even
tuallyEq (h : HasStrictFDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt 
f₁ f' x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_sub_one`：rpow_sub_one {x : Real} (hx : x != 0) (y : Real) : x 
^ (y - 1) = x ^ y / x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
`(x, y) ↦ x ^ y` is strictly differentiable at `p : ℝ × ℝ` such that `p.fst < 0`
.
-/
theorem hasStrictFDerivAt_rpow_of_neg (p : ℝ × ℝ) (hp : p.1 < 0) :
    HasStrictFDerivAt (fun x : ℝ × ℝ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (p.1 ^ p.2 * log p.1 - exp (log p.1 * p.2) * sin (p.2 * π) * π) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have : (fun x : ℝ × ℝ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) * cos (x.2 * π) :=
    (continuousAt_fst.eventually (gt_mem_nhds hp)).mono fun p hp => rpow_def_of_neg hp _
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  convert!
    ((hasStrictFDerivAt_fst.log hp.ne).fun_mul hasStrictFDerivAt_snd).exp.fun_mul
      (hasStrictFDerivAt_snd.mul_const π).cos using 1
  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
    mul_comm (cos _), ← rpow_def_of_neg hp]
  rw [div_eq_mul_inv, add_comm]; congr 2 <;> ring

/-- The function `fun (x, y) => x ^ y` is infinitely smooth at `(x, y)` unless `x = 0`. -/
/-
**Real.contDiffAt_rpow_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_rpow_of_ne (p : Real × Real) (hp : p.1 != 0) {n : WithTop Nat∞}
 : ContDiffAt Real n (fun p : Real × Real => p.1 ^ p.2) p
参数：p : Real × Real；hp : p.1 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `ContDiffAt.congr_of_eventuallyEq`：ContDiffAt.congr_of_eventuallyEq (h : 
ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n f₁ x
· 使用定理 `ContDiffAt.mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E :
 Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {x : E} {
n : …
· 使用定理 `ContDiffAt.exp`：ContDiffAt.exp {n} (hf : ContDiffAt Real n f x) : ContDi
ffAt Real n (fun x => Real.exp (f x)) x
· 使用定理 `ContDiffAt.log`：ContDiffAt.log {n} (hf : ContDiffAt Real n f x) (hx : f 
x != 0) : ContDiffAt Real n (fun x => log (f x)) x
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p
· 使用定理 `ContDiffAt.cos`：ContDiffAt.cos {n} (hf : ContDiffAt Real n f x) : ContDi
ffAt Real n (fun x => Real.cos (f x)) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.rpow_def_of_neg`：rpow_def_of_neg {x : Real} (hx : x < 0) (y : Real)
 : x ^ y = exp (log x * y) * cos (y * π)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)

--- 原说明 ---
The function `fun (x, y) => x ^ y` is infinitely smooth at `(x, y)` unless `x = 
0`.
-/
theorem contDiffAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun p : ℝ × ℝ => p.1 ^ p.2) p := by
  rcases hp.lt_or_gt with hneg | hpos
  exacts
    [(((contDiffAt_fst.log hneg.ne).mul contDiffAt_snd).exp.mul
          (contDiffAt_snd.mul contDiffAt_const).cos).congr_of_eventuallyEq
      ((continuousAt_fst.eventually (gt_mem_nhds hneg)).mono fun p hp => rpow_def_of_neg hp _),
    ((contDiffAt_fst.log hpos.ne').mul contDiffAt_snd).exp.congr_of_eventuallyEq
      ((continuousAt_fst.eventually (lt_mem_nhds hpos)).mono fun p hp => rpow_def_of_pos hp _)]
/-
**Real.differentiableAt_rpow_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_rpow_of_ne (p : Real × Real) (hp : p.1 != 0) : Differenti
ableAt Real (fun p : Real × Real => p.1 ^ p.2) p
参数：p : Real × Real；hp : p.1 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.contDiffAt_rpow_of_ne`：contDiffAt_rpow_of_ne (p : Real × Real) (hp 
: p.1 != 0) {n : WithTop Nat∞} : ContDiffAt Real n (fun p : Real × Real => p.1 ^
 p.2) p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem differentiableAt_rpow_of_ne (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1 ^ p.2) p :=
  (contDiffAt_rpow_of_ne p hp).differentiableAt one_ne_zero
/-
**Real._root_.HasStrictDerivAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasStrictDerivAt.rpow {f g : ℝ → ℝ} {f' g' : ℝ} (hf : HasStrictDerivAt f f' x)
    (hg : HasStrictDerivAt g g' x) (h : 0 < f x) : HasStrictDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  convert!
    (hasStrictFDerivAt_rpow_of_pos ((fun x => (f x, g x)) x) h).comp_hasStrictDerivAt x
      (hf.prodMk hg) using 1
  simp [mul_assoc, mul_comm]
/-
**Real.hasStrictDerivAt_rpow_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_rpow_const_of_ne {x : Real} (hx : x != 0) (p : Real) : Ha
sStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
参数：hx : x != 0；p : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasStrictFDerivAt.comp_hasStrictDerivAt`：HasStrictFDerivAt.comp_hasStric
tDerivAt (hl : HasStrictFDerivAt l l' (f x)) (hf : HasStrictDerivAt f f' x) : Ha
sStrictDerivAt (l ∘ f) (l' f'…
· 使用定理 `Real.hasStrictFDerivAt_rpow_of_neg`：hasStrictFDerivAt_rpow_of_neg (p : R
eal × Real) (hp : p.1 < 0) : HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2
) ((p.2 * p.1 ^ (p.2 - 1…
· 使用定理 `HasStrictDerivAt.prodMk`：HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt
 f₁ f₁' x) (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x,
 f₂ x)) (f₁',…
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
（共 34 条，此处仅展示前 30 条）
-/
theorem hasStrictDerivAt_rpow_const_of_ne {x : ℝ} (hx : x ≠ 0) (p : ℝ) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases hx.lt_or_gt with hx | hx
  · have := (hasStrictFDerivAt_rpow_of_neg (x, p) hx).comp_hasStrictDerivAt x
      ((hasStrictDerivAt_id x).prodMk (hasStrictDerivAt_const x p))
    convert! this using 1; simp
  · simpa using (hasStrictDerivAt_id x).rpow (hasStrictDerivAt_const x p) hx
/-
**Real.hasStrictDerivAt_const_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_const_rpow {a : Real} (ha : 0 < a) (x : Real) : HasStrict
DerivAt (fun x => a ^ x) (a ^ x * log a) x
参数：ha : 0 < a；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasStrictDerivAt.rpow`：∀ {x : ℝ} {f g : ℝ → ℝ} {f' g' : ℝ},   HasStrictD
erivAt f f' x →     HasStrictDerivAt g g' x →       0 < f x → HasStrictDerivAt (
fun x => f …
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x
-/
theorem hasStrictDerivAt_const_rpow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x := by
  simpa using (hasStrictDerivAt_const _ _).rpow (hasStrictDerivAt_id x) ha
/-
**Real.differentiableAt_rpow_const_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：differentiableAt_rpow_const_of_ne (p : Real) {x : Real} (hx : x != 0) : Di
fferentiableAt Real (fun x => x ^ p) x
参数：p : Real；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_3 : Topolo…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用定理 `Real.hasStrictDerivAt_rpow_const_of_ne`：hasStrictDerivAt_rpow_const_of_n
e {x : Real} (hx : x != 0) (p : Real) : HasStrictDerivAt (fun x => x ^ p) (p * x
 ^ (p - 1)) x
-/
lemma differentiableAt_rpow_const_of_ne (p : ℝ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun x => x ^ p) x :=
  (hasStrictDerivAt_rpow_const_of_ne hx p).hasStrictFDerivAt.differentiableAt
/-
**Real.not_differentiableAt_rpow_const_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：not_differentiableAt_rpow_const_zero {r : Real} (hr : r < 1) (hr' : r != 0
) : ¬ DifferentiableAt Real (fun x => x ^ r) (0 : Real)
参数：hr : r < 1；hr' : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_congr`：tendsto_nhdsWithin_congr {f g : α -> β} {s : S
et α} {a : α} {l : Filter β} (hfg : forall x in s, f x = g x) (hf : Tendsto f (𝓝
[s] a) l) : Te…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
（共 62 条，此处仅展示前 30 条）
-/
theorem not_differentiableAt_rpow_const_zero {r : ℝ} (hr : r < 1) (hr' : r ≠ 0) :
    ¬ DifferentiableAt ℝ (fun x ↦ x ^ r) (0 : ℝ) := by
  by_contra h
  set y := deriv (fun x ↦ x ^ r) (0 : ℝ)
  -- If `x ^ r` was differentiable at `0`, then `x ^ (r - 1)` would have a finite limit at `0`.
  have h : Filter.Tendsto (fun t ↦ t ^ (r - 1)) (𝓝[>] 0) (𝓝 y) := by
    apply tendsto_nhdsWithin_congr _ h.hasDerivAt.tendsto_slope_zero_right
    intro x (hx : 0 < x)
    simp only [zero_add, ne_eq, hr', not_false_eq_true, Real.zero_rpow, sub_zero, smul_eq_mul]
    field_simp
    nth_rw 1 [← add_sub_cancel 1 r, Real.rpow_add hx]
    simp
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_rpow_neg_nhdsGT_zero (by simp [hr])) y h
/-
**Real.differentiableOn_rpow_const** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：differentiableOn_rpow_const (p : Real) : DifferentiableOn Real (fun x => (
x : Real) ^ p) {0}ᶜ
参数：p : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `Real.differentiableAt_rpow_const_of_ne`：differentiableAt_rpow_const_of_n
e (p : Real) {x : Real} (hx : x != 0) : DifferentiableAt Real (fun x => x ^ p) x
-/
lemma differentiableOn_rpow_const (p : ℝ) :
    DifferentiableOn ℝ (fun x => (x : ℝ) ^ p) {0}ᶜ :=
  fun _ hx => (Real.differentiableAt_rpow_const_of_ne p hx).differentiableWithinAt

/-- This lemma says that `fun x => a ^ x` is strictly differentiable for `a < 0`. Note that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefine `a ^ x`
for negative `a` if some other definition will be more convenient. -/
/-
**Real.hasStrictDerivAt_const_rpow_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_const_rpow_of_neg {a x : Real} (ha : a < 0) : HasStrictDe
rivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x
参数：ha : a < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `HasStrictFDerivAt.comp_hasStrictDerivAt`：HasStrictFDerivAt.comp_hasStric
tDerivAt (hl : HasStrictFDerivAt l l' (f x)) (hf : HasStrictDerivAt f f' x) : Ha
sStrictDerivAt (l ∘ f) (l' f'…
· 使用定理 `Real.hasStrictFDerivAt_rpow_of_neg`：hasStrictFDerivAt_rpow_of_neg (p : R
eal × Real) (hp : p.1 < 0) : HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2
) ((p.2 * p.1 ^ (p.2 - 1…
· 使用定理 `HasStrictDerivAt.prodMk`：HasStrictDerivAt.prodMk (hf₁ : HasStrictDerivAt
 f₁ f₁' x) (hf₂ : HasStrictDerivAt f₂ f₂' x) : HasStrictDerivAt (fun x => (f₁ x,
 f₂ x)) (f₁',…
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `hasStrictDerivAt_id`：hasStrictDerivAt_id : HasStrictDerivAt id 1 x

--- 原说明 ---
This lemma says that `fun x => a ^ x` is strictly differentiable for `a < 0`. No
te that these
values of `a` are outside of the "official" domain of `a ^ x`, and we may redefi
ne `a ^ x`
for negative `a` if some other definition will be more convenient.
-/
theorem hasStrictDerivAt_const_rpow_of_neg {a x : ℝ} (ha : a < 0) :
    HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a - exp (log a * x) * sin (x * π) * π) x := by
  simpa using! (hasStrictFDerivAt_rpow_of_neg (a, x) ha).comp_hasStrictDerivAt x
    ((hasStrictDerivAt_const _ _).prodMk (hasStrictDerivAt_id _))

end Real

namespace Real

variable {z x y : ℝ}

/-
**Real.hasDerivAt_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_rpow_const {x p : Real} (h : x != 0 ∨ 1 <= p) : HasDerivAt (fun
 x => x ^ p) (p * x ^ (p - 1)) x
参数：h : x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_rpow_const_of_ne`：hasStrictDerivAt_rpow_const_of_n
e {x : Real} (hx : x != 0) (p : Real) : HasStrictDerivAt (fun x => x ^ p) (p * x
 ^ (p - 1)) x
· 使用定理 `Or.neg_resolve_left`：∀ {a b : Prop}, ¬a ∨ b → a → b
· 使用定理 `hasDerivAt_of_hasDerivAt_of_ne`：hasDerivAt_of_hasDerivAt_of_ne {f g : Re
al -> E} {x : Real} (f_diff : forall y != x, HasDerivAt f (g y) y) (hf : Continu
ousAt f x) (hg : Con…
· 使用定理 `ContinuousAt.rpow_const`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f
 : α → ℝ} {x : α} {p : ℝ},   ContinuousAt f x → f x ≠ 0 ∨ 0 ≤ p → ContinuousAt (
fun x => f x …
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ContinuousAt.mul`：ContinuousAt.mul (hf : ContinuousAt f x) (hg : Continu
ousAt g x) : ContinuousAt (f * g) x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hasDerivAt_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x := by
  rcases ne_or_eq x 0 with (hx | rfl)
  · exact (hasStrictDerivAt_rpow_const_of_ne hx _).hasDerivAt
  replace h : 1 ≤ p := h.neg_resolve_left rfl
  apply hasDerivAt_of_hasDerivAt_of_ne fun x hx =>
    (hasStrictDerivAt_rpow_const_of_ne hx p).hasDerivAt
  exacts [continuousAt_id.rpow_const (Or.inr (zero_le_one.trans h)),
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr (sub_nonneg.2 h)))]
/-
**Real.differentiable_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiable_rpow_const {p : Real} (hp : 1 <= p) : Differentiable Real f
un x : Real => x ^ p
参数：hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
-/
theorem differentiable_rpow_const {p : ℝ} (hp : 1 ≤ p) : Differentiable ℝ fun x : ℝ => x ^ p :=
  fun _ => (hasDerivAt_rpow_const (Or.inr hp)).differentiableAt
/-
**Real.deriv_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_rpow_const (x p : Real) : deriv (fun x => x ^ p) x = p * x ^ (p - 1)
参数：x p : Real。
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
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `Real.not_differentiableAt_rpow_const_zero`：not_differentiableAt_rpow_con
st_zero {r : Real} (hr : r < 1) (hr' : r != 0) : ¬ DifferentiableAt Real (fun x 
=> x ^ r) (0 : Real)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem deriv_rpow_const (x p : ℝ) : deriv (fun x ↦ x ^ p) x = p * x ^ (p - 1) := by
  by_cases! h : p = 0
  · simp [h]
  by_cases! h' : x ≠ 0 ∨ 1 ≤ p
  · apply (Real.hasDerivAt_rpow_const h').deriv
  have h'' := deriv_zero_of_not_differentiableAt (not_differentiableAt_rpow_const_zero h'.2 h ·)
  grind [Real.zero_rpow]
/-
**Real.deriv_rpow_const'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_rpow_const' (p : Real) : (deriv fun x : Real => x ^ p) = fun x => p 
* x ^ (p - 1)
参数：p : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.deriv_rpow_const`：deriv_rpow_const (x p : Real) : deriv (fun x => x
 ^ p) x = p * x ^ (p - 1)
-/
theorem deriv_rpow_const' (p : ℝ) :
    (deriv fun x : ℝ => x ^ p) = fun x => p * x ^ (p - 1) :=
  funext (deriv_rpow_const · p)
/-
**Real.contDiffAt_rpow_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_rpow_const_of_ne {x p : Real} {n : WithTop Nat∞} (h : x != 0) :
 ContDiffAt Real n (fun x => x ^ p) x
参数：h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Real.contDiffAt_rpow_of_ne`：contDiffAt_rpow_of_ne (p : Real × Real) (hp 
: p.1 != 0) {n : WithTop Nat∞} : ContDiffAt Real n (fun p : Real × Real => p.1 ^
 p.2) p
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
-/
theorem contDiffAt_rpow_const_of_ne {x p : ℝ} {n : WithTop ℕ∞} (h : x ≠ 0) :
    ContDiffAt ℝ n (fun x => x ^ p) x :=
  (contDiffAt_rpow_of_ne (x, p) h).comp x (contDiffAt_id.prodMk contDiffAt_const)
/-
**Real.contDiff_rpow_const_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiff_rpow_const_of_le {p : Real} {n : Nat} (h : ↑n <= p) : ContDiff Re
al n fun x : Real => x ^ p
参数：h : ↑n <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `Continuous.rpow_const`：Continuous.rpow_const (hf : Continuous f) (h : fo
rall x, f x != 0 ∨ 0 <= p) : Continuous fun x => f x ^ p
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `contDiff_succ_iff_deriv`：contDiff_succ_iff_deriv : ContDiff 𝕜 (n + 1) f 
↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOn 𝕜 f univ) ∧ ContDiff 𝕜 n (deriv f)
· 使用定理 `Real.deriv_rpow_const'`：deriv_rpow_const' (p : Real) : (deriv fun x : Re
al => x ^ p) = fun x => p * x ^ (p - 1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Real.differentiable_rpow_const`：differentiable_rpow_const {p : Real} (hp
 : 1 <= p) : Differentiable Real fun x : Real => x ^ p
· 使用定理 `ContDiff.mul`：ContDiff.mul {f g : E -> 𝔸} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x * g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
（共 32 条，此处仅展示前 30 条）
-/
theorem contDiff_rpow_const_of_le {p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiff ℝ n fun x : ℝ => x ^ p := by
  induction n generalizing p with
  | zero => exact contDiff_zero.2 (continuous_id.rpow_const fun x => Or.inr <| by simpa using h)
  | succ n ihn =>
    have h1 : 1 ≤ p := le_trans (by simp) h
    rw [Nat.cast_add_one, ← le_sub_iff_add_le] at h
    rw [Nat.cast_add_one, contDiff_succ_iff_deriv, deriv_rpow_const' p]
    simp only [WithTop.natCast_ne_top, analyticOn_univ, IsEmpty.forall_iff, true_and]
    exact ⟨differentiable_rpow_const h1, contDiff_const.mul (ihn h)⟩
/-
**Real.contDiffAt_rpow_const_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_rpow_const_of_le {x p : Real} {n : Nat} (h : ↑n <= p) : ContDif
fAt Real n (fun x : Real => x ^ p) x
参数：h : ↑n <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_rpow_const_of_le`：contDiff_rpow_const_of_le {p : Real} {n 
: Nat} (h : ↑n <= p) : ContDiff Real n fun x : Real => x ^ p
-/
theorem contDiffAt_rpow_const_of_le {x p : ℝ} {n : ℕ} (h : ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  (contDiff_rpow_const_of_le h).contDiffAt
/-
**Real.contDiffAt_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_rpow_const {x p : Real} {n : Nat} (h : x != 0 ∨ ↑n <= p) : Cont
DiffAt Real n (fun x : Real => x ^ p) x
参数：h : x != 0 ∨ ↑n <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Real.contDiffAt_rpow_const_of_ne`：contDiffAt_rpow_const_of_ne {x p : Rea
l} {n : WithTop Nat∞} (h : x != 0) : ContDiffAt Real n (fun x => x ^ p) x
· 使用定理 `Real.contDiffAt_rpow_const_of_le`：contDiffAt_rpow_const_of_le {x p : Rea
l} {n : Nat} (h : ↑n <= p) : ContDiffAt Real n (fun x : Real => x ^ p) x
-/
theorem contDiffAt_rpow_const {x p : ℝ} {n : ℕ} (h : x ≠ 0 ∨ ↑n ≤ p) :
    ContDiffAt ℝ n (fun x : ℝ => x ^ p) x :=
  h.elim contDiffAt_rpow_const_of_ne contDiffAt_rpow_const_of_le
/-
**Real.iter_deriv_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：iter_deriv_rpow_const (r x : Real) (k : Nat) : deriv^[k] (fun (x : Real) =
> x ^ r) x = (descPochhammer Real k).eval r * x ^ (r - k)
参数：r x : Real；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `deriv_const_mul_field`：deriv_const_mul_field (u : 𝕜') : deriv (fun y => 
u * v y) x = u * deriv v x
· 使用定理 `Real.deriv_rpow_const`：deriv_rpow_const (x p : Real) : deriv (fun x => x
 ^ p) x = p * x ^ (p - 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem iter_deriv_rpow_const (r x : ℝ) (k : ℕ) :
    deriv^[k] (fun (x : ℝ) ↦ x ^ r) x = (descPochhammer ℝ k).eval r * x ^ (r - k) := by
  apply funext_iff.mp
  induction k with
  | zero => simp
  | succ k IH =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one, IH]
    ext y
    simp only [deriv_const_mul_field, deriv_rpow_const, ← mul_assoc, descPochhammer_succ_right,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
      mul_eq_mul_left_iff, mul_eq_zero]
    grind
/-
**Real.hasStrictDerivAt_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_rpow_const {x p : Real} (hx : x != 0 ∨ 1 <= p) : HasStric
tDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
参数：hx : x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.hasStrictDerivAt'`：ContDiffAt.hasStrictDerivAt' {f : 𝕂 -> F'}
 {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hf' : HasDerivAt f f' x) (hn : n !
= 0) : HasStrictDe…
· 使用定理 `Real.contDiffAt_rpow_const`：contDiffAt_rpow_const {x p : Real} {n : Nat}
 (h : x != 0 ∨ ↑n <= p) : ContDiffAt Real n (fun x : Real => x ^ p) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem hasStrictDerivAt_rpow_const {x p : ℝ} (hx : x ≠ 0 ∨ 1 ≤ p) :
    HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x :=
  ContDiffAt.hasStrictDerivAt' (contDiffAt_rpow_const (by rwa [← Nat.cast_one] at hx))
    (hasDerivAt_rpow_const hx) one_ne_zero

end Real

section Differentiability

open Real

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {f' g' : StrongDual ℝ E}
  {x : E} {s : Set E} {c p : ℝ} {n : WithTop ℕ∞}

/-
**HasFDerivWithinAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.rpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWi
thinAt g g' s x) (h : 0 < f x) : HasFDerivWithinAt (fun x => f x ^ g x) ((g x * 
f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') s x
参数：hf : HasFDerivWithinAt f f' s x；hg : HasFDerivWithinAt g g' s x；h : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp_hasFDerivWithinAt`：HasFDerivAt.comp_hasFDerivWithinAt {
g : F -> G} {g' : F ->L[𝕜] G} (hg : HasFDerivAt g g' (f x)) (hf : HasFDerivWithi
nAt f f' s x) : HasFDeri…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `Real.hasStrictFDerivAt_rpow_of_pos`：hasStrictFDerivAt_rpow_of_pos (p : R
eal × Real) (hp : 0 < p.1) : HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2
) ((p.2 * p.1 ^ (p.2 - 1…
· 使用定理 `HasFDerivWithinAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasFDerivWithinAt.rpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h : 0 < f x) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') s x := by
  -- `by exact` to deal with tricky unification.
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp_hasFDerivWithinAt x
    (hf.prodMk hg)
/-
**HasFDerivAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.rpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h : 
0 < f x) : HasFDerivAt (fun x => f x ^ g x) ((g x * f x ^ (g x - 1)) • f' + (f x
 ^ g x * Real.log (f x)) • g') x
参数：hf : HasFDerivAt f f' x；hg : HasFDerivAt g g' x；h : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `Real.hasStrictFDerivAt_rpow_of_pos`：hasStrictFDerivAt_rpow_of_pos (p : R
eal × Real) (hp : 0 < p.1) : HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2
) ((p.2 * p.1 ^ (p.2 - 1…
· 使用定理 `HasFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type u_…
-/
theorem HasFDerivAt.rpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (h : 0 < f x) :
    HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x := by
  exact (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).hasFDerivAt.comp x (hf.prodMk hg)
/-
**HasStrictFDerivAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.rpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDer
ivAt g g' x) (h : 0 < f x) : HasStrictFDerivAt (fun x => f x ^ g x) ((g x * f x 
^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x
参数：hf : HasStrictFDerivAt f f' x；hg : HasStrictFDerivAt g g' x；h : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{F : Type u_…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Real.hasStrictFDerivAt_rpow_of_pos`：hasStrictFDerivAt_rpow_of_pos (p : R
eal × Real) (hp : 0 < p.1) : HasStrictFDerivAt (fun x : Real × Real => x.1 ^ x.2
) ((p.2 * p.1 ^ (p.2 - 1…
· 使用定理 `HasStrictFDerivAt.prodMk`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
-/
theorem HasStrictFDerivAt.rpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h : 0 < f x) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Real.log (f x)) • g') x :=
  (hasStrictFDerivAt_rpow_of_pos (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
/-
**DifferentiableWithinAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt Real f s x) (hg :
 DifferentiableWithinAt Real g s x) (h : f x != 0) : DifferentiableWithinAt Real
 (fun x => f x ^ g x) s x
参数：hf : DifferentiableWithinAt Real f s x；hg : DifferentiableWithinAt Real g s x
；h : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `Real.differentiableAt_rpow_of_ne`：differentiableAt_rpow_of_ne (p : Real 
× Real) (hp : p.1 != 0) : DifferentiableAt Real (fun p : Real × Real => p.1 ^ p.
2) p
· 使用定理 `DifferentiableWithinAt.prodMk`：DifferentiableWithinAt.prodMk (hf₁ : Diff
erentiableWithinAt 𝕜 f₁ s x) (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) : Different
iableWithinAt 𝕜 (fu…
-/
theorem DifferentiableWithinAt.rpow (hf : DifferentiableWithinAt ℝ f s x)
    (hg : DifferentiableWithinAt ℝ g s x) (h : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => f x ^ g x) s x := by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp_differentiableWithinAt x (hf.prodMk hg)

@[fun_prop]
/-
**DifferentiableAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.rpow (hf : DifferentiableAt Real f x) (hg : Differentiabl
eAt Real g x) (h : f x != 0) : DifferentiableAt Real (fun x => f x ^ g x) x
参数：hf : DifferentiableAt Real f x；hg : DifferentiableAt Real g x；h : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Real.differentiableAt_rpow_of_ne`：differentiableAt_rpow_of_ne (p : Real 
× Real) (hp : p.1 != 0) : DifferentiableAt Real (fun p : Real × Real => p.1 ^ p.
2) p
· 使用定理 `DifferentiableAt.prodMk`：DifferentiableAt.prodMk (hf₁ : DifferentiableAt
 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) : DifferentiableAt 𝕜 (fun x : E => (f₁ 
x, f₂ x)) x
-/
theorem DifferentiableAt.rpow (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (h : f x ≠ 0) : DifferentiableAt ℝ (fun x => f x ^ g x) x := by
  -- `by exact` to deal with tricky unification.
  exact (differentiableAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
/-
**DifferentiableOn.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.rpow (hf : DifferentiableOn Real f s) (hg : Differentiabl
eOn Real g s) (h : forall x in s, f x != 0) : DifferentiableOn Real (fun x => f 
x ^ g x) s
参数：hf : DifferentiableOn Real f s；hg : DifferentiableOn Real g s；h : forall x in
 s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.rpow`：DifferentiableWithinAt.rpow (hf : Different
iableWithinAt Real f s x) (hg : DifferentiableWithinAt Real g s x) (h : f x != 0
) : Differentiabl…
-/
theorem DifferentiableOn.rpow (hf : DifferentiableOn ℝ f s) (hg : DifferentiableOn ℝ g s)
    (h : ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℝ (fun x => f x ^ g x) s := fun x hx =>
  (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
/-
**Differentiable.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.rpow (hf : Differentiable Real f) (hg : Differentiable Real
 g) (h : forall x, f x != 0) : Differentiable Real fun x => f x ^ g x
参数：hf : Differentiable Real f；hg : Differentiable Real g；h : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.rpow`：DifferentiableAt.rpow (hf : DifferentiableAt Real
 f x) (hg : DifferentiableAt Real g x) (h : f x != 0) : DifferentiableAt Real (f
un x => f x…
-/
theorem Differentiable.rpow (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (h : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => f x ^ g x := fun x => (hf x).rpow (hg x) (h x)

@[fun_prop]
/-
**HasFDerivWithinAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.rpow_const (hf : HasFDerivWithinAt f f' s x) (h : f x !=
 0 ∨ 1 <= p) : HasFDerivWithinAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') s
 x
参数：hf : HasFDerivWithinAt f f' s x；h : f x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
-/
theorem HasFDerivWithinAt.rpow_const (hf : HasFDerivWithinAt f f' s x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFDerivWithinAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') s x :=
  (hasDerivAt_rpow_const h).comp_hasFDerivWithinAt x hf

@[fun_prop]
/-
**HasFDerivAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.rpow_const (hf : HasFDerivAt f f' x) (h : f x != 0 ∨ 1 <= p) :
 HasFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x
参数：hf : HasFDerivAt f f' x；h : f x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
-/
theorem HasFDerivAt.rpow_const (hf : HasFDerivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasDerivAt_rpow_const h).comp_hasFDerivAt x hf
/-
**HasStrictFDerivAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.rpow_const (hf : HasStrictFDerivAt f f' x) (h : f x != 0
 ∨ 1 <= p) : HasStrictFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x
参数：hf : HasStrictFDerivAt f f' x；h : f x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_rpow_const`：hasStrictDerivAt_rpow_const {x p : Rea
l} (hx : x != 0 ∨ 1 <= p) : HasStrictDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) 
x
-/
theorem HasStrictFDerivAt.rpow_const (hf : HasStrictFDerivAt f f' x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    HasStrictFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) • f') x :=
  (hasStrictDerivAt_rpow_const h).comp_hasStrictFDerivAt x hf

@[fun_prop]
/-
**DifferentiableWithinAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.rpow_const (hf : DifferentiableWithinAt Real f s x)
 (h : f x != 0 ∨ 1 <= p) : DifferentiableWithinAt Real (fun x => f x ^ p) s x
参数：hf : DifferentiableWithinAt Real f s x；h : f x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivWithinAt.rpow_const`：HasFDerivWithinAt.rpow_const (hf : HasFDer
ivWithinAt f f' s x) (h : f x != 0 ∨ 1 <= p) : HasFDerivWithinAt (fun x => f x ^
 p) ((p * f x ^ (p…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.rpow_const (hf : DifferentiableWithinAt ℝ f s x)
    (h : f x ≠ 0 ∨ 1 ≤ p) : DifferentiableWithinAt ℝ (fun x => f x ^ p) s x :=
  (hf.hasFDerivWithinAt.rpow_const h).differentiableWithinAt

@[simp]
/-
**DifferentiableAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.rpow_const (hf : DifferentiableAt Real f x) (h : f x != 0
 ∨ 1 <= p) : DifferentiableAt Real (fun x => f x ^ p) x
参数：hf : DifferentiableAt Real f x；h : f x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
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
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivAt.rpow_const`：HasFDerivAt.rpow_const (hf : HasFDerivAt f f' x)
 (h : f x != 0 ∨ 1 <= p) : HasFDerivAt (fun x => f x ^ p) ((p * f x ^ (p - 1)) •
 f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.rpow_const (hf : DifferentiableAt ℝ f x) (h : f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableAt ℝ (fun x => f x ^ p) x :=
  (hf.hasFDerivAt.rpow_const h).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.rpow_const (hf : DifferentiableOn Real f s) (h : forall x
 in s, f x != 0 ∨ 1 <= p) : DifferentiableOn Real (fun x => f x ^ p) s
参数：hf : DifferentiableOn Real f s；h : forall x in s, f x != 0 ∨ 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.rpow_const`：DifferentiableWithinAt.rpow_const (hf
 : DifferentiableWithinAt Real f s x) (h : f x != 0 ∨ 1 <= p) : DifferentiableWi
thinAt Real (fun x => f…
-/
theorem DifferentiableOn.rpow_const (hf : DifferentiableOn ℝ f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 1 ≤ p) :
    DifferentiableOn ℝ (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const (h x hx)

@[fun_prop]
/-
**Differentiable.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.rpow_const (hf : Differentiable Real f) (h : forall x, f x 
!= 0 ∨ 1 <= p) : Differentiable Real fun x => f x ^ p
参数：hf : Differentiable Real f；h : forall x, f x != 0 ∨ 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.rpow_const`：DifferentiableAt.rpow_const (hf : Different
iableAt Real f x) (h : f x != 0 ∨ 1 <= p) : DifferentiableAt Real (fun x => f x 
^ p) x
-/
theorem Differentiable.rpow_const (hf : Differentiable ℝ f) (h : ∀ x, f x ≠ 0 ∨ 1 ≤ p) :
    Differentiable ℝ fun x => f x ^ p := fun x => (hf x).rpow_const (h x)
/-
**HasFDerivWithinAt.const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.const_rpow (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c
) : HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') s x
参数：hf : HasFDerivWithinAt f f' s x；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_const_rpow`：hasStrictDerivAt_const_rpow {a : Real}
 (ha : 0 < a) (x : Real) : HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x
-/
theorem HasFDerivWithinAt.const_rpow (hf : HasFDerivWithinAt f f' s x) (hc : 0 < c) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') s x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivWithinAt x hf
/-
**HasFDerivAt.const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.const_rpow (hf : HasFDerivAt f f' x) (hc : 0 < c) : HasFDerivA
t (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x
参数：hf : HasFDerivAt f f' x；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_const_rpow`：hasStrictDerivAt_const_rpow {a : Real}
 (ha : 0 < a) (x : Real) : HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x
-/
theorem HasFDerivAt.const_rpow (hf : HasFDerivAt f f' x) (hc : 0 < c) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).hasDerivAt.comp_hasFDerivAt x hf
/-
**HasStrictFDerivAt.const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.const_rpow (hf : HasStrictFDerivAt f f' x) (hc : 0 < c) 
: HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x
参数：hf : HasStrictFDerivAt f f' x；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Real.hasStrictDerivAt_const_rpow`：hasStrictDerivAt_const_rpow {a : Real}
 (ha : 0 < a) (x : Real) : HasStrictDerivAt (fun x => a ^ x) (a ^ x * log a) x
-/
theorem HasStrictFDerivAt.const_rpow (hf : HasStrictFDerivAt f f' x) (hc : 0 < c) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Real.log c) • f') x :=
  (hasStrictDerivAt_const_rpow hc (f x)).comp_hasStrictFDerivAt x hf

@[fun_prop]
/-
**ContDiffWithinAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.rpow (hf : ContDiffWithinAt Real n f s x) (hg : ContDiffW
ithinAt Real n g s x) (h : f x != 0) : ContDiffWithinAt Real n (fun x => f x ^ g
 x) s x
参数：hf : ContDiffWithinAt Real n f s x；hg : ContDiffWithinAt Real n g s x；h : f x
 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `Real.contDiffAt_rpow_of_ne`：contDiffAt_rpow_of_ne (p : Real × Real) (hp 
: p.1 != 0) {n : WithTop Nat∞} : ContDiffAt Real n (fun p : Real × Real => p.1 ^
 p.2) p
· 使用定理 `ContDiffWithinAt.prodMk`：ContDiffWithinAt.prodMk {s : Set E} {f : E -> F
} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s 
x) : ContDiff…
-/
theorem ContDiffWithinAt.rpow (hf : ContDiffWithinAt ℝ n f s x) (hg : ContDiffWithinAt ℝ n g s x)
    (h : f x ≠ 0) : ContDiffWithinAt ℝ n (fun x => f x ^ g x) s x := by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp_contDiffWithinAt x (hf.prodMk hg)

@[fun_prop]
/-
**ContDiffAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.rpow (hf : ContDiffAt Real n f x) (hg : ContDiffAt Real n g x) 
(h : f x != 0) : ContDiffAt Real n (fun x => f x ^ g x) x
参数：hf : ContDiffAt Real n f x；hg : ContDiffAt Real n g x；h : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Real.contDiffAt_rpow_of_ne`：contDiffAt_rpow_of_ne (p : Real × Real) (hp 
: p.1 != 0) {n : WithTop Nat∞} : ContDiffAt Real n (fun p : Real × Real => p.1 ^
 p.2) p
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
-/
theorem ContDiffAt.rpow (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ g x) x := by
  -- `by exact` to deal with tricky unification.
  exact (contDiffAt_rpow_of_ne (f x, g x) h).comp x (hf.prodMk hg)

@[fun_prop]
/-
**ContDiffOn.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.rpow (hf : ContDiffOn Real n f s) (hg : ContDiffOn Real n g s) 
(h : forall x in s, f x != 0) : ContDiffOn Real n (fun x => f x ^ g x) s
参数：hf : ContDiffOn Real n f s；hg : ContDiffOn Real n g s；h : forall x in s, f x 
!= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.rpow`：ContDiffWithinAt.rpow (hf : ContDiffWithinAt Real
 n f s x) (hg : ContDiffWithinAt Real n g s x) (h : f x != 0) : ContDiffWithinAt
 Real n (fu…
-/
theorem ContDiffOn.rpow (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ g x) s := fun x hx => (hf x hx).rpow (hg x hx) (h x hx)

@[fun_prop]
/-
**ContDiff.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.rpow (hf : ContDiff Real n f) (hg : ContDiff Real n g) (h : foral
l x, f x != 0) : ContDiff Real n fun x => f x ^ g x
参数：hf : ContDiff Real n f；hg : ContDiff Real n g；h : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.rpow`：ContDiffAt.rpow (hf : ContDiffAt Real n f x) (hg : Cont
DiffAt Real n g x) (h : f x != 0) : ContDiffAt Real n (fun x => f x ^ g x) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.rpow (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ g x :=
  contDiff_iff_contDiffAt.mpr fun x => hf.contDiffAt.rpow hg.contDiffAt (h x)

@[fun_prop]
/-
**ContDiffWithinAt.rpow_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.rpow_const_of_ne (hf : ContDiffWithinAt Real n f s x) (h 
: f x != 0) : ContDiffWithinAt Real n (fun x => f x ^ p) s x
参数：hf : ContDiffWithinAt Real n f s x；h : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.rpow`：ContDiffWithinAt.rpow (hf : ContDiffWithinAt Real
 n f s x) (hg : ContDiffWithinAt Real n g s x) (h : f x != 0) : ContDiffWithinAt
 Real n (fu…
· 使用定理 `contDiffWithinAt_const`：contDiffWithinAt_const {c : F} : ContDiffWithinA
t 𝕜 n (fun _ : E => c) s x
-/
theorem ContDiffWithinAt.rpow_const_of_ne (hf : ContDiffWithinAt ℝ n f s x) (h : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => f x ^ p) s x :=
  hf.rpow contDiffWithinAt_const h

@[fun_prop]
/-
**ContDiffAt.rpow_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.rpow_const_of_ne (hf : ContDiffAt Real n f x) (h : f x != 0) : 
ContDiffAt Real n (fun x => f x ^ p) x
参数：hf : ContDiffAt Real n f x；h : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.rpow`：ContDiffAt.rpow (hf : ContDiffAt Real n f x) (hg : Cont
DiffAt Real n g x) (h : f x != 0) : ContDiffAt Real n (fun x => f x ^ g x) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
-/
theorem ContDiffAt.rpow_const_of_ne (hf : ContDiffAt ℝ n f x) (h : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => f x ^ p) x :=
  hf.rpow contDiffAt_const h

@[fun_prop]
/-
**ContDiffOn.rpow_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.rpow_const_of_ne (hf : ContDiffOn Real n f s) (h : forall x in 
s, f x != 0) : ContDiffOn Real n (fun x => f x ^ p) s
参数：hf : ContDiffOn Real n f s；h : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.rpow_const_of_ne`：ContDiffWithinAt.rpow_const_of_ne (hf
 : ContDiffWithinAt Real n f s x) (h : f x != 0) : ContDiffWithinAt Real n (fun 
x => f x ^ p) s x
-/
theorem ContDiffOn.rpow_const_of_ne (hf : ContDiffOn ℝ n f s) (h : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_ne (h x hx)

@[fun_prop]
/-
**ContDiff.rpow_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.rpow_const_of_ne (hf : ContDiff Real n f) (h : forall x, f x != 0
) : ContDiff Real n fun x => f x ^ p
参数：hf : ContDiff Real n f；h : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.rpow`：ContDiff.rpow (hf : ContDiff Real n f) (hg : ContDiff Rea
l n g) (h : forall x, f x != 0) : ContDiff Real n fun x => f x ^ g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
-/
theorem ContDiff.rpow_const_of_ne (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => f x ^ p :=
  hf.rpow contDiff_const h

variable {m : ℕ}

@[fun_prop]
/-
**ContDiffWithinAt.rpow_const_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.rpow_const_of_le (hf : ContDiffWithinAt Real m f s x) (h 
: ↑m <= p) : ContDiffWithinAt Real m (fun x => f x ^ p) s x
参数：hf : ContDiffWithinAt Real m f s x；h : ↑m <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `Real.contDiffAt_rpow_const_of_le`：contDiffAt_rpow_const_of_le {x p : Rea
l} {n : Nat} (h : ↑n <= p) : ContDiffAt Real n (fun x : Real => x ^ p) x
-/
theorem ContDiffWithinAt.rpow_const_of_le (hf : ContDiffWithinAt ℝ m f s x) (h : ↑m ≤ p) :
    ContDiffWithinAt ℝ m (fun x => f x ^ p) s x :=
  (contDiffAt_rpow_const_of_le h).comp_contDiffWithinAt x hf

@[fun_prop]
/-
**ContDiffAt.rpow_const_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.rpow_const_of_le (hf : ContDiffAt Real m f x) (h : ↑m <= p) : C
ontDiffAt Real m (fun x => f x ^ p) x
参数：hf : ContDiffAt Real m f x；h : ↑m <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contDiffWithinAt_univ`：contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f un
iv x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffWithinAt.rpow_const_of_le`：ContDiffWithinAt.rpow_const_of_le (hf
 : ContDiffWithinAt Real m f s x) (h : ↑m <= p) : ContDiffWithinAt Real m (fun x
 => f x ^ p) s x
-/
theorem ContDiffAt.rpow_const_of_le (hf : ContDiffAt ℝ m f x) (h : ↑m ≤ p) :
    ContDiffAt ℝ m (fun x => f x ^ p) x := by
  rw [← contDiffWithinAt_univ] at *; exact hf.rpow_const_of_le h

@[fun_prop]
/-
**ContDiffOn.rpow_const_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.rpow_const_of_le (hf : ContDiffOn Real m f s) (h : ↑m <= p) : C
ontDiffOn Real m (fun x => f x ^ p) s
参数：hf : ContDiffOn Real m f s；h : ↑m <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.rpow_const_of_le`：ContDiffWithinAt.rpow_const_of_le (hf
 : ContDiffWithinAt Real m f s x) (h : ↑m <= p) : ContDiffWithinAt Real m (fun x
 => f x ^ p) s x
-/
theorem ContDiffOn.rpow_const_of_le (hf : ContDiffOn ℝ m f s) (h : ↑m ≤ p) :
    ContDiffOn ℝ m (fun x => f x ^ p) s := fun x hx => (hf x hx).rpow_const_of_le h

@[fun_prop]
/-
**ContDiff.rpow_const_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.rpow_const_of_le (hf : ContDiff Real m f) (h : ↑m <= p) : ContDif
f Real m fun x => f x ^ p
参数：hf : ContDiff Real m f；h : ↑m <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.rpow_const_of_le`：ContDiffAt.rpow_const_of_le (hf : ContDiffA
t Real m f x) (h : ↑m <= p) : ContDiffAt Real m (fun x => f x ^ p) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.rpow_const_of_le (hf : ContDiff ℝ m f) (h : ↑m ≤ p) :
    ContDiff ℝ m fun x => f x ^ p :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.rpow_const_of_le h

end fderiv

section deriv

variable {f g : ℝ → ℝ} {f' g' x y p : ℝ} {s : Set ℝ}

/-
**HasDerivWithinAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithi
nAt g g' s x) (h : 0 < f x) : HasDerivWithinAt (fun x => f x ^ g x) (f' * g x * 
f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) s x
参数：hf : HasDerivWithinAt f f' s x；hg : HasDerivWithinAt g g' s x；h : 0 < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
（共 36 条，此处仅展示前 30 条）
-/
theorem HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h : 0 < f x) : HasDerivWithinAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) s x := by
  convert! (hf.hasFDerivWithinAt.rpow hg.hasFDerivWithinAt h).hasDerivWithinAt using 1
  simp; ring
/-
**HasDerivAt.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 <
 f x) : HasDerivAt (fun x => f x ^ g x) (f' * g x * f x ^ (g x - 1) + g' * f x ^
 g x * Real.log (f x)) x
参数：hf : HasDerivAt f f' x；hg : HasDerivAt g g' x；h : 0 < f x。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.rpow`：HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f'
 s x) (hg : HasDerivWithinAt g g' s x) (h : 0 < f x) : HasDerivWithinAt (fun x =
> f x ^ g x…
-/
theorem HasDerivAt.rpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) (h : 0 < f x) :
    HasDerivAt (fun x => f x ^ g x)
      (f' * g x * f x ^ (g x - 1) + g' * f x ^ g x * Real.log (f x)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow hg h
/-
**HasDerivWithinAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.rpow_const (hf : HasDerivWithinAt f f' s x) (hx : f x != 
0 ∨ 1 <= p) : HasDerivWithinAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) s x
参数：hf : HasDerivWithinAt f f' s x；hx : f x != 0 ∨ 1 <= p。
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
-/
theorem HasDerivWithinAt.rpow_const (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivWithinAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) s x := by
  convert! (hasDerivAt_rpow_const hx).comp_hasDerivWithinAt x hf using 1
  ring
/-
**HasDerivAt.rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x != 0 ∨ 1 <= p) : 
HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x
参数：hf : HasDerivAt f f' x；hx : f x != 0 ∨ 1 <= p。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.rpow_const`：HasDerivWithinAt.rpow_const (hf : HasDerivW
ithinAt f f' s x) (hx : f x != 0 ∨ 1 <= p) : HasDerivWithinAt (fun y => f y ^ p)
 (f' * p * f x ^ …
-/
theorem HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.rpow_const hx
/-
**derivWithin_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_rpow_const (hf : DifferentiableWithinAt Real f s x) (hx : f x 
!= 0 ∨ 1 <= p) (hxs : UniqueDiffWithinAt Real s x) : derivWithin (fun x => f x ^
 p) s x = derivWithin f s x * p * f x ^ (p - 1)
参数：hf : DifferentiableWithinAt Real f s x；hx : f x != 0 ∨ 1 <= p；hxs : UniqueDif
fWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.rpow_const`：HasDerivWithinAt.rpow_const (hf : HasDerivW
ithinAt f f' s x) (hx : f x != 0 ∨ 1 <= p) : HasDerivWithinAt (fun y => f y ^ p)
 (f' * p * f x ^ …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_rpow_const (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0 ∨ 1 ≤ p)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => f x ^ p) s x = derivWithin f s x * p * f x ^ (p - 1) :=
  (hf.hasDerivWithinAt.rpow_const hx).derivWithin hxs

@[simp]
/-
**deriv_rpow_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_rpow_const (hf : DifferentiableAt Real f x) (hx : f x != 0 ∨ 1 <= p)
 : deriv (fun x => f x ^ p) x = deriv f x * p * f x ^ (p - 1)
参数：hf : DifferentiableAt Real f x；hx : f x != 0 ∨ 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.rpow_const`：HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (h
x : f x != 0 ∨ 1 <= p) : HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) 
x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_rpow_const (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
    deriv (fun x => f x ^ p) x = deriv f x * p * f x ^ (p - 1) :=
  (hf.hasDerivAt.rpow_const hx).deriv
/-
**deriv_norm_ofReal_cpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_norm_ofReal_cpow (c : Complex) {t : Real} (ht : 0 < t) : (deriv fun 
x : Real => ‖(x : Complex) ^ c‖) t = c.re * t ^ (c.re - 1)
参数：c : Complex；ht : 0 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.deriv_eq`：Filter.EventuallyEq.deriv_eq (hL : f₁ =ᶠ[𝓝
 x] f) : deriv f₁ x = deriv f x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_gt_nhds`：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b < x
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Complex.norm_cpow_eq_rpow_re_of_pos`：norm_cpow_eq_rpow_re_of_pos {x : Re
al} (hx : 0 < x) (y : Complex) : ‖(x : Complex) ^ y‖ = x ^ y.re
· 使用定理 `Real.deriv_rpow_const`：deriv_rpow_const (x p : Real) : deriv (fun x => x
 ^ p) x = p * x ^ (p - 1)
-/
theorem deriv_norm_ofReal_cpow (c : ℂ) {t : ℝ} (ht : 0 < t) :
    (deriv fun x : ℝ ↦ ‖(x : ℂ) ^ c‖) t = c.re * t ^ (c.re - 1) := by
  rw [EventuallyEq.deriv_eq (f := fun x ↦ x ^ c.re)]
  · rw [Real.deriv_rpow_const t]
  · filter_upwards [eventually_gt_nhds ht] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
/-
**isTheta_deriv_rpow_const_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isTheta_deriv_rpow_const_atTop {p : Real} (hp : p != 0) : deriv (fun (x : 
Real) => x ^ p) =Θ[atTop] fun x => x ^ (p - 1)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.deriv_rpow_const'`：deriv_rpow_const' (p : Real) : (deriv fun x : Re
al => x ^ p) = fun x => p * x ^ (p - 1)
· 使用定理 `Asymptotics.IsTheta.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {𝕜 :
 Type u_14} [inst : Norm F] [inst_1 : NormedField 𝕜] {g : α → F} {l : Filter α} 
  {c : 𝕜} {f : α → 𝕜}, c…
· 使用定理 `Asymptotics.isTheta_rfl`：isTheta_rfl : f =Θ[l] f
-/
lemma isTheta_deriv_rpow_const_atTop {p : ℝ} (hp : p ≠ 0) :
    deriv (fun (x : ℝ) ↦ x ^ p) =Θ[atTop] fun x => x ^ (p - 1) := by
  calc deriv (fun (x : ℝ) ↦ x ^ p) = fun x => p * x ^ (p - 1) := Real.deriv_rpow_const' p
    _ =Θ[atTop] fun x ↦ x ^ (p - 1) :=
      Asymptotics.IsTheta.const_mul_left hp Asymptotics.isTheta_rfl
/-
**isBigO_deriv_rpow_const_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBigO_deriv_rpow_const_atTop (p : Real) : deriv (fun (x : Real) => x ^ p)
 =O[atTop] fun x => x ^ (p - 1)
参数：p : Real。
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
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Real.rpow_neg_one`：rpow_neg_one (x : Real) : x ^ (-1 : Real) = x⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `isTheta_deriv_rpow_const_atTop`：isTheta_deriv_rpow_const_atTop {p : Real
} (hp : p != 0) : deriv (fun (x : Real) => x ^ p) =Θ[atTop] fun x => x ^ (p - 1)
-/
lemma isBigO_deriv_rpow_const_atTop (p : ℝ) :
    deriv (fun (x : ℝ) => x ^ p) =O[atTop] fun x => x ^ (p - 1) := by
  rcases eq_or_ne p 0 with rfl | hp
  case inl =>
    simp [zero_sub, Real.rpow_neg_one, Real.rpow_zero, deriv_const', Asymptotics.isBigO_zero]
  case inr =>
    exact (isTheta_deriv_rpow_const_atTop hp).1

variable {a : ℝ}
/-
**HasDerivWithinAt.const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.const_rpow (ha : 0 < a) (hf : HasDerivWithinAt f f' s x) 
: HasDerivWithinAt (a ^ f ·) (Real.log a * f' * a ^ f x) s x
参数：ha : 0 < a；hf : HasDerivWithinAt f f' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `HasDerivWithinAt.rpow`：HasDerivWithinAt.rpow (hf : HasDerivWithinAt f f'
 s x) (hg : HasDerivWithinAt g g' s x) (h : 0 < f x) : HasDerivWithinAt (fun x =
> f x ^ g x…
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
-/
theorem HasDerivWithinAt.const_rpow (ha : 0 < a) (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (a ^ f ·) (Real.log a * f' * a ^ f x) s x := by
  convert! (hasDerivWithinAt_const x s a).rpow hf ha using 1
  ring
/-
**HasDerivAt.const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.const_rpow (ha : 0 < a) (hf : HasDerivAt f f' x) : HasDerivAt (
a ^ f ·) (Real.log a * f' * a ^ f x) x
参数：ha : 0 < a；hf : HasDerivAt f f' x。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasDerivWithinAt_univ`：hasDerivWithinAt_univ : HasDerivWithinAt f f' uni
v x ↔ HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.const_rpow`：HasDerivWithinAt.const_rpow (ha : 0 < a) (h
f : HasDerivWithinAt f f' s x) : HasDerivWithinAt (a ^ f ·) (Real.log a * f' * a
 ^ f x) s x
-/
theorem HasDerivAt.const_rpow (ha : 0 < a) (hf : HasDerivAt f f' x) :
    HasDerivAt (a ^ f ·) (Real.log a * f' * a ^ f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.const_rpow ha
/-
**derivWithin_const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_const_rpow (ha : 0 < a) (hf : DifferentiableWithinAt Real f s 
x) : derivWithin (a ^ f ·) s x = Real.log a * derivWithin f s x * a ^ f x
参数：ha : 0 < a；hf : DifferentiableWithinAt Real f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `HasDerivWithinAt.const_rpow`：HasDerivWithinAt.const_rpow (ha : 0 < a) (h
f : HasDerivWithinAt f f' s x) : HasDerivWithinAt (a ^ f ·) (Real.log a * f' * a
 ^ f x) s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `derivWithin_zero_of_not_uniqueDiffWithinAt`：derivWithin_zero_of_not_uniq
ueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem derivWithin_const_rpow (ha : 0 < a) (hf : DifferentiableWithinAt ℝ f s x) :
    derivWithin (a ^ f ·) s x = Real.log a * derivWithin f s x * a ^ f x := by
  by_cases hxs : UniqueDiffWithinAt ℝ s x
  · exact (hf.hasDerivWithinAt.const_rpow ha).derivWithin hxs
  · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      derivWithin_zero_of_not_uniqueDiffWithinAt hxs,
      mul_zero, zero_mul]

@[simp]
/-
**deriv_const_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_rpow (ha : 0 < a) (hf : DifferentiableAt Real f x) : deriv (a 
^ f ·) x = Real.log a * deriv f x * a ^ f x
参数：ha : 0 < a；hf : DifferentiableAt Real f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasDerivAt.const_rpow`：HasDerivAt.const_rpow (ha : 0 < a) (hf : HasDeriv
At f f' x) : HasDerivAt (a ^ f ·) (Real.log a * f' * a ^ f x) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_const_rpow (ha : 0 < a) (hf : DifferentiableAt ℝ f x) :
    deriv (a ^ f ·) x = Real.log a * deriv f x * a ^ f x :=
  (hf.hasDerivAt.const_rpow ha).deriv

@[simp]
/-
**deriv_const_rpow_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_const_rpow_id (ha : 0 < a) : deriv (a ^ ·) x = Real.log a * a ^ x
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_const_rpow`：deriv_const_rpow (ha : 0 < a) (hf : DifferentiableAt R
eal f x) : deriv (a ^ f ·) x = Real.log a * deriv f x * a ^ f x
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem deriv_const_rpow_id (ha : 0 < a) :
    deriv (a ^ ·) x = Real.log a * a ^ x := by
  rw [deriv_const_rpow ha differentiableAt_fun_id, deriv_id'', mul_one]

end deriv

end Differentiability

