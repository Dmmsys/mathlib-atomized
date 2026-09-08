/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.RadiusLiminf

/-!
# Gelfand's formula and other results on the spectrum in complex Banach algebras

This file contains results on the spectrum of elements in a complex Banach algebra, including
**Gelfand's formula** and the **Gelfand-Mazur theorem** and the fact that every element in a
complex Banach algebra has nonempty spectrum.

## Main results

* `spectrum.hasDerivAt_resolvent_const_left`: the resolvent function is differentiable on the
  resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.
* `NormedRing.algEquivComplexOfComplete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebraMap ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Implementation notes

Note that it is important here that the complex analysis files are privately imported, since the
material proven here gets used in contexts that have nothing to do with complex analysis
(i.e. C⋆-algebras, etc).

-/

@[expose] public section

variable {𝕜 A : Type*}

open scoped NNReal Topology Ring
open Filter ENNReal

namespace spectrum

section NonTriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-
**spectrum.hasDerivAt_resolvent_const_left** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：hasDerivAt_resolvent_const_left {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 
a) : HasDerivAt (resolvent a) (-resolvent a k ^ 2) k
参数：hk : k in resolventSet 𝕜 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `hasFDerivAt_ringInverse`：hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt 
Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
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
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `LinearMap.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {x : 𝕜
} (e : 𝕜 →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
-/
theorem hasDerivAt_resolvent_const_left {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasDerivAt (resolvent a) (-resolvent a k ^ 2) k := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k := by
    simpa using! (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolvent, sq, hk.unit_spec, ← Ring.inverse_unit hk.unit] using! H₁.comp_hasDerivAt k H₂

@[deprecated (since := "2026-03-26")]
alias hasDerivAt_resolvent := hasDerivAt_resolvent_const_left
/-
**spectrum.hasFDerivAt_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：hasFDerivAt_resolvent {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a) : HasFD
erivAt (resolvent · k) (((ContinuousLinearMap.mulLeftRight 𝕜 A) (resolvent a k))
 (resolvent a k)) a
参数：hk : k in resolventSet 𝕜 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `hasFDerivAt_ringInverse`：hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt 
Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `HasFDerivAt.sub`：HasFDerivAt.sub (hf : HasFDerivAt f f' x) (hg : HasFDer
ivAt g g' x) : HasFDerivAt (f - g) (f' - g') x
· 使用定理 `hasFDerivAt_const`：hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun 
_ => c) (0 : E ->L[𝕜] F) x
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `spectrum.resolvent_eq`：resolvent_eq {a : A} {r : R} (h : r in resolventS
et R a) : resolvent a r = ↑h.unit⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.comp_neg`：comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [
IsTopologicalAddGroup M₂] [IsTopologicalAddGroup M₃] (g : M₂ ->SL[σ₂₃] M₃) (f : 
M ->SL[σ₁₂] M₂) : …
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
-/
theorem hasFDerivAt_resolvent {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasFDerivAt (resolvent · k)
      (((ContinuousLinearMap.mulLeftRight 𝕜 A) (resolvent a k)) (resolvent a k)) a := by
  have H₁ : HasFDerivAt Ring.inverse _ (algebraMap 𝕜 A k - a) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hk.unit
  have H₂ : HasFDerivAt (fun a => algebraMap 𝕜 A k - a) (- .id 𝕜 A) a := by
    simpa using! (hasFDerivAt_const _ a).sub (hasFDerivAt_id a)
  simpa [resolvent_eq hk] using! H₁.comp a H₂

end NonTriviallyNormedField

/-
**spectrum.hasDerivAt_resolvent_const_right** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`
。
形式化陈述：hasDerivAt_resolvent_const_right [NontriviallyNormedField 𝕜] [Nontrivially
NormedField A] [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {k : 𝕜} (hk : k in 
resolventSet 𝕜 a) : HasDerivAt (resolvent · k) (resolvent a k ^ 2) a
参数：hk : k in resolventSet 𝕜 a。
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivAt.hasDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜
] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 
: Topologica…
· 使用定理 `spectrum.hasFDerivAt_resolvent`：hasFDerivAt_resolvent {a : A} {k : 𝕜} (h
k : k in resolventSet 𝕜 a) : HasFDerivAt (resolvent · k) (((ContinuousLinearMap.
mulLeftRight 𝕜 A) (r…
-/
theorem hasDerivAt_resolvent_const_right [NontriviallyNormedField 𝕜] [NontriviallyNormedField A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasDerivAt (resolvent · k) (resolvent a k ^ 2) a := by
  convert! hasFDerivAt_resolvent (𝕜 := A) hk |>.hasDerivAt
  simp [resolvent, pow_two]

open ENNReal in
/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `fun z ↦ (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectralRadius 𝕜 a)⁻¹`. -/
/-
**spectrum.differentiableOn_inverse_one_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 `spec
trum`。
形式化陈述：differentiableOn_inverse_one_sub_smul [NontriviallyNormedField 𝕜] [NormedR
ing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {r : Real>=0} (hr : (r : Re
al>=0∞) < (spectralRadius 𝕜 a)⁻¹) : DifferentiableOn 𝕜 (fun z : 𝕜 => (1 - z • a)
⁻¹ʳ) (Metric.closedBall 0 r)
参数：hr : (r : Real>=0∞) < (spectralRadius 𝕜 a)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `spectrum.isUnit_one_sub_smul_of_lt_inv_radius`：isUnit_one_sub_smul_of_lt
_inv_radius {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹) : IsUnit (1 - z
 • a)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_toNNReal`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E}, ‖
a‖.toNNReal = ‖a‖₊
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `Real.toNNReal_mono`：∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → r₁.toNNReal ≤ r₂.toNNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `Differentiable.const_sub`：Differentiable.const_sub (hf : Differentiable 
𝕜 f) (c : F) : Differentiable 𝕜 fun y => c - f y
· 使用定理 `Differentiable.smul_const`：Differentiable.smul_const (hc : Differentiabl
e 𝕜 c) (f : F) : Differentiable 𝕜 fun y => c y • f
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `differentiableAt_inverse`：differentiableAt_inverse {x : R} (hx : IsUnit 
x) : DifferentiableAt 𝕜 (@Ring.inverse R _) x
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x

--- 原说明 ---
In a Banach algebra `A` over `𝕜`, for `a : A` the function `fun z ↦ (1 - z • a)⁻
¹` is
differentiable on any closed ball centered at zero of radius `r < (spectralRadiu
s 𝕜 a)⁻¹`.
-/
theorem differentiableOn_inverse_one_sub_smul [NontriviallyNormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜 (fun z : 𝕜 => (1 - z • a)⁻¹ʳ) (Metric.closedBall 0 r) := by
  intro z z_mem
  apply DifferentiableAt.differentiableWithinAt
  have hu : IsUnit (1 - z • a) := by
    refine isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono ?_) hr)
    simpa only [norm_toNNReal, Real.toNNReal_coe] using
      Real.toNNReal_mono (mem_closedBall_zero_iff.mp z_mem)
  have H₁ : Differentiable 𝕜 fun w : 𝕜 => 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact DifferentiableAt.comp z (differentiableAt_inverse hu) H₁.differentiableAt

section Complex

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

open ContinuousMultilinearMap in
/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
/-
**spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius** 是 Mathlib 中的一个定理，位于
命名空间 `spectrum`。
形式化陈述：limsup_pow_nnnorm_pow_one_div_le_spectralRadius (a : A) : limsup (fun n : 
Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) atTop <= spectralRadius Complex a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.inv_le_inv`：∀ {a b : ENNReal}, a⁻¹ ≤ b⁻¹ ↔ b ≤ a
· 使用定理 `ENNReal.le_of_forall_pos_nnreal_lt`：le_of_forall_pos_nnreal_lt {x y : Re
al>=0∞} (h : forall r : Real>=0, 0 < r -> ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_limsup`：inv_limsup {ι : Sort _} {x : ι -> Real>=0∞} {l : Fil
ter ι} : (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableOn.hasFPowerSeriesOnBall`：∀ {E : Type u} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {R : NNReal} {c : ℂ}  
 {f : ℂ → E},   Differentiab…
· 使用定理 `spectrum.differentiableOn_inverse_one_sub_smul`：differentiableOn_inverse
_one_sub_smul [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [Co
mpleteSpace A] {a : A} {r : Real>=0}…
· 使用定理 `HasFPowerSeriesOnBall.r_le`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.exchange_radius`：HasFPowerSeriesOnBall.exchange_ra
dius {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {r₁ r₂ : Real>=0∞} {x 
: 𝕜} (h₁ : HasFPowerSeriesO…
· 使用定理 `spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul`：hasFPowerSeriesOnBa
ll_inverse_one_sub_smul [HasSummableGeomSeries A] (a : A) : HasFPowerSeriesOnBal
l (fun z : 𝕜 => Ring.inverse (1 - z • a))…
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FormalMultilinearSeries.radius_eq_liminf`：radius_eq_liminf : p.radius = 
liminf (fun n => (1 / (‖p n‖₊ ^ (1 / (n : Real)) : Real>=0) : Real>=0∞)) atTop
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
The `limsup` relationship for the spectral radius used to prove `spectrum.gelfan
d_formula`.
-/
theorem limsup_pow_nnnorm_pow_one_div_le_spectralRadius (a : A) :
    limsup (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop ≤ spectralRadius ℂ a := by
  refine ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [inv_limsup, ← one_div]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius by
    convert! h
    simp only [p, p.radius_eq_liminf, ← norm_toNNReal, norm_mkPiRing]
    congr
    ext n
    rw [norm_toNNReal, ENNReal.coe_rpow_def ‖a ^ n‖₊ (1 / n : ℝ), if_neg]
    exact fun ha => (lt_self_iff_false _).mp
      (ha.2.trans_le (one_div_nonneg.mpr n.cast_nonneg : 0 ≤ (1 / n : ℝ)))
  have H₁ := (differentiableOn_inverse_one_sub_smul r_lt).hasFPowerSeriesOnBall r_pos
  exact ((hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).exchange_radius H₁).r_le

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
/-
**spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius** 是 Mathlib 中的一个定理
，位于命名空间 `spectrum`。
形式化陈述：pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A) : Tendsto (fun 
n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)) atTop (𝓝 (spectralRadius Comp
lex a))
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_le_liminf_of_limsup_le`：tendsto_of_le_liminf_of_limsup_le {f 
: Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f) (hsup : limsup u f <= 
a) (h : f.IsBoundedUnde…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `spectrum.spectralRadius_le_liminf_pow_nnnorm_pow_one_div`：spectralRadius
_le_liminf_pow_nnnorm_pow_one_div (a : A) : spectralRadius 𝕜 a <= atTop.liminf f
un n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n :…
· 使用定理 `spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius`：limsup_pow_nnn
orm_pow_one_div_le_spectralRadius (a : A) : limsup (fun n : Nat => (‖a ^ n‖₊ : R
eal>=0∞) ^ (1 / n : Real)) atTop <= spectralRa…
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f

--- 原说明 ---
**Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`.
-/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ a)) :=
  tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)

alias gelfand_formula := pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` but for `norm`
instead of `nnnorm`. -/
/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
/-
**spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius** 是 Mathlib 中的一个定理，位
于命名空间 `spectrum`。
形式化陈述：pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) : Tendsto (fun n 
: Nat => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : Real))) atTop (𝓝 (spectralRadius Com
plex a))
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_rpow_of_nonneg`：ofReal_rpow_of_nonneg {x p : Real} (hx_no
nneg : 0 <= x) (hp_nonneg : 0 <= p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^
 p)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`：pow_nnnorm_
pow_one_div_tendsto_nhds_spectralRadius (a : A) : Tendsto (fun n : Nat => (‖a ^ 
n‖₊ : Real>=0∞) ^ (1 / n : Real)) atTop (𝓝 (spect…

--- 原说明 ---
**Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`.
-/
theorem pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a)) := by
  convert! pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  simp

section Nontrivial

variable [Nontrivial A]

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
/-
**spectrum.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : NormedAlgebra ℂ A] [Compl
eteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonempty
参数：a : A；spectrum ℂ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `spectrum.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [inst
_1 : Ring A] [inst_2 : Algebra R A] (a : A),   spectrum R a = (resolventSet R a)
ᶜ
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `spectrum.hasDerivAt_resolvent_const_left`：hasDerivAt_resolvent_const_lef
t {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a) : HasDerivAt (resolvent a) (-reso
lvent a k ^ 2) k
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Differentiable.apply_eq_of_tendsto_cocompact`：apply_eq_of_tendsto_cocomp
act [Nontrivial E] {f : E -> F} (hf : Differentiable Complex f) {c : F} (x : E) 
(hb : Tendsto f (cocompact E) (𝓝 c…
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `spectrum.resolvent_tendsto_cobounded`：resolvent_tendsto_cobounded (a : A
) : Tendsto (resolvent a) (cobounded 𝕜) (𝓝 0)
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `spectrum.isUnit_resolvent`：isUnit_resolvent {r : R} {a : A} : r in resol
ventSet R a ↔ IsUnit (resolvent a r)

--- 原说明 ---
In a (nontrivial) complex Banach algebra, every element has nonempty spectrum.
-/
protected theorem nonempty (a : A) : (spectrum ℂ a).Nonempty := by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet ℂ a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  have H₁ : Differentiable ℂ fun z : ℂ => resolvent a z := fun z =>
    hasDerivAt_resolvent_const_left (H₀.symm ▸ Set.mem_univ z : z ∈ resolventSet ℂ a)
      |>.differentiableAt
  /- Since `resolvent a` tends to zero at infinity, by Liouville's theorem `resolvent a = 0`,
  which contradicts that `resolvent a z` is invertible. -/
  have H₃ := H₁.apply_eq_of_tendsto_cocompact 0 <| by
    simpa [Metric.cobounded_eq_cocompact] using resolvent_tendsto_cobounded a (𝕜 := ℂ)
  exact not_isUnit_zero <| H₃ ▸ (isUnit_resolvent.mp <| H₀.symm ▸ Set.mem_univ 0)

/-- In a complex Banach algebra, the spectral radius is always attained by some element of the
spectrum. -/
/-
**spectrum.exists_nnnorm_eq_spectralRadius** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：exists_nnnorm_eq_spectralRadius (a : A) : exists z in spectrum Complex a, 
(‖z‖₊ : Real>=0∞) = spectralRadius Complex a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty`：exists_nnnorm_eq_s
pectralRadius_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty) : exists
 k in σ a, (‖k‖₊ : Real>=0∞) = spectralRad…
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty

--- 原说明 ---
In a complex Banach algebra, the spectral radius is always attained by some elem
ent of the
spectrum.
-/
theorem exists_nnnorm_eq_spectralRadius (a : A) :
    ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)

/-- In a complex Banach algebra, if every element of the spectrum has norm strictly less than
`r : ℝ≥0`, then the spectral radius is also strictly less than `r`. -/
/-
**spectrum.spectralRadius_lt_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：spectralRadius_lt_of_forall_lt (a : A) {r : Real>=0} (hr : forall z in spe
ctrum Complex a, ‖z‖₊ < r) : spectralRadius Complex a < r
参数：a : A；hr : forall z in spectrum Complex a, ‖z‖₊ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.spectralRadius_lt_of_forall_lt_of_nonempty`：spectralRadius_lt_o
f_forall_lt_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty) {r : Real>
=0} (hr : forall k in σ a, ‖k‖₊ < r) : sp…
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty

--- 原说明 ---
In a complex Banach algebra, if every element of the spectrum has norm strictly 
less than
`r : ℝ≥0`, then the spectral radius is also strictly less than `r`.
-/
theorem spectralRadius_lt_of_forall_lt (a : A) {r : ℝ≥0}
    (hr : ∀ z ∈ spectrum ℂ a, ‖z‖₊ < r) : spectralRadius ℂ a < r :=
  spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr


open Polynomial in
/-- The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`. -/
/-
**spectrum.map_polynomial_aeval** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：map_polynomial_aeval (a : A) (p : Complex[X]) : spectrum Complex (aeval a 
p) = (fun k => eval k p) '' spectrum Complex a
参数：a : A；p : Complex[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.map_polynomial_aeval_of_nonempty`：map_polynomial_aeval_of_nonem
pty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hnon : (σ a).Nonempty) : σ (aeval a p) =
 (fun k => eval k p) '' σ a
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty

--- 原说明 ---
The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`.
-/
theorem map_polynomial_aeval (a : A) (p : ℂ[X]) :
    spectrum ℂ (aeval a p) = (fun k => eval k p) '' spectrum ℂ a :=
  map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)

open Polynomial in
/-- A specialization of the spectral mapping theorem for polynomials in a Banach algebra over `ℂ`
to monic monomials. -/
/-
**spectrum.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : NormedAlgebra ℂ A] [Compl
eteSpace A] [Nontrivial A] (a : A) (n : ℕ),   spectrum ℂ (a ^ n) = (fun x => x ^
 n) '' spectrum ℂ a
参数：a : A；n : ℕ；a ^ n；fun x => x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `spectrum.map_polynomial_aeval`：map_polynomial_aeval (a : A) (p : Complex
[X]) : spectrum Complex (aeval a p) = (fun k => eval k p) '' spectrum Complex a

--- 原说明 ---
A specialization of the spectral mapping theorem for polynomials in a Banach alg
ebra over `ℂ`
to monic monomials.
-/
protected theorem map_pow (a : A) (n : ℕ) :
    spectrum ℂ (a ^ n) = (· ^ n) '' spectrum ℂ a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval a (X ^ n)

end Nontrivial

omit [CompleteSpace A] in
/-
**spectrum.algebraMap_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：algebraMap_eq_of_mem (hA : forall {a : A}, IsUnit a ↔ a != 0) {a : A} {z :
 Complex} (h : z in spectrum Complex a) : algebraMap Complex A z = a
参数：hA : forall {a : A}, IsUnit a ↔ a != 0；h : z in spectrum Complex a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
-/
theorem algebraMap_eq_of_mem (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) {a : A} {z : ℂ}
    (h : z ∈ spectrum ℂ a) : algebraMap ℂ A z = a := by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebraMap ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebraMap_isometry` guarantees this map is an isometry.

Note: because `NormedDivisionRing` requires the field `norm_mul : ∀ a b, ‖a * b‖ = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `NormedRing` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_iff_ne_zero`. -/
@[simps]
/-
**spectrum._root_.NormedRing.algEquivComplexOfComplete** 是 Mathlib 中的一个定义，位于命名空间
 `spectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `a
lgebraMap ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) eleme
nt of
`spectrum ℂ a`. In addition, `algebraMap_isometry` guarantees this map is an iso
metry.

Note: because `NormedDivisionRing` requires the field `norm_mul : ∀ a b, ‖a * b‖
 = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `NormedRing` in which the nonzer
o elements are
precisely the units. This allows for the application of this isomorphism in broa
der contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when
 `A` is actually a
`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_i
ff_ne_zero`.
-/
noncomputable def _root_.NormedRing.algEquivComplexOfComplete (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    ℂ ≃ₐ[ℂ] A :=
  let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId ℂ A with
    toFun := algebraMap ℂ A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using!
        (@spectrum.nonempty _ _ _ _ nt <| algebraMap ℂ A z).some_mem
    right_inv := fun a => algebraMap_eq_of_mem (@hA) (@spectrum.nonempty _ _ _ _ nt a).some_mem }

end Complex

end spectrum

