/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `isConformalMap_complex_linear`: a nonzero complex linear map into an arbitrary complex normed
  space is conformal.

* `isConformalMap_complex_linear_conj`: the composition of a nonzero complex linear map with `conj`
  is complex linear.

* `isConformalMap_iff_is_complex_or_conj_linear`: a real linear map between the complex plane is
  conformal iff it's complex linear or the composition of some complex linear map and `conj`.

* `DifferentiableAt.conformalAt` states that a real-differentiable function with a nonvanishing
  differential from the complex plane into an arbitrary complex-normed space is conformal at a point
  if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

* `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proves that a real-differential
  function with a nonvanishing differential between the complex plane is conformal at a point if and
  only if it's holomorphic or antiholomorphic at that point.

* `differentiableWithinAt_complex_iff_differentiableWithinAt_real` and
  `differentiableAt_complex_iff_differentiableAt_real` characterize complex differentiability in
  terms of the classic Cauchy-Riemann equation.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.

## TODO

* On a connected open set `u`, a function which is `ConformalAt` each point is either holomorphic
  throughout or antiholomorphic throughout.
-/

@[expose] public section


noncomputable section

open Complex ContinuousLinearMap ComplexConjugate

/-
**isConformalMap_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConformalMap_conj : IsConformalMap (conjLIE : Complex ->L[Real] Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.isConformalMap`：∀ {R : Type u_1} {M : Type u_2} {N : Type
 u_3} [inst : NormedField R] [inst_1 : SeminormedAddCommGroup M]   [inst_2 : Sem
inormedAddCommGroup…
-/
theorem isConformalMap_conj : IsConformalMap (conjLIE : ℂ →L[ℝ] ℂ) :=
  conjLIE.toLinearIsometry.isConformalMap

section ConformalIntoComplexNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

/-
**isConformalMap_complex_linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConformalMap_complex_linear {map : Complex ->L[Complex] E} (nonzero : ma
p != 0) : IsConformalMap (map.restrictScalars Real)
参数：nonzero : map != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
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
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
（共 52 条，此处仅展示前 30 条）
-/
theorem isConformalMap_complex_linear {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap (map.restrictScalars ℝ) := by
  have minor₁ : ‖map 1‖ ≠ 0 := by
    simpa only [ContinuousLinearMap.ext_ring_iff, Ne, norm_eq_zero] using! nonzero
  refine ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • ((map : ℂ →ₗ[ℂ] E) : ℂ →ₗ[ℝ] E), ?_⟩, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply]
    have : x = x • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    nth_rw 1 [this]
    rw [LinearMap.coe_restrictScalars]
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    field
  · ext1
    simp [minor₁]
/-
**isConformalMap_complex_linear_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConformalMap_complex_linear_conj {map : Complex ->L[Complex] E} (nonzero
 : map != 0) : IsConformalMap ((map.restrictScalars Real).comp (conjCLE : Comple
x ->L[Real] Complex))
参数：nonzero : map != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConformalMap.comp`：comp (hg : IsConformalMap g) (hf : IsConformalMap f
) : IsConformalMap (g.comp f)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
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
· 使用定理 `isConformalMap_complex_linear`：isConformalMap_complex_linear {map : Comp
lex ->L[Complex] E} (nonzero : map != 0) : IsConformalMap (map.restrictScalars R
eal)
· 使用定理 `isConformalMap_conj`：isConformalMap_conj : IsConformalMap (conjLIE : Com
plex ->L[Real] Complex)
-/
theorem isConformalMap_complex_linear_conj {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) :
    IsConformalMap ((map.restrictScalars ℝ).comp (conjCLE : ℂ →L[ℝ] ℂ)) :=
  (isConformalMap_complex_linear nonzero).comp isConformalMap_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {g : ℂ →L[ℝ] ℂ}

/-
**IsConformalMap.is_complex_or_conj_linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) : (exists 
map : Complex ->L[Complex] Complex, map.restrictScalars Real = g) ∨ exists map :
 Complex ->L[Complex] Complex, map.restrictScalars Real = g ∘L ↑conjCLE
参数：h : IsConformalMap g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `LinearIsometry.ext`：ext {f g : E ->ₛₗᵢ[σ₁₂] E₂} (h : forall x, f x = g x
) : f = g
· 使用定理 `linear_isometry_complex`：linear_isometry_complex (f : Complex ≃ₗᵢ[Real] 
Complex) : exists a : Circle, f = rotation a ∨ f = conjLIE.trans (rotation a)
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
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
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
    (∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
      ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCLE := by
  rcases h with ⟨c, -, li, rfl⟩
  obtain ⟨li, rfl⟩ : ∃ li' : ℂ ≃ₗᵢ[ℝ] ℂ, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine Or.inl ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext1
    simp
  · refine Or.inr ⟨c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ, ?_⟩
    ext1
    simp

/-- A real continuous linear map on the complex plane is conformal if and only if the map or its
conjugate is complex linear, and the map is nonvanishing. -/
/-
**isConformalMap_iff_is_complex_or_conj_linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConformalMap_iff_is_complex_or_conj_linear : IsConformalMap g ↔ ((exists
 map : Complex ->L[Complex] Complex, map.restrictScalars Real = g) ∨ exists map 
: Complex ->L[Complex] Complex, map.restrictScalars Real = g ∘L ↑conjCLE) ∧ g !=
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsConformalMap.is_complex_or_conj_linear`：IsConformalMap.is_complex_or_c
onj_linear (h : IsConformalMap g) : (exists map : Complex ->L[Complex] Complex, 
map.restrictScalars Real = g) …
· 使用定理 `IsConformalMap.ne_zero`：ne_zero [Nontrivial M'] {f' : M' ->L[R] N} (hf' 
: IsConformalMap f') : f' != 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `isConformalMap_complex_linear`：isConformalMap_complex_linear {map : Comp
lex ->L[Complex] E} (nonzero : map != 0) : IsConformalMap (map.restrictScalars R
eal)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.restrictScalars.congr_simp`：∀ {A : Type u_1} {M₁ : T
ype u_2} {M₂ : Type u_3} (R : Type u_4) [inst : Semiring A] [inst_1 : Semiring R
]   [inst_2 : AddCommMonoid M₁] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `starRingEnd_self_apply`：starRingEnd_self_apply (x : R) : starRingEnd R (
starRingEnd R x) = x
· 使用定理 `isConformalMap_complex_linear_conj`：isConformalMap_complex_linear_conj {
map : Complex ->L[Complex] E} (nonzero : map != 0) : IsConformalMap ((map.restri
ctScalars Real).comp (co…
· 使用定理 `ContinuousLinearMap.zero_comp`：zero_comp (f : M₁ ->SL[σ₁₂] M₂) : (0 : M₂
 ->SL[σ₂₃] M₃) ∘SL f = 0

--- 原说明 ---
A real continuous linear map on the complex plane is conformal if and only if th
e map or its
conjugate is complex linear, and the map is nonvanishing.
-/
theorem isConformalMap_iff_is_complex_or_conj_linear :
    IsConformalMap g ↔
      ((∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g) ∨
          ∃ map : ℂ →L[ℂ] ℂ, map.restrictScalars ℝ = g ∘L ↑conjCLE) ∧
        g ≠ 0 := by
  constructor
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.ne_zero⟩
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    · refine isConformalMap_complex_linear ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero]
    · have minor₁ : g = map.restrictScalars ℝ ∘L ↑conjCLE := by
        ext1
        simp only [hmap, ContinuousLinearEquiv.coe_coe, comp_apply, conjCLE_apply,
          starRingEnd_self_apply]
      rw [minor₁] at h₂ ⊢
      refine isConformalMap_complex_linear_conj ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero, zero_comp]

end ConformalIntoComplexPlane

/-! ### Conformality of real-differentiable complex maps -/

section Conformality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : ℂ} {f : ℂ → E}

/-- A real differentiable function of the complex plane into some complex normed space `E` is
conformal at a point `z` if it is holomorphic at that point with a nonvanishing differential.
This is a version of the Cauchy-Riemann equations. -/
/-
**DifferentiableAt.conformalAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.conformalAt (h : DifferentiableAt Complex f z) (hf' : der
iv f z != 0) : ConformalAt f z
参数：h : DifferentiableAt Complex f z；hf' : deriv f z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `conformalAt_iff_isConformalMap_fderiv`：conformalAt_iff_isConformalMap_fd
eriv {f : X -> Y} {x : X} : ConformalAt f x ↔ IsConformalMap (fderiv Real f x)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.restrictScalars`：HasFDerivAt.restrictScalars (h : HasFDerivA
t f f' x) : HasFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `isConformalMap_complex_linear`：isConformalMap_complex_linear {map : Comp
lex ->L[Complex] E} (nonzero : map != 0) : IsConformalMap (map.restrictScalars R
eal)

--- 原说明 ---
A real differentiable function of the complex plane into some complex normed spa
ce `E` is
conformal at a point `z` if it is holomorphic at that point with a nonvanishing 
differential.
This is a version of the Cauchy-Riemann equations.
-/
theorem DifferentiableAt.conformalAt (h : DifferentiableAt ℂ f z) (hf' : deriv f z ≠ 0) :
    ConformalAt f z := by
  rw [conformalAt_iff_isConformalMap_fderiv, (h.hasFDerivAt.restrictScalars ℝ).fderiv]
  apply isConformalMap_complex_linear
  simpa only [Ne, ContinuousLinearMap.ext_ring_iff]

/-- A complex function is conformal if and only if the function is holomorphic or antiholomorphic
with a nonvanishing differential. -/
/-
**conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj {f : Comple
x -> Complex} {z : Complex} : ConformalAt f z ↔ (DifferentiableAt Complex f z ∨ 
DifferentiableAt Complex (f ∘ conj) (conj z)) ∧ fderiv Real f z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `conformalAt_iff_isConformalMap_fderiv`：conformalAt_iff_isConformalMap_fd
eriv {f : X -> Y} {x : X} : ConformalAt f x ↔ IsConformalMap (fderiv Real f x)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isConformalMap_iff_is_complex_or_conj_linear`：isConformalMap_iff_is_comp
lex_or_conj_linear : IsConformalMap g ↔ ((exists map : Complex ->L[Complex] Comp
lex, map.restrictScalars Real = g)…
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `fderiv_zero_of_not_differentiableAt`：fderiv_zero_of_not_differentiableAt
 (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `differentiableAt_iff_restrictScalars`：differentiableAt_iff_restrictScala
rs (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜' f x ↔ exists g' : E ->L[𝕜
'] F, g'.restrictScalars 𝕜…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_conj`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (x : R), (starRingEnd R) ((starRingEnd R) x) = x
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Eq.congr`：∀ {α : Sort u_1} {x₁ y₁ x₂ y₂ : α}, x₁ = y₁ → x₂ = y₂ → (x₁ = 
x₂ ↔ y₁ = y₂)
· 使用定理 `ContinuousLinearEquiv.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {F : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `fderiv_comp`：fderiv_comp {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) 
(hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fd
e…
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A complex function is conformal if and only if the function is holomorphic or an
tiholomorphic
with a nonvanishing differential.
-/
theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj {f : ℂ → ℂ} {z : ℂ} :
    ConformalAt f z ↔
      (DifferentiableAt ℂ f z ∨ DifferentiableAt ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 := by
  rw [conformalAt_iff_isConformalMap_fderiv]
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  apply or_congr
  · rw [differentiableAt_iff_restrictScalars ℝ h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiableAt_iff_restrictScalars ℝ (h_diff.comp _ conjCLE.differentiableAt)]
  refine exists_congr fun g => rfl.congr ?_
  have : fderiv ℝ conj (conj z) = _ := conjCLE.fderiv
  simp [fderiv_comp _ h_diff conjCLE.differentiableAt, this]

end Conformality

/-!
### The Cauchy-Riemann Equation for Complex-Differentiable Functions
-/

section CauchyRiemann

open Complex

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {x : ℂ} {s : Set ℂ}

/--
A real linear map `ℓ : ℂ →ₗ[ℝ] E` respects complex scalar multiplication if it maps `I` to
`I • ℓ 1`.
-/
/-
**real_linearMap_map_smul_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：real_linearMap_map_smul_complex {ℓ : Complex ->ₗ[Real] E} (h : ℓ I = I • ℓ
 1) (a b : Complex) : ℓ (a • b) = a • ℓ b
参数：h : ℓ I = I • ℓ 1；a b : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Complex.coe_smul`：Complex.coe_smul {E : Type*} [AddCommGroup E] [Module 
Complex E] (x : Real) (y : E) : (x : Complex) • y = x • y
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
A real linear map `ℓ : ℂ →ₗ[ℝ] E` respects complex scalar multiplication if it m
aps `I` to
`I • ℓ 1`.
-/
lemma real_linearMap_map_smul_complex {ℓ : ℂ →ₗ[ℝ] E} (h : ℓ I = I • ℓ 1) (a b : ℂ) :
    ℓ (a • b) = a • ℓ b := by
  rw [← re_add_im a, ← re_add_im b, ← smul_eq_mul _ I, ← smul_eq_mul _ I]
  have t₀ : ((a.im : ℂ) • I) • (b.re : ℂ) = (↑(a.im * b.re) : ℂ) • I := by
    simp only [smul_eq_mul, ofReal_mul, ← mul_assoc, mul_comm _ I]
  have t₁ : ((a.im : ℂ) • I) • (b.im : ℂ) • I = (↑(- a.im * b.im) : ℂ) • (1 : ℂ) := by
    simp [mul_mul_mul_comm _ I]
  simp only [add_smul, smul_add, ℓ.map_add, t₀, t₁]
  repeat rw [Complex.coe_smul, ℓ.map_smul]
  have t₂ {r : ℝ} : ℓ (r : ℂ) = r • ℓ (1 : ℂ) := by simp [← ℓ.map_smul]
  simp only [t₂, h]
  match_scalars
  simp [mul_mul_mul_comm _ I]
  ring

/--
Construct a complex-linear map from a real-linear map `ℓ` that maps `I` to `I • ℓ 1`.
-/
/-
**LinearMap.complexOfReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.complexOfReal (ℓ : Complex ->ₗ[Real] E) (h : ℓ I = I • ℓ 1) : Co
mplex ->ₗ[Complex] E where __
参数：ℓ : Complex ->ₗ[Real] E；h : ℓ I = I • ℓ 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `real_linearMap_map_smul_complex`：real_linearMap_map_smul_complex {ℓ : Co
mplex ->ₗ[Real] E} (h : ℓ I = I • ℓ 1) (a b : Complex) : ℓ (a • b) = a • ℓ b

--- 原说明 ---
Construct a complex-linear map from a real-linear map `ℓ` that maps `I` to `I • 
ℓ 1`.
-/
def LinearMap.complexOfReal (ℓ : ℂ →ₗ[ℝ] E) (h : ℓ I = I • ℓ 1) : ℂ →ₗ[ℂ] E where
  __ := ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]
/-
**LinearMap.coe_complexOfReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.coe_complexOfReal {ℓ : Complex ->ₗ[Real] E} (h) : ℓ.complexOfRea
l h = (ℓ : Complex -> E)
参数：h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LinearMap.coe_complexOfReal {ℓ : ℂ →ₗ[ℝ] E} (h) : ℓ.complexOfReal h = (ℓ : ℂ → E) := rfl

/--
Construct a continuous complex-linear map from a continuous real-linear map `ℓ` that maps `I` to
`I • ℓ 1`.
-/
/-
**ContinuousLinearMap.complexOfReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.complexOfReal (ℓ : Complex ->L[Real] E) (h : ℓ I = I •
 ℓ 1) : Complex ->L[Complex] E where __
参数：ℓ : Complex ->L[Real] E；h : ℓ I = I • ℓ 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous complex-linear map from a continuous real-linear map `ℓ` 
that maps `I` to
`I • ℓ 1`.
-/
def ContinuousLinearMap.complexOfReal (ℓ : ℂ →L[ℝ] E) (h : ℓ I = I • ℓ 1) : ℂ →L[ℂ] E where
  __ := ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]
/-
**ContinuousLinearMap.coe_complexOfReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.coe_complexOfReal {ℓ : Complex ->L[Real] E} (h) : ℓ.co
mplexOfReal h = (ℓ : Complex -> E)
参数：h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ContinuousLinearMap.coe_complexOfReal {ℓ : ℂ →L[ℝ] E} (h) : ℓ.complexOfReal h = (ℓ : ℂ → E) :=
  rfl

/--
The **Cauchy-Riemann Equation**: A real-differentiable function `f` on `ℂ` is complex-differentiable
at `x` within `s` iff the derivative `fderivWithin ℝ f s x` maps `I` to
`I • (fderivWithin ℝ f s x) 1`.
-/
/-
**differentiableWithinAt_complex_iff_differentiableWithinAt_real** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_complex_iff_differentiableWithinAt_real (hs : Uniqu
eDiffWithinAt Real s x) : DifferentiableWithinAt Complex f s x ↔ DifferentiableW
ithinAt Real f s x ∧ (fderivWithin Real f s x I = I • fderivWithin Real f s x 1)
参数：hs : UniqueDiffWithinAt Real s x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.restrictScalars`：DifferentiableWithinAt.restrictS
calars (h : DifferentiableWithinAt 𝕜' f s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DifferentiableWithinAt.restrictScalars_fderivWithin`：DifferentiableWithi
nAt.restrictScalars_fderivWithin (hf : DifferentiableWithinAt 𝕜' f s x) (hs : Un
iqueDiffWithinAt 𝕜 s x) : (fderivWithin 𝕜…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableWithinAt_iff_restrictScalars`：differentiableWithinAt_iff_r
estrictScalars (hf : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 
s x) : DifferentiableWithinAt 𝕜'…

--- 原说明 ---
The **Cauchy-Riemann Equation**: A real-differentiable function `f` on `ℂ` is co
mplex-differentiable
at `x` within `s` iff the derivative `fderivWithin ℝ f s x` maps `I` to
`I • (fderivWithin ℝ f s x) 1`.
-/
theorem differentiableWithinAt_complex_iff_differentiableWithinAt_real
    (hs : UniqueDiffWithinAt ℝ s x) :
    DifferentiableWithinAt ℂ f s x ↔ DifferentiableWithinAt ℝ f s x ∧
      (fderivWithin ℝ f s x I = I • fderivWithin ℝ f s x 1) := by
  refine ⟨fun h ↦ ⟨h.restrictScalars ℝ, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · simp only [← h.restrictScalars_fderivWithin ℝ hs, ContinuousLinearMap.coe_restrictScalars']
    rw [(by simp : I = I • 1), (fderivWithin ℂ f s x).map_smul]
    simp
  · apply (differentiableWithinAt_iff_restrictScalars ℝ h₁ hs).2
    use (fderivWithin ℝ f s x).complexOfReal h₂
    rfl

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real derivative.
-/
/-
**HasFDerivWithinAt.complexOfReal** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivWithinAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{f : ℂ → E} {x : ℂ} {s : Set ℂ}   {f' : ℂ →L[ℝ] E},   HasFDerivWithinAt f f' s x
 → ∀ (h₂ : f' Complex.I = Complex.I • f' 1), HasFDerivWithinAt f (f'.complexOfRe
al h₂) s x
参数：h₂ : f' Complex.I = Complex.I • f' 1；f'.complexOfReal h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.of_restrictScalars`：HasFDerivWithinAt.of_restrictScala
rs {g' : E ->L[𝕜] F} (h : HasFDerivWithinAt f g' s x) (H : f'.restrictScalars 𝕜 
= g') : HasFDerivWithinAt …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real deriva
tive.
-/
protected theorem HasFDerivWithinAt.complexOfReal {f' : ℂ →L[ℝ] E} (h₁ : HasFDerivWithinAt f f' s x)
    (h₂ : f' I = I • f' 1) :
    HasFDerivWithinAt f (f'.complexOfReal h₂) s x :=
  .of_restrictScalars ℝ h₁ rfl

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real derivative.
-/
/-
**complexOfReal_fderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：complexOfReal_fderivWithin (h₁ : DifferentiableWithinAt Real f s x) (h₂ : 
fderivWithin Real f s x I = I • fderivWithin Real f s x 1) (hs : UniqueDiffWithi
nAt Real s x) : fderivWithin Complex f s x = (fderivWithin Real f s x).complexOf
Real h₂
参数：h₁ : DifferentiableWithinAt Real f s x；h₂ : fderivWithin Real f s x I = I • f
derivWithin Real f s x 1；hs : UniqueDiffWithinAt Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DifferentiableWithinAt.restrictScalars_fderivWithin`：DifferentiableWithi
nAt.restrictScalars_fderivWithin (hf : DifferentiableWithinAt 𝕜' f s x) (hs : Un
iqueDiffWithinAt 𝕜 s x) : (fderivWithin 𝕜…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableWithinAt_complex_iff_differentiableWithinAt_real`：differen
tiableWithinAt_complex_iff_differentiableWithinAt_real (hs : UniqueDiffWithinAt 
Real s x) : DifferentiableWithinAt Complex f s x ↔ D…

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real deriva
tive.
-/
theorem complexOfReal_fderivWithin (h₁ : DifferentiableWithinAt ℝ f s x)
    (h₂ : fderivWithin ℝ f s x I = I • fderivWithin ℝ f s x 1) (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℂ f s x = (fderivWithin ℝ f s x).complexOfReal h₂ := by
  have := ((differentiableWithinAt_complex_iff_differentiableWithinAt_real hs).2
      ⟨h₁, h₂⟩).restrictScalars_fderivWithin ℝ hs
  simpa [DFunLike.ext_iff]

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real derivative.
-/
/-
**complexOfReal_hasDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：complexOfReal_hasDerivWithinAt (h₁ : DifferentiableWithinAt Real f s x) (h
₂ : fderivWithin Real f s x I = I • fderivWithin Real f s x 1) : HasDerivWithinA
t f ((fderivWithin Real f s x).complexOfReal h₂ 1) s x
参数：h₁ : DifferentiableWithinAt Real f s x；h₂ : fderivWithin Real f s x I = I • f
derivWithin Real f s x 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivWithinAt_iff_hasFDerivWithinAt`：hasDerivWithinAt_iff_hasFDerivWi
thinAt {f' : F} : HasDerivWithinAt f f' s x ↔ HasFDerivWithinAt f (toSpanSinglet
on 𝕜 f') s x
· 使用定理 `ContinuousLinearMap.toSpanSingleton_apply_map_one`：∀ (R₁ : Type u_1) [in
st : Semiring R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCo
mmMonoid M₂]   [inst_3 : _root_.Module …
· 使用定理 `HasFDerivWithinAt.complexOfReal`：∀ {E : Type u_1} [inst : NormedAddCommG
roup E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {x : ℂ} {s : Set ℂ}   {f' : ℂ →L[
ℝ] E},   HasFDerivWit…
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real deriva
tive.
-/
theorem complexOfReal_hasDerivWithinAt (h₁ : DifferentiableWithinAt ℝ f s x)
    (h₂ : fderivWithin ℝ f s x I = I • fderivWithin ℝ f s x 1) :
    HasDerivWithinAt f ((fderivWithin ℝ f s x).complexOfReal h₂ 1) s x := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, toSpanSingleton_apply_map_one]
  exact h₁.hasFDerivWithinAt.complexOfReal h₂

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals the real derivative.
-/
/-
**complexOfReal_derivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：complexOfReal_derivWithin (h₁ : DifferentiableWithinAt Real f s x) (h₂ : f
derivWithin Real f s x I = I • fderivWithin Real f s x 1) (hs : UniqueDiffWithin
At Complex s x) : derivWithin f s x = fderivWithin Real f s x 1
参数：h₁ : DifferentiableWithinAt Real f s x；h₂ : fderivWithin Real f s x I = I • f
derivWithin Real f s x 1；hs : UniqueDiffWithinAt Complex s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `complexOfReal_hasDerivWithinAt`：complexOfReal_hasDerivWithinAt (h₁ : Dif
ferentiableWithinAt Real f s x) (h₂ : fderivWithin Real f s x I = I • fderivWith
in Real f s x 1) : H…

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals the real derivative.
-/
theorem complexOfReal_derivWithin (h₁ : DifferentiableWithinAt ℝ f s x)
    (h₂ : fderivWithin ℝ f s x I = I • fderivWithin ℝ f s x 1) (hs : UniqueDiffWithinAt ℂ s x) :
    derivWithin f s x = fderivWithin ℝ f s x 1 :=
  HasDerivWithinAt.derivWithin (complexOfReal_hasDerivWithinAt h₁ h₂) hs

/--
The **Cauchy-Riemann Equation**: A real-differentiable function `f` on `ℂ` is complex-differentiable
at `x` if and only if the derivative `fderiv ℝ f x` maps `I` to `I • (fderiv ℝ f x) 1`.
-/
/-
**differentiableAt_complex_iff_differentiableAt_real** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：differentiableAt_complex_iff_differentiableAt_real : DifferentiableAt Comp
lex f x ↔ DifferentiableAt Real f x ∧ fderiv Real f x I = I • fderiv Real f x 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `DifferentiableAt.restrictScalars`：DifferentiableAt.restrictScalars (h : 
DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DifferentiableAt.fderiv_restrictScalars`：DifferentiableAt.fderiv_restric
tScalars (h : DifferentiableAt 𝕜' f x) : fderiv 𝕜 f x = (fderiv 𝕜' f x).restrict
Scalars 𝕜
· 使用定理 `fderiv_eq_smul_deriv`：fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -
> F) y = y • deriv f x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_iff_restrictScalars`：differentiableAt_iff_restrictScala
rs (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜' f x ↔ exists g' : E ->L[𝕜
'] F, g'.restrictScalars 𝕜…

--- 原说明 ---
The **Cauchy-Riemann Equation**: A real-differentiable function `f` on `ℂ` is co
mplex-differentiable
at `x` if and only if the derivative `fderiv ℝ f x` maps `I` to `I • (fderiv ℝ f
 x) 1`.
-/
theorem differentiableAt_complex_iff_differentiableAt_real :
    DifferentiableAt ℂ f x ↔ DifferentiableAt ℝ f x ∧
      fderiv ℝ f x I = I • fderiv ℝ f x 1 :=
  ⟨fun h ↦ by simp [h.restrictScalars ℝ, h.fderiv_restrictScalars ℝ],
    fun ⟨h₁, h₂⟩ ↦ (differentiableAt_iff_restrictScalars ℝ h₁).2
    ⟨(fderiv ℝ f x).complexOfReal h₂, rfl⟩⟩

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real derivative.
-/
/-
**HasFDerivAt.complexOfReal_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `HasFDerivAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{f : ℂ → E} {x : ℂ} {f' : ℂ →L[ℝ] E},   HasFDerivAt f f' x → ∀ (h₂ : f' Complex.
I = Complex.I • f' 1), HasFDerivAt f (f'.complexOfReal h₂) x
参数：h₂ : f' Complex.I = Complex.I • f' 1；f'.complexOfReal h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_of_restrictScalars`：hasFDerivAt_of_restrictScalars {g' : E -
>L[𝕜] F} (h : HasFDerivAt f g' x) (H : f'.restrictScalars 𝕜 = g') : HasFDerivAt 
f f' x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real deriva
tive.
-/
protected theorem HasFDerivAt.complexOfReal_hasFDerivAt {f' : ℂ →L[ℝ] E}
    (h₁ : HasFDerivAt f f' x) (h₂ : f' I = I • f' 1) :
    HasFDerivAt f (f'.complexOfReal h₂) x :=
  hasFDerivAt_of_restrictScalars ℝ h₁ rfl

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real derivative.
-/
/-
**complexOfReal_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：complexOfReal_hasDerivAt (h₁ : DifferentiableAt Real f x) (h₂ : fderiv Rea
l f x I = I • fderiv Real f x 1) : HasDerivAt f ((fderiv Real f x).complexOfReal
 h₂ 1) x
参数：h₁ : DifferentiableAt Real f x；h₂ : fderiv Real f x I = I • fderiv Real f x 1
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_hasFDerivAt`：hasDerivAt_iff_hasFDerivAt {f' : F} : HasDer
ivAt f f' x ↔ HasFDerivAt f (toSpanSingleton 𝕜 f') x
· 使用定理 `ContinuousLinearMap.toSpanSingleton_apply_map_one`：∀ (R₁ : Type u_1) [in
st : Semiring R₁] {M₂ : Type u_6} [inst_1 : TopologicalSpace M₂] [inst_2 : AddCo
mmMonoid M₂]   [inst_3 : _root_.Module …
· 使用定理 `hasFDerivAt_of_restrictScalars`：hasFDerivAt_of_restrictScalars {g' : E -
>L[𝕜] F} (h : HasFDerivAt f g' x) (H : f'.restrictScalars 𝕜 = g') : HasFDerivAt 
f f' x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real deriva
tive.
-/
theorem complexOfReal_hasDerivAt (h₁ : DifferentiableAt ℝ f x)
    (h₂ : fderiv ℝ f x I = I • fderiv ℝ f x 1) :
    HasDerivAt f ((fderiv ℝ f x).complexOfReal h₂ 1) x := by
  rw [hasDerivAt_iff_hasFDerivAt, toSpanSingleton_apply_map_one]
  exact hasFDerivAt_of_restrictScalars ℝ h₁.hasFDerivAt rfl

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals the real derivative.
-/
/-
**complexOfReal_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：complexOfReal_deriv (h₁ : DifferentiableAt Real f x) (h₂ : fderiv Real f x
 I = I • fderiv Real f x 1) : deriv f x = fderiv Real f x 1
参数：h₁ : DifferentiableAt Real f x；h₂ : fderiv Real f x I = I • fderiv Real f x 1
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `complexOfReal_hasDerivAt`：complexOfReal_hasDerivAt (h₁ : DifferentiableA
t Real f x) (h₂ : fderiv Real f x I = I • fderiv Real f x 1) : HasDerivAt f ((fd
eriv Real f x)…

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals the real derivative.
-/
theorem complexOfReal_deriv (h₁ : DifferentiableAt ℝ f x)
    (h₂ : fderiv ℝ f x I = I • fderiv ℝ f x 1) :
    deriv f x = fderiv ℝ f x 1 :=
  HasDerivAt.deriv (complexOfReal_hasDerivAt h₁ h₂)

/--
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiability at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real derivative.
-/
/-
**complexOfReal_fderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：complexOfReal_fderiv (h₁ : DifferentiableAt Real f x) (h₂ : fderiv Real f 
x I = I • fderiv Real f x 1) : (fderiv Real f x).complexOfReal h₂ = fderiv Compl
ex f x
参数：h₁ : DifferentiableAt Real f x；h₂ : fderiv Real f x I = I • fderiv Real f x 1
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
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
· 使用定理 `HasFDerivAt.complexOfReal_hasFDerivAt`：∀ {E : Type u_1} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℂ E] {f : ℂ → E} {x : ℂ} {f' : ℂ →L[ℝ] E},  
 HasFDerivAt f f' x → ∀ (h₂…
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x

--- 原说明 ---
In cases where the **Cauchy-Riemann Equation** guarantees complex differentiabil
ity at `x`, the
complex derivative equals `ContinuousLinearMap.complexOfReal` of the real deriva
tive.
-/
theorem complexOfReal_fderiv (h₁ : DifferentiableAt ℝ f x)
    (h₂ : fderiv ℝ f x I = I • fderiv ℝ f x 1) :
    (fderiv ℝ f x).complexOfReal h₂ = fderiv ℂ f x :=
  (h₁.hasFDerivAt.complexOfReal_hasFDerivAt h₂).fderiv.symm

end CauchyRiemann

