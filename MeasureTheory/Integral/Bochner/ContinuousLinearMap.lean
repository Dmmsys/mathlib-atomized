/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Operator.CompleteCodomain
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero

/-!
# Continuous linear maps composed with integration

The goal of this file is to prove that integration commutes with continuous linear maps.
This holds for simple functions. The general result follows from the continuity of all involved
operations on the space `L¹`. Note that composition by a continuous linear map on `L¹` is not just
the composition, as we are dealing with classes of functions, but it has already been defined
as `ContinuousLinearMap.compLp`. We take advantage of this construction here.
-/

public section

open MeasureTheory RCLike
open scoped ENNReal NNReal

variable {X Y E F Fₗ : Type*} [MeasurableSpace X] {μ : Measure X} {𝕜 𝕜' : Type*} [RCLike 𝕜]
  [RCLike 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]
  [NormedAddCommGroup Fₗ] [NormedSpace 𝕜 Fₗ] {p : ℝ≥0∞}

namespace ContinuousLinearMap

variable [NormedSpace ℝ F] [NormedSpace ℝ Fₗ]

variable {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

/-
**ContinuousLinearMap.integral_compLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：integral_compLp (L : E ->SL[σ] F) (φ : Lp E p μ) : ∫ x, (L.compLp φ) x ∂μ 
= ∫ x, L (φ x) ∂μ
参数：L : E ->SL[σ] F；φ : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
-/
theorem integral_compLp (L : E →SL[σ] F) (φ : Lp E p μ) :
    ∫ x, (L.compLp φ) x ∂μ = ∫ x, L (φ x) ∂μ :=
  integral_congr_ae <| coeFn_compLp _ _
/-
**ContinuousLinearMap.setIntegral_compLp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：setIntegral_compLp (L : E ->SL[σ] F) (φ : Lp E p μ) {s : Set X} (hs : Meas
urableSet s) : ∫ x in s, (L.compLp φ) x ∂μ = ∫ x in s, L (φ x) ∂μ
参数：L : E ->SL[σ] F；φ : Lp E p μ；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
-/
theorem setIntegral_compLp (L : E →SL[σ] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, (L.compLp φ) x ∂μ = ∫ x in s, L (φ x) ∂μ :=
  setIntegral_congr_ae hs ((L.coeFn_compLp φ).mono fun _x hx _ => hx)
/-
**ContinuousLinearMap.continuous_integral_comp_L1** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousLinearMap`。
形式化陈述：continuous_integral_comp_L1 (L : E ->SL[σ] F) : Continuous fun φ : X ->₁[μ
] E => ∫ x : X, L (φ x) ∂μ
参数：L : E ->SL[σ] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.integral_compLp`：integral_compLp (L : E ->SL[σ] F) (
φ : Lp E p μ) : ∫ x, (L.compLp φ) x ∂μ = ∫ x, L (φ x) ∂μ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.continuous_integral`：continuous_integral : Continuous fun 
f : α ->₁[μ] G => ∫ a, f a ∂μ
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_integral_comp_L1 (L : E →SL[σ] F) :
    Continuous fun φ : X →₁[μ] E => ∫ x : X, L (φ x) ∂μ := by
  rw [← funext L.integral_compLp]; exact continuous_integral.comp (L.compLpL 1 μ).continuous

variable [CompleteSpace F] [CompleteSpace Fₗ] [NormedSpace ℝ E]
/-
**ContinuousLinearMap.integral_comp_commSL** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：integral_comp_commSL [CompleteSpace E] (hσ : forall (r : Real) (x : 𝕜), σ 
(r • x) = r • σ x) (L : E ->SL[σ] F) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x
, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
参数：hσ : forall (r : Real) (x : 𝕜), σ (r • x) = r • σ x；L : E ->SL[σ] F；φ_int : I
ntegrable φ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator_const`：integral_indicator_const [Comple
teSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) : ∫ x : X, s.indicator
 (fun _ : X => e) x ∂μ = μ.r…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
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
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
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
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Set.indicator_comp_of_zero`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_
4} [inst : Zero M] [inst_1 : Zero N] {s : Set α} {f : α → M} {g : M → N},   g 0 
= 0 → s.indicato…
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
（共 42 条，此处仅展示前 30 条）
-/
theorem integral_comp_commSL [CompleteSpace E] (hσ : ∀ (r : ℝ) (x : 𝕜), σ (r • x) = r • σ x)
    (L : E →SL[σ] F) {φ : X → E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  apply φ_int.induction (P := fun φ => ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ))
  · intro e s s_meas _
    rw [integral_indicator_const e s_meas, ← @smul_one_smul E ℝ 𝕜 _ _ _ _ _ (μ.real s) e,
      map_smulₛₗ, hσ, map_one, smul_assoc, one_smul,
      ← integral_indicator_const (L e) s_meas]
    congr 1 with a
    rw [← Function.comp_def L, Set.indicator_comp_of_zero L.map_zero, Function.comp_apply]
  · intro f g _ f_int g_int hf hg
    simp [L.map_add, integral_add (μ := μ) f_int g_int,
      integral_add (μ := μ) (L.integrable_comp f_int) (L.integrable_comp g_int), hf, hg]
  · exact isClosed_eq L.continuous_integral_comp_L1 (L.continuous.comp continuous_integral)
  · intro f g hfg _ hf
    convert! hf using 1 <;> clear hf
    · exact integral_congr_ae (hfg.fun_comp L).symm
    · rw [integral_congr_ae hfg.symm]
/-
**ContinuousLinearMap.integral_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：integral_comp_comm [CompleteSpace E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int
 : Integrable φ μ) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
参数：L : E ->L[𝕜] Fₗ；φ_int : Integrable φ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_commSL`：integral_comp_commSL [Complete
Space E] (hσ : forall (r : Real) (x : 𝕜), σ (r • x) = r • σ x) (L : E ->SL[σ] F)
 {φ : X -> E} (φ_int : Integra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem integral_comp_comm [CompleteSpace E] (L : E →L[𝕜] Fₗ) {φ : X → E} (φ_int : Integrable φ μ) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := integral_comp_commSL (by simp) L φ_int
/-
**ContinuousLinearMap.integral_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X
 -> H ->L[𝕜] E} (φ_int : Integrable φ μ) (v : H) : (∫ x, φ x ∂μ) v = ∫ x, φ x v 
∂μ
参数：φ_int : Integrable φ μ；v : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 38 条，此处仅展示前 30 条）
-/
theorem integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X → H →L[𝕜] E}
    (φ_int : Integrable φ μ) (v : H) : (∫ x, φ x ∂μ) v = ∫ x, φ x v ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.apply 𝕜 E v).integral_comp_comm φ_int).symm
  · rcases subsingleton_or_nontrivial H with hH | hH
    · simp [Subsingleton.eq_zero v]
    · have : ¬(CompleteSpace (H →L[𝕜] E)) := by
        rwa [SeparatingDual.completeSpace_continuousLinearMap_iff]
      simp [integral, hE, this]
/-
**ContinuousLinearMap._root_.ContinuousMultilinearMap.integral_apply** 是 Mathlib
 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousMultilinearMap.integral_apply {ι : Type*} [Fintype ι] {M : ι → Type*}
    [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)]
    {φ : X → ContinuousMultilinearMap 𝕜 M E} (φ_int : Integrable φ μ) (m : ∀ i, M i) :
    (∫ x, φ x ∂μ) m = ∫ x, φ x m ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousMultilinearMap.apply 𝕜 M E m).integral_comp_comm φ_int).symm
  · by_cases! hm : ∀ i, m i ≠ 0
    · have : ¬ CompleteSpace (ContinuousMultilinearMap 𝕜 M E) := by
        rwa [SeparatingDual.completeSpace_continuousMultilinearMap_iff _ _ hm]
      simp [integral, hE, this]
    · rcases hm with ⟨i, hi⟩
      simp [ContinuousMultilinearMap.map_coord_zero _ i hi]

variable [CompleteSpace E]
/-
**ContinuousLinearMap.integral_comp_comm'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：integral_comp_comm' (L : E ->L[𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ 
: X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
参数：L : E ->L[𝕜] Fₗ；hL : AntilipschitzWith K L；φ : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `MeasureTheory.LipschitzWith.integrable_comp_iff_of_antilipschitz`：∀ {α :
 Type u_1} {β : Type u_2} {γ : Type u_3} {m : MeasurableSpace α} {μ : MeasureThe
ory.Measure α}   [inst : NormedAddCommGroup β] [inst_1…
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_comm' (L : E →L[𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X → E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  by_cases h : Integrable φ μ
  · exact integral_comp_comm L h
  have : ¬Integrable (fun x => L (φ x)) μ := by
    rwa [← Function.comp_def,
      LipschitzWith.integrable_comp_iff_of_antilipschitz L.lipschitz hL L.map_zero]
  simp [integral_undef, h, this]
/-
**ContinuousLinearMap.integral_comp_L1_comm** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：integral_comp_L1_comm (L : E ->L[𝕜] Fₗ) (φ : X ->₁[μ] E) : ∫ x, L (φ x) ∂μ
 = L (∫ x, φ x ∂μ)
参数：L : E ->L[𝕜] Fₗ；φ : X ->₁[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.L1.integrable_coeFn`：integrable_coeFn (f : α ->₁[μ] β) : I
ntegrable f μ
-/
theorem integral_comp_L1_comm (L : E →L[𝕜] Fₗ) (φ : X →₁[μ] E) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.integral_comp_comm (L1.integrable_coeFn φ)

end ContinuousLinearMap

namespace LinearIsometry

variable [CompleteSpace F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E] [NormedSpace ℝ E]

/-
**LinearIsometry.integral_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearIsometry`。
形式化陈述：integral_comp_comm (L : E ->ₗᵢ[𝕜] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫
 x, φ x ∂μ)
参数：L : E ->ₗᵢ[𝕜] F；φ : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_comm'`：integral_comp_comm' (L : E ->L[
𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x,
 φ x ∂μ)
· 使用定理 `LinearIsometry.antilipschitz`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} [inst_2 : Semi…
-/
theorem integral_comp_comm (L : E →ₗᵢ[𝕜] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _

end LinearIsometry

namespace ContinuousLinearEquiv

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace ℝ E]

/-
**ContinuousLinearEquiv.integral_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearEquiv`。
形式化陈述：integral_comp_comm (L : E ≃L[𝕜] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x
, φ x ∂μ)
参数：L : E ≃L[𝕜] F；φ : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `completeSpace_congr`：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbe
dding e) : CompleteSpace α ↔ CompleteSpace β
· 使用引理 `ContinuousLinearEquiv.isUniformEmbedding`：isUniformEmbedding {E₁ E₂ : Ty
pe*} [UniformSpace E₁] [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Mo
dule R₁ E₁] [Module R₂ E₂] [Is…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_iff_and_or_not_and_not`：iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b
 ∨ ¬a ∧ ¬b
· 使用定理 `ContinuousLinearMap.integral_comp_comm'`：integral_comp_comm' (L : E ->L[
𝕜] Fₗ) {K} (hL : AntilipschitzWith K L) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x,
 φ x ∂μ)
· 使用定理 `ContinuousLinearEquiv.antilipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_3} {E
 : Type u_5} {F : Type u_6} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddC
ommGroup F] [inst_2 : Non…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
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
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_comm (L : E ≃L[𝕜] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) := by
  have : CompleteSpace E ↔ CompleteSpace F :=
    completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding
  obtain ⟨_, _⟩ | ⟨_, _⟩ := iff_iff_and_or_not_and_not.mp this
  · exact L.toContinuousLinearMap.integral_comp_comm' L.antilipschitz _
  · simp [integral, *]

end ContinuousLinearEquiv

section ContinuousMap

variable [TopologicalSpace Y] [CompactSpace Y]

/-
**ContinuousMap.integral_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousMap.integral_apply [NormedSpace Real E] [CompleteSpace E] {f : X
 -> C(Y, E)} (hf : Integrable f μ) (y : Y) : (∫ x, f x ∂μ) y = ∫ x, f x y ∂μ
参数：Y, E；hf : Integrable f μ；y : Y。
该定理/引理给出了一组等式。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
-/
lemma ContinuousMap.integral_apply [NormedSpace ℝ E] [CompleteSpace E] {f : X → C(Y, E)}
    (hf : Integrable f μ) (y : Y) : (∫ x, f x ∂μ) y = ∫ x, f x y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMap.evalCLM ℝ y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMap.evalCLM ℝ y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

open scoped ContinuousMapZero in
/-
**ContinuousMapZero.integral_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMapZero.integral_apply {R : Type*} [NormedCommRing R] [Zero Y] [
NormedAlgebra Real R] [CompleteSpace R] {f : X -> C(Y, R)₀} (hf : MeasureTheory.
Integrable f μ) (y : Y) : (∫ (x : X), f x ∂μ) y = ∫ (x : X), (f x) y ∂μ
参数：Y, R；hf : MeasureTheory.Integrable f μ；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `ContinuousMapZero.instCompleteSpaceOfT1SpaceOfContinuousMap`：∀ {X : Type
 u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace X] [inst_2 : Zer
o R]   [inst_3 : UniformSpace R] [T1Space R] [Com…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
-/
theorem ContinuousMapZero.integral_apply {R : Type*} [NormedCommRing R] [Zero Y]
    [NormedAlgebra ℝ R] [CompleteSpace R] {f : X → C(Y, R)₀}
    (hf : MeasureTheory.Integrable f μ) (y : Y) :
    (∫ (x : X), f x ∂μ) y = ∫ (x : X), (f x) y ∂μ := by
  calc (∫ x, f x ∂μ) y = ContinuousMapZero.evalCLM ℝ y (∫ x, f x ∂μ) := rfl
    _ = ∫ x, ContinuousMapZero.evalCLM ℝ y (f x) ∂μ :=
          (ContinuousLinearMap.integral_comp_comm _ hf).symm
    _ = _ := rfl

end ContinuousMap

@[norm_cast]
/-
**integral_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.integral_comp_comm`：integral_comp_comm (L : E ->ₗᵢ[𝕜] F) 
(φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem integral_ofReal {f : X → ℝ} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ) :=
  (@RCLike.ofRealLI 𝕜 _).integral_comp_comm f

@[norm_cast]
/-
**integral_complex_ofReal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_complex_ofReal {f : X -> Real} : ∫ x, (f x : Complex) ∂μ = ∫ x, f
 x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
-/
theorem integral_complex_ofReal {f : X → ℝ} : ∫ x, (f x : ℂ) ∂μ = ∫ x, f x ∂μ := integral_ofReal
/-
**integral_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_re {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLike.re (f x) ∂μ =
 RCLike.re (∫ x, f x ∂μ)
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem integral_re {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.re (f x) ∂μ = RCLike.re (∫ x, f x ∂μ) :=
  (@RCLike.reCLM 𝕜 _).integral_comp_comm hf
/-
**integral_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_im {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, RCLike.im (f x) ∂μ =
 RCLike.im (∫ x, f x ∂μ)
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem integral_im {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, RCLike.im (f x) ∂μ = RCLike.im (∫ x, f x ∂μ) :=
  (@RCLike.imCLM 𝕜 _).integral_comp_comm hf

open scoped ComplexConjugate in
/-
**integral_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_conj {f : X -> 𝕜} : ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.integral_comp_comm`：integral_comp_comm (L : E ->ₗᵢ[𝕜] F) 
(φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
theorem integral_conj {f : X → 𝕜} : ∫ x, conj (f x) ∂μ = conj (∫ x, f x ∂μ) :=
  (@RCLike.conjLIE 𝕜 _).toLinearIsometry.integral_comp_comm f
/-
**integral_coe_re_add_coe_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_coe_re_add_coe_im {f : X -> 𝕜} (hf : Integrable f μ) : ∫ x, (re (
f x) : 𝕜) ∂μ + (∫ x, (im (f x) : 𝕜) ∂μ) * RCLike.I = ∫ x, f x ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.ofReal`：∀ {α : Type u_1} {m : MeasurableSpace α
} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : RCLike 𝕜] {f : α → ℝ},   
MeasureTheory.Integra…
· 使用定理 `MeasureTheory.Integrable.re`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : RCLike 𝕜] {f : α → 𝕜},   Meas
ureTheory.Integra…
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `MeasureTheory.Integrable.im`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ
 : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : RCLike 𝕜] {f : α → 𝕜},   Meas
ureTheory.Integra…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
-/
theorem integral_coe_re_add_coe_im {f : X → 𝕜} (hf : Integrable f μ) :
    ∫ x, (re (f x) : 𝕜) ∂μ + (∫ x, (im (f x) : 𝕜) ∂μ) * RCLike.I = ∫ x, f x ∂μ := by
  rw [mul_comm, ← smul_eq_mul, ← integral_smul, ← integral_add]
  · congr
    ext1 x
    rw [smul_eq_mul, mul_comm, RCLike.re_add_im]
  · exact hf.re.ofReal
  · exact hf.im.ofReal.smul (𝕜 := 𝕜) (β := 𝕜) RCLike.I
/-
**integral_re_add_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_re_add_im {f : X -> 𝕜} (hf : Integrable f μ) : ((∫ x, RCLike.re (
f x) ∂μ : Real) : 𝕜) + (∫ x, RCLike.im (f x) ∂μ : Real) * RCLike.I = ∫ x, f x ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
· 使用定理 `integral_coe_re_add_coe_im`：integral_coe_re_add_coe_im {f : X -> 𝕜} (hf 
: Integrable f μ) : ∫ x, (re (f x) : 𝕜) ∂μ + (∫ x, (im (f x) : 𝕜) ∂μ) * RCLike.I
 = ∫ x, f x ∂μ
-/
theorem integral_re_add_im {f : X → 𝕜} (hf : Integrable f μ) :
    ((∫ x, RCLike.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x, RCLike.im (f x) ∂μ : ℝ) * RCLike.I =
      ∫ x, f x ∂μ := by
  rw [← integral_ofReal, ← integral_ofReal, integral_coe_re_add_coe_im hf]
/-
**setIntegral_re_add_im** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setIntegral_re_add_im {f : X -> 𝕜} {i : Set X} (hf : IntegrableOn f i μ) :
 ((∫ x in i, RCLike.re (f x) ∂μ : Real) : 𝕜) + (∫ x in i, RCLike.im (f x) ∂μ : R
eal) * RCLike.I = ∫ x in i, f x ∂μ
参数：hf : IntegrableOn f i μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integral_re_add_im`：integral_re_add_im {f : X -> 𝕜} (hf : Integrable f μ
) : ((∫ x, RCLike.re (f x) ∂μ : Real) : 𝕜) + (∫ x, RCLike.im (f x) ∂μ : Real) * 
RCLike.I…
-/
theorem setIntegral_re_add_im {f : X → 𝕜} {i : Set X} (hf : IntegrableOn f i μ) :
    ((∫ x in i, RCLike.re (f x) ∂μ : ℝ) : 𝕜) + (∫ x in i, RCLike.im (f x) ∂μ : ℝ) * RCLike.I =
      ∫ x in i, f x ∂μ :=
  integral_re_add_im hf

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
/-
**swap_integral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：swap_integral (f : X -> E × F) : (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ
参数：f : X -> E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.integral_comp_comm`：integral_comp_comm (L : E ≃L[𝕜
] F) (φ : X -> E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
-/
lemma swap_integral (f : X → E × F) : (∫ x, f x ∂μ).swap = ∫ x, (f x).swap ∂μ :=
  .symm <| (ContinuousLinearEquiv.prodComm ℝ E F).integral_comp_comm f
/-
**fst_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fst_integral [CompleteSpace F] {f : X -> E × F} (hf : Integrable f μ) : (∫
 x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用引理 `CompleteSpace.fst_of_prod`：CompleteSpace.fst_of_prod [UniformSpace β] [C
ompleteSpace (α × β)] [h : Nonempty β] : CompleteSpace α where complete hf
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_integral [CompleteSpace F] {f : X → E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ := by
  by_cases hE : CompleteSpace E
  · exact ((ContinuousLinearMap.fst ℝ E F).integral_comp_comm hf).symm
  · have : ¬(CompleteSpace (E × F)) := fun h ↦ hE <| .fst_of_prod (β := F)
    simp [integral, *]
/-
**snd_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：snd_integral [CompleteSpace E] {f : X -> E × F} (hf : Integrable f μ) : (∫
 x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.fst_swap`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, p.swap.1 = p
.2
· 使用引理 `swap_integral`：swap_integral (f : X -> E × F) : (∫ x, f x ∂μ).swap = ∫ x
, (f x).swap ∂μ
· 使用定理 `fst_integral`：fst_integral [CompleteSpace F] {f : X -> E × F} (hf : Inte
grable f μ) : (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ
· 使用定理 `MeasureTheory.Integrable.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAd
dCommGroup β] [inst_1…
· 使用定理 `MeasureTheory.Integrable.snd`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {E : Type u_8} {F : Type u_9}   [inst : NormedAddCo
mmGroup E] [Normed…
· 使用定理 `MeasureTheory.Integrable.fst`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {E : Type u_8} {F : Type u_9}   [inst : NormedAddCo
mmGroup E] [Normed…
-/
theorem snd_integral [CompleteSpace E] {f : X → E × F} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ := by
  rw [← Prod.fst_swap, swap_integral]
  exact fst_integral <| hf.snd.prodMk hf.fst
/-
**integral_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_pair [CompleteSpace E] [CompleteSpace F] {f : X -> E} {g : X -> F
} (hf : Integrable f μ) (hg : Integrable g μ) : ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂
μ, ∫ x, g x ∂μ)
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAd
dCommGroup β] [inst_1…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `fst_integral`：fst_integral [CompleteSpace F] {f : X -> E × F} (hf : Inte
grable f μ) : (∫ x, f x ∂μ).1 = ∫ x, (f x).1 ∂μ
· 使用定理 `snd_integral`：snd_integral [CompleteSpace E] {f : X -> E × F} (hf : Inte
grable f μ) : (∫ x, f x ∂μ).2 = ∫ x, (f x).2 ∂μ
-/
theorem integral_pair [CompleteSpace E] [CompleteSpace F] {f : X → E} {g : X → F}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x, g x) ∂μ = (∫ x, f x ∂μ, ∫ x, g x ∂μ) :=
  have := hf.prodMk hg
  Prod.ext (fst_integral this) (snd_integral this)
/-
**integral_smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpac
e E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c
参数：f : X -> 𝕜；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.integrable_smul_const`：integrable_smul_const {f : α -> 𝕜} 
{c : E} (hc : c != 0) : Integrable (fun x => f x • c) μ ↔ Integrable f μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [CompleteSpace E]
    (f : X → 𝕜) (c : E) :
    ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c := by
  by_cases hf : Integrable f μ
  · exact ((1 : 𝕜 →L[𝕜] 𝕜).smulRight c).integral_comp_comm hf
  · by_cases hc : c = 0
    · simp [hc, integral_zero, smul_zero]
    rw [integral_undef hf, integral_undef, zero_smul]
    rw [integrable_smul_const hc]
    simp_rw [hf, not_false_eq_true]

/-
Note that the integrability hypothesis in the two lemmas below is necessary: consider the case
where `A = ℝ × ℝ`, `c = (1,0)`, and `f` is only integrable on the first component.
-/
/-
**integral_const_mul_of_integrable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integral_const_mul_of_integrable {A : Type*} [NonUnitalNormedRing A] [Norm
edSpace Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {f : X -> A} (
hf : Integrable f μ) {c : A} : ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note that the integrability hypothesis in the two lemmas below is necessary: con
sider the case
where `A = ℝ × ℝ`, `c = (1,0)`, and `f` is only integrable on the first componen
t.
-/
lemma integral_const_mul_of_integrable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {f : X → A} (hf : Integrable f μ) {c : A} :
    ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := by
  by_cases hA : CompleteSpace A
  · change ∫ x, ContinuousLinearMap.mul ℝ _ c (f x) ∂μ = ContinuousLinearMap.mul ℝ _ c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]
/-
**integral_mul_const_of_integrable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integral_mul_const_of_integrable {A : Type*} [NonUnitalNormedRing A] [Norm
edSpace Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {f : X -> A} (
hf : Integrable f μ) {c : A} : ∫ x, f x * c ∂μ = (∫ x, f x ∂μ) * c
参数：hf : Integrable f μ。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_mul_const_of_integrable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {f : X → A} (hf : Integrable f μ) {c : A} :
    ∫ x, f x * c ∂μ = (∫ x, f x ∂μ) * c := by
  by_cases hA : CompleteSpace A
  · change ∫ x, (ContinuousLinearMap.mul ℝ _).flip c (f x) ∂μ
      = (ContinuousLinearMap.mul ℝ _).flip c (∫ x, f x ∂μ)
    rw [ContinuousLinearMap.integral_comp_comm _ hf]
  · simp [integral, hA]
/-
**integral_withDensity_eq_integral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_withDensity_eq_integral_smul {f : X -> Real>=0} (f_meas : Measura
ble f) (g : X -> E) : ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ
参数：f_meas : Measurable f；g : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `NNReal.enorm_eq`：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
（共 59 条，此处仅展示前 30 条）
-/
theorem integral_withDensity_eq_integral_smul {f : X → ℝ≥0} (f_meas : Measurable f) (g : X → E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases hg : Integrable g (μ.withDensity fun x => f x); swap
  · rw [integral_undef hg, integral_undef]
    rwa [← integrable_withDensity_iff_integrable_smul f_meas]
  refine Integrable.induction
    (P := fun g => ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ) ?_ ?_ ?_ ?_ hg
  · intro c s s_meas hs
    rw [integral_indicator s_meas]
    simp_rw [← Set.indicator_smul_apply, integral_indicator s_meas]
    simp only [s_meas, integral_const, Measure.restrict_apply', Set.univ_inter, withDensity_apply,
      measureReal_def]
    rw [lintegral_coe_eq_integral, ENNReal.toReal_ofReal, ← integral_smul_const]
    · rfl
    · exact integral_nonneg fun x => NNReal.coe_nonneg _
    · refine ⟨f_meas.coe_nnreal_real.aemeasurable.aestronglyMeasurable, ?_⟩
      simpa [withDensity_apply _ s_meas, hasFiniteIntegral_iff_enorm] using hs
  · intro u u' _ u_int u'_int h h'
    change
      (∫ x : X, u x + u' x ∂μ.withDensity fun x : X => ↑(f x)) = ∫ x : X, f x • (u x + u' x) ∂μ
    simp_rw [smul_add]
    rw [integral_add u_int u'_int, h, h', integral_add]
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u_int
    · exact (integrable_withDensity_iff_integrable_smul f_meas).1 u'_int
  · have C1 :
      Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) =>
        ∫ x, u x ∂μ.withDensity fun x => f x :=
      continuous_integral
    have C2 : Continuous fun u : Lp E 1 (μ.withDensity fun x => f x) => ∫ x, f x • u x ∂μ := by
      have : Continuous ((fun u : Lp E 1 μ => ∫ x, u x ∂μ) ∘ withDensitySMulLI (E := E) μ f_meas) :=
        continuous_integral.comp (withDensitySMulLI (E := E) μ f_meas).continuous
      convert! this with u
      simp only [Function.comp_apply, withDensitySMulLI_apply]
      exact integral_congr_ae (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp.symm
    exact isClosed_eq C1 C2
  · intro u v huv _ hu
    rw [← integral_congr_ae huv, hu]
    apply integral_congr_ae
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 huv] with x hx
    rcases eq_or_ne (f x) 0 with (h'x | h'x)
    · simp only [h'x, zero_smul]
    · rw [hx _]
      simpa only [Ne, ENNReal.coe_eq_zero] using h'x
/-
**integral_withDensity_eq_integral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_withDensity_eq_integral_smul {f : X -> Real>=0} (f_meas : Measura
ble f) (g : X -> E) : ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ
参数：f_meas : Measurable f；g : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `NNReal.enorm_eq`：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
（共 59 条，此处仅展示前 30 条）
-/
theorem integral_withDensity_eq_integral_smul₀ {f : X → ℝ≥0} (hf : AEMeasurable f μ) (g : X → E) :
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, f x • g x ∂μ := by
  let f' := hf.mk _
  calc
    ∫ x, g x ∂μ.withDensity (fun x => f x) = ∫ x, g x ∂μ.withDensity fun x => f' x := by
      congr 1
      apply withDensity_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
    _ = ∫ x, f' x • g x ∂μ := integral_withDensity_eq_integral_smul hf.measurable_mk _
    _ = ∫ x, f x • g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_eq_mk] with x hx
      rw [hx]
/-
**integral_withDensity_eq_integral_toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_withDensity_eq_integral_toReal_smul {f : X -> Real>=0∞} (f_meas :
 Measurable f) (hf_lt_top : forallᵐ x ∂μ, f x < ∞) (g : X -> E) : ∫ x, g x ∂μ.wi
thDensity f = ∫ x, (f x).toReal • g x ∂μ
参数：f_meas : Measurable f；hf_lt_top : forallᵐ x ∂μ, f x < ∞；g : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `integral_withDensity_eq_integral_toReal_smul₀`：integral_withDensity_eq_i
ntegral_toReal_smul₀ {f : X -> Real>=0∞} (f_meas : AEMeasurable f μ) (hf_lt_top 
: forallᵐ x ∂μ, f x < ∞) (g : X -> …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem integral_withDensity_eq_integral_toReal_smul₀ {f : X → ℝ≥0∞} (f_meas : AEMeasurable f μ)
    (hf_lt_top : ∀ᵐ x ∂μ, f x < ∞) (g : X → E) :
    ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ := by
  dsimp only [ENNReal.toReal, ← NNReal.smul_def]
  rw [← integral_withDensity_eq_integral_smul₀ f_meas.ennreal_toNNReal,
    withDensity_congr_ae (coe_toNNReal_ae_eq hf_lt_top)]
/-
**integral_withDensity_eq_integral_toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_withDensity_eq_integral_toReal_smul {f : X -> Real>=0∞} (f_meas :
 Measurable f) (hf_lt_top : forallᵐ x ∂μ, f x < ∞) (g : X -> E) : ∫ x, g x ∂μ.wi
thDensity f = ∫ x, (f x).toReal • g x ∂μ
参数：f_meas : Measurable f；hf_lt_top : forallᵐ x ∂μ, f x < ∞；g : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `integral_withDensity_eq_integral_toReal_smul₀`：integral_withDensity_eq_i
ntegral_toReal_smul₀ {f : X -> Real>=0∞} (f_meas : AEMeasurable f μ) (hf_lt_top 
: forallᵐ x ∂μ, f x < ∞) (g : X -> …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem integral_withDensity_eq_integral_toReal_smul {f : X → ℝ≥0∞} (f_meas : Measurable f)
    (hf_lt_top : ∀ᵐ x ∂μ, f x < ∞) (g : X → E) :
    ∫ x, g x ∂μ.withDensity f = ∫ x, (f x).toReal • g x ∂μ :=
  integral_withDensity_eq_integral_toReal_smul₀ f_meas.aemeasurable hf_lt_top g
/-
**setIntegral_withDensity_eq_setIntegral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setIntegral_withDensity_eq_setIntegral_smul {f : X -> Real>=0} (f_meas : M
easurable f) (g : X -> E) {s : Set X} (hs : MeasurableSet s) : ∫ x in s, g x ∂μ.
withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ
参数：f_meas : Measurable f；g : X -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `setIntegral_withDensity_eq_setIntegral_smul₀`：setIntegral_withDensity_eq
_setIntegral_smul₀ {f : X -> Real>=0} {s : Set X} (hf : AEMeasurable f (μ.restri
ct s)) (g : X -> E) (hs : Measurab…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_smul₀ {f : X → ℝ≥0} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (g : X → E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_smul₀ hf]
/-
**setIntegral_withDensity_eq_setIntegral_toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：setIntegral_withDensity_eq_setIntegral_toReal_smul {f : X -> Real>=0∞} {s 
: Set X} (hf : Measurable f) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X 
-> E) (hs : MeasurableSet s) : ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x
 in s, (f x).toReal • g x ∂μ
参数：hf : Measurable f；hf_top : forallᵐ x ∂μ.restrict s, f x < ∞；g : X -> E；hs : M
easurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀`：setIntegral_withDen
sity_eq_setIntegral_toReal_smul₀ {f : X -> Real>=0∞} {s : Set X} (hf : AEMeasura
ble f (μ.restrict s)) (hf_top : forallᵐ x…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀ {f : X → ℝ≥0∞} {s : Set X}
    (hf : AEMeasurable f (μ.restrict s)) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E)
    (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, (f x).toReal • g x ∂μ := by
  rw [restrict_withDensity hs, integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]
/-
**setIntegral_withDensity_eq_setIntegral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setIntegral_withDensity_eq_setIntegral_smul {f : X -> Real>=0} (f_meas : M
easurable f) (g : X -> E) {s : Set X} (hs : MeasurableSet s) : ∫ x in s, g x ∂μ.
withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ
参数：f_meas : Measurable f；g : X -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `setIntegral_withDensity_eq_setIntegral_smul₀`：setIntegral_withDensity_eq
_setIntegral_smul₀ {f : X -> Real>=0} {s : Set X} (hf : AEMeasurable f (μ.restri
ct s)) (g : X -> E) (hs : Measurab…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_smul {f : X → ℝ≥0} (f_meas : Measurable f)
    (g : X → E) {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_smul₀ f_meas.aemeasurable _ hs
/-
**setIntegral_withDensity_eq_setIntegral_toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：setIntegral_withDensity_eq_setIntegral_toReal_smul {f : X -> Real>=0∞} {s 
: Set X} (hf : Measurable f) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X 
-> E) (hs : MeasurableSet s) : ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x
 in s, (f x).toReal • g x ∂μ
参数：hf : Measurable f；hf_top : forallᵐ x ∂μ.restrict s, f x < ∞；g : X -> E；hs : M
easurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀`：setIntegral_withDen
sity_eq_setIntegral_toReal_smul₀ {f : X -> Real>=0∞} {s : Set X} (hf : AEMeasura
ble f (μ.restrict s)) (hf_top : forallᵐ x…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul {f : X → ℝ≥0∞} {s : Set X}
    (hf : Measurable f) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, (f x).toReal • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.aemeasurable hf_top g hs
/-
**setIntegral_withDensity_eq_setIntegral_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setIntegral_withDensity_eq_setIntegral_smul {f : X -> Real>=0} (f_meas : M
easurable f) (g : X -> E) {s : Set X} (hs : MeasurableSet s) : ∫ x in s, g x ∂μ.
withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ
参数：f_meas : Measurable f；g : X -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `setIntegral_withDensity_eq_setIntegral_smul₀`：setIntegral_withDensity_eq
_setIntegral_smul₀ {f : X -> Real>=0} {s : Set X} (hf : AEMeasurable f (μ.restri
ct s)) (g : X -> E) (hs : Measurab…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_smul₀' [SFinite μ] {f : X → ℝ≥0} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (g : X → E) :
    ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x in s, f x • g x ∂μ := by
  rw [restrict_withDensity' s, integral_withDensity_eq_integral_smul₀ hf]
/-
**setIntegral_withDensity_eq_setIntegral_toReal_smul** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：setIntegral_withDensity_eq_setIntegral_toReal_smul {f : X -> Real>=0∞} {s 
: Set X} (hf : Measurable f) (hf_top : forallᵐ x ∂μ.restrict s, f x < ∞) (g : X 
-> E) (hs : MeasurableSet s) : ∫ x in s, g x ∂μ.withDensity (fun x => f x) = ∫ x
 in s, (f x).toReal • g x ∂μ
参数：hf : Measurable f；hf_top : forallᵐ x ∂μ.restrict s, f x < ∞；g : X -> E；hs : M
easurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀`：setIntegral_withDen
sity_eq_setIntegral_toReal_smul₀ {f : X -> Real>=0∞} {s : Set X} (hf : AEMeasura
ble f (μ.restrict s)) (hf_top : forallᵐ x…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul₀' [SFinite μ] {f : X → ℝ≥0∞} (s : Set X)
    (hf : AEMeasurable f (μ.restrict s)) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E) :
    ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g x ∂μ := by
  rw [restrict_withDensity' s, integral_withDensity_eq_integral_toReal_smul₀ hf hf_top]
/-
**setIntegral_withDensity_eq_setIntegral_toReal_smul'** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：setIntegral_withDensity_eq_setIntegral_toReal_smul' [SFinite μ] {f : X -> 
Real>=0∞} (s : Set X) (hf : Measurable f) (hf_top : forallᵐ x ∂μ.restrict s, f x
 < ∞) (g : X -> E) : ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g
 x ∂μ
参数：s : Set X；hf : Measurable f；hf_top : forallᵐ x ∂μ.restrict s, f x < ∞；g : X -
> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀'`：setIntegral_withDe
nsity_eq_setIntegral_toReal_smul₀' [SFinite μ] {f : X -> Real>=0∞} (s : Set X) (
hf : AEMeasurable f (μ.restrict s)) (hf_to…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem setIntegral_withDensity_eq_setIntegral_toReal_smul' [SFinite μ] {f : X → ℝ≥0∞} (s : Set X)
    (hf : Measurable f) (hf_top : ∀ᵐ x ∂μ.restrict s, f x < ∞) (g : X → E) :
    ∫ x in s, g x ∂μ.withDensity f = ∫ x in s, (f x).toReal • g x ∂μ :=
  setIntegral_withDensity_eq_setIntegral_toReal_smul₀' s hf.aemeasurable hf_top g
