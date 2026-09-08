/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The Fourier transform

We set up the Fourier transform for complex-valued functions on finite-dimensional spaces.

## Design choices

In namespace `VectorFourier`, we define the Fourier integral in the following context:
* `𝕜` is a commutative ring.
* `V` and `W` are `𝕜`-modules.
* `e` is a unitary additive character of `𝕜`, i.e. an `AddChar 𝕜 Circle`.
* `μ` is a measure on `V`.
* `L` is a `𝕜`-bilinear form `V × W → 𝕜`.
* `E` is a complete normed `ℂ`-vector space.

With these definitions, we define `fourierIntegral` to be the map from functions `V → E` to
functions `W → E` that sends `f` to

`fun w ↦ ∫ v in V, e (-L v w) • f v ∂μ`,

This includes the cases `W` is the dual of `V` and `L` is the canonical pairing, or `W = V` and `L`
is a bilinear form (e.g. an inner product).

In namespace `Fourier`, we consider the more familiar special case when `V = W = 𝕜` and `L` is the
multiplication map (but still allowing `𝕜` to be an arbitrary ring equipped with a measure).

The most familiar case of all is when `V = W = 𝕜 = ℝ`, `L` is multiplication, `μ` is volume, and
`e` is `Real.fourierChar`, i.e. the character `fun x ↦ exp ((2 * π * x) * I)` (for which we
introduced the notation `𝐞` in the scope `FourierTransform`).

Another familiar case (which generalizes the previous one) is when `V = W` is an inner product space
over `ℝ` and `L` is the scalar product. We introduce two notations `𝓕` for the Fourier transform in
this case and `𝓕⁻ f (v) = 𝓕 f (-v)` for the inverse Fourier transform. These notations make
in particular sense for `V = W = ℝ`.

## Main results

At present the only nontrivial lemma we prove is `fourierIntegral_continuous`, stating that the
Fourier transform of an integrable function is continuous (under mild assumptions).
-/

@[expose] public section


noncomputable section

local notation "𝕊" => Circle

open MeasureTheory Filter

open scoped Topology

/-! ## Fourier theory for functions on general vector spaces -/

namespace VectorFourier

variable {𝕜 : Type*} [CommRing 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [MeasurableSpace V]
  {W : Type*} [AddCommGroup W] [Module 𝕜 W]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

section Defs

/-- The Fourier transform integral for `f : V → E`, with respect to a bilinear form `L : V × W → 𝕜`
and an additive character `e`. -/
/-
**VectorFourier.fourierIntegral** 是 Mathlib 中的一个定义，位于命名空间 `VectorFourier`。
形式化陈述：fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜
) (f : V -> E) (w : W) : E
参数：e : AddChar 𝕜 𝕊；μ : Measure V；L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜；f : V -> E；w : W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform integral for `f : V → E`, with respect to a bilinear form 
`L : V × W → 𝕜`
and an additive character `e`.
-/
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E)
    (w : W) : E :=
  ∫ v, e (-L v w) • f v ∂μ
/-
**VectorFourier.fourierIntegral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `VectorFourie
r`。
形式化陈述：fourierIntegral_congr_ae (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W
 ->ₗ[𝕜] 𝕜) {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[μ] f₂) : fourierIntegral e μ L f₁ = four
ierIntegral e μ L f₂
参数：e : AddChar 𝕜 𝕊；μ : Measure V；L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜；hf : f₁ =ᵐ[μ] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fourierIntegral_congr_ae (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜)
    {f₁ f₂ : V → E} (hf : f₁ =ᵐ[μ] f₂) : fourierIntegral e μ L f₁ = fourierIntegral e μ L f₂ := by
  ext
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']
/-
**VectorFourier.fourierIntegral_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `VectorFour
ier`。
形式化陈述：fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜]
 W ->ₗ[𝕜] 𝕜) (f : V -> E) (r : Complex) : fourierIntegral e μ L (r • f) = r • fo
urierIntegral e μ L f
参数：e : AddChar 𝕜 𝕊；μ : Measure V；L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜；f : V -> E；r : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (r : ℂ) :
    fourierIntegral e μ L (r • f) = r • fourierIntegral e μ L f := by
  ext1 w
  simp only [Pi.smul_apply, fourierIntegral, smul_comm _ r, integral_smul]

/-- The uniform norm of the Fourier integral of `f` is bounded by the `L¹` norm of `f`. -/
/-
**VectorFourier.norm_fourierIntegral_le_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 
`VectorFourier`。
形式化陈述：norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V) (L
 : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E) (w : W) : ‖fourierIntegral e μ L f w‖ <= ∫ 
v : V, ‖f v‖ ∂μ
参数：e : AddChar 𝕜 𝕊；μ : Measure V；L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜；f : V -> E；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Circle.norm_smul`：∀ {E : Type u_4} [inst : SeminormedAddCommGroup E] [in
st_1 : NormedSpace ℂ E] (u : Circle) (v : E), ‖u • v‖ = ‖v‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The uniform norm of the Fourier integral of `f` is bounded by the `L¹` norm of `
f`.
-/
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (w : W) :
    ‖fourierIntegral e μ L f w‖ ≤ ∫ v : V, ‖f v‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

/-- The Fourier integral converts right-translation into scalar multiplication by a phase factor. -/
/-
**VectorFourier.fourierIntegral_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Vector
Fourier`。
形式化陈述：fourierIntegral_comp_add_right [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Me
asure V) [μ.IsAddRightInvariant] (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E) (v₀ : V)
 : fourierIntegral e μ L (f ∘ fun v => v + v₀) = fun w => e (L v₀ w) • fourierIn
tegral e μ L f w
参数：e : AddChar 𝕜 𝕊；μ : Measure V；L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜；f : V -> E；v₀ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `MeasureTheory.integral_add_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Circle.coe_mul`：∀ (z w : Circle), ↑(z * w) = ↑z * ↑w
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `LinearMap.neg_apply`：neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -
f x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a

--- 原说明 ---
The Fourier integral converts right-translation into scalar multiplication by a 
phase factor.
-/
theorem fourierIntegral_comp_add_right [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V)
    [μ.IsAddRightInvariant] (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (v₀ : V) :
    fourierIntegral e μ L (f ∘ fun v ↦ v + v₀) =
      fun w ↦ e (L v₀ w) • fourierIntegral e μ L f w := by
  ext1 w
  dsimp only [fourierIntegral, Function.comp_apply, Circle.smul_def]
  conv in L _ => rw [← add_sub_cancel_right v v₀]
  rw [integral_add_right_eq_self fun v : V ↦ (e (-L (v - v₀) w) : ℂ) • f v, ← integral_smul]
  congr 1 with v
  rw [← smul_assoc, smul_eq_mul, ← Circle.coe_mul, ← e.map_add_eq_mul, ← LinearMap.neg_apply,
    ← sub_eq_add_neg, ← LinearMap.sub_apply, map_sub, neg_sub]

end Defs

section Continuous

/-!
In this section we assume 𝕜, `V`, `W` have topologies,
and `L`, `e` are continuous (but `f` needn't be).

This is used to ensure that `e (-L v w)` is (a.e. strongly) measurable. We could get away with
imposing only a measurable-space structure on 𝕜 (it doesn't have to be the Borel sigma-algebra of
a topology); but it seems hard to imagine cases where this extra generality would be useful, and
allowing it would complicate matters in the most important use cases.
-/
variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}

/-- For any `w`, the Fourier integral is convergent iff `f` is integrable. -/
/-
**VectorFourier.fourierIntegral_convergent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Vector
Fourier`。
形式化陈述：fourierIntegral_convergent_iff (he : Continuous e) (hL : Continuous fun p 
: V × W => L p.1 p.2) {f : V -> E} (w : W) : Integrable (fun v : V => e (-L v w)
 • f v) μ ↔ Integrable f μ
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2；w : W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X → 
G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_smul`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `Circle.instCompactSpace`：CompactSpace Circle
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Circle.norm_smul`：∀ {E : Type u_4} [inst : SeminormedAddCommGroup E] [in
st_1 : NormedSpace ℂ E] (u : Circle) (v : E), ‖u • v‖ = ‖v‖
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
For any `w`, the Fourier integral is convergent iff `f` is integrable.
-/
theorem fourierIntegral_convergent_iff (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (w : W) :
    Integrable (fun v : V ↦ e (-L v w) • f v) μ ↔ Integrable f μ := by
  -- first prove one-way implication
  have aux {g : V → E} (hg : Integrable g μ) (x : W) :
      Integrable (fun v : V ↦ e (-L v x) • g v) μ := by
    have c : Continuous fun v ↦ e (-L v x) := he.comp (hL.comp (.prodMk_left _)).neg
    simp_rw [← integrable_norm_iff (c.aestronglyMeasurable.fun_smul hg.1), Circle.norm_smul]
    exact hg.norm
  -- then use it for both directions
  refine ⟨fun hf ↦ ?_, fun hf ↦ aux hf w⟩
  have := aux hf (-w)
  simp_rw [← mul_smul (e _) (e _) (f _), ← e.map_add_eq_mul, map_neg, neg_add_cancel,
    e.map_zero_eq_one, one_smul] at this -- the `(e _)` speeds up elaboration considerably
  exact this
/-
**VectorFourier.fourierIntegral_add** 是 Mathlib 中的一个定理，位于命名空间 `VectorFourier`。
形式化陈述：fourierIntegral_add (he : Continuous e) (hL : Continuous fun p : V × W => 
L p.1 p.2) {f g : V -> E} (hf : Integrable f μ) (hg : Integrable g μ) : fourierI
ntegral e μ L (f + g) = fourierIntegral e μ L f + fourierIntegral e μ L g
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2；hf : Integrable 
f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
-/
theorem fourierIntegral_add (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {f g : V → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierIntegral e μ L (f + g) = fourierIntegral e μ L f + fourierIntegral e μ L g := by
  ext1 w
  dsimp only [Pi.add_apply, fourierIntegral]
  simp_rw [smul_add]
  rw [integral_add]
  · exact (fourierIntegral_convergent_iff he hL w).2 hf
  · exact (fourierIntegral_convergent_iff he hL w).2 hg

/-- The Fourier integral of an `L^1` function is a continuous function. -/
/-
**VectorFourier.fourierIntegral_continuous** 是 Mathlib 中的一个定理，位于命名空间 `VectorFour
ier`。
形式化陈述：fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e) 
(hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> E} (hf : Integrable f μ) 
: Continuous (fourierIntegral e μ L f)
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2；hf : Integrable 
f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.continuous_of_dominated`：continuous_of_dominated {F : X ->
 α -> G} {bound : α -> Real} (hF_meas : forall x, AEStronglyMeasurable (F x) μ) 
(h_bound : forall x, forall…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Circle.norm_smul`：∀ {E : Type u_4} [inst : SeminormedAddCommGroup E] [in
st_1 : NormedSpace ℂ E] (u : Circle) (v : E), ‖u • v‖ = ‖v‖
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
The Fourier integral of an `L^1` function is a continuous function.
-/
theorem fourierIntegral_continuous [FirstCountableTopology W] (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) {f : V → E} (hf : Integrable f μ) :
    Continuous (fourierIntegral e μ L f) := by
  apply continuous_of_dominated
  · exact fun w ↦ ((fourierIntegral_convergent_iff he hL w).2 hf).1
  · exact fun w ↦ ae_of_all _ fun v ↦ le_of_eq (Circle.norm_smul _ _)
  · exact hf.norm
  · filter_upwards with v
    fun_prop

end Continuous

section Fubini

variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [TopologicalSpace V] [BorelSpace V]
  [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜}
  {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν] [SecondCountableTopologyEither W V]

variable {σ : ℂ →+* ℂ} [RingHomIsometric σ]

/-- Fubini's theorem for the Fourier integral.

This is the main technical step in proving both Parseval's identity and self-adjointness of the
Fourier transform. -/
/-
**VectorFourier.integral_fourierIntegral_swap** 是 Mathlib 中的一个定理，位于命名空间 `VectorF
ourier`。
形式化陈述：integral_fourierIntegral_swap {f : V -> E} {g : W -> F} (M : F ->L[Complex
] E ->SL[σ] G) (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) 
(hf : Integrable f μ) (hg : Integrable g ν) : ∫ ξ, (∫ x, M (g ξ) (e (-L x ξ) • f
 x) ∂μ) ∂ν = ∫ x, (∫ ξ, M (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ
参数：M : F ->L[Complex] E ->SL[σ] G；he : Continuous e；hL : Continuous fun p : V × 
W => L p.1 p.2；hf : Integrable f μ；hg : Integrable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `MeasureTheory.integral_integral_swap`：integral_integral_swap ⦃f : α -> β
 -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫
 x, f x y ∂μ ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.mul_prod`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α}
   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.mono`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup β] [inst_1…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_smul`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `Circle.instCompactSpace`：CompactSpace Circle
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X → 
G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd`：MeasureTheory.AEStronglyMea
surable.comp_snd {γ} [TopologicalSpace γ] {f : β -> γ} (hf : AEStronglyMeasurabl
e f ν) : AEStronglyMeasurable (fu…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Fubini's theorem for the Fourier integral.

This is the main technical step in proving both Parseval's identity and self-adj
ointness of the
Fourier transform.
-/
theorem integral_fourierIntegral_swap
    {f : V → E} {g : W → F} (M : F →L[ℂ] E →SL[σ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (∫ x, M (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν =
    ∫ x, (∫ ξ, M (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ := by
  rw [integral_integral_swap]
  have : Integrable (fun (p : W × V) ↦ ‖M‖ * (‖g p.1‖ * ‖f p.2‖)) (ν.prod μ) :=
    (hg.norm.mul_prod hf.norm).const_mul _
  apply this.mono
  · change AEStronglyMeasurable (fun p : W × V ↦ (M (g p.1) (e (-(L p.2) p.1) • f p.2))) _
    have A : AEStronglyMeasurable (fun (p : W × V) ↦ e (-L p.2 p.1) • f p.2) (ν.prod μ) := by
      refine (Continuous.aestronglyMeasurable ?_).fun_smul hf.1.comp_snd
      exact he.comp (hL.comp continuous_swap).neg
    have A' : AEStronglyMeasurable (fun p ↦ (g p.1, e (-(L p.2) p.1) • f p.2) : W × V → F × E)
      (Measure.prod ν μ) := hg.1.comp_fst.prodMk A
    have hM : Continuous (fun q ↦ M q.1 q.2 : F × E → G) :=
      -- There is no `Continuous.clm_apply` for semilinear continuous maps
      (M.flip.cont.comp continuous_snd).clm_apply continuous_fst
    apply hM.comp_aestronglyMeasurable A' -- `exact` works, but `apply` is 10x faster!
  · filter_upwards with ⟨ξ, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul, norm_norm, ge_iff_le, ← mul_assoc]
    convert! M.le_opNorm₂ (g ξ) (e (-L x ξ) • f x) using 2
    simp

variable [CompleteSpace E] [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
/-
**VectorFourier.integral_bilin_fourierIntegral_eq_flip** 是 Mathlib 中的一个定理，位于命名空间
 `VectorFourier`。
形式化陈述：integral_bilin_fourierIntegral_eq_flip {f : V -> E} {g : W -> F} (M : E ->
L[Complex] F ->L[Complex] G) (he : Continuous e) (hL : Continuous fun p : V × W 
=> L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) : ∫ ξ, M (fourierInteg
ral e μ L f ξ) (g ξ) ∂ν = ∫ x, M (f x) (fourierIntegral e ν L.flip g x) ∂μ
参数：M : E ->L[Complex] F ->L[Complex] G；he : Continuous e；hL : Continuous fun p :
 V × W => L p.1 p.2；hf : Integrable f μ；hg : Integrable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `VectorFourier.integral_fourierIntegral_swap`：integral_fourierIntegral_sw
ap {f : V -> E} {g : W -> F} (M : F ->L[Complex] E ->SL[σ] G) (he : Continuous e
) (hL : Continuous fun p : V × W …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoin
t.

Version where the multiplication is replaced by a general bilinear form `M`.
-/
theorem integral_bilin_fourierIntegral_eq_flip
    {f : V → E} {g : W → F} (M : E →L[ℂ] F →L[ℂ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν L.flip g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_comm _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ :=
    integral_fourierIntegral_swap M.flip he hL hf hg
  _ = ∫ x, (∫ ξ, M (f x) (e (-L.flip ξ x) • g ξ) ∂ν) ∂μ := by
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower,
      smul_apply, LinearMap.flip_apply]
  _ = ∫ x, M (f x) (∫ ξ, e (-L.flip ξ x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    apply (fourierIntegral_convergent_iff he _ _).2 hg
    exact hL.comp continuous_swap

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
/-
**VectorFourier.integral_fourierIntegral_smul_eq_flip** 是 Mathlib 中的一个定理，位于命名空间 
`VectorFourier`。
形式化陈述：integral_fourierIntegral_smul_eq_flip {f : V -> Complex} {g : W -> F} (he 
: Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) (hf : Integrable f 
μ) (hg : Integrable g ν) : ∫ ξ, (fourierIntegral e μ L f ξ) • (g ξ) ∂ν = ∫ x, (f
 x) • (fourierIntegral e ν L.flip g x) ∂μ
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2；hf : Integrable 
f μ；hg : Integrable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `VectorFourier.integral_bilin_fourierIntegral_eq_flip`：integral_bilin_fou
rierIntegral_eq_flip {f : V -> E} {g : W -> F} (M : E ->L[Complex] F ->L[Complex
] G) (he : Continuous e) (hL : Continuous …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoin
t.
-/
theorem integral_fourierIntegral_smul_eq_flip
    {f : V → ℂ} {g : W → F} (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, (fourierIntegral e μ L f ξ) • (g ξ) ∂ν =
      ∫ x, (f x) • (fourierIntegral e ν L.flip g x) ∂μ :=
  integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ) he hL hf hg

/-- The Fourier transform satisfies `∫ 𝓕 f * conj g = ∫ f * conj (𝓕⁻¹ g)`, which together
with the Fourier inversion theorem yields Plancherel's theorem. The stated version is more
convenient since it does only require integrability of `f` and `g`.

Version where the multiplication is replaced by a general bilinear form `M`. -/
/-
**VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip** 是 Mathlib 中的一个定理，位于命
名空间 `VectorFourier`。
形式化陈述：integral_sesq_fourierIntegral_eq_neg_flip {f : V -> E} {g : W -> F} (M : E
 ->L⋆[Complex] F ->L[Complex] G) (he : Continuous e) (hL : Continuous fun p : V 
× W => L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) : ∫ ξ, M (fourierI
ntegral e μ L f ξ) (g ξ) ∂ν = ∫ x, M (f x) (fourierIntegral e ν (-L.flip) g x) ∂
μ
参数：M : E ->L⋆[Complex] F ->L[Complex] G；he : Continuous e；hL : Continuous fun p 
: V × W => L p.1 p.2；hf : Integrable f μ；hg : Integrable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_commSL`：integral_comp_commSL [Complete
Space E] (hσ : forall (r : Real) (x : 𝕜), σ (r • x) = r • σ x) (L : E ->SL[σ] F)
 {φ : X -> E} (φ_int : Integra…
· 使用定理 `RCLike.conj_smul`：conj_smul (r : Real) (z : K) : conj (r • z) = r • conj
 z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `VectorFourier.integral_fourierIntegral_swap`：integral_fourierIntegral_sw
ap {f : V -> E} {g : W -> F} (M : F ->L[Complex] E ->SL[σ] G) (he : Continuous e
) (hL : Continuous fun p : V × W …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.map_smul_of_tower`：map_smul_of_tower {R S : Type*} [
Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂] [Module S M₂] [LinearMap.Compa
tibleSMul M₁ M₂ R S] (f : M…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier transform satisfies `∫ 𝓕 f * conj g = ∫ f * conj (𝓕⁻¹ g)`, which tog
ether
with the Fourier inversion theorem yields Plancherel's theorem. The stated versi
on is more
convenient since it does only require integrability of `f` and `g`.

Version where the multiplication is replaced by a general bilinear form `M`.
-/
theorem integral_sesq_fourierIntegral_eq_neg_flip
    {f : V → E} {g : W → F} (M : E →L⋆[ℂ] F →L[ℂ] G) (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ ξ, M (fourierIntegral e μ L f ξ) (g ξ) ∂ν =
      ∫ x, M (f x) (fourierIntegral e ν (-L.flip) g x) ∂μ := by
  by_cases hG : CompleteSpace G; swap; · simp [integral, hG]
  calc
  ∫ ξ, M.flip (g ξ) (∫ x, e (-L x ξ) • f x ∂μ) ∂ν
    = ∫ ξ, (∫ x, M.flip (g ξ) (e (-L x ξ) • f x) ∂μ) ∂ν := by
    congr with ξ
    apply (ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul _ _).symm
    exact (fourierIntegral_convergent_iff he hL _).2 hf
  _ = ∫ x, (∫ ξ, M.flip (g ξ) (e (-L x ξ) • f x) ∂ν) ∂μ :=
    integral_fourierIntegral_swap M.flip he hL hf hg
  _ = ∫ x, (∫ ξ, M (f x) (e (L.flip ξ x) • g ξ) ∂ν) ∂μ := by
    congr with x
    congr with ξ
    rw [← smul_one_smul ℂ _ (f x), ← smul_one_smul ℂ _ (g ξ)]
    simp only [map_smulₛₗ, ContinuousLinearMap.flip_apply, LinearMap.flip_apply, RingHom.id_apply,
      Circle.smul_def, smul_eq_mul, mul_one, ← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv,
      inv_inv]
  _ = ∫ x, (∫ ξ, M (f x) (e (-(-L.flip ξ) x) • g ξ) ∂ν) ∂μ := by
    simp only [LinearMap.flip_apply, ContinuousLinearMap.map_smul_of_tower, LinearMap.neg_apply,
      neg_neg]
  _ = ∫ x, M (f x) (∫ ξ, e (-(-L.flip ξ) x) • g ξ ∂ν) ∂μ := by
    congr with x
    apply ContinuousLinearMap.integral_comp_comm
    have hLflip : Continuous fun (p : W × V) => (-L.flip p.1) p.2 :=
      (continuous_neg.comp hL).comp continuous_swap
    exact (fourierIntegral_convergent_iff (L := -L.flip) he hLflip x).2 hg

end Fubini

/-
**VectorFourier.fourierIntegral_probChar** 是 Mathlib 中的一个引理，位于命名空间 `VectorFourie
r`。
形式化陈述：fourierIntegral_probChar {V W : Type*} {_ : MeasurableSpace V} [AddCommGro
up V] [Module Real V] [AddCommGroup W] [Module Real W] (L : V ->ₗ[Real] W ->ₗ[Re
al] Real) (μ : Measure V) (f : V -> E) (w : W) : fourierIntegral Real.probChar μ
 L f w = ∫ v : V, Complex.exp (- L v w * Complex.I) • f v ∂μ
参数：L : V ->ₗ[Real] W ->ₗ[Real] Real；μ : Measure V；f : V -> E；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourierIntegral_probChar {V W : Type*} {_ : MeasurableSpace V}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (μ : Measure V) (f : V → E) (w : W) :
    fourierIntegral Real.probChar μ L f w =
      ∫ v : V, Complex.exp (- L v w * Complex.I) • f v ∂μ := by
  simp_rw [fourierIntegral, Circle.smul_def, Real.probChar_apply, Complex.ofReal_neg]

end VectorFourier

namespace VectorFourier

variable {𝕜 ι E F V W : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {e : AddChar 𝕜 𝕊} {μ : Measure V} {L : V →L[𝕜] W →L[𝕜] 𝕜}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]

/-
**VectorFourier.fourierIntegral_continuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命
名空间 `VectorFourier`。
形式化陈述：fourierIntegral_continuousLinearMap_apply {f : V -> (F ->L[Real] E)} {a : 
F} {w : W} (he : Continuous e) (hf : Integrable f μ) : fourierIntegral e μ L.toL
inearMap₁₂ f w a = fourierIntegral e μ L.toLinearMap₁₂ (fun x => f x a) w
参数：F ->L[Real] E；he : Continuous e；hf : Integrable f μ。
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
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorFourier.fourierIntegral.eq_1`：∀ {𝕜 : Type u_1} [inst : CommRing 𝕜]
 {V : Type u_2} [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3
 : MeasurableSpace V] {W…
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
· 使用定理 `ContinuousLinearMap.integral_apply`：integral_apply {H : Type*} [NormedAd
dCommGroup H] [NormedSpace 𝕜 H] {φ : X -> H ->L[𝕜] E} (φ_int : Integrable φ μ) (
v : H) : (∫ x, φ x ∂μ) v…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
-/
theorem fourierIntegral_continuousLinearMap_apply
    {f : V → (F →L[ℝ] E)} {a : F} {w : W} (he : Continuous e) (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₁₂ f w a =
      fourierIntegral e μ L.toLinearMap₁₂ (fun x ↦ f x a) w := by
  rw [fourierIntegral, ContinuousLinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂
/-
**VectorFourier.fourierIntegral_continuousMultilinearMap_apply** 是 Mathlib 中的一个定
理，位于命名空间 `VectorFourier`。
形式化陈述：fourierIntegral_continuousMultilinearMap_apply {f : V -> (ContinuousMultil
inearMap Real M E)} {m : (i : ι) -> M i} {w : W} (he : Continuous e) (hf : Integ
rable f μ) : fourierIntegral e μ L.toLinearMap₁₂ f w m = fourierIntegral e μ L.t
oLinearMap₁₂ (fun x => f x m) w
参数：ContinuousMultilinearMap Real M E；i : ι；he : Continuous e；hf : Integrable f μ
。
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
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorFourier.fourierIntegral.eq_1`：∀ {𝕜 : Type u_1} [inst : CommRing 𝕜]
 {V : Type u_2} [inst_1 : AddCommGroup V] [inst_2 : _root_.Module 𝕜 V]   [inst_3
 : MeasurableSpace V] {W…
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
· 使用定理 `ContinuousMultilinearMap.integral_apply`：∀ {X : Type u_1} {E : Type u_3}
 [inst : MeasurableSpace X] {μ : MeasureTheory.Measure X} {𝕜 : Type u_6}   [inst
_1 : RCLike 𝕜] [inst_2 : Norm…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
-/
theorem fourierIntegral_continuousMultilinearMap_apply
    {f : V → (ContinuousMultilinearMap ℝ M E)} {m : (i : ι) → M i} {w : W} (he : Continuous e)
    (hf : Integrable f μ) :
    fourierIntegral e μ L.toLinearMap₁₂ f w m =
      fourierIntegral e μ L.toLinearMap₁₂ (fun x ↦ f x m) w := by
  rw [fourierIntegral, ContinuousMultilinearMap.integral_apply]
  · rfl
  · apply (fourierIntegral_convergent_iff he _ _).2 hf
    exact L.continuous₂

end VectorFourier


/-! ## Fourier theory for functions on `𝕜` -/


namespace Fourier

variable {𝕜 : Type*} [CommRing 𝕜] [MeasurableSpace 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E]

section Defs

/-- The Fourier transform integral for `f : 𝕜 → E`, with respect to the measure `μ` and additive
character `e`. -/
/-
**Fourier.fourierIntegral** 是 Mathlib 中的一个定义，位于命名空间 `Fourier`。
形式化陈述：fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜) : E
参数：e : AddChar 𝕜 𝕊；μ : Measure 𝕜；f : 𝕜 -> E；w : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform integral for `f : 𝕜 → E`, with respect to the measure `μ` 
and additive
character `e`.
-/
def fourierIntegral (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) : E :=
  VectorFourier.fourierIntegral e μ (LinearMap.mul 𝕜 𝕜) f w
/-
**Fourier.fourierIntegral_def** 是 Mathlib 中的一个定理，位于命名空间 `Fourier`。
形式化陈述：fourierIntegral_def (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) (w : 𝕜)
 : fourierIntegral e μ f w = ∫ v : 𝕜, e (-(v * w)) • f v ∂μ
参数：e : AddChar 𝕜 𝕊；μ : Measure 𝕜；f : 𝕜 -> E；w : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fourierIntegral_def (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (w : 𝕜) :
    fourierIntegral e μ f w = ∫ v : 𝕜, e (-(v * w)) • f v ∂μ :=
  rfl
/-
**Fourier.fourierIntegral_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Fourier`。
形式化陈述：fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 -> E) 
(r : Complex) : fourierIntegral e μ (r • f) = r • fourierIntegral e μ f
参数：e : AddChar 𝕜 𝕊；μ : Measure 𝕜；f : 𝕜 -> E；r : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorFourier.fourierIntegral_const_smul`：fourierIntegral_const_smul (e 
: AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V -> E) (r : Compl
ex) : fourierIntegral e μ L (r…
-/
theorem fourierIntegral_const_smul (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f : 𝕜 → E) (r : ℂ) :
    fourierIntegral e μ (r • f) = r • fourierIntegral e μ f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of `f`. -/
/-
**Fourier.norm_fourierIntegral_le_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Fouri
er`。
形式化陈述：norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜) (f
 : 𝕜 -> E) (w : 𝕜) : ‖fourierIntegral e μ f w‖ <= ∫ x : 𝕜, ‖f x‖ ∂μ
参数：e : AddChar 𝕜 𝕊；μ : Measure 𝕜；f : 𝕜 -> E；w : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorFourier.norm_fourierIntegral_le_integral_norm`：norm_fourierIntegra
l_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure V) (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (
f : V -> E) (w : W) : ‖fourierIntegral e …

--- 原说明 ---
The uniform norm of the Fourier transform of `f` is bounded by the `L¹` norm of 
`f`.
-/
theorem norm_fourierIntegral_le_integral_norm (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    (f : 𝕜 → E) (w : 𝕜) : ‖fourierIntegral e μ f w‖ ≤ ∫ x : 𝕜, ‖f x‖ ∂μ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- The Fourier transform converts right-translation into scalar multiplication by a phase
factor. -/
/-
**Fourier.fourierIntegral_comp_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Fourier`。
形式化陈述：fourierIntegral_comp_add_right [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Me
asure 𝕜) [μ.IsAddRightInvariant] (f : 𝕜 -> E) (v₀ : 𝕜) : fourierIntegral e μ (f 
∘ fun v => v + v₀) = fun w => e (v₀ * w) • fourierIntegral e μ f w
参数：e : AddChar 𝕜 𝕊；μ : Measure 𝕜；f : 𝕜 -> E；v₀ : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorFourier.fourierIntegral_comp_add_right`：fourierIntegral_comp_add_r
ight [MeasurableAdd V] (e : AddChar 𝕜 𝕊) (μ : Measure V) [μ.IsAddRightInvariant]
 (L : V ->ₗ[𝕜] W ->ₗ[𝕜] 𝕜) (f : V …

--- 原说明 ---
The Fourier transform converts right-translation into scalar multiplication by a
 phase
factor.
-/
theorem fourierIntegral_comp_add_right [MeasurableAdd 𝕜] (e : AddChar 𝕜 𝕊) (μ : Measure 𝕜)
    [μ.IsAddRightInvariant] (f : 𝕜 → E) (v₀ : 𝕜) :
    fourierIntegral e μ (f ∘ fun v ↦ v + v₀) = fun w ↦ e (v₀ * w) • fourierIntegral e μ f w :=
  VectorFourier.fourierIntegral_comp_add_right _ _ _ _ _

end Defs

end Fourier

open scoped Real

namespace Real

open FourierTransform

variable {V W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-
**Real.vector_fourierIntegral_eq_integral_exp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Re
al`。
形式化陈述：vector_fourierIntegral_eq_integral_exp_smul {V : Type*} [AddCommGroup V] [
Module Real V] [MeasurableSpace V] {W : Type*} [AddCommGroup W] [Module Real W] 
(L : V ->ₗ[Real] W ->ₗ[Real] Real) (μ : Measure V) (f : V -> E) (w : W) : Vector
Fourier.fourierIntegral fourierChar μ L f w = ∫ v : V, Complex.exp (↑(-2 * π * L
 v w) * Complex.I) • f v ∂μ
参数：L : V ->ₗ[Real] W ->ₗ[Real] Real；μ : Measure V；f : V -> E；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vector_fourierIntegral_eq_integral_exp_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    [MeasurableSpace V] {W : Type*} [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (μ : Measure V) (f : V → E) (w : W) :
    VectorFourier.fourierIntegral fourierChar μ L f w =
      ∫ v : V, Complex.exp (↑(-2 * π * L v w) * Complex.I) • f v ∂μ := by
  simp_rw [VectorFourier.fourierIntegral, Circle.smul_def, Real.fourierChar_apply, mul_neg,
    neg_mul]

/-- The Fourier integral is well defined iff the function is integrable. Version with a general
continuous bilinear function `L`. For the specialization to the inner product in an inner product
space, see `Real.fourierIntegral_convergent_iff`. -/
@[simp]
/-
**Real.fourierIntegral_convergent_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourierIntegral_convergent_iff' {V W : Type*} [NormedAddCommGroup V] [Norm
edSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W] [MeasurableSpace V] 
[BorelSpace V] {μ : Measure V} {f : V -> E} (L : V ->L[Real] W ->L[Real] Real) (
w : W) : Integrable (fun v : V => 𝐞 (- L v w) • f v) μ ↔ Integrable f μ
参数：L : V ->L[Real] W ->L[Real] Real；w : W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `VectorFourier.fourierIntegral_convergent_iff`：fourierIntegral_convergent
_iff (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {f : V -> 
E} (w : W) : Integrable (fun v : V…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)

--- 原说明 ---
The Fourier integral is well defined iff the function is integrable. Version wit
h a general
continuous bilinear function `L`. For the specialization to the inner product in
 an inner product
space, see `Real.fourierIntegral_convergent_iff`.
-/
theorem fourierIntegral_convergent_iff' {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    {f : V → E} (L : V →L[ℝ] W →L[ℝ] ℝ) (w : W) :
    Integrable (fun v : V ↦ 𝐞 (- L v w) • f v) μ ↔ Integrable f μ :=
  VectorFourier.fourierIntegral_convergent_iff (E := E) (L := L.toLinearMap₁₂)
    continuous_fourierChar L.continuous₂ _

section Apply

variable {ι F V W : Type*} [Fintype ι]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure V} {L : V →L[ℝ] W →L[ℝ] ℝ}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]

/-
**Real.fourierIntegral_continuousLinearMap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Rea
l`。
形式化陈述：fourierIntegral_continuousLinearMap_apply' {f : V -> (F ->L[Real] E)} {a :
 F} {w : W} (hf : Integrable f μ) : VectorFourier.fourierIntegral 𝐞 μ L.toLinear
Map₁₂ f w a = VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x => f x a)
 w
参数：F ->L[Real] E；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `VectorFourier.fourierIntegral_continuousLinearMap_apply`：fourierIntegral
_continuousLinearMap_apply {f : V -> (F ->L[Real] E)} {a : F} {w : W} (he : Cont
inuous e) (hf : Integrable f μ) : fourierInte…
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
-/
theorem fourierIntegral_continuousLinearMap_apply'
    {f : V → (F →L[ℝ] E)} {a : F} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w a =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x ↦ f x a) w :=
  VectorFourier.fourierIntegral_continuousLinearMap_apply continuous_fourierChar hf
/-
**Real.fourierIntegral_continuousMultilinearMap_apply'** 是 Mathlib 中的一个定理，位于命名空间
 `Real`。
形式化陈述：fourierIntegral_continuousMultilinearMap_apply' {f : V -> ContinuousMultil
inearMap Real M E} {m : (i : ι) -> M i} {w : W} (hf : Integrable f μ) : VectorFo
urier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w m = VectorFourier.fourierIntegral 
𝐞 μ L.toLinearMap₁₂ (fun x => f x m) w
参数：i : ι；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `VectorFourier.fourierIntegral_continuousMultilinearMap_apply`：fourierInt
egral_continuousMultilinearMap_apply {f : V -> (ContinuousMultilinearMap Real M 
E)} {m : (i : ι) -> M i} {w : W} (he : Continuous …
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
-/
theorem fourierIntegral_continuousMultilinearMap_apply'
    {f : V → ContinuousMultilinearMap ℝ M E} {m : (i : ι) → M i} {w : W} (hf : Integrable f μ) :
    VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w m =
      VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ (fun x ↦ f x m) w :=
  VectorFourier.fourierIntegral_continuousMultilinearMap_apply continuous_fourierChar hf

end Apply

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional ℝ W]

open scoped RealInnerProductSpace

/-
**Real.fourierIntegral_convergent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [BorelSpace V] {μ : MeasureTheory.Measure V} {f :
 V → E}   (w : V), MeasureTheory.Integrable (fun v => Real.fourierChar (-inner ℝ
 v w) • f v) μ ↔ MeasureTheory.Integrable f μ
参数：w : V；fun v => Real.fourierChar (-inner ℝ v w) • f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.fourierIntegral_convergent_iff'`：fourierIntegral_convergent_iff' {V
 W : Type*} [NormedAddCommGroup V] [NormedSpace Real V] [NormedAddCommGroup W] [
NormedSpace Real W] [Measu…
-/
@[simp] theorem fourierIntegral_convergent_iff {μ : Measure V} {f : V → E} (w : V) :
    Integrable (fun v : V ↦ 𝐞 (- ⟪v, w⟫) • f v) μ ↔ Integrable f μ :=
  fourierIntegral_convergent_iff' (innerSL ℝ) w

variable [FiniteDimensional ℝ V]
/-
**Real.instFourierTransform** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instFourierTransform : FourierTransform (V -> E) (V -> E) where fourier f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFourierTransform : FourierTransform (V → E) (V → E) where
  fourier f := VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f
/-
**Real.instFourierTransformInv** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：instFourierTransformInv : FourierTransformInv (V -> E) (V -> E) where four
ierInv f w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFourierTransformInv : FourierTransformInv (V → E) (V → E) where
  fourierInv f w := VectorFourier.fourierIntegral 𝐞 volume (-innerₗ V) f w
/-
**Real.fourier_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourier_eq (f : V -> E) (w : V) : 𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v
参数：f : V -> E；w : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourier_eq (f : V → E) (w : V) :
    𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v := rfl
/-
**Real.fourier_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourier_eq' (f : V -> E) (w : V) : 𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪
v, w⟫) * Complex.I)) • f v
参数：f : V -> E；w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourier_eq' (f : V → E) (w : V) :
    𝓕 f w = ∫ v, Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourier_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul]
/-
**Real.fourier_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_congr_ae {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V) : 𝓕 f₁ x
 = 𝓕 f₂ x
参数：hf : f₁ =ᵐ[volume] f₂；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fourier_congr_ae {f₁ f₂ : V → E} (hf : f₁ =ᵐ[volume] f₂) (x : V) : 𝓕 f₁ x = 𝓕 f₂ x := by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']
/-
**Real.fourierInv_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourierInv_eq (f : V -> E) (w : V) : 𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v
参数：f : V -> E；w : V。
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
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourierInv_eq (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, 𝐞 ⟪v, w⟫ • f v := by
  simp [FourierTransformInv.fourierInv, VectorFourier.fourierIntegral]
/-
**Real.fourierInv_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourierInv_eq' (f : V -> E) (w : V) : 𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π 
* ⟪v, w⟫) * Complex.I)) • f v
参数：f : V -> E；w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_eq`：fourierInv_eq (f : V -> E) (w : V) : 𝓕⁻ f w = ∫ v, 𝐞
 ⟪v, w⟫ • f v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourierInv_eq' (f : V → E) (w : V) :
    𝓕⁻ f w = ∫ v, Complex.exp ((↑(2 * π * ⟪v, w⟫) * Complex.I)) • f v := by
  simp_rw [fourierInv_eq, Circle.smul_def, Real.fourierChar_apply]
/-
**Real.fourier_comp_linearIsometry** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourier_comp_linearIsometry (A : W ≃ₗᵢ[Real] V) (f : V -> E) (w : W) : 𝓕 (
f ∘ A) w = (𝓕 f) (A w)
参数：A : W ≃ₗᵢ[Real] V；f : V -> E；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourier_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕 (f ∘ A) w = (𝓕 f) (A w) := by
  simp only [fourier_eq, ← A.inner_map_map, Function.comp_apply,
    ← MeasurePreserving.integral_comp A.measurePreserving A.toHomeomorph.measurableEmbedding]
/-
**Real.fourierInv_eq_fourier_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourierInv_eq_fourier_neg (f : V -> E) (w : V) : 𝓕⁻ f w = 𝓕 f (-w)
参数：f : V -> E；w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_eq`：fourierInv_eq (f : V -> E) (w : V) : 𝓕⁻ f w = ∫ v, 𝐞
 ⟪v, w⟫ • f v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourierInv_eq_fourier_neg (f : V → E) (w : V) :
    𝓕⁻ f w = 𝓕 f (-w) := by
  simp [fourier_eq, fourierInv_eq]
/-
**Real.fourierInv_eq_fourier_comp_neg** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourierInv_eq_fourier_comp_neg (f : V -> E) : 𝓕⁻ f = 𝓕 (fun x => f (-x))
参数：f : V -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_eq_fourier_neg`：fourierInv_eq_fourier_neg (f : V -> E) (
w : V) : 𝓕⁻ f w = 𝓕 f (-w)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.fourier_comp_linearIsometry`：fourier_comp_linearIsometry (A : W ≃ₗᵢ
[Real] V) (f : V -> E) (w : W) : 𝓕 (f ∘ A) w = (𝓕 f) (A w)
-/
lemma fourierInv_eq_fourier_comp_neg (f : V → E) :
    𝓕⁻ f = 𝓕 (fun x ↦ f (-x)) := by
  ext y
  rw [fourierInv_eq_fourier_neg]
  change 𝓕 f (LinearIsometryEquiv.neg ℝ y) = 𝓕 (f ∘ LinearIsometryEquiv.neg ℝ) y
  exact (fourier_comp_linearIsometry _ _ _).symm
/-
**Real.fourierInv_comm** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourierInv_comm (f : V -> E) : 𝓕 (𝓕⁻ f) = 𝓕⁻ (𝓕 f)
参数：f : V -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_eq_fourier_comp_neg`：fourierInv_eq_fourier_comp_neg (f :
 V -> E) : 𝓕⁻ f = 𝓕 (fun x => f (-x))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fourierInv_comm (f : V → E) :
    𝓕 (𝓕⁻ f) = 𝓕⁻ (𝓕 f) := by
  conv_rhs => rw [fourierInv_eq_fourier_comp_neg]
  simp_rw [← fourierInv_eq_fourier_neg]
/-
**Real.fourierInv_comp_linearIsometry** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：fourierInv_comp_linearIsometry (A : W ≃ₗᵢ[Real] V) (f : V -> E) (w : W) : 
𝓕⁻ (f ∘ A) w = (𝓕⁻ f) (A w)
参数：A : W ≃ₗᵢ[Real] V；f : V -> E；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_eq_fourier_neg`：fourierInv_eq_fourier_neg (f : V -> E) (
w : V) : 𝓕⁻ f w = 𝓕 f (-w)
· 使用引理 `Real.fourier_comp_linearIsometry`：fourier_comp_linearIsometry (A : W ≃ₗᵢ
[Real] V) (f : V -> E) (w : W) : 𝓕 (f ∘ A) w = (𝓕 f) (A w)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
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
-/
lemma fourierInv_comp_linearIsometry (A : W ≃ₗᵢ[ℝ] V) (f : V → E) (w : W) :
    𝓕⁻ (f ∘ A) w = (𝓕⁻ f) (A w) := by
  simp [fourierInv_eq_fourier_neg, fourier_comp_linearIsometry]
/-
**Real.fourier_real_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_real_eq (f : Real -> E) (w : Real) : 𝓕 f w = ∫ v : Real, 𝐞 (-(v * 
w)) • f v
参数：f : Real -> E；w : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem fourier_real_eq (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, 𝐞 (-(v * w)) • f v := by
  simp_rw [mul_comm _ w]
  rfl
/-
**Real.fourier_real_eq_integral_exp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_real_eq_integral_exp_smul (f : Real -> E) (w : Real) : 𝓕 f w = ∫ v
 : Real, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v
参数：f : Real -> E；w : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.fourier_real_eq`：fourier_real_eq (f : Real -> E) (w : Real) : 𝓕 f w
 = ∫ v : Real, 𝐞 (-(v * w)) • f v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_real_eq_integral_exp_smul (f : ℝ → E) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • f v := by
  simp_rw [fourier_real_eq, Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul,
    mul_assoc]
/-
**Real.fourier_continuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_continuousLinearMap_apply {F : Type*} [NormedAddCommGroup F] [Norm
edSpace Real F] {f : V -> (F ->L[Real] E)} {a : F} {v : V} (hf : Integrable f) :
 𝓕 f v a = 𝓕 (fun x => f x a) v
参数：F ->L[Real] E；hf : Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Real.fourierIntegral_continuousLinearMap_apply'`：fourierIntegral_continu
ousLinearMap_apply' {f : V -> (F ->L[Real] E)} {a : F} {w : W} (hf : Integrable 
f μ) : VectorFourier.fourierIntegral …
-/
theorem fourier_continuousLinearMap_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → (F →L[ℝ] E)} {a : F} {v : V} (hf : Integrable f) :
    𝓕 f v a = 𝓕 (fun x ↦ f x a) v :=
  fourierIntegral_continuousLinearMap_apply' (L := innerSL ℝ) hf
/-
**Real.fourier_continuousMultilinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_continuousMultilinearMap_apply {ι : Type*} [Fintype ι] {M : ι -> T
ype*} [forall i, NormedAddCommGroup (M i)] [forall i, NormedSpace Real (M i)] {f
 : V -> ContinuousMultilinearMap Real M E} {m : (i : ι) -> M i} {v : V} (hf : In
tegrable f) : 𝓕 f v m = 𝓕 (fun x => f x m) v
参数：M i；M i；i : ι；hf : Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Real.fourierIntegral_continuousMultilinearMap_apply'`：fourierIntegral_co
ntinuousMultilinearMap_apply' {f : V -> ContinuousMultilinearMap Real M E} {m : 
(i : ι) -> M i} {w : W} (hf : Integrable f…
-/
theorem fourier_continuousMultilinearMap_apply {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, NormedAddCommGroup (M i)] [∀ i, NormedSpace ℝ (M i)]
    {f : V → ContinuousMultilinearMap ℝ M E} {m : (i : ι) → M i} {v : V} (hf : Integrable f) :
    𝓕 f v m = 𝓕 (fun x ↦ f x m) v :=
  fourierIntegral_continuousMultilinearMap_apply' (L := innerSL ℝ) hf

open scoped BoundedContinuousFunction

/-- The Fourier transform from `L1` functions to bounded continuous functions. -/
/-
**Real.Lp.fourierTransform** 是 Mathlib 中的一个定义，位于命名空间 `Real.Lp`。
形式化陈述：{V : Type u_1} →   {E : Type u_3} →     [inst : NormedAddCommGroup E] →   
    [NormedSpace ℂ E] →         [inst_2 : NormedAddCommGroup V] →           [ins
t_3 : InnerProductSpace ℝ V] →             [inst_4 : MeasurableSpace V] →       
        [inst_5 : BorelSpace V] →                 [inst_6 : FiniteDimensional ℝ 
V] →                   ↥(MeasureTheory.Lp E 1 MeasureTheory.volume) → BoundedCon
tinuousFunction V E
参数：MeasureTheory.Lp E 1 MeasureTheory.volume。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform from `L1` functions to bounded continuous functions.
-/
def Lp.fourierTransform (f : Lp (α := V) E 1) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (𝓕 (f : V → E))
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (L1.integrable_coeFn f))
  ‖f‖ fun x ↦ by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [Circle.norm_smul]
    exact (L1.norm_eq_integral_norm f).symm.le

@[norm_cast]
/-
**Real.Lp.coe_fourierTransform** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   (f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)), ⇑(Real.Lp.fourierT
ransform f) = FourierTransform.fourier ↑↑f
参数：f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)；Real.Lp.fourierTransform f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem Lp.coe_fourierTransform (f : Lp (α := V) E 1) :
    (Lp.fourierTransform f : V → E) = 𝓕 (f : V → E) := rfl

@[simp]
/-
**Real.Lp.fourierTransform_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   (f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)) (x : V),   (Real.Lp
.fourierTransform f) x = FourierTransform.fourier (↑↑f) x
参数：f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)；x : V；Real.Lp.fourierTransfo
rm f；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem Lp.fourierTransform_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransform f x = 𝓕 (f : V → E) x := rfl

@[simp]
/-
**Real.fourierTransform_toLp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourierTransform_toLp {f : V -> E} (hf : MemLp f 1) : (Lp.fourierTransform
 hf.toLp : V -> E) = 𝓕 f
参数：hf : MemLp f 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.fourier_congr_ae`：fourier_congr_ae {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[vol
ume] f₂) (x : V) : 𝓕 f₁ x = 𝓕 f₂ x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
-/
theorem fourierTransform_toLp {f : V → E} (hf : MemLp f 1) :
    (Lp.fourierTransform hf.toLp : V → E) = 𝓕 f := by
  simp only [Lp.coe_fourierTransform]
  ext x
  exact (Real.fourier_congr_ae hf.coeFn_toLp) x

variable (V E) in
/-- The Fourier transform from `L1` functions to bounded continuous functions as a continuous linear
map. -/
/-
**Real.Lp.fourierTransformCLM** 是 Mathlib 中的一个定义，位于命名空间 `Real.Lp`。
形式化陈述：(V : Type u_1) →   (E : Type u_3) →     [inst : NormedAddCommGroup E] →   
    [inst_1 : NormedSpace ℂ E] →         [inst_2 : NormedAddCommGroup V] →      
     [inst_3 : InnerProductSpace ℝ V] →             [inst_4 : MeasurableSpace V]
 →               [inst_5 : BorelSpace V] →                 [inst_6 : FiniteDimen
sional ℝ V] →                   ↥(MeasureTheory.Lp E 1 MeasureTheory.volume) →L[
ℂ] BoundedContinuousFunction V E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
The Fourier transform from `L1` functions to bounded continuous functions as a c
ontinuous linear
map.
-/
def Lp.fourierTransformCLM : Lp (α := V) E 1 →L[ℂ] V →ᵇ E :=
  LinearMap.mkContinuous
    { toFun := Lp.fourierTransform
      map_add' f g := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_add, Pi.add_apply,
          Real.fourier_eq]
        rw [← integral_add]
        · apply integral_congr_ae
          filter_upwards [Lp.coeFn_add f g] with x h₁
          rw [h₁]
          simp
        · rw [Real.fourierIntegral_convergent_iff]
          exact L1.integrable_coeFn f
        · rw [Real.fourierIntegral_convergent_iff]
          exact L1.integrable_coeFn g
      map_smul' c f := by
        ext x
        simp only [Lp.fourierTransform_apply, BoundedContinuousFunction.coe_smul, Real.fourier_eq]
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with x h
        rw [h, smul_comm]
        simp }
    1 fun f ↦ by
      rw [one_mul, BoundedContinuousFunction.norm_le (by positivity)]
      intro x
      rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.fourierTransform_apply, Real.fourier_eq]
      apply (norm_integral_le_integral_norm _).trans
      simp_rw [Circle.norm_smul]
      exact (L1.norm_eq_integral_norm f).symm.le

@[simp]
/-
**Real.Lp.fourierTransformCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   (f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)), (Real.Lp.fourierTr
ansformCLM V E) f = Real.Lp.fourierTransform f
参数：f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)；Real.Lp.fourierTransformCLM 
V E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem Lp.fourierTransformCLM_apply (f : Lp (α := V) E 1) :
  Lp.fourierTransformCLM V E f = Lp.fourierTransform f := rfl

/-- The inverse Fourier transform from `L1` functions to bounded continuous functions. -/
/-
**Real.Lp.fourierTransformInv** 是 Mathlib 中的一个定义，位于命名空间 `Real.Lp`。
形式化陈述：{V : Type u_1} →   {E : Type u_3} →     [inst : NormedAddCommGroup E] →   
    [NormedSpace ℂ E] →         [inst_2 : NormedAddCommGroup V] →           [ins
t_3 : InnerProductSpace ℝ V] →             [inst_4 : MeasurableSpace V] →       
        [inst_5 : BorelSpace V] →                 [inst_6 : FiniteDimensional ℝ 
V] →                   ↥(MeasureTheory.Lp E 1 MeasureTheory.volume) → BoundedCon
tinuousFunction V E
参数：MeasureTheory.Lp E 1 MeasureTheory.volume。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse Fourier transform from `L1` functions to bounded continuous function
s.
-/
def Lp.fourierTransformInv (f : Lp (α := V) E 1) : V →ᵇ E :=
  (Lp.fourierTransform f).compContinuous (-ContinuousMap.id V)
/-
**Real.fourierInv_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourierInv_congr_ae {f₁ f₂ : V -> E} (hf : f₁ =ᵐ[volume] f₂) (x : V) : 𝓕⁻ 
f₁ x = 𝓕⁻ f₂ x
参数：hf : f₁ =ᵐ[volume] f₂；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fourierInv_congr_ae {f₁ f₂ : V → E} (hf : f₁ =ᵐ[volume] f₂) (x : V) :
    𝓕⁻ f₁ x = 𝓕⁻ f₂ x := by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

@[simp]
/-
**Real.Lp.fourierTransformInv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   (f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)) (x : V),   (Real.Lp
.fourierTransformInv f) x = FourierTransformInv.fourierInv (↑↑f) x
参数：f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)；x : V；Real.Lp.fourierTransfo
rmInv f；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.fourierInv_eq_fourier_neg`：fourierInv_eq_fourier_neg (f : V -> E) (
w : V) : 𝓕⁻ f w = 𝓕 f (-w)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Lp.fourierTransformInv_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformInv f x = 𝓕⁻ (f : V → E) x := by
  simp [Lp.fourierTransformInv, fourierInv_eq_fourier_neg]

@[norm_cast]
/-
**Real.Lp.coe_fourierTransformInv** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   (f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)),   ⇑(Real.Lp.fourie
rTransformInv f) = FourierTransformInv.fourierInv ↑↑f
参数：f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)；Real.Lp.fourierTransformInv 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Lp.fourierTransformInv_apply`：∀ {V : Type u_1} {E : Type u_3} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [inst_2 : NormedAddCommGroup
 V]   [inst_3 : InnerPr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Lp.coe_fourierTransformInv (f : Lp (α := V) E 1) :
    (Lp.fourierTransformInv f : V → E) = 𝓕⁻ (f : V → E) := by
  ext x
  simp

@[simp]
/-
**Real.Lp.fourierTransformInv_toLp** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   {f : V → E} (hf : MeasureTheory.MemLp f 1 MeasureTheory.volume),   ⇑(R
eal.Lp.fourierTransformInv (MeasureTheory.MemLp.toLp f hf)) = FourierTransformIn
v.fourierInv f
参数：hf : MeasureTheory.MemLp f 1 MeasureTheory.volume；Real.Lp.fourierTransformInv
 (MeasureTheory.MemLp.toLp f hf)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Lp.fourierTransformInv_apply`：∀ {V : Type u_1} {E : Type u_3} [inst
 : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [inst_2 : NormedAddCommGroup
 V]   [inst_3 : InnerPr…
· 使用定理 `Real.fourierInv_congr_ae`：fourierInv_congr_ae {f₁ f₂ : V -> E} (hf : f₁ 
=ᵐ[volume] f₂) (x : V) : 𝓕⁻ f₁ x = 𝓕⁻ f₂ x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
-/
theorem Lp.fourierTransformInv_toLp {f : V → E} (hf : MemLp f 1) :
    (Lp.fourierTransformInv hf.toLp : V → E) = 𝓕⁻ f := by
  ext x
  simpa using (Real.fourierInv_congr_ae hf.coeFn_toLp) x

variable (V E) in
/-- The inverse Fourier transform from `L1` functions to bounded continuous functions as a
continuous linear map. -/
/-
**Real.Lp.fourierTransformInvCLM** 是 Mathlib 中的一个定义，位于命名空间 `Real.Lp`。
形式化陈述：(V : Type u_1) →   (E : Type u_3) →     [inst : NormedAddCommGroup E] →   
    [inst_1 : NormedSpace ℂ E] →         [inst_2 : NormedAddCommGroup V] →      
     [inst_3 : InnerProductSpace ℝ V] →             [inst_4 : MeasurableSpace V]
 →               [inst_5 : BorelSpace V] →                 [inst_6 : FiniteDimen
sional ℝ V] →                   ↥(MeasureTheory.Lp E 1 MeasureTheory.volume) →L[
ℂ] BoundedContinuousFunction V E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
The inverse Fourier transform from `L1` functions to bounded continuous function
s as a
continuous linear map.
-/
def Lp.fourierTransformInvCLM : Lp (α := V) E 1 →L[ℂ] V →ᵇ E :=
  BoundedContinuousFunction.compContinuousCLM _ ℂ (-.id V) ∘L Lp.fourierTransformCLM V E

@[simp]
/-
**Real.Lp.fourierTransformInvCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real.Lp`。
形式化陈述：∀ {V : Type u_1} {E : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℂ E] [inst_2 : NormedAddCommGroup V]   [inst_3 : InnerProductSpace ℝ V
] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] [inst_6 : FiniteDimension
al ℝ V]   (f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)),   (Real.Lp.fourier
TransformInvCLM V E) f = Real.Lp.fourierTransformInv f
参数：f : ↥(MeasureTheory.Lp E 1 MeasureTheory.volume)；Real.Lp.fourierTransformInvC
LM V E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Lp.fourierTransformInvCLM_apply (f : Lp (α := V) E 1) :
    Lp.fourierTransformInvCLM V E f = Lp.fourierTransformInv f := by
  simp [Lp.fourierTransformInvCLM, Lp.fourierTransformInv]

end Real

