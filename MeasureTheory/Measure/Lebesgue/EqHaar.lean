/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`MeasureTheory.addHaarMeasure_eq_volume` and `MeasureTheory.addHaarMeasure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite-dimensional real vector space:
* `map_linearMap_addHaar_eq_smul_addHaar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `addHaar_preimage_linearMap` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `addHaar_image_linearMap` : when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `addHaar_submodule` : a strict submodule has measure `0`.
* `addHaar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `addHaar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_closedBall`: the measure of `closedBall x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_sphere`: spheres have zero measure.

This makes it possible to associate a Lebesgue measure to an `n`-alternating map in dimension `n`.
This measure is called `AlternatingMap.measure`. Its main property is
`ω.measure_parallelepiped v`, stating that the associated measure of the parallelepiped spanned
by vectors `v₁, ..., vₙ` is given by `|ω v|`.

We also show that a Lebesgue density point `x` of a set `s` (with respect to closed balls) has
density one for the rescaled copies `{x} + r • t` of a given set `t` with positive measure, in
`tendsto_addHaar_inter_smul_one_of_density_one`. In particular, `s` intersects `{x} + r • t` for
small `r`, see `eventually_nonempty_inter_smul_of_density_one`.

Statements on integrals of functions with respect to an additive Haar measure can be found in
`MeasureTheory.Measure.Haar.NormedSpace`.
-/

@[expose] public section

assert_not_exists MeasureTheory.integral

open TopologicalSpace Set Filter Metric Bornology

open scoped ENNReal Pointwise Topology NNReal

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
/-
**TopologicalSpace.PositiveCompacts.Icc01** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.PositiveCompacts.Icc01 : PositiveCompacts Real where carr
ier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The interval `[0,1]` as a compact set with non-empty interior.
-/
def TopologicalSpace.PositiveCompacts.Icc01 : PositiveCompacts ℝ where
  carrier := Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
/-
**TopologicalSpace.PositiveCompacts.piIcc01** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type*) [Finite ι] : Positiv
eCompacts (ι -> Real) where carrier
参数：ι : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `[0,1]^ι` as a compact set with non-empty interior.
-/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type*) [Finite ι] :
    PositiveCompacts (ι → ℝ) where
  carrier := pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]

namespace Module.Basis

/-- The parallelepiped formed from the standard basis for `ι → ℝ` is `[0,1]^ι` -/
/-
**Module.Basis.parallelepiped_basisFun** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：parallelepiped_basisFun (ι : Type*) [Fintype ι] : (Pi.basisFun Real ι).par
allelepiped = TopologicalSpace.PositiveCompacts.piIcc01 ι
参数：ι : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `parallelepiped_single`：parallelepiped_single [DecidableEq ι] (a : ι -> R
eal) : (parallelepiped fun i => Pi.single i (a i)) = Set.uIcc 0 a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y

--- 原说明 ---
The parallelepiped formed from the standard basis for `ι → ℝ` is `[0,1]^ι`
-/
theorem parallelepiped_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).parallelepiped = TopologicalSpace.PositiveCompacts.piIcc01 ι :=
  SetLike.coe_injective <| by
    refine Eq.trans ?_ ((uIcc_of_le ?_).trans (Set.pi_univ_Icc _ _).symm)
    · classical convert! parallelepiped_single (ι := ι) 1
    · exact zero_le_one

/-- A parallelepiped can be expressed on the standard basis. -/
/-
**Module.Basis.parallelepiped_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：parallelepiped_eq_map {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [No
rmedSpace Real E] (b : Basis ι Real E) : b.parallelepiped = (PositiveCompacts.pi
Icc01 ι).map b.equivFun.symm b.equivFunL.symm.continuous b.equivFunL.symm.isOpen
Map
参数：b : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousLinearEquiv.isOpenMap`：isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpen
Map e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.parallelepiped_basisFun`：parallelepiped_basisFun (ι : Type*
) [Fintype ι] : (Pi.basisFun Real ι).parallelepiped = TopologicalSpace.PositiveC
ompacts.piIcc01 ι
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `LinearMap.isOpenMap_of_finiteDimensional`：isOpenMap_of_finiteDimensional
 (f : F ->ₗ[𝕜] E) (hf : Function.Surjective f) : IsOpenMap f
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Module.Basis.parallelepiped_map`：parallelepiped_map (b : Basis ι Real E)
 (e : E ≃ₗ[Real] F) : (b.map e).parallelepiped = b.parallelepiped.map e (haveI
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A parallelepiped can be expressed on the standard basis.
-/
theorem parallelepiped_eq_map {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Basis ι ℝ E) :
    b.parallelepiped = (PositiveCompacts.piIcc01 ι).map b.equivFun.symm
      b.equivFunL.symm.continuous b.equivFunL.symm.isOpenMap := by
  classical
  rw [← Basis.parallelepiped_basisFun, ← Basis.parallelepiped_map]
  congr with x
  simp [Pi.single_apply]

open MeasureTheory MeasureTheory.Measure
/-
**Module.Basis.map_addHaar** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：map_addHaar {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedAddC
ommGroup F] [NormedSpace Real E] [NormedSpace Real F] [MeasurableSpace E] [Measu
rableSpace F] [BorelSpace E] [BorelSpace F] [SecondCountableTopology F] [SigmaCo
mpactSpace F] (b : Basis ι Real E) (f : E ≃L[Real] F) : map f b.addHaar = (b.map
 f.toLinearEquiv).addHaar
参数：b : Basis ι Real E；f : E ≃L[Real] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Module.Basis.addHaar_eq_iff`：addHaar_eq_iff [SecondCountableTopology E] 
(b : Basis ι Real E) (μ : Measure E) [SigmaFinite μ] [IsAddLeftInvariant μ] : b.
addHaar = μ ↔ μ b…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `ContinuousLinearEquiv.isAddHaarMeasure_map`：∀ {E : Type u_3} {F : Type u
_4} {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [i
nst_2 : AddCommGroup E] [inst_3 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `isAddHaarMeasure_basis_addHaar`：∀ {ι : Type u_1} {E : Type u_3} [inst : 
Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 
: MeasurableSpace E]…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousLinearEquiv.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}   [i
nst_2 : RingHomInvPair…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `Module.Basis.coe_parallelepiped`：coe_parallelepiped (b : Basis ι Real E)
 : (b.parallelepiped : Set E) = _root_.parallelepiped b
· 使用定理 `Module.Basis.coe_map`：coe_map : (b.map f : ι -> M') = f ∘ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.addHaar_self`：addHaar_self (b : Basis ι Real E) : b.addHaar
 (_root_.parallelepiped b) = 1
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
· 使用定理 `image_parallelepiped`：image_parallelepiped (f : E ->ₗ[Real] F) (v : ι ->
 E) : f '' parallelepiped v = parallelepiped (f ∘ v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_addHaar {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology F] [SigmaCompactSpace F]
    (b : Basis ι ℝ E) (f : E ≃L[ℝ] F) :
    map f b.addHaar = (b.map f.toLinearEquiv).addHaar := by
  rw [eq_comm, Basis.addHaar_eq_iff, Measure.map_apply f.continuous.measurable
    (PositiveCompacts.isCompact _).measurableSet, Basis.coe_parallelepiped, Basis.coe_map,
    ← addHaar_self b, ← f.toEquiv.preimage_image (_root_.parallelepiped ⇑b)]
  have := image_parallelepiped f.toLinearMap (⇑b : ι → E)
  simp_all

end Module.Basis

namespace MeasureTheory

open Measure TopologicalSpace.PositiveCompacts Module

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
/-
**MeasureTheory.addHaarMeasure_eq_volume** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：addHaarMeasure_eq_volume : addHaarMeasure Icc01 = volume
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_unique`：∀ {G : Type u_1} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [in
st_3 : MeasurableSpace G] [inst_4…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…

--- 原说明 ---
The Haar measure equals the Lebesgue measure on `ℝ`.
-/
theorem addHaarMeasure_eq_volume : addHaarMeasure Icc01 = volume := by
  convert! (addHaarMeasure_unique volume Icc01).symm; simp [Icc01]

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
/-
**MeasureTheory.addHaarMeasure_eq_volume_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：addHaarMeasure_eq_volume_pi (ι : Type*) [Fintype ι] : addHaarMeasure (piIc
c01 ι) = volume
参数：ι : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.volume_pi_pi`：volume_pi_pi [forall i, MeasureSpace (α i)] 
[forall i, SigmaFinite (volume : Measure (α i))] (s : forall i, Set (α i)) : vol
ume (pi univ s) …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_unique`：∀ {G : Type u_1} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [in
st_3 : MeasurableSpace G] [inst_4…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The Haar measure equals the Lebesgue measure on `ℝ^ι`.
-/
theorem addHaarMeasure_eq_volume_pi (ι : Type*) [Fintype ι] :
    addHaarMeasure (piIcc01 ι) = volume := by
  convert! (addHaarMeasure_unique volume (piIcc01 ι)).symm
  simp only [piIcc01, volume_pi_pi fun _ => Icc (0 : ℝ) 1, PositiveCompacts.coe_mk,
    Compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]
/-
**MeasureTheory.isAddHaarMeasure_volume_pi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] : IsAddHaarMeasure (vol
ume : Measure (ι -> Real))
参数：ι : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
-/
theorem isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
  inferInstance

namespace Measure

/-!
### Strict subspaces have zero measure
-/

open scoped Function -- required for scoped `on` notation

/-- If a set is disjoint from its translates by infinitely many bounded vectors, then it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bounded. -/
/-
**MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates_aux** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_eq_zero_of_disjoint_translates_aux {E : Type*} [NormedAddCommGroup
 E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional R
eal E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E} (u : Nat -> E) (sb : IsB
ounded s) (hu : IsBounded (range u)) (hs : Pairwise (Disjoint on fun n => {u n} 
+ s)) (h's : MeasurableSet s) : μ s = 0
参数：μ : Measure E；u : Nat -> E；sb : IsBounded s；hu : IsBounded (range u)；hs : Pai
rwise (Disjoint on fun n => {u n} + s)；h's : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_const_eq_top_of_ne_zero`：tsum_const_eq_top_of_ne_zero {α : 
Type*} [Infinite α] {c : Real>=0∞} (hc : c != 0) : ∑' _ : α, c = ∞
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `MeasureTheory.measure_preimage_add`：∀ {G : Type u_1} [inst : MeasurableS
pace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)   
[μ.IsAddLeftInvariant] (…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Measurable.const_add`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   [MeasurableAdd M
], Measura…
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `Set.iUnion_add`：∀ {α : Type u_2} {ι : Sort u_5} [inst : Add α] (s : ι → 
Set α) (t : Set α), (⋃ i, s i) + t = ⋃ i, s i + t
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Bornology.IsBounded.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} [inst : PseudoMetricSpace α] [ProperSpace α] {μ : MeasureTheory.Measure α}
   [MeasureTheory.IsFini…
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `Bornology.IsBounded.add`：∀ {E : Type u_1} [inst : SeminormedAddGroup E] 
{s t : Set E},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBou
nded (s + t)

--- 原说明 ---
If a set is disjoint from its translates by infinitely many bounded vectors, the
n it has measure
zero. This auxiliary lemma proves this assuming additionally that the set is bou
nded.
-/
theorem addHaar_eq_zero_of_disjoint_translates_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (sb : IsBounded s) (hu : IsBounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  by_contra h
  apply lt_irrefl ∞
  calc
    ∞ = ∑' _ : ℕ, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : ℕ, μ ({u n} + s) := by
      congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
    _ = μ (⋃ n, {u n} + s) := Eq.symm <| measure_iUnion hs fun n => by
      simpa only [image_add_left, singleton_add] using! measurable_id.const_add _ h's
    _ = μ (range u + s) := by rw [← iUnion_add, iUnion_singleton_eq_range]
    _ < ∞ := (hu.add sb).measure_lt_top

/-- If a set is disjoint from its translates by infinitely many bounded vectors, then it has measure
zero. -/
/-
**MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_eq_zero_of_disjoint_translates {E : Type*} [NormedAddCommGroup E] 
[NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real 
E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E} (u : Nat -> E) (hu : IsBound
ed (range u)) (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : Measurable
Set s) : μ s = 0
参数：μ : Measure E；u : Nat -> E；hu : IsBounded (range u)；hs : Pairwise (Disjoint o
n fun n => {u n} + s)；h's : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates_aux`：addHaa
r_eq_zero_of_disjoint_translates_aux {E : Type*} [NormedAddCommGroup E] [NormedS
pace Real E] [MeasurableSpace E] [BorelSpace E] [Finit…
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `pairwise_disjoint_mono`：pairwise_disjoint_mono [PartialOrder α] [OrderBo
t α] (hs : Pairwise (Disjoint on f)) (h : g <= f) : Pairwise (Disjoint on g)
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurableSet_closedBall`：measurableSet_closedBall : MeasurableSet (Metr
ic.closedBall x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.iUnion_inter_closedBall_nat`：iUnion_inter_closedBall_nat (s : Set
 α) (x : α) : ⋃ n : Nat, s inter closedBall x n = s
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a set is disjoint from its translates by infinitely many bounded vectors, the
n it has measure
zero.
-/
theorem addHaar_eq_zero_of_disjoint_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (hu : IsBounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  suffices H : ∀ R, μ (s ∩ closedBall 0 R) = 0 by
    rw [← nonpos_iff_eq_zero]
    calc
      μ s ≤ ∑' n : ℕ, μ (s ∩ closedBall 0 n) := by
        conv_lhs => rw [← iUnion_inter_closedBall_nat s 0]
        exact measure_iUnion_le _
      _ = 0 := by simp only [H, tsum_zero]
  intro R
  apply addHaar_eq_zero_of_disjoint_translates_aux μ u
    (isBounded_closedBall.subset inter_subset_right) hu _ (h's.inter measurableSet_closedBall)
  refine pairwise_disjoint_mono hs fun n => ?_
  exact add_subset_add Subset.rfl inter_subset_left

/-- A strict vector subspace has measure zero. -/
/-
**MeasureTheory.Measure.addHaar_submodule** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：addHaar_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] 
[MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measure E) [I
sAddHaarMeasure μ] (s : Submodule Real E) (hs : s != ⊤) : μ s = 0
参数：μ : Measure E；s : Submodule Real E；hs : s != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Filter.Tendsto.smul_const`：Filter.Tendsto.smul_const {f : α -> M} {l : F
ilter α} {c : M} (hf : Tendsto f l (𝓝 c)) (a : X) : Tendsto (fun x => f x • a) l
 (𝓝 (c • a))
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.isBounded_range_of_tendsto`：isBounded_range_of_tendsto (u : Nat -
> α) {x : α} (hu : Tendsto u atTop (𝓝 x)) : IsBounded (range u)
· 使用定理 `MeasureTheory.Measure.addHaar_eq_zero_of_disjoint_translates`：addHaar_eq
_zero_of_disjoint_translates {E : Type*} [NormedAddCommGroup E] [NormedSpace Rea
l E] [MeasurableSpace E] [BorelSpace E] [FiniteDim…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
A strict vector subspace has measure zero.
-/
theorem addHaar_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (s : Submodule ℝ E)
    (hs : s ≠ ⊤) : μ s = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 := ⟨1 / 2, by simp, by norm_num⟩
  have A : IsBounded (range fun n : ℕ => c ^ n • x) :=
    have : Tendsto (fun n : ℕ => c ^ n • x) atTop (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one cpos.le cone).smul_const x
    isBounded_range_of_tendsto _ this
  apply addHaar_eq_zero_of_disjoint_translates μ _ A _
    (Submodule.closed_of_finiteDimensional s).measurableSet
  intro m n hmn
  simp only [Function.onFun, image_add_left, singleton_add, disjoint_left, mem_preimage,
    SetLike.mem_coe]
  intro y hym hyn
  have A : (c ^ n - c ^ m) • x ∈ s := by
    convert! s.sub_mem hym hyn using 1
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m ≠ 0 := by
    simpa only [sub_eq_zero, Ne] using (pow_right_strictAnti₀ cpos cone).injective.ne hmn.symm
  have : x ∈ s := by
    convert! s.smul_mem (c ^ n - c ^ m)⁻¹ A
    rw [smul_smul, inv_mul_cancel₀ H, one_smul]
  exact hx this

/-- A strict affine subspace has measure zero. -/
/-
**MeasureTheory.Measure.addHaar_affineSubspace** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：addHaar_affineSubspace {E : Type*} [NormedAddCommGroup E] [NormedSpace Rea
l E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measure 
E) [IsAddHaarMeasure μ] (s : AffineSubspace Real E) (hs : s != ⊤) : μ s = 0
参数：μ : Measure E；s : AffineSubspace Real E；hs : s != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.eq_bot_or_nonempty`：eq_bot_or_nonempty (Q : AffineSubspac
e k P) : Q = ⊥ ∨ (Q : Set P).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.bot_coe`：bot_coe : ((⊥ : AffineSubspace k P) : Set P) = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.coe_direction_eq_vsub_set_right`：coe_direction_eq_vsub_se
t_right {s : AffineSubspace k P} {p : P} (hp : p in s) : (s.direction : Set V) =
 (· -ᵥ p) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeasureTheory.measure_preimage_add_right`：∀ {G : Type u_1} [inst : Measu
rableSpace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure
 G)   [μ.IsAddRightInvariant] …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.addHaar_submodule`：addHaar_submodule {E : Type*} [
NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [F
initeDimensional Real E] (μ :…
· 使用定理 `AffineSubspace.direction_eq_top_iff_of_nonempty`：direction_eq_top_iff_of
_nonempty {s : AffineSubspace k P} (h : (s : Set P).Nonempty) : s.direction = ⊤ 
↔ s = ⊤
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b

--- 原说明 ---
A strict affine subspace has measure zero.
-/
theorem addHaar_affineSubspace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) : μ s = 0 := by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
  rw [Ne, ← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x ∈ s⟩
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg,
    image_add_right, neg_neg, measure_preimage_add_right] using addHaar_submodule μ s.direction hs

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/

/-
**MeasureTheory.Measure.map_linearMap_addHaar_pi_eq_smul_addHaar** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：map_linearMap_addHaar_pi_eq_smul_addHaar {ι : Type*} [Finite ι] {f : (ι ->
 Real) ->ₗ[Real] ι -> Real} (hf : LinearMap.det f != 0) (μ : Measure (ι -> Real)
) [IsAddHaarMeasure μ] : Measure.map f μ = ENNReal.ofReal (abs (LinearMap.det f)
⁻¹) • μ
参数：ι -> Real；hf : LinearMap.det f != 0；μ : Measure (ι -> Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.addHaarMeasure_unique`：∀ {G : Type u_1} [inst : Ad
dGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G]   [in
st_3 : MeasurableSpace G] [inst_4…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instSigmaCompactSpaceForallOfFinite`：∀ {ι : Type u_3} [Finite ι] {X : ι 
→ Type u_4} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), SigmaCompact
Space (X i)], SigmaCompac…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.addHaarMeasure_eq_volume_pi`：addHaarMeasure_eq_volume_pi (
ι : Type*) [Fintype ι] : addHaarMeasure (piIcc01 ι) = volume
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `Real.map_linearMap_volume_pi_eq_smul_volume_pi`：map_linearMap_volume_pi_
eq_smul_volume_pi {f : (ι -> Real) ->ₗ[Real] ι -> Real} (hf : LinearMap.det f !=
 0) : Measure.map f volume = ENNReal…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product
 Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-di
mensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and argui
ng that such a
linear equiv maps Haar measure to Haar measure.
-/
theorem map_linearMap_addHaar_pi_eq_smul_addHaar {ι : Type*} [Finite ι] {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ}
    (hf : LinearMap.det f ≠ 0) (μ : Measure (ι → ℝ)) [IsAddHaarMeasure μ] :
    Measure.map f μ = ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • μ := by
  cases nonempty_fintype ι
  /- We have already proved the result for the Lebesgue product measure, using matrices.
    We deduce it for any Haar measure by uniqueness (up to scalar multiplication). -/
  have := addHaarMeasure_unique μ (piIcc01 ι)
  rw [this, addHaarMeasure_eq_volume_pi, Measure.map_smul,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hf, smul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
/-
**MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：map_linearMap_addHaar_eq_smul_addHaar {f : E ->ₗ[Real] E} (hf : LinearMap.
det f != 0) : Measure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ
参数：hf : LinearMap.det f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.det_conj`：det_conj {N : Type*} [AddCommGroup N] [Module A N] (
f : M ->ₗ[A] M) (e : M ≃ₗ[A] N) : LinearMap.det ((e : M ->ₗ[A] N) ∘ₗ f ∘ₗ (e.sym
m : N ->…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
（共 42 条，此处仅展示前 30 条）
-/
theorem map_linearMap_addHaar_eq_smul_addHaar {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) :
    Measure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻¹| • μ := by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `map_linearMap_addHaar_pi_eq_smul_addHaar`.
  let ι := Fin (finrank ℝ E)
  have : FiniteDimensional ℝ (ι → ℝ) := by infer_instance
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by simp [ι]
  have e : E ≃ₗ[ℝ] ι → ℝ := LinearEquiv.ofFinrankEq E (ι → ℝ) this
  -- next line is to avoid `g` getting reduced by `simp`.
  obtain ⟨g, hg⟩ : ∃ g, g = (e : E →ₗ[ℝ] ι → ℝ).comp (f.comp (e.symm : (ι → ℝ) →ₗ[ℝ] E)) := ⟨_, rfl⟩
  have gdet : LinearMap.det g = LinearMap.det f := by rw [hg]; exact LinearMap.det_conj f e
  rw [← gdet] at hf ⊢
  have fg : f = (e.symm : (ι → ℝ) →ₗ[ℝ] E).comp (g.comp (e : E →ₗ[ℝ] ι → ℝ)) := by
    ext x
    simp only [LinearEquiv.coe_coe, Function.comp_apply, LinearMap.coe_comp,
      LinearEquiv.symm_apply_apply, hg]
  simp only [fg, LinearEquiv.coe_coe, LinearMap.coe_comp]
  have Ce : Continuous e := (e : E →ₗ[ℝ] ι → ℝ).continuous_of_finiteDimensional
  have Cg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have Cesymm : Continuous e.symm := (e.symm : (ι → ℝ) →ₗ[ℝ] E).continuous_of_finiteDimensional
  rw [← map_map Cesymm.measurable (Cg.comp Ce).measurable, ← map_map Cg.measurable Ce.measurable]
  have : IsAddHaarMeasure (map e μ) := (e : E ≃+ (ι → ℝ)).isAddHaarMeasure_map μ Ce Cesymm
  have ecomp : e.symm ∘ e = id := by
    ext x; simp only [id, Function.comp_apply, LinearEquiv.symm_apply_apply]
  rw [map_linearMap_addHaar_pi_eq_smul_addHaar hf (map e μ), Measure.map_smul,
    map_map Cesymm.measurable Ce.measurable, ecomp, Measure.map_id]

/-- The preimage of a set `s` under a linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_preimage_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：addHaar_preimage_linearMap {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0)
 (s : Set E) : μ (f ⁻¹' s) = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s
参数：hf : LinearMap.det f != 0；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`：map_linearM
ap_addHaar_eq_smul_addHaar {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) : Mea
sure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻…

--- 原说明 ---
The preimage of a set `s` under a linear map `f` with nonzero determinant has me
asure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`
.
-/
theorem addHaar_preimage_linearMap {f : E →ₗ[ℝ] E} (hf : LinearMap.det f ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s :=
  calc
    μ (f ⁻¹' s) = Measure.map f μ s :=
      ((f.equivOfDetNeZero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply
          s).symm
    _ = ENNReal.ofReal |(LinearMap.det f)⁻¹| * μ s := by
      rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]; rfl

/-- The preimage of a set `s` under a continuous linear map `f` with nonzero determinant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_preimage_continuousLinearMap** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_preimage_continuousLinearMap {f : E ->L[Real] E} (hf : LinearMap.d
et (f : E ->ₗ[Real] E) != 0) (s : Set E) : μ (f ⁻¹' s) = ENNReal.ofReal (abs (Li
nearMap.det (f : E ->ₗ[Real] E))⁻¹) * μ s
参数：hf : LinearMap.det (f : E ->ₗ[Real] E) != 0；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_linearMap`：addHaar_preimage_linea
rMap {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) (s : Set E) : μ (f ⁻¹' s) =
 ENNReal.ofReal |(LinearMap.det f)⁻¹| …

--- 原说明 ---
The preimage of a set `s` under a continuous linear map `f` with nonzero determi
nant has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`
.
-/
theorem addHaar_preimage_continuousLinearMap {f : E →L[ℝ] E}
    (hf : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal (abs (LinearMap.det (f : E →ₗ[ℝ] E))⁻¹) * μ s :=
  addHaar_preimage_linearMap μ hf s

/-- The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_preimage_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：addHaar_preimage_linearEquiv (f : E ≃ₗ[Real] E) (s : Set E) : μ (f ⁻¹' s) 
= ENNReal.ofReal |LinearMap.det (f.symm : E ->ₗ[Real] E)| * μ s
参数：f : E ≃ₗ[Real] E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `LinearEquiv.isUnit_det'`：LinearEquiv.isUnit_det' {A : Type*} [CommRing A
] [Module A M] (f : M ≃ₗ[A] M) : IsUnit (LinearMap.det (f : M ->ₗ[A] M))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.det_coe_symm`：LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜]
 [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) : LinearMap.det (f.symm : M ->ₗ[𝕜] M) = (LinearMap
.det (f : M ->…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_linearMap`：addHaar_preimage_linea
rMap {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) (s : Set E) : μ (f ⁻¹' s) =
 ENNReal.ofReal |(LinearMap.det f)⁻¹| …

--- 原说明 ---
The preimage of a set `s` under a linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`
.
-/
theorem addHaar_preimage_linearEquiv (f : E ≃ₗ[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E →ₗ[ℝ] E)| * μ s := by
  have A : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  convert! addHaar_preimage_linearMap μ A s
  simp only [LinearEquiv.det_coe_symm]

/-- The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_preimage_continuousLinearEquiv** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_preimage_continuousLinearEquiv (f : E ≃L[Real] E) (s : Set E) : μ 
(f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E ->ₗ[Real] E)| * μ s
参数：f : E ≃L[Real] E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_linearEquiv`：addHaar_preimage_lin
earEquiv (f : E ≃ₗ[Real] E) (s : Set E) : μ (f ⁻¹' s) = ENNReal.ofReal |LinearMa
p.det (f.symm : E ->ₗ[Real] E)| * μ s

--- 原说明 ---
The preimage of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the inverse of the determinant of `f`
.
-/
theorem addHaar_preimage_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E →ₗ[ℝ] E)| * μ s :=
  addHaar_preimage_linearEquiv μ _ s

/-- The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_image_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：addHaar_image_linearMap (f : E ->ₗ[Real] E) (s : Set E) : μ (f '' s) = ENN
Real.ofReal |LinearMap.det f| * μ s
参数：f : E ->ₗ[Real] E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.image_eq_preimage_symm`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_continuousLinearEquiv`：addHaar_pr
eimage_continuousLinearEquiv (f : E ≃L[Real] E) (s : Set E) : μ (f ⁻¹' s) = ENNR
eal.ofReal |LinearMap.det (f.symm : E ->ₗ[Real] E)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `MeasureTheory.Measure.addHaar_submodule`：addHaar_submodule {E : Type*} [
NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [F
initeDimensional Real E] (μ :…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LinearMap.range_lt_top_of_det_eq_zero`：range_lt_top_of_det_eq_zero [IsDo
main R] [Free R M] {f : M ->ₗ[R] M} (hf : f.det = 0) : range f < ⊤
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
The image of a set `s` under a linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`.
-/
theorem addHaar_image_linearMap (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s := by
  rcases ne_or_eq (LinearMap.det f) 0 with (hf | hf)
  · let g := (f.equivOfDetNeZero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage_symm g s, addHaar_preimage_continuousLinearEquiv]
    congr
  · simpa [hf] using (measure_mono (image_subset_range _ _)).trans_eq <|
      addHaar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).ne

/-- The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_image_continuousLinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_image_continuousLinearMap (f : E ->L[Real] E) (s : Set E) : μ (f '
' s) = ENNReal.ofReal |LinearMap.det (f : E ->ₗ[Real] E)| * μ s
参数：f : E ->L[Real] E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.addHaar_image_linearMap`：addHaar_image_linearMap (
f : E ->ₗ[Real] E) (s : Set E) : μ (f '' s) = ENNReal.ofReal |LinearMap.det f| *
 μ s

--- 原说明 ---
The image of a set `s` under a continuous linear map `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`.
-/
theorem addHaar_image_continuousLinearMap (f : E →L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E →ₗ[ℝ] E)| * μ s :=
  addHaar_image_linearMap μ _ s

/-- The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_image_continuousLinearEquiv** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_image_continuousLinearEquiv (f : E ≃L[Real] E) (s : Set E) : μ (f 
'' s) = ENNReal.ofReal |LinearMap.det (f : E ->ₗ[Real] E)| * μ s
参数：f : E ≃L[Real] E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.addHaar_image_linearMap`：addHaar_image_linearMap (
f : E ->ₗ[Real] E) (s : Set E) : μ (f '' s) = ENNReal.ofReal |LinearMap.det f| *
 μ s

--- 原说明 ---
The image of a set `s` under a continuous linear equiv `f` has measure
equal to `μ s` times the absolute value of the determinant of `f`.
-/
theorem addHaar_image_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E →ₗ[ℝ] E)| * μ s :=
  μ.addHaar_image_linearMap (f : E →ₗ[ℝ] E) s
/-
**MeasureTheory.Measure.LinearMap.quasiMeasurePreserving** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure.LinearMap`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   [FiniteDimensional ℝ E] (μ : Measu
reTheory.Measure E) [μ.IsAddHaarMeasure] (f : E →ₗ[ℝ] E),   LinearMap.det f ≠ 0 
→ MeasureTheory.Measure.QuasiMeasurePreserving (⇑f) μ μ
参数：μ : MeasureTheory.Measure E；f : E →ₗ[ℝ] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`：map_linearM
ap_addHaar_eq_smul_addHaar {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) : Mea
sure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻…
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
-/
theorem LinearMap.quasiMeasurePreserving (f : E →ₗ[ℝ] E) (hf : LinearMap.det f ≠ 0) :
    QuasiMeasurePreserving f μ μ := by
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [map_linearMap_addHaar_eq_smul_addHaar μ hf]
  exact smul_absolutelyContinuous
/-
**MeasureTheory.Measure.ContinuousLinearMap.quasiMeasurePreserving** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure.ContinuousLinearMap`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   [FiniteDimensional ℝ E] (μ : Measu
reTheory.Measure E) [μ.IsAddHaarMeasure] (f : E →L[ℝ] E),   f.det ≠ 0 → MeasureT
heory.Measure.QuasiMeasurePreserving (⇑f) μ μ
参数：μ : MeasureTheory.Measure E；f : E →L[ℝ] E；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.LinearMap.quasiMeasurePreserving`：∀ {E : Type u_1}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSp
ace E] [BorelSpace E]   [FiniteDimensional ℝ…
-/
theorem ContinuousLinearMap.quasiMeasurePreserving (f : E →L[ℝ] E) (hf : f.det ≠ 0) :
    QuasiMeasurePreserving f μ μ :=
  LinearMap.quasiMeasurePreserving μ (f : E →ₗ[ℝ] E) hf

/-!
### Basic properties of Haar measures on real vector spaces
-/


/-
**MeasureTheory.Measure.map_addHaar_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：map_addHaar_smul {r : Real} (hr : r != 0) : Measure.map (r • ·) μ = ENNRea
l.ofReal (abs (r ^ finrank Real E)⁻¹) • μ
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.det_smul`：det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) 
: LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`：map_linearM
ap_addHaar_eq_smul_addHaar {f : E ->ₗ[Real] E} (hf : LinearMap.det f != 0) : Mea
sure.map f μ = ENNReal.ofReal |(LinearMap.det f)⁻…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Basic properties of Haar measures on real vector spaces
-/
theorem map_addHaar_smul {r : ℝ} (hr : r ≠ 0) :
    Measure.map (r • ·) μ = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) • μ := by
  let f : E →ₗ[ℝ] E := r • (1 : E →ₗ[ℝ] E)
  change Measure.map f μ = _
  have hf : LinearMap.det f ≠ 0 := by
    simp only [f, mul_one, LinearMap.det_smul, Ne, map_one]
    exact pow_ne_zero _ hr
  simp only [f, map_linearMap_addHaar_eq_smul_addHaar μ hf, mul_one, LinearMap.det_smul, map_one]
/-
**MeasureTheory.Measure.quasiMeasurePreserving_smul** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：quasiMeasurePreserving_smul {r : Real} (hr : r != 0) : QuasiMeasurePreserv
ing (r • ·) μ μ
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_addHaar_smul`：map_addHaar_smul {r : Real} (hr 
: r != 0) : Measure.map (r • ·) μ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) 
• μ
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
-/
theorem quasiMeasurePreserving_smul {r : ℝ} (hr : r ≠ 0) :
    QuasiMeasurePreserving (r • ·) μ μ := by
  refine ⟨measurable_const_smul r, ?_⟩
  rw [map_addHaar_smul μ hr]
  exact smul_absolutelyContinuous

@[simp]
/-
**MeasureTheory.Measure.addHaar_preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：addHaar_preimage_smul {r : Real} (hr : r != 0) (s : Set E) : μ ((r • ·) ⁻¹
' s) = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) * μ s
参数：hr : r != 0；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_addHaar_smul`：map_addHaar_smul {r : Real} (hr 
: r != 0) : Measure.map (r • ·) μ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) 
• μ
· 使用定理 `MeasureTheory.Measure.coe_smul`：coe_smul {_m : MeasurableSpace α} (c : R
) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem addHaar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    μ ((r • ·) ⁻¹' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s :=
  calc
    μ ((r • ·) ⁻¹' s) = Measure.map (r • ·) μ s :=
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)⁻¹) * μ s := by
      rw [map_addHaar_smul μ hr, coe_smul, Pi.smul_apply, smul_eq_mul]

/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
@[simp]
/-
**MeasureTheory.Measure.addHaar_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：addHaar_smul (r : Real) (s : Set E) : μ (r • s) = ENNReal.ofReal (abs (r ^
 finrank Real E)) * μ s
参数：r : Real；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.preimage_smul_inv₀`：preimage_smul_inv₀ (ha : a != 0) (t : Set β) : (
fun x => a⁻¹ • x) ⁻¹' t = a • t
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_smul`：addHaar_preimage_smul {r : 
Real} (hr : r != 0) (s : Set E) : μ ((r • ·) ⁻¹' s) = ENNReal.ofReal (abs (r ^ f
inrank Real E)⁻¹) * μ s
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `Set.singleton_zero`：∀ {α : Type u_2} [inst : Zero α], {0} = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finrank_zero_iff`：Module.finrank_zero_iff [IsDomain R] [IsTorsion
Free R M] : finrank R M = 0 ↔ Subsingleton M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Subsingleton.eq_univ_of_nonempty`：eq_univ_of_nonempty {s : Set α} : s.No
nempty -> s = univ
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`.
-/
theorem addHaar_smul (r : ℝ) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, addHaar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs, ← singleton_zero]
  by_cases h : finrank ℝ E = 0
  · have : Subsingleton E := finrank_zero_iff.1 h
    simp only [h, one_mul, ENNReal.ofReal_one, abs_one, Subsingleton.eq_univ_of_nonempty hs,
      pow_zero, Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
  · have : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [h, zero_mul, ENNReal.ofReal_zero, abs_zero, Ne, not_false_iff,
      zero_pow, measure_singleton]
/-
**MeasureTheory.Measure.addHaar_smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：addHaar_smul_of_nonneg {r : Real} (hr : 0 <= r) (s : Set E) : μ (r • s) = 
ENNReal.ofReal (r ^ finrank Real E) * μ s
参数：hr : 0 <= r；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem addHaar_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (r ^ finrank ℝ E) * μ s := by
  rw [addHaar_smul, abs_pow, abs_of_nonneg hr]

@[simp]
/-
**MeasureTheory.Measure.addHaar_nnreal_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：addHaar_nnreal_smul (r : Real>=0) (s : Set E) : μ (r • s) = r ^ Module.fin
rank Real E * μ s
参数：r : Real>=0；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addHaar_nnreal_smul (r : ℝ≥0) (s : Set E) :
    μ (r • s) = r ^ Module.finrank ℝ E * μ s := by
  simp [NNReal.smul_def]

variable {μ} {s : Set E}

-- Note: We might want to rename this once we acquire the lemma corresponding to
-- `MeasurableSet.const_smul`
/-
**MeasureTheory.Measure.NullMeasurableSet.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.NullMeasurableSet`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : MeasurableSpace E] [BorelSpace E]   [FiniteDimensional ℝ E] {μ : Measu
reTheory.Measure E} [μ.IsAddHaarMeasure] {s : Set E},   MeasureTheory.NullMeasur
ableSet s μ → ∀ (r : ℝ), MeasureTheory.NullMeasurableSet (r • s) μ
参数：r : ℝ；r • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `MeasureTheory.nullMeasurableSet_singleton`：nullMeasurableSet_singleton (
x : α) : NullMeasurableSet {x} μ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSet.const_smul_of_ne_zero`：MeasurableSet.const_smul_of_ne_zero
 {G₀ α : Type*} [GroupWithZero G₀] [MulAction G₀ α] [MeasurableSpace α] [Measura
bleConstSMul G₀ α] {s : S…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.measure_symmDiff_eq_zero_iff`：measure_symmDiff_eq_zero_iff
 {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t
（共 33 条，此处仅展示前 30 条）
-/
theorem NullMeasurableSet.const_smul (hs : NullMeasurableSet s μ) (r : ℝ) :
    NullMeasurableSet (r • s) μ := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | hr := eq_or_ne r 0
  · simpa [zero_smul_set hs'] using! nullMeasurableSet_singleton _
  obtain ⟨t, ht, hst⟩ := hs
  refine ⟨_, ht.const_smul_of_ne_zero hr, ?_⟩
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  rw [← smul_set_symmDiff₀ hr, addHaar_smul μ, hst, mul_zero]

variable (μ)

@[simp]
/-
**MeasureTheory.Measure.addHaar_image_homothety** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：addHaar_image_homothety (x : E) (r : Real) (s : Set E) : μ (AffineMap.homo
thety x r '' s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
参数：x : E；r : Real；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_add_right`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {b
 : α}, (fun x => x + b) '' t = (fun x => x + -b) ⁻¹' t
· 使用定理 `MeasureTheory.measure_preimage_add_right`：∀ {G : Type u_1} [inst : Measu
rableSpace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure
 G)   [μ.IsAddRightInvariant] …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addHaar_image_homothety (x : E) (r : ℝ) (s : Set E) :
    μ (AffineMap.homothety x r '' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s :=
  calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]; rfl
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, addHaar_smul]

/-! We don't need to state `map_addHaar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/

/-
**MeasureTheory.Measure.addHaar_ball_center** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：addHaar_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
 [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) : μ (bal
l x r) = μ (ball (0 : E) r)
参数：μ : Measure E；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preimage_add_ball`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a
 b : E) (r : ℝ),   (fun x => b + x) ⁻¹' Metric.ball a r = Metric.ball (a - b) r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_preimage_add`：∀ {G : Type u_1} [inst : MeasurableS
pace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)   
[μ.IsAddLeftInvariant] (…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…

--- 原说明 ---
### Measure of balls
-/
theorem addHaar_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) : μ (ball x r) = μ (ball (0 : E) r) := by
  have : ball (0 : E) r = (x + ·) ⁻¹' ball x r := by simp [preimage_add_ball]
  rw [this, measure_preimage_add]
/-
**MeasureTheory.Measure.addHaar_real_ball_center** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：addHaar_real_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpa
ce E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) : μ
.real (ball x r) = μ.real (ball (0 : E) r)
参数：μ : Measure E；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_ball_center`：addHaar_ball_center {E : Type
*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Is
AddHaarMeasure μ] (x : E) (r : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addHaar_real_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ.real (ball x r) = μ.real (ball (0 : E) r) := by
  simp [measureReal_def, addHaar_ball_center]
/-
**MeasureTheory.Measure.addHaar_closedBall_center** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：addHaar_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSp
ace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Real) : 
μ (closedBall x r) = μ (closedBall (0 : E) r)
参数：μ : Measure E；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `preimage_add_closedBall`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup
 E] (a b : E) (r : ℝ),   (fun x => b + x) ⁻¹' Metric.closedBall a r = Metric.clo
sedBall (a - …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_preimage_add`：∀ {G : Type u_1} [inst : MeasurableS
pace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)   
[μ.IsAddLeftInvariant] (…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
-/
theorem addHaar_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (closedBall (0 : E) r) := by
  have : closedBall (0 : E) r = (x + ·) ⁻¹' closedBall x r := by simp [preimage_add_closedBall]
  rw [this, measure_preimage_add]
/-
**MeasureTheory.Measure.addHaar_real_closedBall_center** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：addHaar_real_closedBall_center {E : Type*} [NormedAddCommGroup E] [Measura
bleSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : Rea
l) : μ.real (closedBall x r) = μ.real (closedBall (0 : E) r)
参数：μ : Measure E；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_center`：addHaar_closedBall_cent
er {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Me
asure E) [IsAddHaarMeasure μ] (x : E)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addHaar_real_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ.real (closedBall x r) = μ.real (closedBall (0 : E) r) := by
  simp [measureReal_def, addHaar_closedBall_center]
/-
**MeasureTheory.Measure.addHaar_ball_mul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：addHaar_ball_mul_of_pos (x : E) {r : Real} (hr : 0 < r) (s : Real) : μ (ba
ll x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 s)
参数：x : E；hr : 0 < r；s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_ball`：smul_ball {c : 𝕜} (hc : c != 0) (x : E) (r : Real) : c • ball
 x r = ball (c • x) (‖c‖ * r)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaar_ball_center`：addHaar_ball_center {E : Type
*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Is
AddHaarMeasure μ] (x : E) (r : …
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
-/
theorem addHaar_ball_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) := by
  have : ball (0 : E) (r * s) = r • ball (0 : E) s := by
    simp only [_root_.smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_ball_center, abs_pow]
/-
**MeasureTheory.Measure.addHaar_ball_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：addHaar_ball_of_pos (x : E) {r : Real} (hr : 0 < r) : μ (ball x r) = ENNRe
al.ofReal (r ^ finrank Real E) * μ (ball 0 1)
参数：x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.addHaar_ball_mul_of_pos`：addHaar_ball_mul_of_pos (
x : E) {r : Real} (hr : 0 < r) (s : Real) : μ (ball x (r * s)) = ENNReal.ofReal 
(r ^ finrank Real E) * μ (ball 0 s)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem addHaar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul_of_pos μ x hr, mul_one]
/-
**MeasureTheory.Measure.addHaar_ball_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：addHaar_ball_mul [Nontrivial E] (x : E) {r : Real} (hr : 0 <= r) (s : Real
) : μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 s)
参数：x : E；hr : 0 <= r；s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Metric.ball_zero`：ball_zero : ball x 0 = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaar_ball_mul_of_pos`：addHaar_ball_mul_of_pos (
x : E) {r : Real} (hr : 0 < r) (s : Real) : μ (ball x (r * s)) = ENNReal.ofReal 
(r ^ finrank Real E) * μ (ball 0 s)
-/
theorem addHaar_ball_mul [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) := by
  rcases hr.eq_or_lt with (rfl | h)
  · simp only [zero_pow (finrank_pos (R := ℝ) (M := E)).ne', measure_empty, zero_mul,
      ENNReal.ofReal_zero, ball_zero]
  · exact addHaar_ball_mul_of_pos μ x h s
/-
**MeasureTheory.Measure.addHaar_ball** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：addHaar_ball [Nontrivial E] (x : E) {r : Real} (hr : 0 <= r) : μ (ball x r
) = ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 1)
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.addHaar_ball_mul`：addHaar_ball_mul [Nontrivial E] 
(x : E) {r : Real} (hr : 0 <= r) (s : Real) : μ (ball x (r * s)) = ENNReal.ofRea
l (r ^ finrank Real E) * μ (…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem addHaar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul μ x hr, mul_one]
/-
**MeasureTheory.Measure.addHaar_closedBall_mul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：addHaar_closedBall_mul_of_pos (x : E) {r : Real} (hr : 0 < r) (s : Real) :
 μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall 
0 s)
参数：x : E；hr : 0 < r；s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_closedBall'`：smul_closedBall' {c : 𝕜} (hc : c != 0) (x : E) (r : Re
al) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_center`：addHaar_closedBall_cent
er {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Me
asure E) [IsAddHaarMeasure μ] (x : E)…
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
-/
theorem addHaar_closedBall_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_closedBall_center, abs_pow]
/-
**MeasureTheory.Measure.addHaar_closedBall_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：addHaar_closedBall_mul (x : E) {r : Real} (hr : 0 <= r) {s : Real} (hs : 0
 <= s) : μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank Real E) * μ (clo
sedBall 0 s)
参数：x : E；hr : 0 <= r；hs : 0 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_closedBall`：smul_closedBall (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r
) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_center`：addHaar_closedBall_cent
er {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] (μ : Me
asure E) [IsAddHaarMeasure μ] (x : E)…
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
-/
theorem addHaar_closedBall_mul (x : E) {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (hs : 0 ≤ s) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, addHaar_smul, abs_of_nonneg hr, addHaar_closedBall_center, abs_pow]

/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `addHaar_closedBall`, which uses the measure of the open unit ball as a standard
form. -/
/-
**MeasureTheory.Measure.addHaar_closedBall'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：addHaar_closedBall' (x : E) {r : Real} (hr : 0 <= r) : μ (closedBall x r) 
= ENNReal.ofReal (r ^ finrank Real E) * μ (closedBall 0 1)
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_mul`：addHaar_closedBall_mul (x 
: E) {r : Real} (hr : 0 <= r) {s : Real} (hs : 0 <= s) : μ (closedBall x (r * s)
) = ENNReal.ofReal (r ^ finrank Re…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The measure of a closed ball can be expressed in terms of the measure of the clo
sed unit ball.
Use instead `addHaar_closedBall`, which uses the measure of the open unit ball a
s a standard
form.
-/
theorem addHaar_closedBall' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 1) := by
  rw [← addHaar_closedBall_mul μ x hr zero_le_one, mul_one]
/-
**MeasureTheory.Measure.addHaar_real_closedBall'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：addHaar_real_closedBall' (x : E) {r : Real} (hr : 0 <= r) : μ.real (closed
Ball x r) = r ^ finrank Real E * μ.real (closedBall 0 1)
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall'`：addHaar_closedBall' (x : E) {
r : Real} (hr : 0 <= r) : μ (closedBall x r) = ENNReal.ofReal (r ^ finrank Real 
E) * μ (closedBall 0 1)
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem addHaar_real_closedBall' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ.real (closedBall x r) = r ^ finrank ℝ E * μ.real (closedBall 0 1) := by
  simp only [measureReal_def, addHaar_closedBall' μ x hr, ENNReal.toReal_mul, mul_eq_mul_right_iff,
    ENNReal.toReal_ofReal_eq_iff]
  left
  positivity
/-
**MeasureTheory.Measure.addHaar_unitClosedBall_eq_addHaar_unitBall** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_unitClosedBall_eq_addHaar_unitBall : μ (closedBall (0 : E) 1) = μ 
(ball 0 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ENNReal.Tendsto.mul`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       F
ilter.Ten…
· 使用定理 `ENNReal.tendsto_ofReal`：tendsto_ofReal {f : Filter α} {m : α -> Real} {a
 : Real} (h : Tendsto m f (𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 
(ENNReal.ofR…
· 使用定理 `Filter.Tendsto.pow`：Filter.Tendsto.pow {l : Filter α} {f : α -> M} {x : 
M} (hf : Tendsto f l (𝓝 x)) (n : Nat) : Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 48 条，此处仅展示前 30 条）
-/
theorem addHaar_unitClosedBall_eq_addHaar_unitBall :
    μ (closedBall (0 : E) 1) = μ (ball 0 1) := by
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  have A : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall (0 : E) 1)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ finrank ℝ E) * μ (closedBall (0 : E) 1))) := by
    refine ENNReal.Tendsto.mul ?_ (by simp) tendsto_const_nhds (by simp)
    exact ENNReal.tendsto_ofReal ((tendsto_id'.2 nhdsWithin_le_nhds).pow _)
  simp only [one_pow, one_mul, ENNReal.ofReal_one] at A
  refine le_of_tendsto A ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  rw [← addHaar_closedBall' μ (0 : E) hr.1.le]
  exact measure_mono (closedBall_subset_ball hr.2)
/-
**MeasureTheory.Measure.addHaar_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：addHaar_closedBall (x : E) {r : Real} (hr : 0 <= r) : μ (closedBall x r) =
 ENNReal.ofReal (r ^ finrank Real E) * μ (ball 0 1)
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall'`：addHaar_closedBall' (x : E) {
r : Real} (hr : 0 <= r) : μ (closedBall x r) = ENNReal.ofReal (r ^ finrank Real 
E) * μ (closedBall 0 1)
· 使用定理 `MeasureTheory.Measure.addHaar_unitClosedBall_eq_addHaar_unitBall`：addHaa
r_unitClosedBall_eq_addHaar_unitBall : μ (closedBall (0 : E) 1) = μ (ball 0 1)
-/
theorem addHaar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [addHaar_closedBall' μ x hr, addHaar_unitClosedBall_eq_addHaar_unitBall]
/-
**MeasureTheory.Measure.addHaar_real_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：addHaar_real_closedBall (x : E) {r : Real} (hr : 0 <= r) : μ.real (closedB
all x r) = r ^ finrank Real E * μ.real (ball 0 1)
参数：x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_real_closedBall'`：addHaar_real_closedBall'
 (x : E) {r : Real} (hr : 0 <= r) : μ.real (closedBall x r) = r ^ finrank Real E
 * μ.real (closedBall 0 1)
· 使用定理 `MeasureTheory.Measure.addHaar_unitClosedBall_eq_addHaar_unitBall`：addHaa
r_unitClosedBall_eq_addHaar_unitBall : μ (closedBall (0 : E) 1) = μ (ball 0 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addHaar_real_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ.real (closedBall x r) = r ^ finrank ℝ E * μ.real (ball 0 1) := by
  simp [addHaar_real_closedBall' μ x hr, measureReal_def,
    addHaar_unitClosedBall_eq_addHaar_unitBall]
/-
**MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_closedBall_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (
closedBall x r) = μ (ball x r)
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall`：addHaar_closedBall (x : E) {r 
: Real} (hr : 0 <= r) : μ (closedBall x r) = ENNReal.ofReal (r ^ finrank Real E)
 * μ (ball 0 1)
· 使用定理 `MeasureTheory.Measure.addHaar_ball`：addHaar_ball [Nontrivial E] (x : E) 
{r : Real} (hr : 0 <= r) : μ (ball x r) = ENNReal.ofReal (r ^ finrank Real E) * 
μ (ball 0 1)
-/
theorem addHaar_closedBall_eq_addHaar_ball [Nontrivial E] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (ball x r) := by
  by_cases! h : r < 0
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
  rw [addHaar_closedBall μ x h, addHaar_ball μ x h]
/-
**MeasureTheory.Measure.addHaar_real_closedBall_eq_addHaar_real_ball** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_real_closedBall_eq_addHaar_real_ball [Nontrivial E] (x : E) (r : R
eal) : μ.real (closedBall x r) = μ.real (ball x r)
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball`：addHaar_closed
Ball_eq_addHaar_ball [Nontrivial E] (x : E) (r : Real) : μ (closedBall x r) = μ 
(ball x r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addHaar_real_closedBall_eq_addHaar_real_ball [Nontrivial E] (x : E) (r : ℝ) :
    μ.real (closedBall x r) = μ.real (ball x r) := by
  simp [measureReal_def, addHaar_closedBall_eq_addHaar_ball μ x r]
/-
**MeasureTheory.Measure.addHaar_sphere_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：addHaar_sphere_of_ne_zero (x : E) {r : Real} (hr : r != 0) : μ (sphere x r
) = 0
参数：x : E；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedBall_sdiff_ball`：closedBall_sdiff_ball : closedBall x ε \ b
all x ε = sphere x ε
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `measurableSet_ball`：measurableSet_ball : MeasurableSet (Metric.ball x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_ball_lt_top`：measure_ball_lt_top [PseudoMetricSpac
e α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {x : α} {r : 
Real} : μ (Metric.ball …
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.addHaar_ball_of_pos`：addHaar_ball_of_pos (x : E) {
r : Real} (hr : 0 < r) : μ (ball x r) = ENNReal.ofReal (r ^ finrank Real E) * μ 
(ball 0 1)
· 使用定理 `MeasureTheory.Measure.addHaar_closedBall`：addHaar_closedBall (x : E) {r 
: Real} (hr : 0 <= r) : μ (closedBall x r) = ENNReal.ofReal (r ^ finrank Real E)
 * μ (ball 0 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem addHaar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (sphere x r) = 0 := by
  rcases hr.lt_or_gt with (h | h)
  · simp only [empty_sdiff, measure_empty, ← closedBall_sdiff_ball, closedBall_eq_empty.2 h]
  · rw [← closedBall_sdiff_ball,
      measure_sdiff ball_subset_closedBall measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne,
      addHaar_ball_of_pos μ _ h, addHaar_closedBall μ _ h.le, tsub_self]
/-
**MeasureTheory.Measure.addHaar_sphere** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：addHaar_sphere [Nontrivial E] (x : E) (r : Real) : μ (sphere x r) = 0
参数：x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.sphere_zero`：∀ {γ : Type w} [inst : MetricSpace γ] {x : γ}, Metri
c.sphere x 0 = {x}
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass`：∀ {G : Type u
_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace 
G]   [IsTopologicalAddGroup G] [BorelSpace G] […
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.addHaar_sphere_of_ne_zero`：addHaar_sphere_of_ne_ze
ro (x : E) {r : Real} (hr : r != 0) : μ (sphere x r) = 0
-/
theorem addHaar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
  · exact addHaar_sphere_of_ne_zero μ x h
/-
**MeasureTheory.Measure.addHaar_singleton_add_smul_div_singleton_add_smul** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：addHaar_singleton_add_smul_div_singleton_add_smul {r : Real} (hr : r != 0)
 (x y : E) (s t : Set E) : μ ({x} + r • s) / μ ({y} + r • t) = μ s / μ t
参数：hr : r != 0；x y : E；s t : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `MeasureTheory.measure_preimage_add`：∀ {G : Type u_1} [inst : MeasurableS
pace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)   
[μ.IsAddLeftInvariant] (…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 41 条，此处仅展示前 30 条）
-/
theorem addHaar_singleton_add_smul_div_singleton_add_smul {r : ℝ} (hr : r ≠ 0) (x y : E)
    (s t : Set E) : μ ({x} + r • s) / μ ({y} + r • t) = μ s / μ t :=
  calc
    μ ({x} + r • s) / μ ({y} + r • t) = ENNReal.ofReal (|r| ^ finrank ℝ E) * μ s *
        (ENNReal.ofReal (|r| ^ finrank ℝ E) * μ t)⁻¹ := by
      simp only [div_eq_mul_inv, addHaar_smul, image_add_left, measure_preimage_add, abs_pow,
        singleton_add]
    _ = ENNReal.ofReal (|r| ^ finrank ℝ E) * (ENNReal.ofReal (|r| ^ finrank ℝ E))⁻¹ *
          (μ s * (μ t)⁻¹) := by
      rw [ENNReal.mul_inv]
      · ring
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne, true_or]
      · simp only [ENNReal.ofReal_ne_top, true_or, Ne, not_false_iff]
    _ = μ s / μ t := by
      rw [ENNReal.mul_inv_cancel, one_mul, div_eq_mul_inv]
      · simp only [pow_pos (abs_pos.mpr hr), ENNReal.ofReal_eq_zero, not_le, Ne]
      · simp only [ENNReal.ofReal_ne_top, Ne, not_false_iff]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isUnifLocDoublingMeasureOfIsAddHaarMeasure :
    IsUnifLocDoublingMeasure μ := by
  refine ⟨⟨(2 : ℝ≥0) ^ finrank ℝ E, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with r hr x
  rw [addHaar_closedBall_mul μ x zero_le_two (le_of_lt hr), addHaar_closedBall_center μ x,
    ENNReal.ofReal, Real.toNNReal_pow zero_le_two]
  simp only [Real.toNNReal_ofNat, le_refl]

section

/-!
### The Lebesgue measure associated to an alternating map
-/

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-
**MeasureTheory.Measure.addHaar_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：addHaar_parallelepiped (b : Basis ι Real G) (v : ι -> G) : b.addHaar (para
llelepiped v) = ENNReal.ofReal |b.det v|
参数：b : Basis ι Real G；v : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_parallelepiped`：image_parallelepiped (f : E ->ₗ[Real] F) (v : ι ->
 E) : f '' parallelepiped v = parallelepiped (f ∘ v)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `MeasureTheory.Measure.addHaar_image_linearMap`：addHaar_image_linearMap (
f : E ->ₗ[Real] E) (s : Set E) : μ (f '' s) = ENNReal.ofReal |LinearMap.det f| *
 μ s
· 使用定理 `isAddHaarMeasure_basis_addHaar`：∀ {ι : Type u_1} {E : Type u_3} [inst : 
Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 
: MeasurableSpace E]…
· 使用定理 `Module.Basis.addHaar_self`：addHaar_self (b : Basis ι Real E) : b.addHaar
 (_root_.parallelepiped b) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `Module.Basis.toMatrix_eq_toMatrix_constr`：toMatrix_eq_toMatrix_constr [F
intype ι] [DecidableEq ι] (v : ι -> M) : e.toMatrix v = LinearMap.toMatrix e e (
e.constr Nat v)
· 使用定理 `Module.Basis.det_apply`：det_apply (v : ι -> M) : e.det v = Matrix.det (e
.toMatrix v)
-/
theorem addHaar_parallelepiped (b : Basis ι ℝ G) (v : ι → G) :
    b.addHaar (parallelepiped v) = ENNReal.ofReal |b.det v| := by
  have : FiniteDimensional ℝ G := b.finiteDimensional_of_finite
  have A : parallelepiped v = b.constr ℕ v '' parallelepiped b := by
    rw [image_parallelepiped]
    exact congr_arg _ <| funext fun i ↦ (b.constr_basis ℕ v i).symm
  rw [A, addHaar_image_linearMap, b.addHaar_self, mul_one, ← LinearMap.det_toMatrix b,
    ← Basis.toMatrix_eq_toMatrix_constr, Basis.det_apply]

variable [FiniteDimensional ℝ G] {n : ℕ} [_i : Fact (finrank ℝ G = n)]

/-- The Lebesgue measure associated to an alternating map. It gives measure `|ω v|` to the
parallelepiped spanned by the vectors `v₁, ..., vₙ`. Note that it is not always a Haar measure,
as it can be zero, but it is always locally finite and translation invariant. -/
noncomputable irreducible_def _root_.AlternatingMap.measure (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) :
    Measure G :=
  ‖ω (finBasisOfFinrankEq ℝ G _i.out)‖₊ • (finBasisOfFinrankEq ℝ G _i.out).addHaar

/-
**MeasureTheory.Measure._root_.AlternatingMap.measure_parallelepiped** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlternatingMap.measure_parallelepiped (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ)
    (v : Fin n → G) : ω.measure (parallelepiped v) = ENNReal.ofReal |ω v| := by
  conv_rhs => rw [ω.eq_smul_basis_det (finBasisOfFinrankEq ℝ G _i.out)]
  simp only [addHaar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    ← Real.enorm_eq_ofReal_abs, enorm]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) : IsAddLeftInvariant ω.measure := by
  rw [AlternatingMap.measure]; infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) : IsLocallyFiniteMeasure ω.measure := by
  rw [AlternatingMap.measure]; infer_instance

end

/-!
### Density points

Besicovitch covering theorem ensures that, for any locally finite measure on a finite-dimensional
real vector space, almost every point of a set `s` is a density point, i.e.,
`μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `1` as `r` tends to `0`
(see `Besicovitch.ae_tendsto_measure_inter_div`).
When `μ` is a Haar measure, one can deduce the same property for any rescaling sequence of sets,
of the form `{x} + r • t` where `t` is a set with positive finite measure, instead of the sequence
of closed balls.

We argue first for the dual property, i.e., if `s` has density `0` at `x`, then
`μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)` tends to `0`. First when `t` is contained in the ball
of radius `1`, in `tendsto_addHaar_inter_smul_zero_of_density_zero_aux1`,
(by arguing by inclusion). Then when `t` is bounded, reducing to the previous one by rescaling, in
`tendsto_addHaar_inter_smul_zero_of_density_zero_aux2`.
Then for a general set `t`, by cutting it into a bounded part and a part with small measure, in
`tendsto_addHaar_inter_smul_zero_of_density_zero`.
Going to the complement, one obtains the desired property at points of density `1`, first when
`s` is measurable in `tendsto_addHaar_inter_smul_one_of_density_one_aux`, and then without this
assumption in `tendsto_addHaar_inter_smul_one_of_density_one` by applying the previous lemma to
the measurable hull `toMeasurable μ s`
-/

/-
**MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_aux1** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E) (
h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) 
(𝓝 0)) (t : Set E) (u : Set E) (h'u : μ u != 0) (t_bound : t subseteq closedBall
 0 1) : Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • u)) (𝓝
[>] 0) (𝓝 0)
参数：s : Set E；x : E；h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedB
all x r)) (𝓝[>] 0) (𝓝 0)；t : Set E；u : Set E；h'u : μ u != 0；t_bound : t subseteq
 closedBall 0 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Set.instAddLeftMono`：∀ {α : Type u_2} [inst : Add α], AddLeftMono (Set α
)
· 使用定理 `Set.instAddRightMono`：∀ {α : Type u_2} [inst : Add α], AddRightMono (Set
 α)
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `Set.singleton_vadd`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {t
 : Set β} {a : α}, {a} +ᵥ t = a +ᵥ t
· 使用定理 `affinity_unitClosedBall`：affinity_unitClosedBall {r : Real} (hr : 0 <= r
) (x : E) : x +ᵥ r • closedBall (0 : E) 1 = closedBall x r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_closedBall`：smul_closedBall (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r
) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
### Density points

Besicovitch covering theorem ensures that, for any locally finite measure on a f
inite-dimensional
real vector space, almost every point of a set `s` is a density point, i.e.,
`μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `1` as `r` tends to `0`
(see `Besicovitch.ae_tendsto_measure_inter_div`).
When `μ` is a Haar measure, one can deduce the same property for any rescaling s
equence of sets,
of the form `{x} + r • t` where `t` is a set with positive finite measure, inste
ad of the sequence
of closed balls.

We argue first for the dual property, i.e., if `s` has density `0` at `x`, then
`μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)` tends to `0`. First when `t` is contai
ned in the ball
of radius `1`, in `tendsto_addHaar_inter_smul_zero_of_density_zero_aux1`,
(by arguing by inclusion). Then when `t` is bounded, reducing to the previous on
e by rescaling, in
`tendsto_addHaar_inter_smul_zero_of_density_zero_aux2`.
Then for a general set `t`, by cutting it into a bounded part and a part with sm
all measure, in
`tendsto_addHaar_inter_smul_zero_of_density_zero`.
Going to the complement, one obtains the desired property at points of density `
1`, first when
`s` is measurable in `tendsto_addHaar_inter_smul_one_of_density_one_aux`, and th
en without this
assumption in `tendsto_addHaar_inter_smul_one_of_density_one` by applying the pr
evious lemma to
the measurable hull `toMeasurable μ s`
-/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u ≠ 0) (t_bound : t ⊆ closedBall 0 1) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  have A : Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    apply
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
        (Eventually.of_forall fun b => zero_le)
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    grw [t_bound]
    rw [← vadd_eq_add, singleton_vadd, affinity_unitClosedBall rpos.le]
  have B :
    Tendsto (fun r : ℝ => μ (closedBall x r) / μ ({x} + r • u)) (𝓝[>] 0)
      (𝓝 (μ (closedBall x 1) / μ ({x} + u))) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    have : closedBall x r = {x} + r • closedBall (0 : E) 1 := by
      simp only [_root_.smul_closedBall, Real.norm_of_nonneg rpos.le, zero_le_one, add_zero,
        mul_one, singleton_add_closedBall, smul_zero]
    simp only [this, addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne']
    simp only [addHaar_closedBall_center, image_add_left, measure_preimage_add, singleton_add]
  have C : Tendsto (fun r : ℝ =>
        μ (s ∩ ({x} + r • t)) / μ (closedBall x r) * (μ (closedBall x r) / μ ({x} + r • u)))
      (𝓝[>] 0) (𝓝 (0 * (μ (closedBall x 1) / μ ({x} + u)))) := by
    apply ENNReal.Tendsto.mul A _ B (Or.inr ENNReal.zero_ne_top)
    simp [ENNReal.div_eq_top, h'u, measure_closedBall_lt_top.ne]
  simp only [zero_mul] at C
  apply C.congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  calc μ (s ∩ ({x} + r • t)) / μ (closedBall x r) * (μ (closedBall x r) / μ ({x} + r • u))
    _ = μ (closedBall x r) * (μ (closedBall x r))⁻¹ *
        (μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) := by simp only [div_eq_mul_inv]; ring
    _ = μ (s ∩ ({x} + r • t)) / μ ({x} + r • u) := by
      rw [ENNReal.mul_inv_cancel (measure_closedBall_pos μ x rpos).ne'
          measure_closedBall_lt_top.ne,
        one_mul]
/-
**MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_aux2** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 (s : Set E) (x : E) (
h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) 
(𝓝 0)) (t : Set E) (u : Set E) (h'u : μ u != 0) (R : Real) (Rpos : 0 < R) (t_bou
nd : t subseteq closedBall 0 R) : Tendsto (fun r : Real => μ (s inter ({x} + r •
 t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0)
参数：s : Set E；x : E；h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedB
all x r)) (𝓝[>] 0) (𝓝 0)；t : Set E；u : Set E；h'u : μ u != 0；R : Real；Rpos : 0 < 
R；t_bound : t subseteq closedBall 0 R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero_au
x1`：tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 (s : Set E) (x : E) (h 
: Tendsto (fun r => μ (s inter closedBall x r) / μ (closedBall x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
· 使用定理 `smul_closedBall`：smul_closedBall (c : 𝕜) (x : E) {r : Real} (hr : 0 <= r
) : c • closedBall x r = closedBall (c • x) (‖c‖ * r)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
（共 47 条，此处仅展示前 30 条）
-/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (u : Set E) (h'u : μ u ≠ 0) (R : ℝ) (Rpos : 0 < R) (t_bound : t ⊆ closedBall 0 R) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • u)) (𝓝[>] 0) (𝓝 0) := by
  set t' := R⁻¹ • t with ht'
  set u' := R⁻¹ • u with hu'
  have A : Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t')) / μ ({x} + r • u')) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_addHaar_inter_smul_zero_of_density_zero_aux1 μ s x h t' u'
    · simp only [u', h'u, (pow_pos Rpos _).ne', abs_nonpos_iff, addHaar_smul, not_false_iff,
        ENNReal.ofReal_eq_zero, inv_eq_zero, inv_pow, Ne, or_self_iff, mul_eq_zero]
    · refine (smul_set_mono t_bound).trans_eq ?_
      rw [smul_closedBall _ _ Rpos.le, smul_zero, Real.norm_of_nonneg (inv_nonneg.2 Rpos.le),
        inv_mul_cancel₀ Rpos.ne']
  have B : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] (R * 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (tendsto_const_nhds.mul tendsto_id).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin]
      intro r rpos
      rw [mul_zero]
      exact mul_pos Rpos rpos
  rw [mul_zero] at B
  apply (A.comp B).congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r -
  have T : (R * r) • t' = r • t := by
    rw [mul_comm, ht', smul_smul, mul_assoc, mul_inv_cancel₀ Rpos.ne', mul_one]
  have U : (R * r) • u' = r • u := by
    rw [mul_comm, hu', smul_smul, mul_assoc, mul_inv_cancel₀ Rpos.ne', mul_one]
  dsimp
  rw [T, U]

/-- Consider a point `x` at which a set `s` has density zero, with respect to closed balls. Then it
also has density zero with respect to any measurable set `t`: the proportion of points in `s`
belonging to a rescaled copy `{x} + r • t` of `t` tends to zero as `r` tends to zero. -/
/-
**MeasureTheory.Measure.tendsto_addHaar_inter_smul_zero_of_density_zero** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：tendsto_addHaar_inter_smul_zero_of_density_zero (s : Set E) (x : E) (h : T
endsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)
) (t : Set E) (ht : MeasurableSet t) (h''t : μ t != ∞) : Tendsto (fun r : Real =
> μ (s inter ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0)
参数：s : Set E；x : E；h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedB
all x r)) (𝓝[>] 0) (𝓝 0)；t : Set E；ht : MeasurableSet t；h''t : μ t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.not_lt_zero`：not_lt_zero : ¬a < 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_add`：∀ {α : Type u_2} [inst : Add α] {t : Set α} {a : α}, 
{a} + t = (fun x => a + x) '' t
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `MeasureTheory.measure_preimage_add`：∀ {G : Type u_1} [inst : MeasurableS
pace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)   
[μ.IsAddLeftInvariant] (…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.addHaar_smul`：addHaar_smul (r : Real) (s : Set E) 
: μ (r • s) = ENNReal.ofReal (abs (r ^ finrank Real E)) * μ s
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a point `x` at which a set `s` has density zero, with respect to closed
 balls. Then it
also has density zero with respect to any measurable set `t`: the proportion of 
points in `s`
belonging to a rescaled copy `{x} + r • t` of `t` tends to zero as `r` tends to 
zero.
-/
theorem tendsto_addHaar_inter_smul_zero_of_density_zero (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0)) (t : Set E)
    (ht : MeasurableSet t) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a' ha' => (ENNReal.not_lt_zero ha').elim, fun ε (εpos : 0 < ε) => ?_⟩
  rcases eq_or_ne (μ t) 0 with (h't | h't)
  · filter_upwards with r
    suffices H : μ (s ∩ ({x} + r • t)) = 0 by
      rw [H]; simpa only [ENNReal.zero_div] using εpos
    rw [← nonpos_iff_eq_zero]
    calc
      μ (s ∩ ({x} + r • t)) ≤ μ ({x} + r • t) := measure_mono inter_subset_right
      _ = 0 := by
        simp only [h't, addHaar_smul, image_add_left, measure_preimage_add, singleton_add,
          mul_zero]
  obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ μ (t \ closedBall 0 n) < ε / 2 * μ t := by
    have A :
      Tendsto (fun n : ℕ => μ (t \ closedBall 0 n)) atTop
        (𝓝 (μ (⋂ n : ℕ, t \ closedBall 0 n))) := by
      have N : ∃ n : ℕ, μ (t \ closedBall 0 n) ≠ ∞ :=
        ⟨0, ((measure_mono sdiff_subset).trans_lt h''t.lt_top).ne⟩
      refine tendsto_measure_iInter_atTop
        (fun n ↦ (ht.diff measurableSet_closedBall).nullMeasurableSet) (fun m n hmn ↦ ?_) N
      exact sdiff_subset_sdiff Subset.rfl (by gcongr)
    have : ⋂ n : ℕ, t \ closedBall 0 n = ∅ := by
      simp_rw [sdiff_eq, ← inter_iInter, iInter_eq_compl_iUnion_compl, compl_compl,
        iUnion_closedBall_nat, compl_univ, inter_empty]
    simp only [this, measure_empty] at A
    have I : 0 < ε / 2 * μ t := ENNReal.mul_pos (ENNReal.half_pos εpos.ne').ne' h't
    exact (Eventually.and (Ioi_mem_atTop 0) ((tendsto_order.1 A).2 _ I)).exists
  have L :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) / μ ({x} + r • t)) (𝓝[>] 0)
      (𝓝 0) :=
    tendsto_addHaar_inter_smul_zero_of_density_zero_aux2 μ s x h _ t h't n (Nat.cast_pos.2 npos)
      inter_subset_right
  filter_upwards [(tendsto_order.1 L).2 _ (ENNReal.half_pos εpos.ne'), self_mem_nhdsWithin]
  rintro r hr (rpos : 0 < r)
  have I :
    μ (s ∩ ({x} + r • t)) ≤
      μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n)) :=
    calc
      μ (s ∩ ({x} + r • t)) =
          μ (s ∩ ({x} + r • (t ∩ closedBall 0 n)) ∪ s ∩ ({x} + r • (t \ closedBall 0 n))) := by
        rw [← inter_union_distrib_left, ← add_union, ← smul_set_union, inter_union_sdiff]
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ (s ∩ ({x} + r • (t \ closedBall 0 n))) :=
        measure_union_le _ _
      _ ≤ μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n)) := by
        gcongr; apply inter_subset_right
  calc
    μ (s ∩ ({x} + r • t)) / μ ({x} + r • t) ≤
        (μ (s ∩ ({x} + r • (t ∩ closedBall 0 n))) + μ ({x} + r • (t \ closedBall 0 n))) /
          μ ({x} + r • t) := by gcongr
    _ < ε / 2 + ε / 2 := by
      rw [ENNReal.add_div]
      apply ENNReal.add_lt_add hr _
      rwa [addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne',
        ENNReal.div_lt_iff (Or.inl h't) (Or.inl h''t)]
    _ = ε := ENNReal.add_halves _
/-
**MeasureTheory.Measure.tendsto_addHaar_inter_smul_one_of_density_one_aux** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：tendsto_addHaar_inter_smul_one_of_density_one_aux (s : Set E) (hs : Measur
ableSet s) (x : E) (h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closed
Ball x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E) (ht : MeasurableSet t) (h't : μ t != 0) (
h''t : μ t != ∞) : Tendsto (fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} +
 r • t)) (𝓝[>] 0) (𝓝 1)
参数：s : Set E；hs : MeasurableSet s；x : E；h : Tendsto (fun r => μ (s inter closedB
all x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)；t : Set E；ht : MeasurableSet t；h't
 : μ t != 0；h''t : μ t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.sub_mul`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) 
* c = a * c - b * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENNReal.eq_sub_of_add_eq'`：∀ {a b c : ENNReal}, b ≠ ⊤ → a + c = b → a = 
b - c
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Metric.measure_closedBall_pos`：measure_closedBall_pos (x : X) {r : Real}
 (hr : 0 < r) : 0 < μ (closedBall x r)
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.measure_closedBall_lt_top`：measure_closedBall_lt_top [Pseu
doMetricSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {
x : α} {r : Real} : μ (Metric…
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ENNReal.Tendsto.sub`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     Filter.Tendsto mb f (nh
ds b) → a…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
（共 65 条，此处仅展示前 30 条）
-/
theorem tendsto_addHaar_inter_smul_one_of_density_one_aux (s : Set E) (hs : MeasurableSet s)
    (x : E) (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1))
    (t : Set E) (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have I : ∀ u v, μ u ≠ 0 → μ u ≠ ∞ → MeasurableSet v →
    μ u / μ u - μ (vᶜ ∩ u) / μ u = μ (v ∩ u) / μ u := by
    intro u v uzero utop vmeas
    simp_rw [div_eq_mul_inv]
    rw [← ENNReal.sub_mul]; swap
    · simp only [uzero, ENNReal.inv_eq_top, imp_true_iff, Ne, not_false_iff]
    congr 1
    rw [inter_comm _ u, inter_comm _ u, eq_comm]
    exact ENNReal.eq_sub_of_add_eq' utop (measure_inter_add_sdiff u vmeas)
  have L : Tendsto (fun r => μ (sᶜ ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    have A : Tendsto (fun r => μ (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_const_nhds.congr' _
      filter_upwards [self_mem_nhdsWithin]
      intro r hr
      rw [div_eq_mul_inv, ENNReal.mul_inv_cancel]
      · exact (measure_closedBall_pos μ _ hr).ne'
      · exact measure_closedBall_lt_top.ne
    have B := ENNReal.Tendsto.sub A h (Or.inl ENNReal.one_ne_top)
    simp only [tsub_self] at B
    apply B.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    convert!
      I (closedBall x r) sᶜ (measure_closedBall_pos μ _ rpos).ne' measure_closedBall_lt_top.ne
        hs.compl
    rw [compl_compl]
  have L' : Tendsto (fun r : ℝ => μ (sᶜ ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_addHaar_inter_smul_zero_of_density_zero μ sᶜ x L t ht h''t
  have L'' : Tendsto (fun r : ℝ => μ ({x} + r • t) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
    apply tendsto_const_nhds.congr' _
    filter_upwards [self_mem_nhdsWithin]
    rintro r (rpos : 0 < r)
    rw [addHaar_singleton_add_smul_div_singleton_add_smul μ rpos.ne', ENNReal.div_self h't h''t]
  have := ENNReal.Tendsto.sub L'' L' (Or.inl ENNReal.one_ne_top)
  simp only [tsub_zero] at this
  apply this.congr' _
  filter_upwards [self_mem_nhdsWithin]
  rintro r (rpos : 0 < r)
  refine I ({x} + r • t) s ?_ ?_ hs
  · simp only [h't, abs_of_nonneg rpos.le, pow_pos rpos, addHaar_smul, image_add_left,
      ENNReal.ofReal_eq_zero, not_le, or_false, Ne, measure_preimage_add, abs_pow,
      singleton_add, mul_eq_zero]
  · simp [h''t, ENNReal.ofReal_ne_top, addHaar_smul, image_add_left, ENNReal.mul_eq_top,
      Ne, measure_preimage_add, singleton_add]

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` has also density one at `x` with respect to any
measurable set `t`: the proportion of points in `s` belonging to a rescaled copy `{x} + r • t`
of `t` tends to one as `r` tends to zero. -/
/-
**MeasureTheory.Measure.tendsto_addHaar_inter_smul_one_of_density_one** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：tendsto_addHaar_inter_smul_one_of_density_one (s : Set E) (x : E) (h : Ten
dsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) 
(t : Set E) (ht : MeasurableSet t) (h't : μ t != 0) (h''t : μ t != ∞) : Tendsto 
(fun r : Real => μ (s inter ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1)
参数：s : Set E；x : E；h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedB
all x r)) (𝓝[>] 0) (𝓝 1)；t : Set E；ht : MeasurableSet t；h't : μ t != 0；h''t : μ 
t != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.tendsto_addHaar_inter_smul_one_of_density_one_aux`
：tendsto_addHaar_inter_smul_one_of_density_one_aux (s : Set E) (hs : MeasurableS
et s) (x : E) (h : Tendsto (fun r => μ (s inter closedBall x …
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite`：measure_toM
easurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s) (t : S
et α) : μ (toMeasurable μ t inter s) = μ (t inter…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a point `x` at which a set `s` has density one, with respect to closed 
balls (i.e.,
a Lebesgue density point of `s`). Then `s` has also density one at `x` with resp
ect to any
measurable set `t`: the proportion of points in `s` belonging to a rescaled copy
 `{x} + r • t`
of `t` tends to one as `r` tends to zero.
-/
theorem tendsto_addHaar_inter_smul_one_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) (h''t : μ t ≠ ∞) :
    Tendsto (fun r : ℝ => μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)) (𝓝[>] 0) (𝓝 1) := by
  have : Tendsto (fun r : ℝ => μ (toMeasurable μ s ∩ ({x} + r • t)) / μ ({x} + r • t))
    (𝓝[>] 0) (𝓝 1) := by
    apply
      tendsto_addHaar_inter_smul_one_of_density_one_aux μ _ (measurableSet_toMeasurable _ _) _ _
        t ht h't h''t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h tendsto_const_nhds
    · refine Eventually.of_forall fun r ↦ ?_
      gcongr
      apply subset_toMeasurable
    · filter_upwards [self_mem_nhdsWithin]
      rintro r -
      apply ENNReal.div_le_of_le_mul
      rw [one_mul]
      exact measure_mono inter_subset_right
  refine this.congr fun r => ?_
  congr 1
  apply measure_toMeasurable_inter_of_sFinite
  simp only [image_add_left, singleton_add]
  apply (continuous_const_add (-x)).measurable (ht.const_smul₀ r)

/-- Consider a point `x` at which a set `s` has density one, with respect to closed balls (i.e.,
a Lebesgue density point of `s`). Then `s` intersects the rescaled copies `{x} + r • t` of a given
set `t` with positive measure, for any small enough `r`. -/
/-
**MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：eventually_nonempty_inter_smul_of_density_one (s : Set E) (x : E) (h : Ten
dsto (fun r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) 
(t : Set E) (ht : MeasurableSet t) (h't : μ t != 0) : forallᶠ r in 𝓝[>] (0 : Rea
l), (s inter ({x} + r • t)).Nonempty
参数：s : Set E；x : E；h : Tendsto (fun r => μ (s inter closedBall x r) / μ (closedB
all x r)) (𝓝[>] 0) (𝓝 1)；t : Set E；ht : MeasurableSet t；h't : μ t != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.exists_subset_measure_lt_top`：exists_subset_measur
e_lt_top [SigmaFinite μ] {r : Real>=0∞} (hs : MeasurableSet s) (h's : r < μ s) :
 exists t, MeasurableSet t ∧ t subseteq …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.Measure.tendsto_addHaar_inter_smul_one_of_density_one`：ten
dsto_addHaar_inter_smul_one_of_density_one (s : Set E) (x : E) (h : Tendsto (fun
 r => μ (s inter closedBall x r) / μ (closedBall x r)) (𝓝…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a point `x` at which a set `s` has density one, with respect to closed 
balls (i.e.,
a Lebesgue density point of `s`). Then `s` intersects the rescaled copies `{x} +
 r • t` of a given
set `t` with positive measure, for any small enough `r`.
-/
theorem eventually_nonempty_inter_smul_of_density_one (s : Set E) (x : E)
    (h : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 1)) (t : Set E)
    (ht : MeasurableSet t) (h't : μ t ≠ 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • t)).Nonempty := by
  obtain ⟨t', t'_meas, t't, t'pos, t'top⟩ : ∃ t', MeasurableSet t' ∧ t' ⊆ t ∧ 0 < μ t' ∧ μ t' < ⊤ :=
    exists_subset_measure_lt_top ht h't.bot_lt
  filter_upwards [(tendsto_order.1
          (tendsto_addHaar_inter_smul_one_of_density_one μ s x h t' t'_meas t'pos.ne' t'top.ne)).1
      0 zero_lt_one]
  intro r hr
  have : μ (s ∩ ({x} + r • t')) ≠ 0 := fun h' => by
    simp only [ENNReal.not_lt_zero, ENNReal.zero_div, h'] at hr
  have : (s ∩ ({x} + r • t')).Nonempty := nonempty_of_measure_ne_zero this
  apply this.mono (inter_subset_inter Subset.rfl _)
  exact add_subset_add Subset.rfl (smul_set_mono t't)

end Measure

end MeasureTheory

