/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Facts about star-ordered rings that depend on the continuous functional calculus

This file contains various basic facts about star-ordered rings (i.e. mainly C⋆-algebras)
that depend on the continuous functional calculus.

We also put an order instance on `A⁺¹ := Unitization ℂ A` when `A` is a C⋆-algebra via
the spectral order.

## Main theorems

* `IsSelfAdjoint.le_algebraMap_norm_self` and `IsSelfAdjoint.le_algebraMap_norm_self`,
  which respectively show that `a ≤ algebraMap ℝ A ‖a‖` and `-(algebraMap ℝ A ‖a‖) ≤ a` in a
  C⋆-algebra.
* `mul_star_le_algebraMap_norm_sq` and `star_mul_le_algebraMap_norm_sq`, which give similar
  statements for `a * star a` and `star a * a`.
* `CStarAlgebra.norm_le_norm_of_nonneg_of_le`: in a non-unital C⋆-algebra, if `0 ≤ a ≤ b`, then
  `‖a‖ ≤ ‖b‖`.
* `CStarAlgebra.conjugate_le_norm_smul`: in a non-unital C⋆-algebra, we have that
  `star a * b * a ≤ ‖b‖ • (star a * a)` (and a primed version for the `a * b * star a` case).
* `CStarAlgebra.inv_le_inv_iff`: in a unital C⋆-algebra, `b⁻¹ ≤ a⁻¹` iff `a ≤ b`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

public section

open scoped NNReal CStarAlgebra

local notation "σₙ" => quasispectrum

/-
**cfc_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cfc_tsub {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarR
ing A] [StarOrderedRing A] [Algebra Real A] [IsTopologicalRing A] [T2Space A] [C
ontinuousFunctionalCalculus Real A IsSelfAdjoint] [NonnegSpectrumClass Real A] (
f g : Real>=0 -> Real>=0) (a : A) (hfg : forall x in spectrum Real>=0 a, g x <= 
f x) (ha : 0 <= a
参数：f g : Real>=0 -> Real>=0；a : A；hfg : forall x in spectrum Real>=0 a, g x <= f
 x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `SpectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [PartialOrder A] [N
onnegSpectrumClass Real A] {a : A} (ha : 0 <= a) : SpectrumRestricts a Continuou
sMap.realToNNReal
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `SpectrumRestricts.apply_mem`：apply_mem (h : SpectrumRestricts a f) {s : 
S} (hs : s in spectrum S a) : f s in spectrum R a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用引理 `cfc_sub`：cfc_sub : cfc (fun x => f x - g x) a = cfc f a - cfc g a
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
-/
theorem cfc_tsub {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Algebra ℝ A] [IsTopologicalRing A] [T2Space A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ spectrum ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac) :
    cfc (fun x ↦ f x - g x) a = cfc f a - cfc g a := by
  have ha' := SpectrumRestricts.nnreal_of_nonneg ha
  have : (spectrum ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfc_nnreal_eq_real .., cfc_nnreal_eq_real .., cfc_nnreal_eq_real .., cfc_congr this]
  refine cfc_sub _ _ a ?_ ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cfcₙ_tsub {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
    [StarOrderedRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [IsTopologicalRing A] [T2Space A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] (f g : ℝ≥0 → ℝ≥0)
    (a : A) (hfg : ∀ x ∈ σₙ ℝ≥0 a, g x ≤ f x) (ha : 0 ≤ a := by cfc_tac)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ ℝ≥0 a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ f x - g x) a = cfcₙ f a - cfcₙ g a := by
  have ha' := QuasispectrumRestricts.nnreal_of_nonneg ha
  have : (σₙ ℝ a).EqOn (fun x ↦ ((f x.toNNReal - g x.toNNReal : ℝ≥0) : ℝ))
      (fun x ↦ f x.toNNReal - g x.toNNReal) :=
    fun x hx ↦ NNReal.coe_sub <| hfg _ <| ha'.apply_mem hx
  rw [cfcₙ_nnreal_eq_real .., cfcₙ_nnreal_eq_real .., cfcₙ_nnreal_eq_real .., cfcₙ_congr this]
  refine cfcₙ_sub _ _ a ?_ (by simpa) ?_
  all_goals
    exact continuous_subtype_val.comp_continuousOn <|
      ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..

namespace Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-
**Unitization.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instPartialOrder : PartialOrder A⁺¹
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instPartialOrder : PartialOrder A⁺¹ :=
    CStarAlgebra.spectralOrder _
/-
**Unitization.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instStarOrderedRing : StarOrderedRing A⁺¹
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.spectralOrderedRing`：CStarAlgebra.spectralOrderedRing : @St
arOrderedRing A _ (CStarAlgebra.spectralOrder A) _
-/
instance instStarOrderedRing : StarOrderedRing A⁺¹ :=
    CStarAlgebra.spectralOrderedRing _
/-
**Unitization.inr_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：inr_le_iff (a b : A) (ha : IsSelfAdjoint a
参数：a b : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用引理 `StarOrderedRing.nonneg_iff_spectrum_nonneg`：StarOrderedRing.nonneg_iff_s
pectrum_nonneg [NonnegSpectrumClass R A] (a : A) (ha : p a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Unitization.inr_sub`：inr_sub [AddGroup R] [AddGroup A] (m₁ m₂ : A) : (↑(
m₁ - m₂) : Unitization R A) = m₁ - m₂
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `StarOrderedRing.nonneg_iff_quasispectrum_nonneg`：StarOrderedRing.nonneg_
iff_quasispectrum_nonneg [NonnegSpectrumClass R A] (a : A) (ha : p a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
（共 32 条，此处仅展示前 30 条）
-/
lemma inr_le_iff (a b : A) (ha : IsSelfAdjoint a := by cfc_tac)
    (hb : IsSelfAdjoint b := by cfc_tac) :
    (a : A⁺¹) ≤ (b : A⁺¹) ↔ a ≤ b := by
  -- TODO: prove the more general result for star monomorphisms and use it here.
  rw [← sub_nonneg, ← sub_nonneg (a := b), StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _,
    ← inr_sub ℂ b a, ← Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ]
  exact StarOrderedRing.nonneg_iff_quasispectrum_nonneg _ |>.symm

@[simp, norm_cast]
/-
**Unitization.inr_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：inr_nonneg_iff {a : A} : 0 <= (a : A⁺¹) ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Unitization.inr_le_iff`：inr_le_iff (a b : A) (ha : IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unitization.inr_zero`：inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Uniti
zation R A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Unitization.isSelfAdjoint_inr`：isSelfAdjoint_inr : IsSelfAdjoint (a : Un
itization R A) ↔ IsSelfAdjoint a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
-/
lemma inr_nonneg_iff {a : A} : 0 ≤ (a : A⁺¹) ↔ 0 ≤ a := by
  by_cases ha : IsSelfAdjoint a
  · exact inr_zero ℂ (A := A) ▸ inr_le_iff 0 a
  · refine ⟨?_, ?_⟩
    all_goals refine fun h ↦ (ha ?_).elim
    · exact isSelfAdjoint_inr (R := ℂ) |>.mp <| .of_nonneg h
    · exact .of_nonneg h
/-
**Unitization.convexOn_of_convexOn_inr_comp** 是 Mathlib 中的一个引理，位于命名空间 `Unitizati
on`。
形式化陈述：convexOn_of_convexOn_inr_comp {f : A -> A} {s : Set A} (hf : forall x, IsS
elfAdjoint (f x)) (hf₂ : ConvexOn Real s (Unitization.inr (R
参数：hf : forall x, IsSelfAdjoint (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.inr_le_iff`：inr_le_iff (a b : A) (ha : IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsSelfAdjoint.add`：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x + y)
· 使用定理 `IsSelfAdjoint.smul`：smul [Star R] [Star A] [SMul R A] [StarModule R A] {
r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r 
• x)
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.inr_add`：inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m
₁ + m₂) : Unitization R A) = m₁ + m₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma convexOn_of_convexOn_inr_comp {f : A → A} {s : Set A}
    (hf : ∀ x, IsSelfAdjoint (f x))
    (hf₂ : ConvexOn ℝ s (Unitization.inr (R := ℂ) ∘ f)) : ConvexOn ℝ s f := by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab
/-
**Unitization.concaveOn_of_concaveOn_inr_comp** 是 Mathlib 中的一个引理，位于命名空间 `Unitiza
tion`。
形式化陈述：concaveOn_of_concaveOn_inr_comp {f : A -> A} {s : Set A} (hf : forall x, I
sSelfAdjoint (f x)) (hf₂ : ConcaveOn Real s (Unitization.inr (R
参数：hf : forall x, IsSelfAdjoint (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.inr_le_iff`：inr_le_iff (a b : A) (ha : IsSelfAdjoint a
· 使用定理 `IsSelfAdjoint.add`：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x + y)
· 使用定理 `IsSelfAdjoint.smul`：smul [Star R] [Star A] [SMul R A] [StarModule R A] {
r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r 
• x)
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.inr_add`：inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m
₁ + m₂) : Unitization R A) = m₁ + m₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma concaveOn_of_concaveOn_inr_comp {f : A → A} {s : Set A}
    (hf : ∀ x, IsSelfAdjoint (f x))
    (hf₂ : ConcaveOn ℝ s (Unitization.inr (R := ℂ) ∘ f)) : ConcaveOn ℝ s f := by
  refine ⟨hf₂.1, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [← Unitization.inr_le_iff _ _]
  simpa using hf₂.2 hx hy ha hb hab

alias ⟨LE.le.of_inr, LE.le.inr⟩ := inr_nonneg_iff
/-
**Unitization.nnreal_cfc** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnreal_cfcₙ_eq_cfc_inr (a : A) (f : ℝ≥0 → ℝ≥0)
    (hf₀ : f 0 = 0 := by cfc_zero_tac) : cfcₙ f a = cfc f (a : A⁺¹) :=
  cfcₙ_eq_cfc_inr inr_nonneg_iff ..
/-
**Unitization.sqrt_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：sqrt_inr {a : A} : CFC.sqrt (a : A⁺¹) = (↑(CFC.sqrt a) : A⁺¹)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.inr_nonneg_iff`：inr_nonneg_iff {a : A} : 0 <= (a : A⁺¹) ↔ 0 
<= a
· 使用引理 `CFC.sqrt_eq_iff`：sqrt_eq_iff (a b : A) (ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.inr_mul`：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [
SMulWithZero R A] (a₁ a₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `CFC.sqrt.eq_1`：∀ {A : Type u_1} [inst : PartialOrder A] [inst_1 : NonUni
talRing A] [inst_2 : TopologicalSpace A] [inst_3 : StarRing A]   [inst_4 : _root
_.M…
· 使用引理 `cfcₙ_apply_of_not_predicate`：cfcₙ_apply_of_not_predicate {f : R -> R} (a
 : A) (ha : ¬ p a) : cfcₙ f a = 0
（共 31 条，此处仅展示前 30 条）
-/
lemma sqrt_inr {a : A} : CFC.sqrt (a : A⁺¹) = (↑(CFC.sqrt a) : A⁺¹) := by
  by_cases ha : 0 ≤ a <;> have ha' := by rwa [← Unitization.inr_nonneg_iff] at ha
  · rw [CFC.sqrt_eq_iff .., ← inr_mul, CFC.sqrt_mul_sqrt_self a]
  · rw [CFC.sqrt, CFC.sqrt, cfcₙ_apply_of_not_predicate _ ha,
      cfcₙ_apply_of_not_predicate _ ha', inr_zero]

end Unitization

/-- `cfc_le_iff` only applies to a scalar ring where `R` is an actual `Ring`, and not a `Semiring`.
However, this theorem still holds for `ℝ≥0` as long as the algebra `A` itself is an `ℝ`-algebra. -/
/-
**cfc_nnreal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nnreal_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [
PartialOrder A] [StarOrderedRing A] [Algebra Real A] [IsTopologicalRing A] [Nonn
egSpectrumClass Real A] [T2Space A] [ContinuousFunctionalCalculus Real A IsSelfA
djoint] (f : Real>=0 -> Real>=0) (g : Real>=0 -> Real>=0) (a : A) (ha_spec : Spe
ctrumRestricts a ContinuousMap.realToNNReal) (hf : ContinuousOn f (spectrum Real
>=0 a)
参数：f : Real>=0 -> Real>=0；g : Real>=0 -> Real>=0；a : A；ha_spec : SpectrumRestric
ts a ContinuousMap.realToNNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.ofReal_map_toNNReal`：∀ {f : NNReal → NNReal} {s : Set ℝ} {t
 : Set NNReal},   ContinuousOn f t → Set.MapsTo Real.toNNReal s t → ContinuousOn
 (fun x => ↑(f x.toNNR…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `cfc_le_iff`：cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spec
trum R a)
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.realToNNReal_apply`：⇑ContinuousMap.realToNNReal = Real.toN
NReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`cfc_le_iff` only applies to a scalar ring where `R` is an actual `Ring`, and no
t a `Semiring`.
However, this theorem still holds for `ℝ≥0` as long as the algebra `A` itself is
 an `ℝ`-algebra.
-/
lemma cfc_nnreal_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [IsTopologicalRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (f : ℝ≥0 → ℝ≥0) (g : ℝ≥0 → ℝ≥0) (a : A)
    (ha_spec : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hf : ContinuousOn f (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (hg : ContinuousOn g (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) :
    cfc f a ≤ cfc g a ↔ ∀ x ∈ spectrum ℝ≥0 a, f x ≤ g x := by
  have hf' := hf.ofReal_map_toNNReal <| ha_spec.image ▸ Set.mapsTo_image ..
  have hg' := hg.ofReal_map_toNNReal <| ha_spec.image ▸ Set.mapsTo_image ..
  rw [cfc_nnreal_eq_real .., cfc_nnreal_eq_real .., cfc_le_iff ..]
  simp [NNReal.coe_le_coe, ← ha_spec.image]

open ContinuousFunctionalCalculus in
/-- In a unital `ℝ`-algebra `A` with a continuous functional calculus, an element `a : A` is larger
than some `algebraMap ℝ A r` if and only if every element of the `ℝ`-spectrum is nonnegative. -/
/-
**CFC.exists_pos_algebraMap_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.exists_pos_algebraMap_le_iff {A : Type*} [TopologicalSpace A] [Ring A]
 [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra Real A] [NonnegSpect
rumClass Real A] [Nontrivial A] [ContinuousFunctionalCalculus Real A IsSelfAdjoi
nt] {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `algebraMap_le_iff_le_spectrum`：algebraMap_le_iff_le_spectrum {r : R} {a 
: A} (ha : p a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s

--- 原说明 ---
In a unital `ℝ`-algebra `A` with a continuous functional calculus, an element `a
 : A` is larger
than some `algebraMap ℝ A r` if and only if every element of the `ℝ`-spectrum is
 nonnegative.
-/
lemma CFC.exists_pos_algebraMap_le_iff {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [Algebra ℝ A] [NonnegSpectrumClass ℝ A] [Nontrivial A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    (∃ r > 0, algebraMap ℝ A r ≤ a) ↔ (∀ x ∈ spectrum ℝ a, 0 < x) := by
  have h_cpct : IsCompact (spectrum ℝ a) := isCompact_iff_compactSpace.mpr inferInstance
  simp_rw [algebraMap_le_iff_le_spectrum (a := a)]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨r, hr, hr_le⟩
    exact (hr.trans_le <| hr_le · ·)
  · obtain ⟨r, hr, hr_min⟩ := h_cpct.exists_isMinOn
      (ContinuousFunctionalCalculus.spectrum_nonempty a ha) continuousOn_id
    exact ⟨r, h _ hr, hr_min⟩

section CStar_unital

variable {A : Type*} [CStarAlgebra A]

section StarOrderedRing

variable [PartialOrder A] [StarOrderedRing A]

/-
**IsSelfAdjoint.le_algebraMap_norm_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.le_algebraMap_norm_self {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_algebraMap_of_spectrum_le`：le_algebraMap_of_spectrum_le {r : R} {a : 
A} (h : forall x in spectrum R a, x <= r) (ha : p a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Real.le_norm_self`：le_norm_self (r : Real) : r <= ‖r‖
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarRing.instNormOneClassOfNontrivial`：∀ {E : Type u_2} [inst : NormedR
ing E] [inst_1 : StarRing E] [CStarRing E] [Nontrivial E], NormOneClass E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma IsSelfAdjoint.le_algebraMap_norm_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    a ≤ algebraMap ℝ A ‖a‖ := by
  by_cases! nontriv : Nontrivial A
  · refine le_algebraMap_of_spectrum_le fun r hr => ?_
    calc r ≤ ‖r‖ := Real.le_norm_self r
      _ ≤ ‖a‖ := spectrum.norm_le_norm_of_mem hr
  · simp
/-
**IsSelfAdjoint.neg_algebraMap_norm_le_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.neg_algebraMap_norm_le_self {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)
-/
lemma IsSelfAdjoint.neg_algebraMap_norm_le_self {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    -(algebraMap ℝ A ‖a‖) ≤ a := by
  rw [neg_le, ← norm_neg]
  exact ha.neg.le_algebraMap_norm_self
/-
**CStarAlgebra.mul_star_le_algebraMap_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.mul_star_le_algebraMap_norm_sq {a : A} : a * star a <= algebr
aMap Real A (‖a‖ ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_self_mul_star`：norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x
‖ * ‖x‖
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
-/
lemma CStarAlgebra.mul_star_le_algebraMap_norm_sq {a : A} :
    a * star a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : a * star a ≤ algebraMap ℝ A ‖a * star a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_self_mul_star, ← pow_two] at this
/-
**CStarAlgebra.star_mul_le_algebraMap_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.star_mul_le_algebraMap_norm_sq {a : A} : star a * a <= algebr
aMap Real A (‖a‖ ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
-/
lemma CStarAlgebra.star_mul_le_algebraMap_norm_sq {a : A} :
    star a * a ≤ algebraMap ℝ A (‖a‖ ^ 2) := by
  have : star a * a ≤ algebraMap ℝ A ‖star a * a‖ := IsSelfAdjoint.le_algebraMap_norm_self
  rwa [CStarRing.norm_star_mul_self, ← pow_two] at this

end StarOrderedRing

/-
**IsSelfAdjoint.toReal_spectralRadius_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.toReal_spectralRadius_eq_norm {a : A} (ha : IsSelfAdjoint a)
 : (spectralRadius Real a).toReal = ‖a‖
参数：ha : IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.spectralRadius_eq`：spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*}
 [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAl
gebra 𝕜₂ A] [NormedAlgebr…
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSelfAdjoint.toReal_spectralRadius_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius ℝ a).toReal = ‖a‖ := by
  simp [ha.spectrumRestricts.spectralRadius_eq, ha.spectralRadius_eq_nnnorm]

namespace CStarAlgebra

/-
**CStarAlgebra.norm_or_neg_norm_mem_spectrum** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlg
ebra`。
形式化陈述：norm_or_neg_norm_mem_spectrum [Nontrivial A] {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsSelfAdjoint.toReal_spectralRadius_eq_norm`：IsSelfAdjoint.toReal_spectr
alRadius_eq_norm {a : A} (ha : IsSelfAdjoint a) : (spectralRadius Real a).toReal
 = ‖a‖
· 使用定理 `Real.spectralRadius_mem_spectrum_or`：∀ {A : Type u_4} [inst : NormedRing
 A] [inst_1 : NormedAlgebra ℝ A] [CompleteSpace A] {a : A},   (spectrum ℝ a).Non
empty → (spectralRadius ℝ…
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
-/
lemma norm_or_neg_norm_mem_spectrum [Nontrivial A] {a : A}
    (ha : IsSelfAdjoint a := by cfc_tac) : ‖a‖ ∈ spectrum ℝ a ∨ -‖a‖ ∈ spectrum ℝ a := by
  have ha' : SpectrumRestricts a Complex.reCLM := ha.spectrumRestricts
  rw [← ha.toReal_spectralRadius_eq_norm]
  exact Real.spectralRadius_mem_spectrum_or (ha'.image ▸ (spectrum.nonempty a).image _)

variable [PartialOrder A] [StarOrderedRing A]
/-
**CStarAlgebra.nnnorm_mem_spectrum_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlg
ebra`。
形式化陈述：nnnorm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.spectralRadius_eq`：spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*}
 [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAl
gebra 𝕜₂ A] [NormedAlgebr…
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNReal.spectralRadius_mem_spectrum`：∀ {A : Type u_4} [inst : NormedRing 
A] [inst_1 : NormedAlgebra ℝ A] [CompleteSpace A] {a : A},   (spectrum ℝ a).None
mpty →     SpectrumRestr…
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
· 使用引理 `SpectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [PartialOrder A] [N
onnegSpectrumClass Real A] {a : A} (ha : 0 <= a) : SpectrumRestricts a Continuou
sMap.realToNNReal
-/
lemma nnnorm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ∈ spectrum ℝ≥0 a := by
  have : IsSelfAdjoint a := .of_nonneg ha
  convert! NNReal.spectralRadius_mem_spectrum (a := a) ?_ (.nnreal_of_nonneg ha)
  · simp [this.spectrumRestricts.spectralRadius_eq, this.spectralRadius_eq_nnnorm]
  · exact this.spectrumRestricts.image ▸ (spectrum.nonempty a).image _
/-
**CStarAlgebra.norm_mem_spectrum_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgeb
ra`。
形式化陈述：norm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.algebraMap_mem`：∀ (S : Type u_1) {R : Type u_2} {A : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Ring A]   [inst_3 : 
Algebra R S] …
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `CStarAlgebra.nnnorm_mem_spectrum_of_nonneg`：nnnorm_mem_spectrum_of_nonne
g [Nontrivial A] {a : A} (ha : 0 <= a
-/
lemma norm_mem_spectrum_of_nonneg [Nontrivial A] {a : A} (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ∈ spectrum ℝ a := by
  simpa using spectrum.algebraMap_mem ℝ <| nnnorm_mem_spectrum_of_nonneg ha
/-
**CStarAlgebra.norm_le_iff_le_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra
`。
形式化陈述：norm_le_iff_le_algebraMap (a : A) {r : Real} (hr : 0 <= r) (ha : 0 <= a
参数：a : A；hr : 0 <= r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_algebraMap_iff_spectrum_le`：le_algebraMap_iff_spectrum_le {r : R} {a 
: A} (ha : p a
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.le_norm_self`：le_norm_self (r : Real) : r <= ‖r‖
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarRing.instNormOneClassOfNontrivial`：∀ {E : Type u_2} [inst : NormedR
ing E] [inst_1 : StarRing E] [CStarRing E] [Nontrivial E], NormOneClass E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
（共 31 条，此处仅展示前 30 条）
-/
lemma norm_le_iff_le_algebraMap (a : A) {r : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ≤ r ↔ a ≤ algebraMap ℝ A r := by
  rw [le_algebraMap_iff_spectrum_le]
  obtain (h | _) := subsingleton_or_nontrivial A
  · simp [Subsingleton.elim a 0, hr]
  · exact ⟨fun h x hx ↦ Real.le_norm_self x |>.trans (spectrum.norm_le_norm_of_mem hx) |>.trans h,
      fun h ↦ h ‖a‖ <| norm_mem_spectrum_of_nonneg⟩
/-
**CStarAlgebra.nnnorm_le_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：nnnorm_le_iff_of_nonneg (a : A) (r : Real>=0) (ha : 0 <= a
参数：a : A；r : Real>=0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用引理 `CStarAlgebra.norm_le_iff_le_algebraMap`：norm_le_iff_le_algebraMap (a : A
) {r : Real} (hr : 0 <= r) (ha : 0 <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma nnnorm_le_iff_of_nonneg (a : A) (r : ℝ≥0) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ≤ r ↔ a ≤ algebraMap ℝ≥0 A r := by
  rw [← NNReal.coe_le_coe]
  exact norm_le_iff_le_algebraMap a r.2
/-
**CStarAlgebra.norm_le_one_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra
`。
形式化陈述：norm_le_one_iff_of_nonneg (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `CStarAlgebra.norm_le_iff_le_algebraMap`：norm_le_iff_le_algebraMap (a : A
) {r : Real} (hr : 0 <= r) (ha : 0 <= a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma norm_le_one_iff_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ≤ 1 ↔ a ≤ 1 := by
  simpa using norm_le_iff_le_algebraMap a zero_le_one
/-
**CStarAlgebra.nnnorm_le_one_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgeb
ra`。
形式化陈述：nnnorm_le_one_iff_of_nonneg (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用引理 `CStarAlgebra.norm_le_one_iff_of_nonneg`：norm_le_one_iff_of_nonneg (a : A
) (ha : 0 <= a
-/
lemma nnnorm_le_one_iff_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ≤ 1 ↔ a ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  exact norm_le_one_iff_of_nonneg a
/-
**CStarAlgebra.norm_le_natCast_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlg
ebra`。
形式化陈述：norm_le_natCast_iff_of_nonneg (a : A) (n : Nat) (ha : 0 <= a
参数：a : A；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `CStarAlgebra.norm_le_iff_le_algebraMap`：norm_le_iff_le_algebraMap (a : A
) {r : Real} (hr : 0 <= r) (ha : 0 <= a
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma norm_le_natCast_iff_of_nonneg (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖ ≤ n ↔ a ≤ n := by
  simpa using norm_le_iff_le_algebraMap a n.cast_nonneg
/-
**CStarAlgebra.nnnorm_le_natCast_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarA
lgebra`。
形式化陈述：nnnorm_le_natCast_iff_of_nonneg (a : A) (n : Nat) (ha : 0 <= a
参数：a : A；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用引理 `CStarAlgebra.nnnorm_le_iff_of_nonneg`：nnnorm_le_iff_of_nonneg (a : A) (r
 : Real>=0) (ha : 0 <= a
-/
lemma nnnorm_le_natCast_iff_of_nonneg (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) :
    ‖a‖₊ ≤ n ↔ a ≤ n := by
  simpa using nnnorm_le_iff_of_nonneg a n


section Icc

open Set

/-
**CStarAlgebra.mem_Icc_algebraMap_iff_norm_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarAl
gebra`。
形式化陈述：mem_Icc_algebraMap_iff_norm_le {x : A} {r : Real} (hr : 0 <= r) : x in Icc
 0 (algebraMap Real A r) ↔ 0 <= x ∧ ‖x‖ <= r
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用引理 `CStarAlgebra.norm_le_iff_le_algebraMap`：norm_le_iff_le_algebraMap (a : A
) {r : Real} (hr : 0 <= r) (ha : 0 <= a
-/
lemma mem_Icc_algebraMap_iff_norm_le {x : A} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ Icc 0 (algebraMap ℝ A r) ↔ 0 ≤ x ∧ ‖x‖ ≤ r := by
  rw [mem_Icc, and_congr_right_iff, iff_comm]
  exact (norm_le_iff_le_algebraMap _ hr ·)
/-
**CStarAlgebra.mem_Icc_algebraMap_iff_nnnorm_le** 是 Mathlib 中的一个引理，位于命名空间 `CStar
Algebra`。
形式化陈述：mem_Icc_algebraMap_iff_nnnorm_le {x : A} {r : Real>=0} : x in Icc 0 (algeb
raMap Real>=0 A r) ↔ 0 <= x ∧ ‖x‖₊ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.mem_Icc_algebraMap_iff_norm_le`：mem_Icc_algebraMap_iff_norm
_le {x : A} {r : Real} (hr : 0 <= r) : x in Icc 0 (algebraMap Real A r) ↔ 0 <= x
 ∧ ‖x‖ <= r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma mem_Icc_algebraMap_iff_nnnorm_le {x : A} {r : ℝ≥0} :
    x ∈ Icc 0 (algebraMap ℝ≥0 A r) ↔ 0 ≤ x ∧ ‖x‖₊ ≤ r :=
  mem_Icc_algebraMap_iff_norm_le (hr := r.2)
/-
**CStarAlgebra.mem_Icc_iff_norm_le_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：mem_Icc_iff_norm_le_one {x : A} : x in Icc 0 1 ↔ 0 <= x ∧ ‖x‖ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `CStarAlgebra.mem_Icc_algebraMap_iff_norm_le`：mem_Icc_algebraMap_iff_norm
_le {x : A} {r : Real} (hr : 0 <= r) : x in Icc 0 (algebraMap Real A r) ↔ 0 <= x
 ∧ ‖x‖ <= r
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma mem_Icc_iff_norm_le_one {x : A} :
    x ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖ ≤ 1 := by
  simpa only [map_one] using mem_Icc_algebraMap_iff_norm_le zero_le_one (A := A)
/-
**CStarAlgebra.mem_Icc_iff_nnnorm_le_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra
`。
形式化陈述：mem_Icc_iff_nnnorm_le_one {x : A} : x in Icc 0 1 ↔ 0 <= x ∧ ‖x‖₊ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.mem_Icc_iff_norm_le_one`：mem_Icc_iff_norm_le_one {x : A} : 
x in Icc 0 1 ↔ 0 <= x ∧ ‖x‖ <= 1
-/
lemma mem_Icc_iff_nnnorm_le_one {x : A} :
    x ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖₊ ≤ 1 :=
  mem_Icc_iff_norm_le_one

end Icc

end CStarAlgebra

section Inv

open CFC

variable [PartialOrder A] [StarOrderedRing A]

/-
**CFC.conjugate_rpow_neg_one_half** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.conjugate_rpow_neg_one_half (a : A) (ha : IsStrictlyPositive a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.rpow_one`：rpow_one (a : A) (ha : 0 <= a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CFC.rpow_add`：rpow_add {a : A} {x y : Real} (ha : IsUnit a) : a ^ (x + y
) = a ^ x * a ^ y
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℤ}, Mathlib.Meta.NormNum.IsRat a n 1 → Mathlib.Meta.NormNum.IsInt a n
· 使用定理 `Mathlib.Meta.NormNum.isRat_add`：isRat_add {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HAdd.hAdd -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {n n' : ℤ} {d : ℕ},   f = Neg.neg → Mathlib.Meta.NormNum.IsRat a n 
d → n.neg = n' → Mat…
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
（共 35 条，此处仅展示前 30 条）
-/
lemma CFC.conjugate_rpow_neg_one_half (a : A) (ha : IsStrictlyPositive a := by cfc_tac) :
    a ^ (-(1 / 2) : ℝ) * a * a ^ (-(1 / 2) : ℝ) = 1 := by
  lift a to Aˣ using ha.isUnit
  nth_rw 2 [← rpow_one (a : A)]
  simp only [← rpow_add a.isUnit]
  norm_num
  exact rpow_zero _

/-- In a unital C⋆-algebra, if `a` is strictly positive, and `a ≤ b`, then `b` is
invertible. -/
/-
**CStarAlgebra.isUnit_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.isUnit_of_le (a : A) {b : A} (hab : a <= b) (h : IsStrictlyPo
sitive a
参数：a : A；hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectrum.zero_notMem_iff`：zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUn
it a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CFC.exists_pos_algebraMap_le_iff`：CFC.exists_pos_algebraMap_le_iff {A : 
Type*} [TopologicalSpace A] [Ring A] [StarRing A] [PartialOrder A] [StarOrderedR
ing A] [Algebra Real A…
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `IsStrictlyPositive.isSelfAdjoint`：isSelfAdjoint [Semiring A] [PartialOrd
er A] [StarRing A] [StarOrderedRing A] {a : A} (ha : IsStrictlyPositive a) : IsS
elfAdjoint a
· 使用引理 `IsStrictlyPositive.spectrum_pos`：spectrum_pos [CommSemiring 𝕜] [PartialO
rder 𝕜] [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : IsStrictlyPositive
 a) {x : 𝕜} (hx : x i…
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `algebraMap_le_iff_le_spectrum`：algebraMap_le_iff_le_spectrum {r : R} {a 
: A} (ha : p a
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a

--- 原说明 ---
In a unital C⋆-algebra, if `a` is strictly positive, and `a ≤ b`, then `b` is
invertible.
-/
lemma CStarAlgebra.isUnit_of_le (a : A) {b : A} (hab : a ≤ b)
    (h : IsStrictlyPositive a := by cfc_tac) : IsUnit b := by
  nontriviality A
  rw [← spectrum.zero_notMem_iff ℝ]
  obtain ⟨r, hr, hr_le⟩ : ∃ r > 0, (algebraMap ℝ A) r ≤ a :=
    (exists_pos_algebraMap_le_iff h.isSelfAdjoint).2 fun x hx ↦ h.spectrum_pos hx
  exact fun h0 ↦ not_le_of_gt hr <| (algebraMap_le_iff_le_spectrum <| .of_nonneg <|
    h.nonneg.trans hab).1 (hr_le.trans hab) 0 h0
/-
**le_iff_norm_sqrt_mul_rpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_norm_sqrt_mul_rpow (a b : A) (ha : 0 <= a
参数：a b : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `conjugate_nonneg_of_nonneg`：conjugate_nonneg_of_nonneg {a : R} (ha : 0 <
= a) {c : R} (hc : 0 <= c) : 0 <= c * a * c
· 使用引理 `CFC.rpow_nonneg`：rpow_nonneg {a : A} {y : Real} : 0 <= a ^ y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_le_one_iff₀`：sq_le_one_iff₀ (ha : 0 <= a) : a ^ 2 <= 1 ↔ a <= 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `CFC.sqrt_mul_sqrt_self`：sqrt_mul_sqrt_self (a : A) (ha : 0 <= a
（共 67 条，此处仅展示前 30 条）
-/
lemma le_iff_norm_sqrt_mul_rpow (a b : A) (ha : 0 ≤ a := by cfc_tac)
    (hb : IsStrictlyPositive b := by cfc_tac) :
    a ≤ b ↔ ‖sqrt a * (b : A) ^ (-(1 / 2) : ℝ)‖ ≤ 1 := by
  lift b to Aˣ using hb.isUnit
  have hbab : 0 ≤ (b : A) ^ (-(1 / 2) : ℝ) * a * (b : A) ^ (-(1 / 2) : ℝ) :=
    conjugate_nonneg_of_nonneg ha rpow_nonneg
  conv_rhs =>
    rw [← sq_le_one_iff₀ (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self, star_mul,
      IsSelfAdjoint.of_nonneg (sqrt_nonneg a), IsSelfAdjoint.of_nonneg rpow_nonneg,
      ← mul_assoc, mul_assoc _ _ (sqrt a), sqrt_mul_sqrt_self a,
      CStarAlgebra.norm_le_one_iff_of_nonneg _ hbab]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · calc
      _ ≤ ↑b ^ (-(1 / 2) : ℝ) * (b : A) * ↑b ^ (-(1 / 2) : ℝ) :=
        IsSelfAdjoint.of_nonneg rpow_nonneg |>.conjugate_le_conjugate h
      _ = 1 := conjugate_rpow_neg_one_half (b : A)
  · calc
      a = (sqrt ↑b * ↑b ^ (-(1 / 2) : ℝ)) * a * (↑b ^ (-(1 / 2) : ℝ) * sqrt ↑b) := by
        simp only [CFC.sqrt_eq_rpow .., ← CFC.rpow_add b.isUnit]
        norm_num
        simp [CFC.rpow_zero (b : A)]
      _ = sqrt ↑b * (↑b ^ (-(1 / 2) : ℝ) * a * ↑b ^ (-(1 / 2) : ℝ)) * sqrt ↑b := by
        simp only [mul_assoc]
      _ ≤ b := conjugate_le_conjugate_of_nonneg h (sqrt_nonneg _) |>.trans <| by
        simp [CFC.sqrt_mul_sqrt_self (b : A)]
/-
**le_iff_norm_sqrt_mul_sqrt_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_norm_sqrt_mul_sqrt_inv {a : A} {b : Aˣ} (ha : 0 <= a) (hb : 0 <= (b
 : A)) : a <= b ↔ ‖sqrt a * sqrt (↑b⁻¹ : A)‖ <= 1
参数：ha : 0 <= a；hb : 0 <= (b : A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.sqrt_eq_rpow`：sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : Real)
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.rpow_neg_one_eq_inv`：rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) <= a
· 使用引理 `CFC.rpow_rpow`：rpow_rpow [IsSemitopologicalRing A] [T2Space A] (a : A) (
x y : Real) (hx : x != 0) (ha : IsStrictlyPositive a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Units.isStrictlyPositive_of_le`：∀ {A : Type u_1} [inst : LE A] [inst_1 :
 Monoid A] [inst_2 : Zero A] {a : Aˣ}, 0 ≤ ↑a → IsStrictlyPositive ↑a
· 使用引理 `le_iff_norm_sqrt_mul_rpow`：le_iff_norm_sqrt_mul_rpow (a b : A) (ha : 0 <
= a
· 使用定理 `IsUnit.isStrictlyPositive`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsUnit a → 0 ≤ a → IsStrictlyPositive a
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
（共 36 条，此处仅展示前 30 条）
-/
lemma le_iff_norm_sqrt_mul_sqrt_inv {a : A} {b : Aˣ} (ha : 0 ≤ a) (hb : 0 ≤ (b : A)) :
    a ≤ b ↔ ‖sqrt a * sqrt (↑b⁻¹ : A)‖ ≤ 1 := by
  rw [CFC.sqrt_eq_rpow (a := (↑b⁻¹ : A)), ← CFC.rpow_neg_one_eq_inv b,
    CFC.rpow_rpow (b : A) _ _ (by simp),
    le_iff_norm_sqrt_mul_rpow a (hb := b.isUnit.isStrictlyPositive hb)]
  simp

namespace CStarAlgebra

/-- In a unital C⋆-algebra, if `0 ≤ a ≤ b` and `a` and `b` are units, then `b⁻¹ ≤ a⁻¹`. -/
/-
**CStarAlgebra.inv_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `CStarAlgebra`。
形式化陈述：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst_1 : PartialOrder A] [StarOr
deredRing A] {a b : Aˣ},   0 ≤ ↑a → ↑a ≤ ↑b → ↑b⁻¹ ≤ ↑a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CFC.inv_nonneg_of_nonneg`：CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A
) <= a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_norm_sqrt_mul_sqrt_inv`：le_iff_norm_sqrt_mul_sqrt_inv {a : A} {b 
: Aˣ} (ha : 0 <= a) (hb : 0 <= (b : A)) : a <= b ↔ ‖sqrt a * sqrt (↑b⁻¹ : A)‖ <=
 1
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_le_one_iff₀`：sq_le_one_iff₀ (ha : 0 <= a) : a ^ 2 <= 1 ↔ a <= 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_self_mul_star`：norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x
‖ * ‖x‖
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `CFC.sqrt_nonneg`：sqrt_nonneg (a : A) : 0 <= sqrt a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖

--- 原说明 ---
In a unital C⋆-algebra, if `0 ≤ a ≤ b` and `a` and `b` are units, then `b⁻¹ ≤ a⁻
¹`.
-/
protected lemma inv_le_inv {a b : Aˣ} (ha : 0 ≤ (a : A))
    (hab : (a : A) ≤ b) : (↑b⁻¹ : A) ≤ a⁻¹ := by
  have hb := ha.trans hab
  have hb_inv : (0 : A) ≤ b⁻¹ := inv_nonneg_of_nonneg b hb
  have ha_inv : (0 : A) ≤ a⁻¹ := inv_nonneg_of_nonneg a ha
  rw [le_iff_norm_sqrt_mul_sqrt_inv ha hb, ← sq_le_one_iff₀ (norm_nonneg _), sq,
    ← CStarRing.norm_star_mul_self] at hab
  rw [le_iff_norm_sqrt_mul_sqrt_inv hb_inv ha_inv, inv_inv, ← sq_le_one_iff₀ (norm_nonneg _), sq,
    ← CStarRing.norm_self_mul_star]
  rwa [star_mul, IsSelfAdjoint.of_nonneg (sqrt_nonneg _),
    IsSelfAdjoint.of_nonneg (sqrt_nonneg _)] at hab ⊢

/-- In a unital C⋆-algebra, if `0 ≤ a` and `0 ≤ b` and `a` and `b` are units, then `a⁻¹ ≤ b⁻¹`
if and only if `b ≤ a`. -/
/-
**CStarAlgebra.inv_le_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `CStarAlgebra`。
形式化陈述：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst_1 : PartialOrder A] [StarOr
deredRing A] {a b : Aˣ},   0 ≤ ↑a → 0 ≤ ↑b → (↑a⁻¹ ≤ ↑b⁻¹ ↔ ↑b ≤ ↑a)
参数：↑a⁻¹ ≤ ↑b⁻¹ ↔ ↑b ≤ ↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.inv_le_inv`：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst_
1 : PartialOrder A] [StarOrderedRing A] {a b : Aˣ},   0 ≤ ↑a → ↑a ≤ ↑b → ↑b⁻¹ ≤ 
↑a⁻¹
· 使用引理 `CFC.inv_nonneg_of_nonneg`：CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A
) <= a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ

--- 原说明 ---
In a unital C⋆-algebra, if `0 ≤ a` and `0 ≤ b` and `a` and `b` are units, then `
a⁻¹ ≤ b⁻¹`
if and only if `b ≤ a`.
-/
protected lemma inv_le_inv_iff {a b : Aˣ} (ha : 0 ≤ (a : A)) (hb : 0 ≤ (b : A)) :
    (↑a⁻¹ : A) ≤ b⁻¹ ↔ (b : A) ≤ a :=
  ⟨CStarAlgebra.inv_le_inv (inv_nonneg_of_nonneg a ha), CStarAlgebra.inv_le_inv hb⟩
/-
**CStarAlgebra.inv_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：inv_le_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A)) : (↑a⁻¹ : A
) <= b ↔ (↑b⁻¹ : A) <= a
参数：ha : 0 <= (a : A)；hb : 0 <= (↑b : A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `CStarAlgebra.inv_le_inv_iff`：∀ {A : Type u_1} [inst : CStarAlgebra A] [i
nst_1 : PartialOrder A] [StarOrderedRing A] {a b : Aˣ},   0 ≤ ↑a → 0 ≤ ↑b → (↑a⁻
¹ ≤ ↑b⁻¹ ↔ ↑b ≤ ↑…
· 使用引理 `CFC.inv_nonneg_of_nonneg`：CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A
) <= a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
-/
lemma inv_le_iff {a b : Aˣ} (ha : 0 ≤ (a : A)) (hb : 0 ≤ (↑b : A)) :
    (↑a⁻¹ : A) ≤ b ↔ (↑b⁻¹ : A) ≤ a := by
  simpa using CStarAlgebra.inv_le_inv_iff ha (inv_nonneg_of_nonneg b hb)
/-
**CStarAlgebra.le_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：le_inv_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb : 0 <= (↑b : A)) : a <= (↑b⁻
¹ : A) ↔ b <= (↑a⁻¹ : A)
参数：ha : 0 <= (a : A)；hb : 0 <= (↑b : A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `CStarAlgebra.inv_le_inv_iff`：∀ {A : Type u_1} [inst : CStarAlgebra A] [i
nst_1 : PartialOrder A] [StarOrderedRing A] {a b : Aˣ},   0 ≤ ↑a → 0 ≤ ↑b → (↑a⁻
¹ ≤ ↑b⁻¹ ↔ ↑b ≤ ↑…
· 使用引理 `CFC.inv_nonneg_of_nonneg`：CFC.inv_nonneg_of_nonneg (a : Aˣ) (ha : (0 : A
) <= a
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
-/
lemma le_inv_iff {a b : Aˣ} (ha : 0 ≤ (a : A)) (hb : 0 ≤ (↑b : A)) :
    a ≤ (↑b⁻¹ : A) ↔ b ≤ (↑a⁻¹ : A) := by
  simpa using CStarAlgebra.inv_le_inv_iff (inv_nonneg_of_nonneg a ha) hb
/-
**CStarAlgebra.one_le_inv_iff_le_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：one_le_inv_iff_le_one {a : Aˣ} (ha : 0 <= (a : A)) : 1 <= (↑a⁻¹ : A) ↔ a <
= 1
参数：ha : 0 <= (a : A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `CStarAlgebra.le_inv_iff`：le_inv_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb :
 0 <= (↑b : A)) : a <= (↑b⁻¹ : A) ↔ b <= (↑a⁻¹ : A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
-/
lemma one_le_inv_iff_le_one {a : Aˣ} (ha : 0 ≤ (a : A)) :
    1 ≤ (↑a⁻¹ : A) ↔ a ≤ 1 := by
  simpa using! CStarAlgebra.le_inv_iff (a := 1) (by simp) ha
/-
**CStarAlgebra.inv_le_one_iff_one_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：inv_le_one_iff_one_le {a : Aˣ} (ha : 0 <= (a : A)) : (↑a⁻¹ : A) <= 1 ↔ 1 <
= a
参数：ha : 0 <= (a : A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `CStarAlgebra.inv_le_iff`：inv_le_iff {a b : Aˣ} (ha : 0 <= (a : A)) (hb :
 0 <= (↑b : A)) : (↑a⁻¹ : A) <= b ↔ (↑b⁻¹ : A) <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
-/
lemma inv_le_one_iff_one_le {a : Aˣ} (ha : 0 ≤ (a : A)) :
    (↑a⁻¹ : A) ≤ 1 ↔ 1 ≤ a := by
  simpa using! CStarAlgebra.inv_le_iff ha (b := 1) (by simp)
/-
**CStarAlgebra.inv_le_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：inv_le_one {a : Aˣ} (ha : 1 <= a) : (↑a⁻¹ : A) <= 1
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CStarAlgebra.inv_le_one_iff_one_le`：inv_le_one_iff_one_le {a : Aˣ} (ha :
 0 <= (a : A)) : (↑a⁻¹ : A) <= 1 ↔ 1 <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
-/
lemma inv_le_one {a : Aˣ} (ha : 1 ≤ a) : (↑a⁻¹ : A) ≤ 1 :=
  CStarAlgebra.inv_le_one_iff_one_le (zero_le_one.trans ha) |>.mpr ha
/-
**CStarAlgebra.le_one_of_one_le_inv** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：le_one_of_one_le_inv {a : Aˣ} (ha : 1 <= (↑a⁻¹ : A)) : (a : A) <= 1
参数：ha : 1 <= (↑a⁻¹ : A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `CStarAlgebra.inv_le_one`：inv_le_one {a : Aˣ} (ha : 1 <= a) : (↑a⁻¹ : A) 
<= 1
-/
lemma le_one_of_one_le_inv {a : Aˣ} (ha : 1 ≤ (↑a⁻¹ : A)) : (a : A) ≤ 1 := by
  simpa using CStarAlgebra.inv_le_one ha
/-
**CStarAlgebra.rpow_neg_one_le_rpow_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlge
bra`。
形式化陈述：rpow_neg_one_le_rpow_neg_one {a b : A} (hab : a <= b) (ha : IsStrictlyPosi
tive a
参数：hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用引理 `CStarAlgebra.isUnit_of_le`：CStarAlgebra.isUnit_of_le (a : A) {b : A} (ha
b : a <= b) (h : IsStrictlyPositive a
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_neg_one_eq_inv`：rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) <= a
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CStarAlgebra.inv_le_inv`：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst_
1 : PartialOrder A] [StarOrderedRing A] {a b : Aˣ},   0 ≤ ↑a → ↑a ≤ ↑b → ↑b⁻¹ ≤ 
↑a⁻¹
-/
lemma rpow_neg_one_le_rpow_neg_one {a b : A} (hab : a ≤ b)
    (ha : IsStrictlyPositive a := by cfc_tac) :
    b ^ (-1 : ℝ) ≤ a ^ (-1 : ℝ) := by
  lift b to Aˣ using isUnit_of_le a hab
  lift a to Aˣ using ha.isUnit
  rw [rpow_neg_one_eq_inv a, rpow_neg_one_eq_inv b (ha.nonneg.trans hab)]
  exact CStarAlgebra.inv_le_inv ha.nonneg hab
/-
**CStarAlgebra.rpow_neg_one_le_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：rpow_neg_one_le_one {a : A} (ha : 1 <= a) : a ^ (-1 : Real) <= 1
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用引理 `CStarAlgebra.isUnit_of_le`：CStarAlgebra.isUnit_of_le (a : A) {b : A} (ha
b : a <= b) (h : IsStrictlyPositive a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CFC.rpow_neg_one_eq_inv`：rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `CStarAlgebra.inv_le_one`：inv_le_one {a : Aˣ} (ha : 1 <= a) : (↑a⁻¹ : A) 
<= 1
-/
lemma rpow_neg_one_le_one {a : A} (ha : 1 ≤ a) : a ^ (-1 : ℝ) ≤ 1 := by
  lift a to Aˣ using isUnit_of_le 1 ha
  rw [rpow_neg_one_eq_inv a (zero_le_one.trans ha)]
  exact inv_le_one ha
/-
**CStarAlgebra._root_.IsStrictlyPositive.of_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarA
lgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.IsStrictlyPositive.of_le {a b : A} (ha : IsStrictlyPositive a)
    (hab : a ≤ b) : IsStrictlyPositive b :=
  ⟨ha.nonneg.trans hab, CStarAlgebra.isUnit_of_le a hab⟩
/-
**CStarAlgebra._root_.IsStrictlyPositive.add_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `C
StarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsStrictlyPositive.add_nonneg {a b : A}
    (ha : IsStrictlyPositive a) (hb : 0 ≤ b) : IsStrictlyPositive (a + b) :=
  IsStrictlyPositive.of_le ha ((le_add_iff_nonneg_right a).mpr hb)
/-
**CStarAlgebra._root_.IsStrictlyPositive.nonneg_add** 是 Mathlib 中的一个定理，位于命名空间 `C
StarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsStrictlyPositive.nonneg_add {a b : A}
    (ha : 0 ≤ a) (hb : IsStrictlyPositive b) : IsStrictlyPositive (a + b) :=
  add_comm a b ▸ hb.add_nonneg ha

@[grind ←, aesop 90% apply]
/-
**CStarAlgebra._root_.isStrictlyPositive_add** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlg
ebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isStrictlyPositive_add {a b : A}
    (h : IsStrictlyPositive a ∧ 0 ≤ b ∨ 0 ≤ a ∧ IsStrictlyPositive b) :
    IsStrictlyPositive (a + b) := by
  grind [IsStrictlyPositive.add_nonneg, IsStrictlyPositive.nonneg_add]
/-
**CStarAlgebra.antitoneOn_ringInverse** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：antitoneOn_ringInverse : AntitoneOn Ring.inverse {a : A | IsStrictlyPositi
ve a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.inverse_of_isUnit`：inverse_of_isUnit {x : M₀} (h : IsUnit x) : x⁻¹ʳ
 = ((h.unit⁻¹ : M₀ˣ) : M₀)
· 使用定理 `CStarAlgebra.inv_le_inv`：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst_
1 : PartialOrder A] [StarOrderedRing A] {a b : Aˣ},   0 ≤ ↑a → ↑a ≤ ↑b → ↑b⁻¹ ≤ 
↑a⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.isStrictlyPositive_iff`：∀ {A : Type u_1} [inst : LE A] [inst_1 : M
onoid A] [inst_2 : Zero A] {a : Aˣ}, IsStrictlyPositive ↑a ↔ 0 ≤ ↑a
-/
lemma antitoneOn_ringInverse : AntitoneOn Ring.inverse {a : A | IsStrictlyPositive a} := by
  intro a (apos : IsStrictlyPositive a) b (bpos : IsStrictlyPositive b) hab
  rw [Ring.inverse_of_isUnit (by grind), Ring.inverse_of_isUnit (by grind)]
  exact CStarAlgebra.inv_le_inv (Units.isStrictlyPositive_iff.mp apos) hab

open Ring in
@[gcongr]
/-
**CStarAlgebra.ringInverse_le_ringInverse** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebr
a`。
形式化陈述：ringInverse_le_ringInverse {a b : A} (hab : a <= b) (ha : IsStrictlyPositi
ve a
参数：hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.antitoneOn_ringInverse`：antitoneOn_ringInverse : AntitoneOn
 Ring.inverse {a : A | IsStrictlyPositive a}
· 使用定理 `IsStrictlyPositive.of_le`：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst
_1 : PartialOrder A] [StarOrderedRing A] {a b : A},   IsStrictlyPositive a → a ≤
 b → IsStrictl…
-/
lemma ringInverse_le_ringInverse {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a := by cfc_tac) :
    b⁻¹ʳ ≤ a⁻¹ʳ :=
  antitoneOn_ringInverse ha (IsStrictlyPositive.of_le ha hab) hab

end CStarAlgebra

end Inv

end CStar_unital

section CStar_nonunital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace CStarAlgebra

open ComplexOrder in
/-
**CStarAlgebra.instNonnegSpectrumClassComplexNonUnital** 是 Mathlib 中的一个实例，位于命名空间
 `CStarAlgebra`。
形式化陈述：instNonnegSpectrumClassComplexNonUnital : NonnegSpectrumClass Complex A wh
ere quasispectrum_nonneg_of_nonneg a ha x hx
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Unitization.inr_nonneg_iff`：inr_nonneg_iff {a : A} : 0 <= (a : A⁺¹) ↔ 0 
<= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
-/
instance instNonnegSpectrumClassComplexNonUnital : NonnegSpectrumClass ℂ A where
  quasispectrum_nonneg_of_nonneg a ha x hx := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' ℂ ℂ a] at hx
    exact spectrum_nonneg_of_nonneg (Unitization.inr_nonneg_iff.mpr ha) hx
/-
**CStarAlgebra.norm_le_norm_of_nonneg_of_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlge
bra`。
形式化陈述：norm_le_norm_of_nonneg_of_le {a b : A} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CStarAlgebra.norm_le_iff_le_algebraMap`：norm_le_iff_le_algebraMap (a : A
) {r : Real} (hr : 0 <= r) (ha : 0 <= a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
· 使用引理 `Unitization.inr_le_iff`：inr_le_iff (a b : A) (ha : IsSelfAdjoint a
-/
lemma norm_le_norm_of_nonneg_of_le {a b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖ ≤ ‖b‖ := by
  suffices ∀ a b : A⁺¹, 0 ≤ a → a ≤ b → ‖a‖ ≤ ‖b‖ by
    have hb := ha.trans hab
    simpa only [ge_iff_le, Unitization.norm_inr] using
      this a b (by simpa) (by rwa [Unitization.inr_le_iff a b])
  intro a b ha hab
  have hb : 0 ≤ b := ha.trans hab
  exact (norm_le_iff_le_algebraMap a (norm_nonneg _) ha).2 <| hab.trans <|
    IsSelfAdjoint.le_algebraMap_norm_self (.of_nonneg hb)
/-
**CStarAlgebra.nnnorm_le_nnnorm_of_nonneg_of_le** 是 Mathlib 中的一个定理，位于命名空间 `CStar
Algebra`。
形式化陈述：nnnorm_le_nnnorm_of_nonneg_of_le {a : A} {b : A} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.norm_le_norm_of_nonneg_of_le`：norm_le_norm_of_nonneg_of_le 
{a b : A} (ha : 0 <= a
-/
theorem nnnorm_le_nnnorm_of_nonneg_of_le {a : A} {b : A} (ha : 0 ≤ a := by cfc_tac) (hab : a ≤ b) :
    ‖a‖₊ ≤ ‖b‖₊ :=
  norm_le_norm_of_nonneg_of_le ha hab
/-
**CStarAlgebra.star_left_conjugate_le_norm_smul** 是 Mathlib 中的一个引理，位于命名空间 `CStar
Algebra`。
形式化陈述：star_left_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `star_left_conjugate_le_conjugate`：star_left_conjugate_le_conjugate {a b 
: R} (hab : a <= b) (c : R) : star c * a * c <= star c * b * c
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用引理 `IsSelfAdjoint.le_algebraMap_norm_self`：IsSelfAdjoint.le_algebraMap_norm_
self {a : A} (ha : IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.inr_le_iff`：inr_le_iff (a b : A) (ha : IsSelfAdjoint a
· 使用定理 `IsSelfAdjoint.conjugate'`：conjugate' {x : R} (hx : IsSelfAdjoint x) (z :
 R) : IsSelfAdjoint (star z * x * z)
· 使用定理 `IsSelfAdjoint.smul`：smul [Star R] [Star A] [SMul R A] [StarModule R A] {
r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r 
• x)
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `IsSelfAdjoint.all`：all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint 
r
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unitization.inr_mul`：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [
SMulWithZero R A] (a₁ a₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
· 使用定理 `Unitization.inr_star`：inr_star [AddMonoid R] [StarAddMonoid R] [Star A] 
(a : A) : ↑(star a) = star (a : Unitization R A)
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
· 使用定理 `IsSelfAdjoint.inr`：∀ (R : Type u_1) {A : Type u_2} [inst : Semiring R] [
inst_1 : StarAddMonoid R] [inst_2 : Star A] {a : A},   IsSelfAdjoint a → IsSelfA
djoint …
-/
lemma star_left_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    star a * b * a ≤ ‖b‖ • (star a * a) := by
  suffices ∀ a b : A⁺¹, IsSelfAdjoint b → star a * b * a ≤ ‖b‖ • (star a * a) by
    rw [← Unitization.inr_le_iff _ _ (by aesop) ((IsSelfAdjoint.all _).smul (.star_mul_self a))]
    simpa [Unitization.norm_inr] using this a b <| hb.inr ℂ
  intro a b hb
  calc
    star a * b * a ≤ star a * (algebraMap ℝ A⁺¹ ‖b‖) * a :=
      star_left_conjugate_le_conjugate hb.le_algebraMap_norm_self _
    _ = ‖b‖ • (star a * a) := by simp [Algebra.algebraMap_eq_smul_one]
/-
**CStarAlgebra.star_right_conjugate_le_norm_smul** 是 Mathlib 中的一个引理，位于命名空间 `CSta
rAlgebra`。
形式化陈述：star_right_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `CStarAlgebra.star_left_conjugate_le_norm_smul`：star_left_conjugate_le_no
rm_smul {a b : A} (hb : IsSelfAdjoint b
-/
lemma star_right_conjugate_le_norm_smul {a b : A} (hb : IsSelfAdjoint b := by cfc_tac) :
    a * b * star a ≤ ‖b‖ • (a * star a) := by
  simpa using star_left_conjugate_le_norm_smul (a := star a)

/-- The set of nonnegative elements in a C⋆-algebra is closed. -/
/-
**CStarAlgebra.isClosed_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：isClosed_nonneg : IsClosed {a : A | 0 <= a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `SpectrumRestricts.nnreal_iff_nnnorm`：SpectrumRestricts.nnreal_iff_nnnorm
 {a : A} {t : Real>=0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ <= t) : SpectrumRestric
ts a ContinuousMap.realTo…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.star`：Continuous.star (hf : Continuous f) : Continuous fun x 
=> star (f x)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `Continuous.nnnorm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous 
fun x =…
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The set of nonnegative elements in a C⋆-algebra is closed.
-/
lemma isClosed_nonneg : IsClosed {a : A | 0 ≤ a} := by
  suffices IsClosed {a : A⁺¹ | 0 ≤ a} by
    rw [Unitization.isometry_inr (𝕜 := ℂ) |>.isClosedEmbedding.isClosed_iff_image_isClosed]
    convert! this.inter <| (Unitization.isometry_inr (𝕜 := ℂ)).isClosedEmbedding.isClosed_range
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_range,
      ← exists_and_left]
    congr! 2 with x
    exact and_congr_left fun h ↦ by simp [← h]
  simp only [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts,
    and_congr_right (SpectrumRestricts.nnreal_iff_nnnorm · le_rfl), Set.ofPred_and]
  refine isClosed_eq ?_ ?_ |>.inter <| isClosed_le ?_ ?_
  all_goals fun_prop
/-
**CStarAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderClosedTopology A where
  isClosed_le' := isClosed_le_of_isClosed_nonneg isClosed_nonneg

open Unitization in
/-
**CStarAlgebra.convexOn_cfc** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convexOn_cfcₙ_of_convexOn_cfc {f : ℝ → ℝ} {s : Set A}
    (hf : ConvexOn ℝ (inr (R := ℂ) '' s) (cfc f)) : ConvexOn ℝ s (cfcₙ f) := by
  let inrl : A →ₗ[ℝ] A⁺¹ := inrHom ℝ ℂ A
  by_cases hf₀ : f 0 = 0
  case neg =>
    have : (cfcₙ f : A → A) = fun _ => 0 := by
      ext x
      simp [cfcₙ_apply_of_not_map_zero _ hf₀]
    rw [this]
    refine convexOn_const _ ?_
    have : Convex ℝ (inrl ⁻¹' inrl '' s) := Convex.linear_preimage hf.1 _
    rwa [Set.preimage_image_eq _ inrHom_injective] at this
  refine convexOn_of_convexOn_inr_comp (fun _ => IsSelfAdjoint.cfcₙ) ?_
  have h₁ : inr (R := ℂ) ∘ (cfcₙ f) = fun x : A => ((cfcₙ f x : A) : A⁺¹) := rfl
  have h₂ : (fun x : A => ((cfcₙ f x : A) : A⁺¹))
      = fun x : A => cfc f (x : A⁺¹) := by ext1; rw [real_cfcₙ_eq_cfc_inr ..]
  rw [h₁, h₂]
  have h₃ : ConvexOn ℝ (inrl ⁻¹' inrl '' s) ((cfc f) ∘ inrl) :=
    ConvexOn.comp_linearMap (g := inrl) hf
  rwa [Set.preimage_image_eq _ inrHom_injective] at h₃

open Unitization in
/-
**CStarAlgebra.concaveOn_cfc** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma concaveOn_cfcₙ_of_concaveOn_cfc {f : ℝ → ℝ} {s : Set A}
    (hf : ConcaveOn ℝ (inr (R := ℂ) '' s) (cfc f)) : ConcaveOn ℝ s (cfcₙ f) := by
  have : ConcaveOn ℝ s (- -cfcₙ f) := by
    rw [← cfcₙ_neg' f]
    refine (convexOn_cfcₙ_of_convexOn_cfc ?_).neg
    rw [cfc_neg']
    exact hf.neg
  simpa using this

section Icc

open Unitization Set Metric

/-
**CStarAlgebra.inr_mem_Icc_iff_norm_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：inr_mem_Icc_iff_norm_le {x : A} : (x : A⁺¹) in Icc 0 1 ↔ 0 <= x ∧ ‖x‖ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
· 使用引理 `Unitization.inr_nonneg_iff`：inr_nonneg_iff {a : A} : 0 <= (a : A⁺¹) ↔ 0 
<= a
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用引理 `CStarAlgebra.norm_le_one_iff_of_nonneg`：norm_le_one_iff_of_nonneg (a : A
) (ha : 0 <= a
-/
lemma inr_mem_Icc_iff_norm_le {x : A} :
    (x : A⁺¹) ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖ ≤ 1 := by
  simp only [mem_Icc, inr_nonneg_iff, and_congr_right_iff]
  rw [← norm_inr (𝕜 := ℂ), ← inr_nonneg_iff, iff_comm]
  exact (norm_le_one_iff_of_nonneg _ ·)
/-
**CStarAlgebra.inr_mem_Icc_iff_nnnorm_le** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra
`。
形式化陈述：inr_mem_Icc_iff_nnnorm_le {x : A} : (x : A⁺¹) in Icc 0 1 ↔ 0 <= x ∧ ‖x‖₊ <
= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CStarAlgebra.inr_mem_Icc_iff_norm_le`：inr_mem_Icc_iff_norm_le {x : A} : 
(x : A⁺¹) in Icc 0 1 ↔ 0 <= x ∧ ‖x‖ <= 1
-/
lemma inr_mem_Icc_iff_nnnorm_le {x : A} :
    (x : A⁺¹) ∈ Icc 0 1 ↔ 0 ≤ x ∧ ‖x‖₊ ≤ 1 :=
  inr_mem_Icc_iff_norm_le
/-
**CStarAlgebra.preimage_inr_Icc_zero_one** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra
`。
形式化陈述：preimage_inr_Icc_zero_one : ((↑) : A -> A⁺¹) ⁻¹' Icc 0 1 = {x : A | 0 <= x
} inter closedBall 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_inr_Icc_zero_one :
    ((↑) : A → A⁺¹) ⁻¹' Icc 0 1 = {x : A | 0 ≤ x} ∩ closedBall 0 1 := by
  ext
  simp [-mem_Icc, inr_mem_Icc_iff_norm_le]
/-
**CStarAlgebra.inr_map_Ici_zero** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：inr_map_Ici_zero : inr '' (Ici (0 : A)) subseteq Ici (0 : A⁺¹)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Unitization.inr_nonneg_iff`：inr_nonneg_iff {a : A} : 0 <= (a : A⁺¹) ↔ 0 
<= a
-/
lemma inr_map_Ici_zero : inr '' (Ici (0 : A)) ⊆ Ici (0 : A⁺¹) := by
  rintro - ⟨a, ha, rfl⟩
  exact Unitization.inr_nonneg_iff.mpr ha

end Icc

end CStarAlgebra

open CStarAlgebra Unitization CFC in
/-
**IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le {a e : A} (he : Is
StarProjection e) (ha : 0 <= a) (hae : a <= e) : a * e = a ∧ e * a = a
参数：he : IsStarProjection e；ha : 0 <= a；hae : a <= e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `CFC.norm_star_mul_mul_self_of_nonneg`：norm_star_mul_mul_self_of_nonneg {
a : A} (b : A) (ha : 0 <= a
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `star_left_conjugate_le_conjugate`：star_left_conjugate_le_conjugate {a b 
: R} (hab : a <= b) (c : R) : star c * a * c <= star c * b * c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `IsStarProjection.mul_one_sub_self`：mul_one_sub_self [Star R] (hp : IsSta
rProjection p) : p * (1 - p) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `star_left_conjugate_nonneg`：star_left_conjugate_nonneg {a : R} (ha : 0 <
= a) (c : R) : 0 <= star c * a * c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 46 条，此处仅展示前 30 条）
-/
lemma IsStarProjection.mul_right_and_mul_left_of_nonneg_of_le {a e : A}
    (he : IsStarProjection e) (ha : 0 ≤ a) (hae : a ≤ e) : a * e = a ∧ e * a = a := by
  suffices a * e = a from
    ⟨this, by simpa [ha.star_eq, he.isSelfAdjoint.star_eq] using congr(star $this)⟩
  suffices ∀ a e : A⁺¹, IsStarProjection e → 0 ≤ a → a ≤ e → a * e = a from
    mod_cast this a e he.inr ha.inr (inr_le_iff a e |>.mpr hae)
  intro a e he ha hae
  suffices sqrt a * (1 - e : A⁺¹) = 0 by
    simpa [← mul_assoc, sqrt_mul_sqrt_self a, mul_sub, sub_eq_zero, eq_comm (a := a)]
      using congr(sqrt a * $this)
  rw [← norm_eq_zero, ← sq_eq_zero_iff, ← norm_star_mul_mul_self_of_nonneg, norm_eq_zero]
  refine le_antisymm ?_ <| star_left_conjugate_nonneg ha _
  grw [star_left_conjugate_le_conjugate hae (1 - e), mul_assoc, he.mul_one_sub_self, mul_zero]
/-
**IsStarProjection.conjugate_of_nonneg_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStarProjection.conjugate_of_nonneg_of_le {a e : A} (he : IsStarProjectio
n e) (ha : 0 <= a) (hae : a <= e) : e * a * e = a
参数：he : IsStarProjection e；ha : 0 <= a；hae : a <= e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsStarProjection.conjugate_of_nonneg_of_le {a e : A} (he : IsStarProjection e)
    (ha : 0 ≤ a) (hae : a ≤ e) : e * a * e = a := by
  grind [he.mul_right_and_mul_left_of_nonneg_of_le ha hae]

end CStar_nonunital

section Pow

namespace CStarAlgebra

variable {A : Type*} {B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-
**CStarAlgebra.pow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：pow_nonneg {a : A} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
· 使用引理 `cfc_nonneg_of_predicate`：cfc_nonneg_of_predicate [LE A] [ContinuousFunct
ionalCalculus R A (0 <= ·)] {f : R -> R} {a : A} : 0 <= cfc f a
-/
lemma pow_nonneg {a : A} (ha : 0 ≤ a := by cfc_tac) (n : ℕ) : 0 ≤ a ^ n := by
  rw [← cfc_pow_id (R := ℝ≥0) a]
  exact cfc_nonneg_of_predicate
/-
**CStarAlgebra.pow_monotone** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：pow_monotone {a : A} (ha : 1 <= a) : Monotone (a ^ · : Nat -> A)
参数：ha : 1 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `instZeroLEOneClass`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : Parti
alOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   ZeroLEOneClass R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `cfc_le_iff`：cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spec
trum R a)
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `CFC.one_le_iff`：CFC.one_le_iff (a : A) (ha : p a
-/
lemma pow_monotone {a : A} (ha : 1 ≤ a) : Monotone (a ^ · : ℕ → A) := by
  have ha' : 0 ≤ a := zero_le_one.trans ha
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := ℝ) a, ← cfc_pow_id (R := ℝ) a, cfc_le_iff ..]
  rw [CFC.one_le_iff (R := ℝ) a] at ha
  peel ha with x hx _
  exact pow_le_pow_right₀ (ha x hx) hnm
/-
**CStarAlgebra.pow_antitone** 是 Mathlib 中的一个引理，位于命名空间 `CStarAlgebra`。
形式化陈述：pow_antitone {a : A} (ha₀ : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `cfc_le_iff`：cfc_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (spec
trum R a)
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
· 使用引理 `CFC.le_one_iff`：CFC.le_one_iff (a : A) (ha : p a
-/
lemma pow_antitone {a : A} (ha₀ : 0 ≤ a := by cfc_tac) (ha₁ : a ≤ 1) :
    Antitone (a ^ · : ℕ → A) := by
  intro n m hnm
  simp only
  rw [← cfc_pow_id (R := ℝ) a, ← cfc_pow_id (R := ℝ) a, cfc_le_iff ..]
  rw [CFC.le_one_iff (R := ℝ) a] at ha₁
  peel ha₁ with x hx _
  exact pow_le_pow_of_le_one (spectrum_nonneg_of_nonneg ha₀ hx) (ha₁ x hx) hnm

end CStarAlgebra

end Pow

