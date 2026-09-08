/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Continuous linear maps on a Hilbert space are a `StarOrderedRing`

In this file we show that the continuous linear maps on a complex Hilbert space form a
`StarOrderedRing`.  Note that they are already equipped with the Loewner partial order. We also
prove that, with respect to this partial order, a map is positive if every element of the
real spectrum is nonnegative. Consequently, when `H` is a Hilbert space, then `H →L[ℂ] H` is
equipped with all the usual instances of the continuous functional calculus.

-/

public section

namespace ContinuousLinearMap

open RCLike
open scoped NNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]

open scoped InnerProductSpace in
/-
**ContinuousLinearMap.IsPositive.spectrumRestricts** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap.IsPositive`。
形式化陈述：∀ {𝕜 : Type u_1} {H : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommG
roup H] [inst_2 : InnerProductSpace 𝕜 H]   [CompleteSpace H] [inst_4 : Algebra ℝ
 (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] {f : H →L[𝕜] H},   f.IsPositive → 
SpectrumRestricts f ⇑ContinuousMap.realToNNReal
参数：H →L[𝕜] H；H →L[𝕜] H。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `spectrum.notMem_iff`：notMem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r
 - a)
· 使用定理 `IsUnit.sub_iff`：IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsU
nit (y - x)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`：isUnit_of_forall
_le_norm_inner_map [CompleteSpace E] (f : E ->L[𝕜] E) {c : Real>=0} (hc : 0 < c)
 (h : forall x, ‖x‖ ^ 2 * c <= ‖⟪f x, x⟫_𝕜‖)…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RCLike.algebraMap_eq_ofReal`：algebraMap_eq_ofReal : ⇑(algebraMap Real K)
 = ofReal
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `RCLike.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : K) : re (↑r * z) = r
 * re z
（共 48 条，此处仅展示前 30 条）
-/
lemma IsPositive.spectrumRestricts {f : H →L[𝕜] H} (hf : f.IsPositive) :
    SpectrumRestricts f ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.notMem_iff, IsUnit.sub_iff, sub_eq_add_neg, ← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_norm_inner_map _ (c := ⟨c, hc.le⟩) hc fun x ↦ calc
    ‖x‖ ^ 2 * c = re ⟪algebraMap ℝ (H →L[𝕜] H) c x, x⟫_𝕜 := by
      rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul 𝕜 c (1 : (H →L[𝕜] H)), smul_apply,
        one_apply_eq_self, inner_smul_left, RCLike.algebraMap_eq_ofReal, conj_ofReal, re_ofReal_mul,
        inner_self_eq_norm_sq, mul_comm]
    _ ≤ re ⟪(f + (algebraMap ℝ (H →L[𝕜] H)) c) x, x⟫_𝕜 := by
      simpa only [add_apply, inner_add_left, map_add, le_add_iff_nonneg_left]
        using hf.re_inner_nonneg_left x
    _ ≤ ‖⟪(f + (algebraMap ℝ (H →L[𝕜] H)) c) x, x⟫_𝕜‖ := RCLike.re_le_norm _
/-
**ContinuousLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonnegSpectrumClass ℝ (H →L[𝕜] H) where
  quasispectrum_nonneg_of_nonneg f hf :=
    QuasispectrumRestricts.nnreal_iff.mp <| sub_zero f ▸ hf.spectrumRestricts

/-- Because this takes `ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint` as an argument,
and for the moment we only have this for `𝕜 := ℂ`, this is not registered as an instance. -/
/-
**ContinuousLinearMap.instStarOrderedRingRCLike** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：instStarOrderedRingRCLike [ContinuousFunctionalCalculus Real (H ->L[𝕜] H) 
IsSelfAdjoint] : StarOrderedRing (H ->L[𝕜] H) where le_iff f g
参数：H ->L[𝕜] H。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts`：CFC.exists_s
qrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A] [St
arRing A] [TopologicalSpace A] [Module Real A] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.IsPositive.isSelfAdjoint`：∀ {𝕜 : Type u_1} {E : Type
 u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   [inst_3 : CompleteSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousLinearMap.le_def`：le_def (f g : E ->L[𝕜] E) : f <= g ↔ (g - f)
.IsPositive
· 使用定理 `ContinuousLinearMap.IsPositive.spectrumRestricts`：∀ {𝕜 : Type u_1} {H : 
Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup H] [inst_2 : InnerProdu
ctSpace 𝕜 H]   [CompleteSpace H] [inst…
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `ContinuousLinearMap.IsPositive.adjoint_conj`：∀ {𝕜 : Type u_1} {E : Type 
u_2} {F : Type u_3} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedAddCommGroup F] [inst_3 :…
· 使用定理 `ContinuousLinearMap.isPositive_one`：isPositive_one : IsPositive (1 : E -
>L[𝕜] E)
· 使用定理 `ContinuousLinearMap.isPositive_zero`：isPositive_zero : IsPositive (0 : E
 ->L[𝕜] E)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Because this takes `ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint` as
 an argument,
and for the moment we only have this for `𝕜 := ℂ`, this is not registered as an 
instance.
-/
lemma instStarOrderedRingRCLike
    [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint] :
    StarOrderedRing (H →L[𝕜] H) where
  le_iff f g := by
    constructor
    · intro h
      rw [le_def] at h
      obtain ⟨p, hp₁, -, hp₃⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
        h.isSelfAdjoint h.spectrumRestricts
      refine ⟨p ^ 2, ?_, by symm; rwa [add_comm, ← eq_sub_iff_add_eq]⟩
      exact AddSubmonoid.subset_closure ⟨p, by simp only [hp₁.star_eq, sq]⟩
    · rintro ⟨p, hp, rfl⟩
      rw [le_def, add_sub_cancel_left]
      induction hp using AddSubmonoid.closure_induction with
      | mem _ hf =>
        obtain ⟨f, rfl⟩ := hf
        simpa using! ContinuousLinearMap.IsPositive.adjoint_conj isPositive_one f
      | zero => exact isPositive_zero
      | add f g _ _ hf hg => exact hf.add hg
/-
**ContinuousLinearMap.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：instStarOrderedRing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 
Complex H] [CompleteSpace H] : StarOrderedRing (H ->L[Complex] H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.instStarOrderedRingRCLike`：instStarOrderedRingRCLike
 [ContinuousFunctionalCalculus Real (H ->L[𝕜] H) IsSelfAdjoint] : StarOrderedRin
g (H ->L[𝕜] H) where le_iff f g
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
instance instStarOrderedRing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : StarOrderedRing (H →L[ℂ] H) :=
  instStarOrderedRingRCLike

end ContinuousLinearMap

