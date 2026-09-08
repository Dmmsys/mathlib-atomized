/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.Simple
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Finite-dimensional topological vector spaces over complete fields

Let `𝕜` be a complete nontrivially normed field, and `E` a topological vector space (TVS) over
`𝕜` (i.e we have `[AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]`
and `[ContinuousSMul 𝕜 E]`).

If `E` is finite dimensional and Hausdorff, then all linear maps from `E` to any other TVS are
continuous.

When `E` is a normed space, this gets us the equivalence of norms in finite dimension.

## Main results :

* `LinearMap.continuous_iff_isClosed_ker` : a linear form is continuous if and only if its kernel
  is closed.
* `LinearMap.continuous_of_finiteDimensional` : a linear map on a finite-dimensional Hausdorff
  space over a complete field is continuous.

## TODO

Generalize more of `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` to general TVSs.

## Implementation detail

The main result from which everything follows is the fact that, if `ξ : ι → E` is a finite basis,
then `ξ.equivFun : E →ₗ (ι → 𝕜)` is continuous. However, for technical reasons, it is easier to
prove this when `ι` and `E` live in the same universe. So we start by doing that as a private
lemma, then we deduce `LinearMap.continuous_of_finiteDimensional` from it, and then the general
result follows as `continuous_equivFun_basis`.

-/

@[expose] public section

open Filter Module Set TopologicalSpace Topology

universe u v w x

noncomputable section

section FiniteDimensional

variable {𝕜 E F : Type*}
  [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]

-- Note: ideally this would be in `Mathlib.Topology.Algebra.Module.Basic`, but `CoFG` imports
-- too much at the moment for this to be allowed.
/-
**Submodule.CoFG.topologicalClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.CoFG.topologicalClosure [Ring 𝕜] [Module 𝕜 E] [ContinuousAdd E] 
[ContinuousConstSMul 𝕜 E] (s : Submodule 𝕜 E) [s.CoFG] : s.topologicalClosure.Co
FG
参数：s : Submodule 𝕜 E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.CoFG.of_le`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Submodule R M}, S 
≤ T → S.Co…
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure
-/
instance Submodule.CoFG.topologicalClosure [Ring 𝕜] [Module 𝕜 E] [ContinuousAdd E]
    [ContinuousConstSMul 𝕜 E] (s : Submodule 𝕜 E) [s.CoFG] : s.topologicalClosure.CoFG :=
  ‹s.CoFG›.of_le s.le_topologicalClosure

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
/-
**ContinuousLinearMap.instModuleFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.instModuleFinite [CommRing 𝕜] [Module 𝕜 E] [Module.Fin
ite 𝕜 E] [Module 𝕜 F] [IsNoetherian 𝕜 F] [ContinuousConstSMul 𝕜 F] : Module.Fini
te 𝕜 (E ->L[𝕜] F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_injective`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_
3} {N : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommM
onoid M] [inst_3…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)

--- 原说明 ---
The space of continuous linear maps between finite-dimensional spaces is finite-
dimensional.
-/
instance ContinuousLinearMap.instModuleFinite [CommRing 𝕜] [Module 𝕜 E] [Module.Finite 𝕜 E]
    [Module 𝕜 F] [IsNoetherian 𝕜 F] [ContinuousConstSMul 𝕜 F] :
    Module.Finite 𝕜 (E →L[𝕜] F) :=
  .of_injective (ContinuousLinearMap.coeLM 𝕜 : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional.

This theorem is here to match searches looking for `FiniteDimensional` instead of `Module.Finite`.
We use a strictly more general `ContinuousLinearMap.instModuleFinite` as an instance. -/
/-
**ContinuousLinearMap.finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : AddCommGroup E] [in
st_1 : TopologicalSpace E]   [inst_2 : AddCommGroup F] [inst_3 : TopologicalSpac
e F] [inst_4 : IsTopologicalAddGroup F] [inst_5 : Field 𝕜]   [inst_6 : _root_.Mo
dule 𝕜 E] [FiniteDimensional 𝕜 E] [inst_8 : _root_.Module 𝕜 F] [FiniteDimensiona
l 𝕜 F]   [inst_10 : ContinuousConstSMul 𝕜 F], FiniteDimensional 𝕜 (E →L[𝕜] F)
参数：E →L[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R

--- 原说明 ---
The space of continuous linear maps between finite-dimensional spaces is finite-
dimensional.

This theorem is here to match searches looking for `FiniteDimensional` instead o
f `Module.Finite`.
We use a strictly more general `ContinuousLinearMap.instModuleFinite` as an inst
ance.
-/
protected theorem ContinuousLinearMap.finiteDimensional [Field 𝕜] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [Module 𝕜 F] [FiniteDimensional 𝕜 F] [ContinuousConstSMul 𝕜 F] :
    FiniteDimensional 𝕜 (E →L[𝕜] F) :=
  inferInstance

end FiniteDimensional

section NormedField

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [IsTopologicalAddGroup F']
  [ContinuousSMul 𝕜 F']

/-- If `𝕜` is a nontrivially normed field, any T2 topology on `𝕜` which makes it a topological
vector space over itself (with the norm topology) is *equal* to the norm topology. -/
/-
**unique_topology_of_t2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @IsTopologicalAddGrou
p 𝕜 t _) (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) 
(h₃ : @T2Space 𝕜 t) : t = hnorm.toUniformSpace.toTopologicalSpace
参数：h₁ : @IsTopologicalAddGroup 𝕜 t _；h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformS
pace.toTopologicalSpace t；h₃ : @T2Space 𝕜 t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {t t' : 
TopologicalSpace G},   IsTopologicalAddGroup G → IsTopologicalAddGroup G → nhds 
0 = nhds 0 → t …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `balancedCore_mem_nhds_zero`：balancedCore_mem_nhds_zero (hU : U in 𝓝 (0 :
 E)) : balancedCore 𝕜 U in 𝓝 (0 : E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.mem_closedBall_self`：mem_closedBall_self (h : 0 <= ε) : x in clos
edBall x ε
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Balanced.smul_mem`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRin
g 𝕜] [inst_1 : SMul 𝕜 E] {s : Set E},   Balanced 𝕜 s → ∀ ⦃a : 𝕜⦄, ‖a‖ ≤ 1 → ∀ ⦃x
 : E⦄, …
· 使用定理 `balancedCore_balanced`：balancedCore_balanced (s : Set E) : Balanced 𝕜 (b
alancedCore 𝕜 s)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `mul_inv_le_iff₀`：mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= a * 
c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If `𝕜` is a nontrivially normed field, any T2 topology on `𝕜` which makes it a t
opological
vector space over itself (with the norm topology) is *equal* to the norm topolog
y.
-/
theorem unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @IsTopologicalAddGroup 𝕜 t _)
    (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace := by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine IsTopologicalAddGroup.ext h₁ inferInstance (le_antisymm ?_ ?_)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [Metric.nhds_basis_closedBall.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nontrivially normed, we have `0 < ‖ξ₀‖ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedField.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := IsOpen.mem_nhds isOpen_compl_singleton <|
      mem_compl_singleton_iff.mpr <| Ne.symm <| norm_ne_zero_iff.mp hξ₀.ne.symm
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : balancedCore 𝕜 {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := balancedCore_mem_nhds_zero this
    refine mem_of_superset this fun ξ hξ => ?_
    -- Let `ξ ∈ 𝓑`. We want to show `‖ξ‖ < ε`. If `ξ = 0`, this is trivial.
    by_cases hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closedBall_self hε.le
    · rw [mem_closedBall_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ‖ξ‖`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra! h
      suffices (ξ₀ * ξ⁻¹) • ξ ∈ balancedCore 𝕜 {ξ₀}ᶜ by
        rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hξ0, mul_one] at this
        exact notMem_compl_iff.mpr (mem_singleton ξ₀) ((balancedCore_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `‖ξ₀‖ < ε < ‖ξ‖`, we have `‖ξ₀ / ξ‖ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine (balancedCore_balanced _).smul_mem ?_ hξ
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.mpr hξ0), one_mul]
      exact (hξ₀ε.trans h).le
  · -- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (fun x ↦ x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0 =
          map id (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) :=
        map_id.symm
      _ = map (fun x => id x • (1 : 𝕜)) (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) := by
        simp
      _ ≤ @nhds 𝕜 t ((0 : 𝕜) • (1 : 𝕜)) :=
        (@Tendsto.smul_const _ _ _ hnorm.toUniformSpace.toTopologicalSpace t _ _ _ _ _
          tendsto_id (1 : 𝕜))
      _ = @nhds 𝕜 t 0 := by rw [zero_smul]

/-- Any linear form on a topological vector space over a nontrivially normed field is continuous if
its kernel is closed. -/
/-
**LinearMap.continuous_of_isClosed_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_of_isClosed_ker (l : E ->ₗ[𝕜] 𝕜) (hl : IsClosed (Line
arMap.ker l : Set E)) : Continuous l
参数：l : E ->ₗ[𝕜] 𝕜；hl : IsClosed (LinearMap.ker l : Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_bot`：range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ 
↔ f = 0
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ker_liftQ_eq_bot`：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h
' : ker f <= p) : ker (p.liftQ f h) = ⊥
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `unique_topology_of_t2`：unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h
₁ : @IsTopologicalAddGroup 𝕜 t _) (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpa
ce.toTopolo…
· 使用定理 `topologicalAddGroup_induced`：∀ {G : Type w} {H : Type x} [inst : Topolog
icalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {F : Type u_1}   [i
nst_3 : AddGroup …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `continuousSMul_induced`：continuousSMul_induced : @ContinuousSMul R M₁ _ 
u (t.induced f)
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Any linear form on a topological vector space over a nontrivially normed field i
s continuous if
its kernel is closed.
-/
theorem LinearMap.continuous_of_isClosed_ker (l : E →ₗ[𝕜] 𝕜)
    (hl : IsClosed (LinearMap.ker l : Set E)) :
    Continuous l := by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 (LinearMap.range l) = 1 :=
      le_antisymm (finrank_self 𝕜 ▸ (LinearMap.range l).finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _)
    have hs : Function.Surjective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
      exact Submodule.eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ LinearMap.ker l) ≃ₗ[𝕜] 𝕜 :=
      LinearEquiv.ofBijective ((LinearMap.ker l).liftQ l (le_refl _)) ⟨hi, hs⟩
    have hlφ : (l : E → 𝕜) = φ ∘ (LinearMap.ker l).mkQ := by ext; rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.toEquiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.toEquiv.symm inferInstance = hnorm.toUniformSpace.toTopologicalSpace := by
      refine unique_topology_of_t2 (topologicalAddGroup_induced φ.symm.toLinearMap)
        (continuousSMul_induced φ.symm.toMulActionHom) ?_
      rw [t2Space_iff]
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _
          (φ.toEquiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    simp_rw +instances [this.symm, Equiv.induced_symm]
    exact continuous_coinduced_rng

/-- Any linear form on a topological vector space over a nontrivially normed field is continuous if
and only if its kernel is closed. -/
/-
**LinearMap.continuous_iff_isClosed_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_iff_isClosed_ker (l : E ->ₗ[𝕜] 𝕜) : Continuous l ↔ Is
Closed (LinearMap.ker l : Set E)
参数：l : E ->ₗ[𝕜] 𝕜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LinearMap.continuous_of_isClosed_ker`：LinearMap.continuous_of_isClosed_k
er (l : E ->ₗ[𝕜] 𝕜) (hl : IsClosed (LinearMap.ker l : Set E)) : Continuous l

--- 原说明 ---
Any linear form on a topological vector space over a nontrivially normed field i
s continuous if
and only if its kernel is closed.
-/
theorem LinearMap.continuous_iff_isClosed_ker (l : E →ₗ[𝕜] 𝕜) :
    Continuous l ↔ IsClosed (LinearMap.ker l : Set E) :=
  ⟨fun h => isClosed_singleton.preimage h, l.continuous_of_isClosed_ker⟩

/-- Over a nontrivially normed field, any linear form which is nonzero on a nonempty open set is
automatically continuous. -/
/-
**LinearMap.continuous_of_nonzero_on_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_of_nonzero_on_open (l : E ->ₗ[𝕜] 𝕜) (s : Set E) (hs₁ 
: IsOpen s) (hs₂ : s.Nonempty) (hs₃ : forall x in s, l x != 0) : Continuous l
参数：l : E ->ₗ[𝕜] 𝕜；s : Set E；hs₁ : IsOpen s；hs₂ : s.Nonempty；hs₃ : forall x in s,
 l x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_isClosed_ker`：LinearMap.continuous_of_isClosed_k
er (l : E ->ₗ[𝕜] 𝕜) (hl : IsClosed (LinearMap.ker l : Set E)) : Continuous l
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `LinearMap.isClosed_or_dense_ker`：LinearMap.isClosed_or_dense_ker (l : M 
->ₗ[R] N) : IsClosed (LinearMap.ker l : Set M) ∨ Dense (LinearMap.ker l : Set M)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Dense.interior_compl`：Dense.interior_compl (h : Dense s) : interior sᶜ =
 ∅

--- 原说明 ---
Over a nontrivially normed field, any linear form which is nonzero on a nonempty
 open set is
automatically continuous.
-/
theorem LinearMap.continuous_of_nonzero_on_open (l : E →ₗ[𝕜] 𝕜) (s : Set E) (hs₁ : IsOpen s)
    (hs₂ : s.Nonempty) (hs₃ : ∀ x ∈ s, l x ≠ 0) : Continuous l := by
  refine l.continuous_of_isClosed_ker (l.isClosed_or_dense_ker.resolve_right fun hl => ?_)
  rcases hs₂ with ⟨x, hx⟩
  have : x ∈ interior (LinearMap.ker l : Set E)ᶜ := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hs₁.mem_nhds hx) hs₃
  rwa [hl.interior_compl] at this

variable [CompleteSpace 𝕜]

/-- This version imposes `ι` and `E` to live in the same universe, so you should instead use
`continuous_equivFun_basis` which gives the same result without universe restrictions. -/
/-
**continuous_equivFun_basis_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This version imposes `ι` and `E` to live in the same universe, so you should ins
tead use
`continuous_equivFun_basis` which gives the same result without universe restric
tions.
-/
private theorem continuous_equivFun_basis_aux [T2Space E] {ι : Type v} [Finite ι]
    (ξ : Basis ι 𝕜 E) : Continuous ξ.equivFun := by
  have := Fintype.ofFinite ι
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  suffices ∀ n, Fintype.card ι = n → Continuous ξ.equivFun by exact this _ rfl
  intro n hn
  induction n generalizing ι E with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at hn
    exact continuous_of_const fun x y => funext hn.elim
  | succ n IH =>
    have : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀ s : Submodule 𝕜 E, finrank 𝕜 s = n → IsClosed (s : Set E) := by
      intro s s_dim
      let : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
      let b := Basis.ofVectorSpace 𝕜 s
      have U : IsUniformEmbedding b.equivFun.symm.toEquiv := by
        have : Fintype.card (Basis.ofVectorSpaceIndex 𝕜 s) = n := by
          rw [← s_dim]
          exact (finrank_eq_card_basis b).symm
        have : Continuous b.equivFun := IH b inferInstance this
        exact
          b.equivFun.symm.isUniformEmbedding b.equivFun.symm.toLinearMap.continuous_on_pi this
      have : IsComplete (s : Set E) :=
        completeSpace_coe_iff_isComplete.1 ((completeSpace_congr U).1 inferInstance)
      exact this.isClosed
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f := by
      intro f
      by_cases H : finrank 𝕜 (LinearMap.range f) = 0
      · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
        rw [H]
        exact continuous_zero
      · have : finrank 𝕜 (LinearMap.ker f) = n := by
          have Z := f.finrank_range_add_finrank_ker
          rw [finrank_eq_card_basis ξ, hn] at Z
          have : finrank 𝕜 (LinearMap.range f) = 1 :=
            le_antisymm (finrank_self 𝕜 ▸ (LinearMap.range f).finrank_le) (zero_lt_iff.mpr H)
          rw [this, add_comm, Nat.add_one] at Z
          exact Nat.succ.inj Z
        have : IsClosed (LinearMap.ker f : Set E) := H₁ _ this
        exact LinearMap.continuous_of_isClosed_ker f this
    rw [continuous_pi_iff]
    intro i
    change Continuous (ξ.coord i)
    exact H₂ (ξ.coord i)

/-- A finite-dimensional t2 vector space over a complete field must carry the module topology.

Not declared as a global instance only for performance reasons. -/
@[local instance]
/-
**isModuleTopologyOfFiniteDimensional** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isModuleTopologyOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] : 
IsModuleTopology 𝕜 E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `_private.Mathlib.Topology.Algebra.Module.FiniteDimension.0.continuous_eq
uivFun_basis_aux`：∀ {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v
} [inst : AddCommGroup E] [inst_1 : _root_.Module 𝕜 E]   [inst_2 : Topological…
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsModuleTopology.iso`：∀ {R : Type u_1} [τR : TopologicalSpace R] [inst :
 Semiring R] {A : Type u_3} [inst_1 : AddCommMonoid A]   [inst_2 : _root_.Module
 R A] [τA …

--- 原说明 ---
A finite-dimensional t2 vector space over a complete field must carry the module
 topology.

Not declared as a global instance only for performance reasons.
-/
lemma isModuleTopologyOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    IsModuleTopology 𝕜 E :=
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equivFun_basis`, and
  -- use that it has the module topology
  let b := Basis.ofVectorSpace 𝕜 E
  have continuousEquiv : E ≃L[𝕜] (Basis.ofVectorSpaceIndex 𝕜 E) → 𝕜 :=
    { __ := b.equivFun
      continuous_toFun := continuous_equivFun_basis_aux b
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := 𝕜)
        (A := (Basis.ofVectorSpaceIndex 𝕜 E) → 𝕜) (B := E) b.equivFun.symm }
  IsModuleTopology.iso continuousEquiv.symm

/-- Any linear map on a finite-dimensional space over a complete field is continuous. -/
/-
**LinearMap.continuous_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.continuous_of_finiteDimensional [T2Space E] [FiniteDimensional 𝕜
 E] (f : E ->ₗ[𝕜] F') : Continuous f
参数：f : E ->ₗ[𝕜] F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.continuous_of_linearMap`：continuous_of_linearMap (φ : A
 ->ₗ[R] B) : Continuous φ
· 使用引理 `isModuleTopologyOfFiniteDimensional`：isModuleTopologyOfFiniteDimensional
 [T2Space E] [FiniteDimensional 𝕜 E] : IsModuleTopology 𝕜 E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G

--- 原说明 ---
Any linear map on a finite-dimensional space over a complete field is continuous
.
-/
theorem LinearMap.continuous_of_finiteDimensional [T2Space E] [FiniteDimensional 𝕜 E]
    (f : E →ₗ[𝕜] F') : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f
/-
**LinearMap.continuousLinearMapClassOfFiniteDimensional** 是 Mathlib 中的一个实例，位于命名空
间 ``。
形式化陈述：LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteD
imensional 𝕜 E] : ContinuousLinearMapClass (E ->ₗ[𝕜] F') 𝕜 E F'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
-/
instance LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    ContinuousLinearMapClass (E →ₗ[𝕜] F') 𝕜 E F' :=
  { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finiteDimensional }

/-- In finite dimensions over a non-discrete complete normed field, the canonical identification
(in terms of a basis) with `𝕜^n` (endowed with the product topology) is continuous.
This is the key fact which makes all linear maps from a T2 finite-dimensional TVS over such a field
continuous (see `LinearMap.continuous_of_finiteDimensional`), which in turn implies that all
norms are equivalent in finite dimensions. -/
/-
**continuous_equivFun_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_equivFun_basis [T2Space E] {ι : Type*} [Finite ι] (ξ : Basis ι 
𝕜 E) : Continuous ξ.equivFun
参数：ξ : Basis ι 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…

--- 原说明 ---
In finite dimensions over a non-discrete complete normed field, the canonical id
entification
(in terms of a basis) with `𝕜^n` (endowed with the product topology) is continuo
us.
This is the key fact which makes all linear maps from a T2 finite-dimensional TV
S over such a field
continuous (see `LinearMap.continuous_of_finiteDimensional`), which in turn impl
ies that all
norms are equivalent in finite dimensions.
-/
theorem continuous_equivFun_basis [T2Space E] {ι : Type*} [Finite ι] (ξ : Basis ι 𝕜 E) :
    Continuous ξ.equivFun :=
  haveI : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
  ξ.equivFun.toLinearMap.continuous_of_finiteDimensional

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite-dimensional space -/
/-
**LinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃ₗ[𝕜] E ->L[𝕜] F' where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f

--- 原说明 ---
The continuous linear map induced by a linear map on a finite-dimensional space
-/
def toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' where
  toFun f := ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl

/-- Algebra equivalence between the linear maps and continuous linear maps on a finite-dimensional
space. -/
/-
**LinearMap._root_.Module.End.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `L
inearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra equivalence between the linear maps and continuous linear maps on a fini
te-dimensional
space.
-/
def _root_.Module.End.toContinuousLinearMap (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : (E →ₗ[𝕜] E) ≃ₐ[𝕜] (E →L[𝕜] E) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

@[simp]
/-
**LinearMap.coe_toContinuousLinearMap'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_toContinuousLinearMap' (f : E ->ₗ[𝕜] F') : ⇑(LinearMap.toContinuousLin
earMap f) = f
参数：f : E ->ₗ[𝕜] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem coe_toContinuousLinearMap' (f : E →ₗ[𝕜] F') : ⇑(LinearMap.toContinuousLinearMap f) = f :=
  rfl

@[simp]
/-
**LinearMap.coe_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_toContinuousLinearMap (f : E ->ₗ[𝕜] F') : ((LinearMap.toContinuousLine
arMap f) : E ->ₗ[𝕜] F') = f
参数：f : E ->ₗ[𝕜] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem coe_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    ((LinearMap.toContinuousLinearMap f) : E →ₗ[𝕜] F') = f :=
  rfl

@[simp]
/-
**LinearMap.coe_toContinuousLinearMap_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：coe_toContinuousLinearMap_symm : ⇑(toContinuousLinearMap : (E ->ₗ[𝕜] F') ≃
ₗ[𝕜] E ->L[𝕜] F').symm = ((↑) : (E ->L[𝕜] F') -> E ->ₗ[𝕜] F')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem coe_toContinuousLinearMap_symm :
    ⇑(toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm =
      ((↑) : (E →L[𝕜] F') → E →ₗ[𝕜] F') :=
  rfl

@[simp]
/-
**LinearMap.det_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：det_toContinuousLinearMap (f : E ->ₗ[𝕜] E) : (LinearMap.toContinuousLinear
Map f).det = LinearMap.det f
参数：f : E ->ₗ[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem det_toContinuousLinearMap (f : E →ₗ[𝕜] E) :
    (LinearMap.toContinuousLinearMap f).det = LinearMap.det f :=
  rfl

/-- A surjective linear map `f` with finite-dimensional codomain is an open map. -/
/-
**LinearMap.isOpenMap_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：isOpenMap_of_finiteDimensional (f : F ->ₗ[𝕜] E) (hf : Function.Surjective 
f) : IsOpenMap f
参数：f : F ->ₗ[𝕜] E；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsModuleTopology.isOpenMap_of_surjective`：isOpenMap_of_surjective [Topol
ogicalSpace B] [IsModuleTopology R B] [ContinuousAdd A] [ContinuousSMul R A] {φ 
: A ->ₗ[R] B} (hφ : Function.S…
· 使用引理 `isModuleTopologyOfFiniteDimensional`：isModuleTopologyOfFiniteDimensional
 [T2Space E] [FiniteDimensional 𝕜 E] : IsModuleTopology 𝕜 E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G

--- 原说明 ---
A surjective linear map `f` with finite-dimensional codomain is an open map.
-/
theorem isOpenMap_of_finiteDimensional (f : F →ₗ[𝕜] E) (hf : Function.Surjective f) :
    IsOpenMap f :=
  IsModuleTopology.isOpenMap_of_surjective hf
/-
**LinearMap.canLiftContinuousLinearMap** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：canLiftContinuousLinearMap : CanLift (E ->ₗ[𝕜] F) (E ->L[𝕜] F) (↑) fun _ =
> True
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
instance canLiftContinuousLinearMap : CanLift (E →ₗ[𝕜] F) (E →L[𝕜] F) (↑) fun _ => True :=
  ⟨fun f _ => ⟨LinearMap.toContinuousLinearMap f, rfl⟩⟩
/-
**LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap** 是 Mathlib 中的一个引理，位于命名空
间 `LinearMap`。
形式化陈述：toContinuousLinearMap_eq_iff_eq_toLinearMap (f : E ->ₗ[𝕜] E) (g : E ->L[𝕜]
 E) : f.toContinuousLinearMap = g ↔ f = g.toLinearMap
参数：f : E ->ₗ[𝕜] E；g : E ->L[𝕜] E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toContinuousLinearMap_eq_iff_eq_toLinearMap (f : E →ₗ[𝕜] E) (g : E →L[𝕜] E) :
    f.toContinuousLinearMap = g ↔ f = g.toLinearMap := by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]
/-
**LinearMap._root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearM
ap** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap (g : E →L[𝕜] E)
    (f : E →ₗ[𝕜] E) : g.toLinearMap = f ↔ g = f.toContinuousLinearMap := by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

end LinearMap

section

variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

namespace LinearEquiv

/-- The continuous linear equivalence induced by a linear equivalence on a finite-dimensional
space. -/
/-
**LinearEquiv.toContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F
参数：e : E ≃ₗ[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear equivalence induced by a linear equivalence on a finite-di
mensional
space.
-/
def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
/-
**LinearEquiv.coe_toContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv
`。
形式化陈述：coe_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv :
 E ->ₗ[𝕜] F) = e
参数：e : E ≃ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E →ₗ[𝕜] F) = e :=
  rfl

@[simp]
/-
**LinearEquiv.coe_toContinuousLinearEquiv'** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v`。
形式化陈述：coe_toContinuousLinearEquiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv 
: E -> F) = e
参数：e : E ≃ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearEquiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E → F) = e :=
  rfl

@[simp]
/-
**LinearEquiv.coe_toContinuousLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Equiv`。
形式化陈述：coe_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEq
uiv.toLinearEquiv.symm : F ->ₗ[𝕜] E) = e.symm
参数：e : E ≃ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.toLinearEquiv.symm : F →ₗ[𝕜] E) = e.symm := rfl

@[simp]
/-
**LinearEquiv.coe_toContinuousLinearEquiv_symm'** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rEquiv`。
形式化陈述：coe_toContinuousLinearEquiv_symm' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearE
quiv.symm : F -> E) = e.symm
参数：e : E ≃ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearEquiv_symm' (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F → E) = e.symm :=
  rfl

@[simp]
/-
**LinearEquiv.toLinearEquiv_toContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `L
inearEquiv`。
形式化陈述：toLinearEquiv_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : e.toContinuousLine
arEquiv.toLinearEquiv = e
参数：e : E ≃ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem toLinearEquiv_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.toLinearEquiv = e := by
  ext x
  rfl
/-
**LinearEquiv.toLinearEquiv_toContinuousLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名
空间 `LinearEquiv`。
形式化陈述：toLinearEquiv_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) : e.toContinuou
sLinearEquiv.symm.toLinearEquiv = e.symm
参数：e : E ≃ₗ[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem toLinearEquiv_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.symm.toLinearEquiv = e.symm := by
  ext x
  rfl
/-
**LinearEquiv.canLiftContinuousLinearEquiv** 是 Mathlib 中的一个实例，位于命名空间 `LinearEqui
v`。
形式化陈述：canLiftContinuousLinearEquiv : CanLift (E ≃ₗ[𝕜] F) (E ≃L[𝕜] F) ContinuousL
inearEquiv.toLinearEquiv fun _ => True
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearEquiv_toContinuousLinearEquiv`：toLinearEquiv_toConti
nuousLinearEquiv (e : E ≃ₗ[𝕜] F) : e.toContinuousLinearEquiv.toLinearEquiv = e
-/
instance canLiftContinuousLinearEquiv :
    CanLift (E ≃ₗ[𝕜] F) (E ≃L[𝕜] F) ContinuousLinearEquiv.toLinearEquiv fun _ => True :=
  ⟨fun f _ => ⟨_, f.toLinearEquiv_toContinuousLinearEquiv⟩⟩

end LinearEquiv

variable [FiniteDimensional 𝕜 F]

/-- Two finite-dimensional topological vector spaces over a complete normed field are continuously
linearly equivalent if they have the same (finite) dimension. -/
/-
**FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (cond : fin
rank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F)
参数：cond : finrank 𝕜 E = finrank 𝕜 F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`：FiniteDimensional.
nonempty_linearEquiv_of_finrank_eq [Module.Finite R M] [Module.Finite R M'] (con
d : finrank R M = finrank R M') : Nonempty…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
Two finite-dimensional topological vector spaces over a complete normed field ar
e continuously
linearly equivalent if they have the same (finite) dimension.
-/
theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linearEquiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

/-- Two finite-dimensional topological vector spaces over a complete normed field are continuously
linearly equivalent if and only if they have the same (finite) dimension. -/
/-
**FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq : Nonempty
 (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq`：FiniteDi
mensional.nonempty_continuousLinearEquiv_of_finrank_eq (cond : finrank 𝕜 E = fin
rank 𝕜 F) : Nonempty (E ≃L[𝕜] F)

--- 原说明 ---
Two finite-dimensional topological vector spaces over a complete normed field ar
e continuously
linearly equivalent if and only if they have the same (finite) dimension.
-/
theorem FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq :
    Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h =>
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩

/-- A continuous linear equivalence between two finite-dimensional topological vector spaces over a
complete normed field of the same (finite) dimension. -/
/-
**ContinuousLinearEquiv.ofFinrankEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃
L[𝕜] F
参数：cond : finrank 𝕜 E = finrank 𝕜 F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence between two finite-dimensional topological vecto
r spaces over a
complete normed field of the same (finite) dimension.
-/
def ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

end

namespace Module.Basis
variable {ι : Type*} [Finite ι] [T2Space E]

/-- Construct a continuous linear map given the value at a finite basis. -/
/-
**Module.Basis.constrL** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：constrL (v : Basis ι 𝕜 E) (f : ι -> F) : E ->L[𝕜] F
参数：v : Basis ι 𝕜 E；f : ι -> F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear map given the value at a finite basis.
-/
def constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F :=
  haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)

@[simp]
/-
**Module.Basis.coe_constrL** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_constrL (v : Basis ι 𝕜 E) (f : ι -> F) : (v.constrL f : E ->ₗ[𝕜] F) = 
v.constr 𝕜 f
参数：v : Basis ι 𝕜 E；f : ι -> F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
@[simps! apply]
/-
**Module.Basis.equivFunL** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι -> 𝕜
参数：v : Basis ι 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous linear equivalence between a vector space over `𝕜` with a finite 
basis and
functions from its basis indexing type to `𝕜`.
-/
def equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
/-
**Module.Basis.equivFunL_symm_apply_repr** 是 Mathlib 中的一个引理，位于命名空间 `Module.Basis
`。
形式化陈述：equivFunL_symm_apply_repr (v : Basis ι 𝕜 E) (x : E) : v.equivFunL.symm (v.
repr x) = x
参数：v : Basis ι 𝕜 E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
lemma equivFunL_symm_apply_repr (v : Basis ι 𝕜 E) (x : E) :
    v.equivFunL.symm (v.repr x) = x :=
  v.equivFunL.symm_apply_apply x

@[simp]
/-
**Module.Basis.constrL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constrL_apply {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) (f : ι -> F) (e : 
E) : v.constrL f e = ∑ i, v.equivFun e i • f i
参数：v : Basis ι 𝕜 E；f : ι -> F；e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.constr_apply_fintype`：constr_apply_fintype [Fintype ι] (b :
 Basis ι R M) (f : ι -> M') (x : M) : (constr (M'
-/
theorem constrL_apply {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) (f : ι → F) (e : E) :
    v.constrL f e = ∑ i, v.equivFun e i • f i :=
  v.constr_apply_fintype 𝕜 _ _

@[simp 1100]
/-
**Module.Basis.constrL_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：constrL_basis (v : Basis ι 𝕜 E) (f : ι -> F) (i : ι) : v.constrL f (v i) =
 f i
参数：v : Basis ι 𝕜 E；f : ι -> F；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
theorem constrL_basis (v : Basis ι 𝕜 E) (f : ι → F) (i : ι) : v.constrL f (v i) = f i :=
  v.constr_basis 𝕜 _ _

end Module.Basis

namespace ContinuousLinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- Builds a continuous linear equivalence from a continuous linear map on a finite-dimensional
vector space whose determinant is nonzero. -/
/-
**ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero** 是 Mathlib 中的一个定义，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：toContinuousLinearEquivOfDetNeZero (f : E ->L[𝕜] E) (hf : f.det != 0) : E 
≃L[𝕜] E
参数：f : E ->L[𝕜] E；hf : f.det != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Builds a continuous linear equivalence from a continuous linear map on a finite-
dimensional
vector space whose determinant is nonzero.
-/
def toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
  ((f : E →ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv

@[simp]
/-
**ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousLinearMap`。
形式化陈述：coe_toContinuousLinearEquivOfDetNeZero (f : E ->L[𝕜] E) (hf : f.det != 0) 
: (f.toContinuousLinearEquivOfDetNeZero hf : E ->L[𝕜] E) = f
参数：f : E ->L[𝕜] E；hf : f.det != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem coe_toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) :
    (f.toContinuousLinearEquivOfDetNeZero hf : E →L[𝕜] E) = f := by
  ext x
  rfl

@[simp]
/-
**ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：toContinuousLinearEquivOfDetNeZero_apply (f : E ->L[𝕜] E) (hf : f.det != 0
) (x : E) : f.toContinuousLinearEquivOfDetNeZero hf x = f x
参数：f : E ->L[𝕜] E；hf : f.det != 0；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquivOfDetNeZero_apply (f : E →L[𝕜] E) (hf : f.det ≠ 0) (x : E) :
    f.toContinuousLinearEquivOfDetNeZero hf x = f x :=
  rfl
/-
**ContinuousLinearMap._root_.Matrix.toLin_finTwoProd_toContinuousLinearMap** 是 M
athlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.toLin_finTwoProd_toContinuousLinearMap (a b c d : 𝕜) :
    LinearMap.toContinuousLinearMap
      (Matrix.toLin (Basis.finTwoProd 𝕜) (Basis.finTwoProd 𝕜) !![a, b; c, d]) =
      (a • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + b • ContinuousLinearMap.snd 𝕜 𝕜 𝕜).prod
        (c • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + d • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) :=
  ContinuousLinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _

end ContinuousLinearMap

end NormedField

section IsUniformAddGroup

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [AddCommGroup E] [UniformSpace E] [T2Space E] [IsUniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

include 𝕜 in
/-
**FiniteDimensional.complete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_fin_fun`：Module.finrank_fin_fun {n : Nat} : finrank R (Fi
n n -> R) = n
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `ContinuousLinearEquiv.isUniformEmbedding`：isUniformEmbedding {E₁ E₂ : Ty
pe*} [UniformSpace E₁] [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Mo
dule R₁ E₁] [Module R₂ E₂] [Is…
· 使用定理 `Pi.instIsUniformAddGroup`：∀ {ι : Type u_4} {G : ι → Type u_5} [inst : (i
 : ι) → UniformSpace (G i)] [inst_1 : (i : ι) → AddGroup (G i)]   [∀ (i : ι), Is
UniformAddGrou…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_congr`：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbe
dding e) : CompleteSpace α ↔ CompleteSpace β
-/
theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance

variable {𝕜 E}

/-- A finite-dimensional subspace is complete. -/
/-
**Submodule.complete_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensi
onal 𝕜 s] : IsComplete (s : Set E)
参数：s : Submodule 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_coe_iff_isComplete`：completeSpace_coe_iff_isComplete {s : 
Set α} : CompleteSpace s ↔ IsComplete s
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `AddSubgroup.isUniformAddGroup`：∀ {α : Type u_1} [inst : UniformSpace α] 
[inst_1 : AddGroup α] [IsUniformAddGroup α] (S : AddSubgroup α),   IsUniformAddG
roup ↥S

--- 原说明 ---
A finite-dimensional subspace is complete.
-/
theorem Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsComplete (s : Set E) :=
  haveI : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)

end IsUniformAddGroup

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F]

/-- A finite-dimensional subspace is closed. -/
/-
**Submodule.closed_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.closed_of_finiteDimensional [T2Space E] (s : Submodule 𝕜 E) [Fin
iteDimensional 𝕜 s] : IsClosed (s : Set E)
参数：s : Submodule 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.isClosed`：IsComplete.isClosed [UniformSpace α] [T0Space α] {s
 : Set α} (h : IsComplete s) : IsClosed s
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Submodule.complete_of_finiteDimensional`：Submodule.complete_of_finiteDim
ensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsComplete (s : Set E)
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G

--- 原说明 ---
A finite-dimensional subspace is closed.
-/
theorem Submodule.closed_of_finiteDimensional
    [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  s.complete_of_finiteDimensional.isClosed

/-- If `s` is a closed subspace with finite codimension, any subspace containing `s` is closed. -/
/-
**Submodule.isClosed_mono_of_finiteDimensional_quotient** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Submodule.isClosed_mono_of_finiteDimensional_quotient {s t : Submodule 𝕜 E
} [FiniteDimensional 𝕜 (E ⧸ s)] (s_closed : IsClosed (s : Set E)) (s_le_t : s <=
 t) : IsClosed (t : Set E)
参数：E ⧸ s；s_closed : IsClosed (s : Set E)；s_le_t : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.comap_map_mkQ`：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p 
⊔ p'
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
· 使用定理 `Submodule.closed_of_finiteDimensional`：Submodule.closed_of_finiteDimensi
onal [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set
 E)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X

--- 原说明 ---
If `s` is a closed subspace with finite codimension, any subspace containing `s`
 is closed.
-/
theorem Submodule.isClosed_mono_of_finiteDimensional_quotient
    {s t : Submodule 𝕜 E} [FiniteDimensional 𝕜 (E ⧸ s)] (s_closed : IsClosed (s : Set E))
    (s_le_t : s ≤ t) :
    IsClosed (t : Set E) := by
  rw [show t = comap s.mkQ (map s.mkQ t) by simpa]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

/-- The supremum of a closed subspace and a finite dimensional subspace is closed. -/
/-
**Submodule.isClosed_sup_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isClosed_sup_finiteDimensional (s t : Submodule 𝕜 E) (hs : IsClo
sed (s : Set E)) [ht : FiniteDimensional 𝕜 t] : IsClosed ((s ⊔ t : Submodule 𝕜 E
) : Set E)
参数：s t : Submodule 𝕜 E；hs : IsClosed (s : Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_map_mkQ`：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p 
⊔ p'
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
· 使用定理 `Submodule.closed_of_finiteDimensional`：Submodule.closed_of_finiteDimensi
onal [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set
 E)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `FiniteDimensional.instSubtypeMemSubmoduleMap`：∀ (K : Type u) {V : Type v
} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   {V₂ : Type v'} [inst_3 : AddCom…

--- 原说明 ---
The supremum of a closed subspace and a finite dimensional subspace is closed.
-/
theorem Submodule.isClosed_sup_finiteDimensional
    (s t : Submodule 𝕜 E) (hs : IsClosed (s : Set E)) [ht : FiniteDimensional 𝕜 t] :
    IsClosed ((s ⊔ t : Submodule 𝕜 E) : Set E) := by
  rw [← comap_map_mkQ]
  exact (map s.mkQ t).closed_of_finiteDimensional.preimage continuous_quot_mk

/-- A sufficient condition for a linear map taking values in a TVS to have closed range is that
there exists a finite-codimension subspace of the domain whose image is closed. -/
/-
**LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient {E 
: Type*} [AddCommGroup E] [Module 𝕜 E] {f : E ->ₗ[𝕜] F} {s : Submodule 𝕜 E} [s.C
oFG] (h : IsClosed (s.map f : Set F)) : IsClosed (f.range : Set F)
参数：h : IsClosed (s.map f : Set F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Submodule.CoFG.fg_of_isCompl`：∀ {R : Type u_1} [inst : Ring R] {M : Type
 u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Submodule 
R M}, IsCompl S T …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.isClosed_sup_finiteDimensional`：Submodule.isClosed_sup_finiteD
imensional (s t : Submodule 𝕜 E) (hs : IsClosed (s : Set E)) [ht : FiniteDimensi
onal 𝕜 t] : IsClosed ((s ⊔ t :…
· 使用定理 `FiniteDimensional.instSubtypeMemSubmoduleMap`：∀ (K : Type u) {V : Type v
} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   {V₂ : Type v'} [inst_3 : AddCom…

--- 原说明 ---
A sufficient condition for a linear map taking values in a TVS to have closed ra
nge is that
there exists a finite-codimension subspace of the domain whose image is closed.
-/
theorem LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E →ₗ[𝕜] F} {s : Submodule 𝕜 E}
    [s.CoFG] (h : IsClosed (s.map f : Set F)) :
    IsClosed (f.range : Set F) := by
  obtain ⟨t, s_compl_t⟩ := Submodule.exists_isCompl s
  have : FiniteDimensional 𝕜 t := .of_fg <| Submodule.CoFG.fg_of_isCompl s_compl_t inferInstance
  rw [← Submodule.map_top, ← s_compl_t.sup_eq_top, Submodule.map_sup]
  exact Submodule.isClosed_sup_finiteDimensional _ _ h

/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
/-
**LinearMap.isClosedEmbedding_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isClosedEmbedding_of_injective [T2Space E] [FiniteDimensional 𝕜 
E] [T2Space F] {f : E ->ₗ[𝕜] F} (hf : LinearMap.ker f = ⊥) : IsClosedEmbedding f
参数：hf : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `Submodule.closed_of_finiteDimensional`：Submodule.closed_of_finiteDimensi
onal [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] : IsClosed (s : Set
 E)

--- 原说明 ---
An injective linear map with finite-dimensional domain is a closed embedding.
-/
theorem LinearMap.isClosedEmbedding_of_injective [T2Space E] [FiniteDimensional 𝕜 E] [T2Space F]
    {f : E →ₗ[𝕜] F} (hf : LinearMap.ker f = ⊥) : IsClosedEmbedding f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { IsEmbedding.subtypeVal.comp g.toContinuousLinearEquiv.toHomeomorph.isEmbedding with
    isClosed_range := by
      simpa [LinearMap.coe_range f] using (LinearMap.range f).closed_of_finiteDimensional }
/-
**isClosedEmbedding_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedEmbedding_smul_left [T2Space E] {c : E} (hc : c != 0) : IsClosedEm
bedding fun x : 𝕜 => x • c
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isClosedEmbedding_of_injective`：LinearMap.isClosedEmbedding_of
_injective [T2Space E] [FiniteDimensional 𝕜 E] [T2Space F] {f : E ->ₗ[𝕜] F} (hf 
: LinearMap.ker f = ⊥) : IsClo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LinearMap.ker_toSpanSingleton`：ker_toSpanSingleton {x : M} (h : x != 0) 
: LinearMap.ker (toSpanSingleton R M x) = ⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem isClosedEmbedding_smul_left [T2Space E] {c : E} (hc : c ≠ 0) :
    IsClosedEmbedding fun x : 𝕜 => x • c :=
  LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 hc)

-- `smul` is a closed map in the first argument.
/-
**isClosedMap_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_smul_left [T2Space E] (c : E) : IsClosedMap fun x : 𝕜 => x • c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `isClosedMap_const`：isClosedMap_const {X Y} [TopologicalSpace X] [Topolog
icalSpace Y] [T1Space Y] {y : Y} : IsClosedMap (Function.const X y)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `isClosedEmbedding_smul_left`：isClosedEmbedding_smul_left [T2Space E] {c 
: E} (hc : c != 0) : IsClosedEmbedding fun x : 𝕜 => x • c
-/
theorem isClosedMap_smul_left [T2Space E] (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]
    exact isClosedMap_const
  · exact (isClosedEmbedding_smul_left hc).isClosedMap
/-
**ContinuousLinearMap.exists_rightInverse_of_surjective** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：ContinuousLinearMap.exists_rightInverse_of_surjective [T2Space F] [FiniteD
imensional 𝕜 F] (f : E ->L[𝕜] F) (hf : f.range = ⊤) : exists g : F ->L[𝕜] E, f.c
omp g = ContinuousLinearMap.id 𝕜 F
参数：f : E ->L[𝕜] F；hf : f.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_rightInverse_of_surjective`：∀ {R : Type u_1} [inst : Se
miring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]
   {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearMap.coe_inj`：coe_inj {f g : M₁ ->SL[σ₁₂] M₂} : (f : M₁ -
>ₛₗ[σ₁₂] M₂) = g ↔ f = g
-/
theorem ContinuousLinearMap.exists_rightInverse_of_surjective [T2Space F] [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) (hf : f.range = ⊤) : ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.coe_inj.1 hg⟩

@[deprecated (since := "2026-04-24")]
alias ContinuousLinearMap.exists_right_inverse_of_surjective :=
  ContinuousLinearMap.exists_rightInverse_of_surjective
/-
**ContinuousLinearMap.isQuotientMap_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContinuousLinearMap.isQuotientMap_of_finiteDimensional [T2Space F] [Finite
Dimensional 𝕜 F] (f : E ->L[𝕜] F) (hf : f.range = ⊤) : IsQuotientMap f
参数：f : E ->L[𝕜] F；hf : f.range = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.exists_rightInverse_of_surjective`：ContinuousLinearM
ap.exists_rightInverse_of_surjective [T2Space F] [FiniteDimensional 𝕜 F] (f : E 
->L[𝕜] F) (hf : f.range = ⊤) : exists g : F…
· 使用定理 `Topology.IsQuotientMap.of_inverse`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {g : Y → X},   
Continuous f → Continuo…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ContinuousLinearMap.isQuotientMap_of_finiteDimensional [T2Space F] [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) (hf : f.range = ⊤) :
    IsQuotientMap f :=
  let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective hf
  .of_inverse g.continuous f.continuous (fun _ ↦ congr($hg _))
/-
**ContinuousLinearMap.isStrictMap_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：ContinuousLinearMap.isStrictMap_of_finiteDimensional [T2Space F] [FiniteDi
mensional 𝕜 F] (f : E ->L[𝕜] F) : IsStrictMap f
参数：f : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.isStrictMap_iff_isQuotientMap_rangeFactorization`：isStrictMap_i
ff_isQuotientMap_rangeFactorization : IsStrictMap f ↔ IsQuotientMap (Set.rangeFa
ctorization f)
· 使用定理 `ContinuousLinearMap.isQuotientMap_of_finiteDimensional`：ContinuousLinear
Map.isQuotientMap_of_finiteDimensional [T2Space F] [FiniteDimensional 𝕜 F] (f : 
E ->L[𝕜] F) (hf : f.range = ⊤) : IsQuotientM…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ContinuousLinearMap.isStrictMap_of_finiteDimensional [T2Space F] [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) :
    IsStrictMap f := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact f.rangeRestrict.isQuotientMap_of_finiteDimensional (by simp)

/-- If `K` is a complete field and `V` is a finite-dimensional vector space over `K` (equipped with
any topology so that `V` is a topological `K`-module, meaning `[IsTopologicalAddGroup V]`
and `[ContinuousSMul K V]`), and `K` is locally compact, then `V` is locally compact.

This is not an instance because `K` cannot be inferred. -/
/-
**LocallyCompactSpace.of_finiteDimensional_of_complete** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：LocallyCompactSpace.of_finiteDimensional_of_complete (K V : Type*) [Nontri
viallyNormedField K] [CompleteSpace K] [LocallyCompactSpace K] [AddCommGroup V] 
[TopologicalSpace V] [IsTopologicalAddGroup V] [Module K V] [ContinuousSMul K V]
 [FiniteDimensional K V] : LocallyCompactSpace V
参数：K V : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Module.Basis.exists_basis`：exists_basis : exists s : Set V, Nonempty (Ba
sis s K V)
· 使用定理 `Topology.IsOpenEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Type
 u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactS
pace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SeparationQuotient.instIsTopologicalAddGroup`：∀ {G : Type u_1} [inst : T
opologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup G],   I
sTopologicalAddGroup (SeparationQu…
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `Topology.IsInducing.locallyCompactSpace`：Topology.IsInducing.locallyComp
actSpace [LocallyCompactSpace Y] {f : X -> Y} (hf : IsInducing f) (h : IsLocally
Closed (range f)) : LocallyCo…
· 使用定理 `SeparationQuotient.isInducing_mk`：isInducing_mk : IsInducing (mk : X -> 
SeparationQuotient X)
· 使用引理 `IsClosed.isLocallyClosed`：IsClosed.isLocallyClosed (hs : IsClosed s) : I
sLocallyClosed s
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeparationQuotient.range_mk`：range_mk : range (mk : X -> SeparationQuoti
ent X) = univ

--- 原说明 ---
If `K` is a complete field and `V` is a finite-dimensional vector space over `K`
 (equipped with
any topology so that `V` is a topological `K`-module, meaning `[IsTopologicalAdd
Group V]`
and `[ContinuousSMul K V]`), and `K` is locally compact, then `V` is locally com
pact.

This is not an instance because `K` cannot be inferred.
-/
theorem LocallyCompactSpace.of_finiteDimensional_of_complete (K V : Type*)
    [NontriviallyNormedField K] [CompleteSpace K] [LocallyCompactSpace K]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [Module K V] [ContinuousSMul K V] [FiniteDimensional K V] :
    LocallyCompactSpace V :=
  -- Reduce to `SeparationQuotient V`, which is a `T2Space`.
  suffices LocallyCompactSpace (SeparationQuotient V) from
    SeparationQuotient.isInducing_mk.locallyCompactSpace <|
      SeparationQuotient.range_mk (X := V) ▸ isClosed_univ.isLocallyClosed
  let ⟨_, ⟨b⟩⟩ := Basis.exists_basis K (SeparationQuotient V)
  have := FiniteDimensional.fintypeBasisIndex b
  b.equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace

section Riesz

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E Eᵤ : Type*} [AddCommGroup E] [AddCommGroup Eᵤ] [Module 𝕜 E] [Module 𝕜 Eᵤ]
  [TopologicalSpace E] [UniformSpace Eᵤ] [T2Space E] [T2Space Eᵤ]
  [IsTopologicalAddGroup E] [IsUniformAddGroup Eᵤ]
  [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 Eᵤ]

open scoped Pointwise in
/-- **Riesz's theorem**: a T2 topological vector space over a complete non-trivial normed field
which admits a totally bounded neighborhood of `0` is finite-dimensional. -/
/-
**FiniteDimensional.of_totallyBounded_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_totallyBounded_nhds_zero {U : Set Eᵤ} (hU_nhds : U in
 𝓝 (0 : Eᵤ)) (hU_tb : TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ
参数：hU_nhds : U in 𝓝 (0 : Eᵤ)；hU_tb : TotallyBounded U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `totallyBounded_iff_subset_finite_iUnion_nhds_zero`：∀ {α : Type u_1} [ins
t : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {s : Set α},   T
otallyBounded s ↔ ∀ U ∈ nhds 0, ∃ t, t.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Module.Finite.span_of_finite`：span_of_finite {A : Set M} (hA : Set.Finit
e A) : Module.Finite R (span R A)
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Set.instAddLeftMono`：∀ {α : Type u_2} [inst : Add α], AddLeftMono (Set α
)
· 使用定理 `Set.instAddRightMono`：∀ {α : Type u_2} [inst : Add α], AddRightMono (Set
 α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.smul_set_mono`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s 
t : Set β} {a : α}, s ⊆ t → a • s ⊆ a • t
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Lean.Meta.Rfl.rel_of_eq_and_refl`：∀ {α : Sort u_1} {R : α → α → Prop} {x
 y : α}, x = y → R x x → R x y
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
**Riesz's theorem**: a T2 topological vector space over a complete non-trivial n
ormed field
which admits a totally bounded neighborhood of `0` is finite-dimensional.
-/
theorem FiniteDimensional.of_totallyBounded_nhds_zero {U : Set Eᵤ} (hU_nhds : U ∈ 𝓝 (0 : Eᵤ))
    (hU_tb : TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ := by
  obtain ⟨c, hc0, hc1⟩ : ∃ c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < 1 := NormedField.exists_norm_lt 𝕜 zero_lt_one
  have hc_ne : c ≠ 0 := norm_pos_iff.mp hc0
  obtain ⟨F, hF_finite, hF_cover⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hU_tb
    (c • U) ((set_smul_mem_nhds_zero_iff hc_ne).mpr hU_nhds)
  let M : Submodule 𝕜 Eᵤ := Submodule.span 𝕜 F
  let : FiniteDimensional 𝕜 M := Finite.span_of_finite 𝕜 hF_finite
  have h_cover : U ⊆ M + c • U := fun x hx ↦ by
    obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_iUnion₂.mp <| hF_cover hx
    exact ⟨f, Submodule.subset_span hf, y, hy, rfl⟩
  have h_ind (n : ℕ) : U ⊆ M + c ^ n • U := by
    induction n with
    | zero => simpa using! fun x hx ↦ ⟨0, M.zero_mem, x, hx, zero_add x⟩
    | succ n ih =>
      calc
        U ⊆ M + c ^ n • U := ih
        _ ⊆ M + c ^ n • (M + c • U) := by gcongr
        _ ⊆ M + c ^ (n + 1) • U := by
          rw [smul_add, smul_smul, pow_succ, ← add_assoc]
          congr!
          lift c to 𝕜ˣ using isUnit_iff_ne_zero.mpr hc_ne
          simp [← Units.val_pow_eq_pow_val, ← Units.smul_def]
  have h_small : Tendsto (fun n ↦ c ^ n • U) atTop (𝓝 0).smallSets :=
    (TotallyBounded.isVonNBounded 𝕜 hU_tb).tendsto_smallSets_nhds.comp
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)
  have hU_sub_M : U ⊆ M := by
    intro x hx
    choose m hm u hu h_eq using fun n ↦ h_ind n hx
    have hu_tendsto : Tendsto u atTop (𝓝 0) := by
      intro W hW
      exact (tendsto_smallSets_iff.mp h_small W hW).mono fun n hn ↦ hn (hu n)
    have hm_tendsto : Tendsto m atTop (𝓝 x) := by
      simpa [show m = fun n ↦ x - u n by grind] using! tendsto_const_nhds.sub hu_tendsto
    exact M.closed_of_finiteDimensional.mem_of_tendsto hm_tendsto (Eventually.of_forall hm)
  have hM_top : M = ⊤ := absorbent_nhds_zero (𝕜 := 𝕜) hU_nhds |>.mono hU_sub_M |>.submodule_eq_top
  exact FiniteDimensional.of_surjective M.subtype fun x ↦ ⟨⟨x, by simp [hM_top]⟩, rfl⟩

open scoped Pointwise in
/-- **Riesz's theorem**: if a T2 topological vector space over a complete non-trivial
normed field admits a totally bounded neighborhood of some point, then it is
finite-dimensional. -/
/-
**FiniteDimensional.of_totallyBounded_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_totallyBounded_nhds {x : Eᵤ} {U : Set Eᵤ} (hU_nhds : 
U in 𝓝 x) (hU_tb : TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ
参数：hU_nhds : U in 𝓝 x；hU_tb : TotallyBounded U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_neg_vadd`：∀ {G : Type u_3} {α : Type u_5} [inst : AddGroup G] [inst
_1 : AddAction G α] (g : G) (a : α), g +ᵥ -g +ᵥ a = a
· 使用定理 `FiniteDimensional.of_totallyBounded_nhds_zero`：FiniteDimensional.of_tota
llyBounded_nhds_zero {U : Set Eᵤ} (hU_nhds : U in 𝓝 (0 : Eᵤ)) (hU_tb : TotallyBo
unded U) : FiniteDimensional 𝕜 Eᵤ
· 使用定理 `vadd_mem_nhds_self`：∀ {G : Type u_4} [inst : AddGroup G] [inst_1 : Topol
ogicalSpace G] [ContinuousConstVAdd G G] {g : G} {s : Set G},   g +ᵥ s ∈ nhds g 
↔ s ∈ nh…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TotallyBounded.image`：TotallyBounded.image [UniformSpace β] {f : α -> β}
 {s : Set α} (hs : TotallyBounded s) (hf : UniformContinuous f) : TotallyBounded
 (f '' s)
· 使用定理 `UniformContinuous.sub`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSp
ace α] [inst_1 : AddGroup α] [IsUniformAddGroup α]   [inst_3 : UniformSpace β] {
f g : β → α…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
· 使用定理 `uniformContinuous_const`：uniformContinuous_const {b : β} : UniformContin
uous fun _ : α => b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Riesz's theorem**: if a T2 topological vector space over a complete non-trivia
l
normed field admits a totally bounded neighborhood of some point, then it is
finite-dimensional.
-/
theorem FiniteDimensional.of_totallyBounded_nhds {x : Eᵤ} {U : Set Eᵤ} (hU_nhds : U ∈ 𝓝 x)
    (hU_tb : TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ := by
  replace hU_nhds : x +ᵥ (-x) +ᵥ U ∈ 𝓝 x := by simpa
  rw [vadd_mem_nhds_self] at hU_nhds
  refine .of_totallyBounded_nhds_zero _ hU_nhds ?_
  have : -x +ᵥ U = (· - x) '' U := by simp [← Set.image_vadd, neg_add_eq_sub]
  exact this ▸ hU_tb.image (uniformContinuous_id.sub uniformContinuous_const)

/-- **Riesz's theorem**: in a T2 topological vector space over a complete non-trivial normed field,
if there exists a totally bounded neighborhood of some point, then the space is finite-dimensional.
-/
/-
**FiniteDimensional.of_exists_totallyBounded_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_exists_totallyBounded_nhds (h : exists x : Eᵤ, exists
 U in 𝓝 x, TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ
参数：h : exists x : Eᵤ, exists U in 𝓝 x, TotallyBounded U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_totallyBounded_nhds`：FiniteDimensional.of_totallyBo
unded_nhds {x : Eᵤ} {U : Set Eᵤ} (hU_nhds : U in 𝓝 x) (hU_tb : TotallyBounded U)
 : FiniteDimensional 𝕜 Eᵤ

--- 原说明 ---
**Riesz's theorem**: in a T2 topological vector space over a complete non-trivia
l normed field,
if there exists a totally bounded neighborhood of some point, then the space is 
finite-dimensional.
-/
theorem FiniteDimensional.of_exists_totallyBounded_nhds
    (h : ∃ x : Eᵤ, ∃ U ∈ 𝓝 x, TotallyBounded U) : FiniteDimensional 𝕜 Eᵤ := by
  rcases h with ⟨x, U, hU_nhds, hU_tb⟩
  exact FiniteDimensional.of_totallyBounded_nhds (𝕜 := 𝕜) hU_nhds hU_tb

/-- **Riesz's theorem**: a locally compact topological vector space is finite-dimensional. -/
/-
**FiniteDimensional.of_locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_locallyCompactSpace [WeaklyLocallyCompactSpace E] : F
initeDimensional 𝕜 E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `FiniteDimensional.of_totallyBounded_nhds_zero`：FiniteDimensional.of_tota
llyBounded_nhds_zero {U : Set Eᵤ} (hU_nhds : U in 𝓝 (0 : Eᵤ)) (hU_tb : TotallyBo
unded U) : FiniteDimensional 𝕜 Eᵤ
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s

--- 原说明 ---
**Riesz's theorem**: a locally compact topological vector space is finite-dimens
ional.
-/
theorem FiniteDimensional.of_locallyCompactSpace [WeaklyLocallyCompactSpace E] :
    FiniteDimensional 𝕜 E :=
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let ⟨_, hU_compact, hU_nhds⟩ := exists_compact_mem_nhds (0 : E)
  .of_totallyBounded_nhds_zero 𝕜 hU_nhds hU_compact.totallyBounded

/-- If a function has compact support, then either the function is trivial
or the space is finite-dimensional. -/
/-
**HasCompactSupport.eq_zero_or_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.eq_zero_or_finiteDimensional {X : Type*} [TopologicalSpa
ce X] [Zero X] [T1Space X] {f : E -> X} (hf : HasCompactSupport f) (h'f : Contin
uous f) : f = 0 ∨ FiniteDimensional 𝕜 E
参数：hf : HasCompactSupport f；h'f : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup`：∀ {G : Typ
e w} {α : Type u} [inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologic
alAddGroup G]   [inst_3 : TopologicalSpace α] [ins…

--- 原说明 ---
If a function has compact support, then either the function is trivial
or the space is finite-dimensional.
-/
theorem HasCompactSupport.eq_zero_or_finiteDimensional {X : Type*} [TopologicalSpace X] [Zero X]
    [T1Space X] {f : E → X} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ FiniteDimensional 𝕜 E :=
  (HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup hf h'f).imp_right fun h ↦
    have : LocallyCompactSpace E := h; .of_locallyCompactSpace 𝕜

/-- If a function has compact multiplicative support, then either the function is trivial
or the space is finite-dimensional. -/
/-
**HasCompactMulSupport.eq_one_or_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type*} [TopologicalS
pace X] [One X] [T1Space X] {f : E -> X} (hf : HasCompactMulSupport f) (h'f : Co
ntinuous f) : f = 1 ∨ FiniteDimensional 𝕜 E
参数：hf : HasCompactMulSupport f；h'f : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.eq_zero_or_finiteDimensional`：HasCompactSupport.eq_zer
o_or_finiteDimensional {X : Type*} [TopologicalSpace X] [Zero X] [T1Space X] {f 
: E -> X} (hf : HasCompactSupport f)…

--- 原说明 ---
If a function has compact multiplicative support, then either the function is tr
ivial
or the space is finite-dimensional.
-/
theorem HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type*} [TopologicalSpace X] [One X]
    [T1Space X] {f : E → X} (hf : HasCompactMulSupport f) (h'f : Continuous f) :
    f = 1 ∨ FiniteDimensional 𝕜 E :=
  have : T1Space (Additive X) := ‹_›
  HasCompactSupport.eq_zero_or_finiteDimensional 𝕜 (X := Additive X) hf h'f

end Riesz

section Compl

open Submodule

/-- If `p` is a closed subspace with finite codimension, then any algebraic complement `q` to `p`
is a topological complement. -/
/-
**Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient {p q : Submodul
e 𝕜 E} (h : IsCompl p q) (hp : IsClosed (p : Set E)) [FiniteDimensional 𝕜 (E ⧸ p
)] : IsTopCompl p q
参数：h : IsCompl p q；hp : IsClosed (p : Set E)；E ⧸ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `ContinuousLinearMap.isTopCompl_of_proj`：∀ {R : Type u_1} [inst : Ring R]
 {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_
3 : _root_.Module R M] {p : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.liftQ_mkQ`：liftQ_mkQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : (p.liftQ f h).
comp p.mkQ = f
· 使用定理 `Submodule.ker_projectionOnto`：ker_projectionOnto (h : IsCompl p q) : ker
 (projectionOnto p q h) = q
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G

--- 原说明 ---
If `p` is a closed subspace with finite codimension, then any algebraic compleme
nt `q` to `p`
is a topological complement.
-/
theorem Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient {p q : Submodule 𝕜 E}
    (h : IsCompl p q) (hp : IsClosed (p : Set E)) [FiniteDimensional 𝕜 (E ⧸ p)] :
    IsTopCompl p q := by
  let φ : E ⧸ p →L[𝕜] q := (p.quotientEquivOfIsCompl q h).toLinearMap.toContinuousLinearMap
  have := (φ ∘L p.mkQL).isTopCompl_of_proj fun x ↦ by simp [φ]
  simpa [φ] using this.symm

/-- Assume that `p q : Submodule 𝕜 E` are algebraic complements. If `p` is closed and `q`
has finite dimension, then they are in fact topological complements.

Note that this theorem does not help you to build a closed complement to a finite dimensional
subspace. That requires the Hahn-Banach theorem, and you don't get much control over what the
complement is. See `Submodule.ClosedComplemented.of_finiteDimensional`. -/
/-
**Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional {p q : Submo
dule 𝕜 E} (h : IsCompl p q) (hp : IsClosed (p : Set E)) [hq : FiniteDimensional 
𝕜 q] : IsTopCompl p q
参数：h : IsCompl p q；hp : IsClosed (p : Set E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient`：Submodule.Is
Compl.isTopCompl_of_finiteDimensional_quotient {p q : Submodule 𝕜 E} (h : IsComp
l p q) (hp : IsClosed (p : Set E)) [FiniteDimens…

--- 原说明 ---
Assume that `p q : Submodule 𝕜 E` are algebraic complements. If `p` is closed an
d `q`
has finite dimension, then they are in fact topological complements.

Note that this theorem does not help you to build a closed complement to a finit
e dimensional
subspace. That requires the Hahn-Banach theorem, and you don't get much control 
over what the
complement is. See `Submodule.ClosedComplemented.of_finiteDimensional`.
-/
theorem Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional {p q : Submodule 𝕜 E}
    (h : IsCompl p q) (hp : IsClosed (p : Set E)) [hq : FiniteDimensional 𝕜 q] :
    IsTopCompl p q := by
  suffices FiniteDimensional 𝕜 (E ⧸ p) from h.isTopCompl_of_finiteDimensional_quotient hp
  exact (p.quotientEquivOfIsCompl q h).symm.finiteDimensional
/-
**Submodule.ClosedComplemented.of_finiteDimensional_quotient** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：Submodule.ClosedComplemented.of_finiteDimensional_quotient {p : Submodule 
𝕜 E} (hp : IsClosed (p : Set E)) [hq : FiniteDimensional 𝕜 (E ⧸ p)] : p.ClosedCo
mplemented
参数：hp : IsClosed (p : Set E)；E ⧸ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
· 使用定理 `Submodule.IsTopCompl.closedComplemented`：∀ {R : Type u_1} [inst : Ring R
] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst
_3 : _root_.Module R M] {p q …
· 使用定理 `Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient`：Submodule.Is
Compl.isTopCompl_of_finiteDimensional_quotient {p q : Submodule 𝕜 E} (h : IsComp
l p q) (hp : IsClosed (p : Set E)) [FiniteDimens…
-/
theorem Submodule.ClosedComplemented.of_finiteDimensional_quotient {p : Submodule 𝕜 E}
    (hp : IsClosed (p : Set E)) [hq : FiniteDimensional 𝕜 (E ⧸ p)] : p.ClosedComplemented := by
  obtain ⟨q, hq⟩ : ∃ q, IsCompl p q := p.exists_isCompl
  exact hq.isTopCompl_of_finiteDimensional_quotient hp |>.closedComplemented

@[deprecated (since := "2026-05-09")]
alias Submodule.ClosedComplemented.of_quotient_finiteDimensional :=
  Submodule.ClosedComplemented.of_finiteDimensional_quotient
/-
**Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient {A 
B : Submodule 𝕜 E} [B_cofg : FiniteDimensional 𝕜 (E ⧸ B)] (hB : IsClosed (B : Se
t E)) (hAB : Disjoint A B) : A.ClosedComplemented
参数：E ⧸ B；hB : IsClosed (B : Set E)；hAB : Disjoint A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.exists_isCompl`：∀ {α : Type u_1} [inst : Lattice α] [IsModularL
attice α] [inst_2 : BoundedOrder α] [ComplementedLattice α] {a b : α},   Disjoin
t a b → ∃ a',…
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `IsSemisimpleModule.toComplementedLattice`：∀ {R : Type u_2} {inst : Ring 
R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self
 : IsSemisimpleModule R M], Co…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Submodule.CoFG.of_le`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_2} [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {S T : Submodule R M}, S 
≤ T → S.Co…
· 使用定理 `Submodule.isClosed_mono_of_finiteDimensional_quotient`：Submodule.isClose
d_mono_of_finiteDimensional_quotient {s t : Submodule 𝕜 E} [FiniteDimensional 𝕜 
(E ⧸ s)] (s_closed : IsClosed (s : Set E)) …
· 使用定理 `Submodule.IsTopCompl.closedComplemented`：∀ {R : Type u_1} [inst : Ring R
] {M : Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst
_3 : _root_.Module R M] {p q …
· 使用定理 `Submodule.IsTopCompl.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_
2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] {p q …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Submodule.IsCompl.isTopCompl_of_finiteDimensional_quotient`：Submodule.Is
Compl.isTopCompl_of_finiteDimensional_quotient {p q : Submodule 𝕜 E} (h : IsComp
l p q) (hp : IsClosed (p : Set E)) [FiniteDimens…
-/
theorem Submodule.ClosedComplemented.of_disjoint_of_finiteDimensional_quotient
    {A B : Submodule 𝕜 E} [B_cofg : FiniteDimensional 𝕜 (E ⧸ B)] (hB : IsClosed (B : Set E))
    (hAB : Disjoint A B) : A.ClosedComplemented := by
  obtain ⟨C, B_le_C, C_compl_A⟩ := hAB.symm.exists_isCompl
  have C_cofg : FiniteDimensional 𝕜 (E ⧸ C) := CoFG.of_le B_le_C B_cofg
  have hC : IsClosed (C : Set E) := isClosed_mono_of_finiteDimensional_quotient hB B_le_C
  exact C_compl_A.isTopCompl_of_finiteDimensional_quotient hC |>.symm.closedComplemented
/-
**Submodule.ClosedComplemented.of_finiteDimensional_of_le** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：Submodule.ClosedComplemented.of_finiteDimensional_of_le {A B : Submodule 𝕜
 E} [FiniteDimensional 𝕜 A] (hA : A.ClosedComplemented) [T2Space A] (hB : B <= A
) : B.ClosedComplemented
参数：hA : A.ClosedComplemented；hB : B <= A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.projectionOnto_apply_left`：projectionOnto_apply_left (h : IsCo
mpl p q) (x : p) : projectionOnto p q h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Submodule.ClosedComplemented.of_finiteDimensional_of_le
    {A B : Submodule 𝕜 E} [FiniteDimensional 𝕜 A] (hA : A.ClosedComplemented) [T2Space A]
    (hB : B ≤ A) : B.ClosedComplemented := by
  obtain ⟨p, hp⟩ := hA
  obtain ⟨C, hBC⟩ := B.exists_isCompl
  refine ⟨((projectionOnto B C hBC).domRestrict A).toContinuousLinearMap ∘SL p, fun x ↦ ?_⟩
  simp [hp ⟨x, hB x.2⟩]

omit [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] in
/-
**ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range** 是 Math
lib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range [T2S
pace F] (f : E ->L[𝕜] F) [FiniteDimensional 𝕜 f.range] : f.ker.ClosedComplemente
d
参数：f : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `Submodule.ClosedComplemented.of_finiteDimensional_quotient`：Submodule.Cl
osedComplemented.of_finiteDimensional_quotient {p : Submodule 𝕜 E} (hp : IsClose
d (p : Set E)) [hq : FiniteDimensional 𝕜 (E ⧸ p)…
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
theorem ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range [T2Space F]
    (f : E →L[𝕜] F) [FiniteDimensional 𝕜 f.range] : f.ker.ClosedComplemented := by
  suffices FiniteDimensional 𝕜 (E ⧸ f.ker) from .of_finiteDimensional_quotient f.isClosed_ker
  exact f.toLinearMap.quotKerEquivRange.symm.finiteDimensional

end Compl

