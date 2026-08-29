/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Lemmas
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Engel
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Weight spaces of Lie modules of nilpotent Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieModule.genWeightSpaceOf`
  * `LieModule.genWeightSpace`
  * `LieModule.Weight`
  * `LieModule.posFittingCompOf`
  * `LieModule.posFittingComp`
  * `LieModule.iSup_ucs_eq_genWeightSpace_zero`
  * `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`
  * `LieModule.isCompl_genWeightSpace_zero_posFittingComp`
  * `LieModule.iSupIndep_genWeightSpace`
  * `LieModule.iSup_genWeightSpace_eq_top`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

@[expose] public section

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open Set Function TensorProduct LieModule

variable (M) in
/--
Definition of `weightSpace` / `weightSpace` 的定义

English:
definition weightSpace
  signature: (χ : L -> R)
  body: ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]

中文:
定义 weightSpace
  签名: (χ : L -> R)
  定义体: ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]

Depends on / 依赖: eigenspace
-/
def weightSpace (χ : L -> R) : LieSubmodule R L M where
  __ := ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]

/--
lemma `mem_weightSpace` / 引理 `mem_weightSpace`

English:
lemma mem_weightSpace
  given: (χ : L -> R) (m : M)
  statement: m in weightSpace M χ ↔ forall x, ⁅x, m⁆ = χ x • m
  proof: by
  simp [weightSpace]

中文:
引理 mem_weightSpace
  条件: (χ : L -> R) (m : M)
  结论: m in weightSpace M χ ↔ 对任意 x, ⁅x, m⁆ = χ x • m
  证明: by
  simp [weightSpace]

Depends on / 依赖: weightSpace
-/
lemma mem_weightSpace (χ : L -> R) (m : M) : m in weightSpace M χ ↔ forall x, ⁅x, m⁆ = χ x • m := by
  simp [weightSpace]

section notation_genWeightSpaceOf

/-- Until we define `LieModule.genWeightSpaceOf`, it is useful to have some notation as follows: -/
local notation3 "𝕎("M", " χ", " x")" => (toEnd R L M x).maxGenEigenspace χ

/--
theorem `weight_vector_multiplication` / 定理 `weight_vector_multiplication`

English:
theorem weight_vector_multiplication
  statement: (M₁ M₂ M₃ : Type*)
  proof: by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [TensorProduct.mapIncl, LinearMap.mem_range, LinearMap.coe_comp,
    LieModuleHom.coe_toLinearMap, Function.comp_apply, exists_imp, Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ :=

中文:
定理 weight_vector_multiplication
  结论: (M₁ M₂ M₃ : 类型)
  证明: by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [TensorProduct.mapIncl, LinearMap.mem_range, LinearMap.coe_comp,
    LieModuleHom.coe_toLinearMap, Function.comp_apply, exists_imp, Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ :=
-/
protected theorem weight_vector_multiplication (M₁ M₂ M₃ : Type*)
    [AddCommGroup M₁] [Module R M₁] [LieRingModule L M₁] [LieModule R L M₁] [AddCommGroup M₂]
    [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂] [AddCommGroup M₃] [Module R M₃]
    [LieRingModule L M₃] [LieModule R L M₃] (g : M₁ otimes[R] M₂ ->ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : R) (x : L) :
    LinearMap.range ((g : M₁ otimes[R] M₂ ->ₗ[R] M₃).comp (mapIncl 𝕎(M₁, χ₁, x) 𝕎(M₂, χ₂, x))) <=
      𝕎(M₃, χ₁ + χ₂, x) := by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [TensorProduct.mapIncl, LinearMap.mem_range, LinearMap.coe_comp,
    LieModuleHom.coe_toLinearMap, Function.comp_apply, exists_imp, Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ := toEnd R L M₃ x - (χ₁ + χ₂) • ↑1
  -- The goal is linear in `t` so use induction to reduce to the case that `t` is a pure tensor.
  refine t.induction_on ?_ ?_ ?_
  · use 0; simp only [map_zero]
  swap
  · rintro t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩; use max k₁ k₂
    simp only [map_add, Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁,
      Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero]
  -- Now the main argument: pure tensors.
  rintro ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
  change exists k, (F ^ k) ((g : M₁ otimes[R] M₂ ->ₗ[R] M₃) (m₁ otimesₜ m₂)) = (0 : M₃)
  -- Eliminate `g` from the picture.
  let f₁ : Module.End R (M₁ otimes[R] M₂) := (toEnd R L M₁ x - χ₁ • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ otimes[R] M₂) := (toEnd R L M₂ x - χ₂ • ↑1).lTensor M₁
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ otimes[R] M₂ ->ₗ[R] M₃).comp (f₁ + f₂) := by
    ext m₁ m₂
    simp only [f₁, f₂, F, ← g.map_lie x (m₁ otimesₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul,
      lie_tmul_right, tmul_smul, toEnd_apply_apply, map_smul, Module.End.one_apply,
      LieModuleHom.coe_toLinearMap, LinearMap.smul_apply, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
      LinearMap.lTensor_tmul, AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
    abel
  rsuffices ⟨k, hk⟩ : exists k : Nat, ((f₁ + f₂) ^ k) (m₁ otimesₜ m₂) = 0
  · use k
    rw [← LinearMap.comp_apply]; rw [Module.End.commute_pow_left_of_commute h_comm_square]; rw [LinearMap.comp_apply]; rw [hk]; rw [map_zero]
  -- Unpack the information we have about `m₁`, `m₂`.
  simp only [Module.End.mem_maxGenEigenspace] at hm₁ hm₂
  obtain ⟨k₁, hk₁⟩ := hm₁
  obtain ⟨k₂, hk₂⟩ := hm₂
  have hf₁ : (f₁ ^ k₁) (m₁ otimesₜ m₂) = 0 := by
    simp only [f₁, hk₁, zero_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_pow]
  have hf₂ : (f₂ ^ k₂) (m₁ otimesₜ m₂) = 0 := by
    simp only [f₂, hk₂, tmul_zero, LinearMap.lTensor_tmul, LinearMap.lTensor_pow]
  -- It's now just an application of the binomial theorem.
  use k₁ + k₂ - 1
  have hf_comm : Commute f₁ f₂ := by
    ext m₁ m₂
    simp only [f₁, f₂, Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, LinearMap.lTensor_tmul, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
  rw [hf_comm.add_pow']
  simp only [Finset.sum_apply, LinearMap.coe_sum, LinearMap.smul_apply]
  -- The required sum is zero because each individual term is zero.
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  -- Eliminate the binomial coefficients from the picture.
  suffices (f₁ ^ i * f₂ ^ j) (m₁ otimesₜ m₂) = 0 by rw [this]; apply smul_zero
  -- Finish off with appropriate case analysis.
  rcases Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi | hj
  · rw [(hf_comm.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hf₁,
      map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hf₂, map_zero]

/--
lemma `lie_mem_maxGenEigenspace_toEnd` / 引理 `lie_mem_maxGenEigenspace_toEnd`

English:
lemma lie_mem_maxGenEigenspace_toEnd
  proof: by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ otimesₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply,

中文:
引理 lie_mem_maxGenEigenspace_toEnd
  证明: by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ otimesₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply,

Depends on / 依赖: Function, Function.comp_apply, IsLocalizedModule, IsLocalizedModule.mk, LieModule, LieModule.weight_vector_multiplication, LieModuleHom, LieModuleHom.coe_toLinearMap, LinearMap, LinearMap.coe_comp, LinearMap.mem_range, Submodule, Submodule.subtype_apply, TensorProduct, TensorProduct.mapIncl, TensorProduct.map_tmul, _smul_mk, coe_comp, coe_toLinearMap, comp_apply
-/
lemma lie_mem_maxGenEigenspace_toEnd
    {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y in 𝕎(L, χ₁, x)) (hm : m in 𝕎(M, χ₂, x)) :
    ⁅y, m⁆ in 𝕎(M, χ₁ + χ₂, x) := by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ otimesₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, TensorProduct.map_tmul]

variable (M)

/--
Definition of `genWeightSpaceOf` / `genWeightSpaceOf` 的定义

English:
definition genWeightSpaceOf
  signature: [LieRing.IsNilpotent L] (χ : R) (x : L)
  body: { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

中文:
定义 genWeightSpaceOf
  签名: [LieRing.IsNilpotent L] (χ : R) (x : L)
  定义体: { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, Submodule, Submodule.mem_toAddSubmonoid, lie_mem, lie_mem_maxGenEigenspace_toEnd, mem_carrier, mem_toAddSubmonoid, mem_toSubsemigroup, zero_add
-/
def genWeightSpaceOf [LieRing.IsNilpotent L] (χ : R) (x : L) : LieSubmodule R L M :=
  { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

end notation_genWeightSpaceOf

variable (M)
variable [LieRing.IsNilpotent L]

/--
theorem `mem_genWeightSpaceOf` / 定理 `mem_genWeightSpaceOf`

English:
theorem mem_genWeightSpaceOf
  given: (χ : R) (x : L) (m : M)
  proof: by
  simp [genWeightSpaceOf]

中文:
定理 mem_genWeightSpaceOf
  条件: (χ : R) (x : L) (m : M)
  证明: by
  simp [genWeightSpaceOf]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mk, Submonoid, Submonoid.smul_def, _cancel, _eq_span, _surjective, algebraMap_smul, choice, choice_eq, genWeightSpaceOf, le_l_u, localized, map_le_iff_le_comap, map_le_iff_le_comap.mpr, mem_comap, restrictScalars_mem, smul_def, smul_mem, span_le
-/
theorem mem_genWeightSpaceOf (χ : R) (x : L) (m : M) :
    m in genWeightSpaceOf M χ x ↔ exists k : Nat, ((toEnd R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [genWeightSpaceOf]

/--
theorem `coe_genWeightSpaceOf_zero` / 定理 `coe_genWeightSpaceOf_zero`

English:
theorem coe_genWeightSpaceOf_zero
  given: (x : L)
  proof: by
  simp [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

中文:
定理 coe_genWeightSpaceOf_zero
  条件: (x : L)
  证明: by
  simp [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

Depends on / 依赖: Module, Module.End.iSup_genEigenspace_eq, genWeightSpaceOf, iSup_genEigenspace_eq
-/
theorem coe_genWeightSpaceOf_zero (x : L) :
    ↑(genWeightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k) := by
  simp [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

/--
Definition of `genWeightSpace` / `genWeightSpace` 的定义

English:
definition genWeightSpace
  signature: (χ : L -> R)
  body: ⨅ x, genWeightSpaceOf M (χ x) x

中文:
定义 genWeightSpace
  签名: (χ : L -> R)
  定义体: ⨅ x, genWeightSpaceOf M (χ x) x

Depends on / 依赖: genWeightSpaceOf
-/
def genWeightSpace (χ : L -> R) : LieSubmodule R L M :=
  ⨅ x, genWeightSpaceOf M (χ x) x

/--
theorem `mem_genWeightSpace` / 定理 `mem_genWeightSpace`

English:
theorem mem_genWeightSpace
  given: (χ : L -> R) (m : M)
  proof: by
  simp [genWeightSpace, mem_genWeightSpaceOf]

中文:
定理 mem_genWeightSpace
  条件: (χ : L -> R) (m : M)
  证明: by
  simp [genWeightSpace, mem_genWeightSpaceOf]

Depends on / 依赖: SetLike, SetLike.ext, Submodule, Submodule.localized, _iff, _iff.mp, genWeightSpace, mem_genWeightSpaceOf
-/
theorem mem_genWeightSpace (χ : L -> R) (m : M) :
    m in genWeightSpace M χ ↔ forall x, exists k : Nat, ((toEnd R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [genWeightSpace, mem_genWeightSpaceOf]

/--
lemma `genWeightSpace_le_genWeightSpaceOf` / 引理 `genWeightSpace_le_genWeightSpaceOf`

English:
lemma genWeightSpace_le_genWeightSpaceOf
  given: (x : L) (χ : L -> R)
  proof: iInf_le _ x

中文:
引理 genWeightSpace_le_genWeightSpaceOf
  条件: (x : L) (χ : L -> R)
  证明: iInf_le _ x

Depends on / 依赖: iInf_le
-/
lemma genWeightSpace_le_genWeightSpaceOf (x : L) (χ : L -> R) :
    genWeightSpace M χ <= genWeightSpaceOf M (χ x) x :=
  iInf_le _ x

/--
lemma `weightSpace_le_genWeightSpace` / 引理 `weightSpace_le_genWeightSpace`

English:
lemma weightSpace_le_genWeightSpace
  given: (χ : L -> R)
  proof: by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

中文:
引理 weightSpace_le_genWeightSpace
  条件: (χ : L -> R)
  证明: by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

Depends on / 依赖: LieSubmodule, LieSubmodule.toSubmodule_orderEmbedding, SetLike, SetLike.ext, Submodule, Submodule.localized, _iff, _iff.mp, genEigenspace, iInf_le, le_iInf, le_iff_le, le_top, monotone, toSubmodule_orderEmbedding
-/
lemma weightSpace_le_genWeightSpace (χ : L -> R) :
    weightSpace M χ <= genWeightSpace M χ := by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

variable (R L) in
/--
Definition of `Weight` / `Weight` 的定义

English:
structure Weight
  parameters: where
  axioms and operations (2):
    - toFun : L -> R
    - genWeightSpace_ne_bot' : genWeightSpace M toFun != ⊥

中文:
结构 Weight
  参数: where
  公理与运算 (2 个):
    - toFun : L -> R
    - genWeightSpace_ne_bot' : genWeightSpace M toFun != ⊥
-/
structure Weight where
  /-- The family of eigenvalues corresponding to a weight. -/
  toFun : L -> R
  genWeightSpace_ne_bot' : genWeightSpace M toFun != ⊥

namespace Weight

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Weight R L M) L R where
  body: χ.1
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all

中文:
实例 instFunLike
  签名: : FunLike (Weight R L M) L R where
  定义体: χ.1
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all

Depends on / 依赖: SetLike, SetLike.ext, Submodule, Submodule.localized, _iff, _iff.mp
-/
instance instFunLike : FunLike (Weight R L M) L R where
  coe χ := χ.1
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; simp_all

/--
lemma `coe_weight_mk` / 引理 `coe_weight_mk`

English:
lemma coe_weight_mk
  given: (χ : L -> R) (h)
  proof: rfl

中文:
引理 coe_weight_mk
  条件: (χ : L -> R) (h)
  证明: rfl

Depends on / 依赖: GaloisConnection, GaloisConnection.l_iSup, l_iSup, localized
-/
@[simp] lemma coe_weight_mk (χ : L -> R) (h) :
    (↑(⟨χ, h⟩ : Weight R L M) : L -> R) = χ :=
  rfl

/--
lemma `genWeightSpace_ne_bot` / 引理 `genWeightSpace_ne_bot`

English:
lemma genWeightSpace_ne_bot
  given: (χ : Weight R L M)
  statement: genWeightSpace M χ != ⊥
  proof: χ.genWeightSpace_ne_bot'

中文:
引理 genWeightSpace_ne_bot
  条件: (χ : Weight R L M)
  结论: genWeightSpace M χ != ⊥
  证明: χ.genWeightSpace_ne_bot'

Depends on / 依赖: genWeightSpace_ne_bot
-/
lemma genWeightSpace_ne_bot (χ : Weight R L M) : genWeightSpace M χ != ⊥ := χ.genWeightSpace_ne_bot'

variable {M}

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {χ₁ χ₂ : Weight R L M} (h : forall x, χ₁ x = χ₂ x)
  statement: χ₁ = χ₂
  proof: DFunLike.ext _ _ h

中文:
引理 ext
  条件: {χ₁ χ₂ : Weight R L M} (h : 对任意 x, χ₁ x = χ₂ x)
  结论: χ₁ = χ₂
  证明: DFunLike.ext _ _ h
-/
@[ext] lemma ext {χ₁ χ₂ : Weight R L M} (h : forall x, χ₁ x = χ₂ x) : χ₁ = χ₂ := DFunLike.ext _ _ h

/--
lemma `ext_iff'` / 引理 `ext_iff'`

English:
lemma ext_iff'
  given: {χ₁ χ₂ : Weight R L M}
  statement: (χ₁ : L -> R) = χ₂ ↔ χ₁ = χ₂
  proof: by simp

中文:
引理 ext_iff'
  条件: {χ₁ χ₂ : Weight R L M}
  结论: (χ₁ : L -> R) = χ₂ ↔ χ₁ = χ₂
  证明: by simp
-/
lemma ext_iff' {χ₁ χ₂ : Weight R L M} : (χ₁ : L -> R) = χ₂ ↔ χ₁ = χ₂ := by simp

/--
lemma `exists_ne_zero` / 引理 `exists_ne_zero`

English:
lemma exists_ne_zero
  given: (χ : Weight R L M)
  proof: by
  simpa [LieSubmodule.eq_bot_iff] using χ.genWeightSpace_ne_bot

中文:
引理 exists_ne_zero
  条件: (χ : Weight R L M)
  证明: by
  simpa [LieSubmodule.eq_bot_iff] using χ.genWeightSpace_ne_bot

Depends on / 依赖: LieSubmodule, LieSubmodule.eq_bot_iff, eq_bot_iff, genWeightSpace_ne_bot, localized
-/
lemma exists_ne_zero (χ : Weight R L M) :
    exists x in genWeightSpace M χ, x != 0 := by
  simpa [LieSubmodule.eq_bot_iff] using χ.genWeightSpace_ne_bot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : IsEmpty (Weight R L M)
  body: ⟨fun h => h.2 (Subsingleton.elim _ _)⟩

中文:
实例 [Subsingleton
  签名: M] : IsEmpty (Weight R L M)
  定义体: ⟨fun h => h.2 (Subsingleton.elim _ _)⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [Subsingleton M] : IsEmpty (Weight R L M) :=
  ⟨fun h => h.2 (Subsingleton.elim _ _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: (genWeightSpace M (0 : L -> R))] : Zero (Weight R L M)
  body: ⟨0, fun e => not_nontrivial (⊥ : LieSubmodule R L M) (e ▸ ‹_›)⟩

中文:
实例 [Nontrivial
  签名: (genWeightSpace M (0 : L -> R))] : Zero (Weight R L M)
  定义体: ⟨0, fun e => not_nontrivial (⊥ : LieSubmodule R L M) (e ▸ ‹_›)⟩

Depends on / 依赖: LieSubmodule, _eq_span, localized, map_coe, map_span, not_nontrivial, span_span_of_tower
-/
instance [Nontrivial (genWeightSpace M (0 : L -> R))] : Zero (Weight R L M) :=
  ⟨0, fun e => not_nontrivial (⊥ : LieSubmodule R L M) (e ▸ ‹_›)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: (genWeightSpace M (0 : L -> R))] : IsZeroApply (Weight R L M) L R where
  body: rfl

@[deprecated (since := "2026-07-27")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply

中文:
实例 [Nontrivial
  签名: (genWeightSpace M (0 : L -> R))] : IsZeroApply (Weight R L M) L R where
  定义体: rfl

@[deprecated (since := "2026-07-27")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply
-/
instance [Nontrivial (genWeightSpace M (0 : L -> R))] : IsZeroApply (Weight R L M) L R where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-27")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply

/--
Definition of `IsZero` / `IsZero` 的定义

English:
definition IsZero
  signature: (χ : Weight R L M)
  body: (χ : L -> R) = 0

中文:
定义 IsZero
  签名: (χ : Weight R L M)
  定义体: (χ : L -> R) = 0

Depends on / 依赖: IsLocalization, IsLocalization.mk, Submodule, Submodule.restrictScalars_mem, Submodule.smul_le.mpr, Submodule.smul_mem_smul, _eq_mk, _eq_mul_mk, _one, add_mem, algebraMap_smul, le_antisymm, mul_smul, restrictScalars_mem, smul_induction_on, smul_le, smul_mem, smul_mem_smul
-/
def IsZero (χ : Weight R L M) := (χ : L -> R) = 0

/--
lemma `IsZero.eq` / 引理 `IsZero.eq`

English:
lemma IsZero.eq
  given: {χ : Weight R L M} (hχ : χ.IsZero)
  statement: (χ : L -> R) = 0
  proof: hχ

中文:
引理 IsZero.eq
  条件: {χ : Weight R L M} (hχ : χ.IsZero)
  结论: (χ : L -> R) = 0
  证明: hχ

Depends on / 依赖: Submodule, Submodule.restrictScalars_injective, _smul, restrictScalars_injective, restrictScalars_localized, simp_rw
-/
@[simp] lemma IsZero.eq {χ : Weight R L M} (hχ : χ.IsZero) : (χ : L -> R) = 0 := hχ

/--
lemma `coe_eq_zero_iff` / 引理 `coe_eq_zero_iff`

English:
lemma coe_eq_zero_iff
  given: (χ : Weight R L M)
  statement: (χ : L -> R) = 0 ↔ χ.IsZero
  proof: Iff.rfl

中文:
引理 coe_eq_zero_iff
  条件: (χ : Weight R L M)
  结论: (χ : L -> R) = 0 ↔ χ.IsZero
  证明: Iff.rfl
-/
@[simp] lemma coe_eq_zero_iff (χ : Weight R L M) : (χ : L -> R) = 0 ↔ χ.IsZero := Iff.rfl

/--
lemma `isZero_iff_eq_zero` / 引理 `isZero_iff_eq_zero`

English:
lemma isZero_iff_eq_zero
  given: [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weight R L M}
  proof: Weight.ext_iff' (χ₂ := 0)

中文:
引理 isZero_iff_eq_zero
  条件: [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weight R L M}
  证明: Weight.ext_iff' (χ₂ := 0)

Depends on / 依赖: Weight, Weight.ext_iff, ext_iff
-/
lemma isZero_iff_eq_zero [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weight R L M} :
    χ.IsZero ↔ χ = 0 := Weight.ext_iff' (χ₂ := 0)

/--
lemma `isZero_zero` / 引理 `isZero_zero`

English:
lemma isZero_zero
  given: [Nontrivial (genWeightSpace M (0 : L -> R))]
  statement: IsZero (0 : Weight R L M)
  proof: rfl

中文:
引理 isZero_zero
  条件: [Nontrivial (genWeightSpace M (0 : L -> R))]
  结论: IsZero (0 : Weight R L M)
  证明: rfl
-/
lemma isZero_zero [Nontrivial (genWeightSpace M (0 : L -> R))] : IsZero (0 : Weight R L M) := rfl

/--
Definition of `IsNonZero` / `IsNonZero` 的定义

English:
abbreviation IsNonZero
  signature: (χ : Weight R L M)
  body: ¬ IsZero (χ : Weight R L M)

中文:
缩写 IsNonZero
  签名: (χ : Weight R L M)
  定义体: ¬ IsZero (χ : Weight R L M)

Depends on / 依赖: IsZero, Weight
-/
abbrev IsNonZero (χ : Weight R L M) := ¬ IsZero (χ : Weight R L M)

/--
lemma `isNonZero_iff_ne_zero` / 引理 `isNonZero_iff_ne_zero`

English:
lemma isNonZero_iff_ne_zero
  given: [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weight R L M}
  proof: isZero_iff_eq_zero.not

中文:
引理 isNonZero_iff_ne_zero
  条件: [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weight R L M}
  证明: isZero_iff_eq_zero.not

Depends on / 依赖: isZero_iff_eq_zero, isZero_iff_eq_zero.not
-/
lemma isNonZero_iff_ne_zero [Nontrivial (genWeightSpace M (0 : L -> R))] {χ : Weight R L M} :
    χ.IsNonZero ↔ χ != 0 := isZero_iff_eq_zero.not

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (IsNonZero (R := R) (L := L) (M := M))
  body: Classical.decPred _

中文:
实例 :
  签名: DecidablePred (IsNonZero (R := R) (L := L) (M := M))
  定义体: Classical.decPred _

Depends on / 依赖: Classical, Classical.decPred, decPred
-/
noncomputable instance : DecidablePred (IsNonZero (R := R) (L := L) (M := M)) := Classical.decPred _

variable (R L M) in
/--
Definition of `equivSetOfPred` / `equivSetOfPred` 的定义

English:
definition equivSetOfPred
  signature: : Weight R L M ≃ {χ : L -> R | genWeightSpace M χ != ⊥} where
  body: ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

@[deprecated (since := "2026-07-09")] alias equivSetOf := equivSetOfPred

中文:
定义 equivSetOfPred
  签名: : Weight R L M ≃ {χ : L -> R | genWeightSpace M χ != ⊥} where
  定义体: ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

@[deprecated (since := "2026-07-09")] alias equivSetOf := equivSetOfPred
-/
def equivSetOfPred : Weight R L M ≃ {χ : L -> R | genWeightSpace M χ != ⊥} where
  toFun w := ⟨w.1, w.2⟩
  invFun w := ⟨w.1, w.2⟩
  left_inv w := by simp
  right_inv w := by simp

@[deprecated (since := "2026-07-09")] alias equivSetOf := equivSetOfPred

/--
lemma `genWeightSpaceOf_ne_bot` / 引理 `genWeightSpaceOf_ne_bot`

English:
lemma genWeightSpaceOf_ne_bot
  given: (χ : Weight R L M) (x : L)
  proof: by
  have : ⨅ x, genWeightSpaceOf M (χ x) x != ⊥ := χ.genWeightSpace_ne_bot
  contrapose this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this

中文:
引理 genWeightSpaceOf_ne_bot
  条件: (χ : Weight R L M) (x : L)
  证明: by
  have : ⨅ x, genWeightSpaceOf M (χ x) x != ⊥ := χ.genWeightSpace_ne_bot
  contrapose this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this

Depends on / 依赖: contrapose, eq_bot_iff, genWeightSpaceOf, genWeightSpace_ne_bot, iInf_le, le_of_le_of_eq
-/
lemma genWeightSpaceOf_ne_bot (χ : Weight R L M) (x : L) :
    genWeightSpaceOf M (χ x) x != ⊥ := by
  have : ⨅ x, genWeightSpaceOf M (χ x) x != ⊥ := χ.genWeightSpace_ne_bot
  contrapose this
  rw [eq_bot_iff]
  exact le_of_le_of_eq (iInf_le _ _) this

/--
lemma `hasEigenvalueAt` / 引理 `hasEigenvalueAt`

English:
lemma hasEigenvalueAt
  given: (χ : Weight R L M) (x : L)
  proof: by
  obtain ⟨k : Nat, hk : (toEnd R L M x).genEigenspace (χ x) k != ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using χ.genWeightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk

中文:
引理 hasEigenvalueAt
  条件: (χ : Weight R L M) (x : L)
  证明: by
  obtain ⟨k : Nat, hk : (toEnd R L M x).genEigenspace (χ x) k != ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using χ.genWeightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk

Depends on / 依赖: Module, Module.End.hasEigenvalue_of_hasGenEigenvalue, Module.End.iSup_genEigenspace_eq, genEigenspace, genWeightSpaceOf, genWeightSpaceOf_ne_bot, hasEigenvalue_of_hasGenEigenvalue, iSup_genEigenspace_eq
-/
lemma hasEigenvalueAt (χ : Weight R L M) (x : L) :
    (toEnd R L M x).HasEigenvalue (χ x) := by
  obtain ⟨k : Nat, hk : (toEnd R L M x).genEigenspace (χ x) k != ⊥⟩ := by
    simpa [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq] using χ.genWeightSpaceOf_ne_bot x
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue hk

/--
lemma `apply_eq_zero_of_isNilpotent` / 引理 `apply_eq_zero_of_isNilpotent`

English:
lemma apply_eq_zero_of_isNilpotent
  statement: [IsDomain R] [Module.IsTorsionFree R M] [IsReduced R]
  proof: ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

中文:
引理 apply_eq_zero_of_isNilpotent
  结论: [IsDomain R] [Module.IsTorsionFree R M] [IsReduced R]
  证明: ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

Depends on / 依赖: eq_zero, hasEigenvalueAt, isNilpotent_of_isNilpotent
-/
lemma apply_eq_zero_of_isNilpotent [IsDomain R] [Module.IsTorsionFree R M] [IsReduced R]
    (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : Weight R L M) :
    χ x = 0 :=
  ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

end Weight

/-- See also the more useful form `LieModule.zero_genWeightSpace_eq_top_of_nilpotent`. -/
@[simp]
/--
theorem `zero_genWeightSpace_eq_top_of_nilpotent'` / 定理 `zero_genWeightSpace_eq_top_of_nilpotent'`

English:
theorem zero_genWeightSpace_eq_top_of_nilpotent'
  given: [IsNilpotent L M]
  proof: by
  simp [genWeightSpace, genWeightSpaceOf]

中文:
定理 zero_genWeightSpace_eq_top_of_nilpotent'
  条件: [IsNilpotent L M]
  证明: by
  simp [genWeightSpace, genWeightSpaceOf]

Depends on / 依赖: genWeightSpace, genWeightSpaceOf
-/
theorem zero_genWeightSpace_eq_top_of_nilpotent' [IsNilpotent L M] :
    genWeightSpace M (0 : L -> R) = ⊤ := by
  simp [genWeightSpace, genWeightSpaceOf]

/--
theorem `coe_genWeightSpace_of_top` / 定理 `coe_genWeightSpace_of_top`

English:
theorem coe_genWeightSpace_of_top
  given: (χ : L -> R)
  proof: by
  ext m
  simp only [mem_genWeightSpace, LieSubmodule.mem_toSubmodule, Subtype.forall]
  apply forall_congr'
  simp

@[simp]

中文:
定理 coe_genWeightSpace_of_top
  条件: (χ : L -> R)
  证明: by
  ext m
  simp only [mem_genWeightSpace, LieSubmodule.mem_toSubmodule, Subtype.forall]
  apply forall_congr'
  simp

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_toSubmodule, Subtype, Subtype.forall, forall_congr, mem_genWeightSpace, mem_toSubmodule
-/
theorem coe_genWeightSpace_of_top (χ : L -> R) :
    (genWeightSpace M (χ ∘ (⊤ : LieSubalgebra R L).incl) : Submodule R M) = genWeightSpace M χ := by
  ext m
  simp only [mem_genWeightSpace, LieSubmodule.mem_toSubmodule, Subtype.forall]
  apply forall_congr'
  simp

@[simp]
/--
theorem `zero_genWeightSpace_eq_top_of_nilpotent` / 定理 `zero_genWeightSpace_eq_top_of_nilpotent`

English:
theorem zero_genWeightSpace_eq_top_of_nilpotent
  given: [IsNilpotent L M]
  proof: by
  simp_all

中文:
定理 zero_genWeightSpace_eq_top_of_nilpotent
  条件: [IsNilpotent L M]
  证明: by
  simp_all

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.toLocalizedQuotient, toLocalizedQuotient
-/
theorem zero_genWeightSpace_eq_top_of_nilpotent [IsNilpotent L M] :
    genWeightSpace M (0 : (⊤ : LieSubalgebra R L) -> R) = ⊤ := by
  simp_all

/--
theorem `exists_genWeightSpace_le_ker_of_isNoetherian` / 定理 `exists_genWeightSpace_le_ker_of_isNoetherian`

English:
theorem exists_genWeightSpace_le_ker_of_isNoetherian
  given: [IsNoetherian R M] (χ : L -> R) (x : L)
  proof: by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m in (toEnd R L M x).maxGenEigenspace (χ x) :=
    genWeightSpace_le_genWeightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq, Module.End.genEigenspace_nat] at hm

中文:
定理 exists_genWeightSpace_le_ker_of_isNoetherian
  条件: [IsNoetherian R M] (χ : L -> R) (x : L)
  证明: by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m in (toEnd R L M x).maxGenEigenspace (χ x) :=
    genWeightSpace_le_genWeightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq, Module.End.genEigenspace_nat] at hm

Depends on / 依赖: Module, Module.End.genEigenspace_nat, Module.End.maxGenEigenspace_eq, genEigenspace_nat, genWeightSpace_le_genWeightSpaceOf, maxGenEigenspace, maxGenEigenspaceIndex, maxGenEigenspace_eq, replace
-/
theorem exists_genWeightSpace_le_ker_of_isNoetherian [IsNoetherian R M] (χ : L -> R) (x : L) :
    exists k : Nat,
      genWeightSpace M χ <= ((toEnd R L M x - algebraMap R _ (χ x)) ^ k).ker := by
  use (toEnd R L M x).maxGenEigenspaceIndex (χ x)
  intro m hm
  replace hm : m in (toEnd R L M x).maxGenEigenspace (χ x) :=
    genWeightSpace_le_genWeightSpaceOf M x χ hm
  rwa [Module.End.maxGenEigenspace_eq, Module.End.genEigenspace_nat] at hm

variable (R) in
/--
theorem `exists_genWeightSpace_zero_le_ker_of_isNoetherian` / 定理 `exists_genWeightSpace_zero_le_ker_of_isNoetherian`

English:
theorem exists_genWeightSpace_zero_le_ker_of_isNoetherian
  proof: by
  simpa using exists_genWeightSpace_le_ker_of_isNoetherian M (0 : L -> R) x

中文:
定理 exists_genWeightSpace_zero_le_ker_of_isNoetherian
  证明: by
  simpa using exists_genWeightSpace_le_ker_of_isNoetherian M (0 : L -> R) x

Depends on / 依赖: exists_genWeightSpace_le_ker_of_isNoetherian
-/
theorem exists_genWeightSpace_zero_le_ker_of_isNoetherian
    [IsNoetherian R M] (x : L) :
    exists k : Nat, genWeightSpace M (0 : L -> R) <= LinearMap.ker (toEnd R L M x ^ k) := by
  simpa using exists_genWeightSpace_le_ker_of_isNoetherian M (0 : L -> R) x

/--
lemma `isNilpotent_toEnd_sub_algebraMap` / 引理 `isNilpotent_toEnd_sub_algebraMap`

English:
lemma isNilpotent_toEnd_sub_algebraMap
  given: [IsNoetherian R M] (χ : L -> R) (x : L)
  proof: by
  have : toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm => sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := exists_genWeightSpace_le_ker_of_isNoetherian M χ x
  use

中文:
引理 isNilpotent_toEnd_sub_algebraMap
  条件: [IsNoetherian R M] (χ : L -> R) (x : L)
  证明: by
  have : toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm => sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := exists_genWeightSpace_le_ker_of_isNoetherian M χ x
  use

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_mem, LinearMap, LinearMap.zero_apply, Module, Module.End.pow_restrict, Submodule, Submodule.smul_mem, ZeroMemClass, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_eq_zero.mp, ZeroMemClass.coe_zero, algebraMap, coe_eq_zero, coe_zero, exists_genWeightSpace_le_ker_of_isNoetherian, genWeightSpace, lie_mem, pow_restrict, restrict
-/
lemma isNilpotent_toEnd_sub_algebraMap [IsNoetherian R M] (χ : L -> R) (x : L) :
_root_.IsNilpotent toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) := by
  have : toEnd R L (genWeightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm => sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := exists_genWeightSpace_le_ker_of_isNoetherian M χ x
  use k
  ext ⟨m, hm⟩
  simp only [this, Module.End.pow_restrict _, LinearMap.zero_apply, ZeroMemClass.coe_zero,
    ZeroMemClass.coe_eq_zero]
  exact ZeroMemClass.coe_eq_zero.mp (hk hm)

/--
theorem `isNilpotent_toEnd_genWeightSpace_zero` / 定理 `isNilpotent_toEnd_genWeightSpace_zero`

English:
theorem isNilpotent_toEnd_genWeightSpace_zero
  given: [IsNoetherian R M] (x : L)
  proof: by
  simpa using isNilpotent_toEnd_sub_algebraMap M (0 : L -> R) x

中文:
定理 isNilpotent_toEnd_genWeightSpace_zero
  条件: [IsNoetherian R M] (x : L)
  证明: by
  simpa using isNilpotent_toEnd_sub_algebraMap M (0 : L -> R) x

Depends on / 依赖: isNilpotent_toEnd_sub_algebraMap
-/
theorem isNilpotent_toEnd_genWeightSpace_zero [IsNoetherian R M] (x : L) :
_root_.IsNilpotent toEnd R L (genWeightSpace M (0 : L -> R)) x := by
  simpa using isNilpotent_toEnd_sub_algebraMap M (0 : L -> R) x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherian
  signature: R M] :
  body: isNilpotent_iff_forall'.mpr isNilpotent_toEnd_genWeightSpace_zero M

中文:
实例 [IsNoetherian
  签名: R M] :
  定义体: isNilpotent_iff_forall'.mpr isNilpotent_toEnd_genWeightSpace_zero M

Depends on / 依赖: isNilpotent_iff_forall, isNilpotent_toEnd_genWeightSpace_zero
-/
instance [IsNoetherian R M] :
    IsNilpotent L (genWeightSpace M (0 : L -> R)) :=
isNilpotent_iff_forall'.mpr isNilpotent_toEnd_genWeightSpace_zero M

variable (R L)

@[simp]
/--
lemma `genWeightSpace_zero_normalizer_eq_self` / 引理 `genWeightSpace_zero_normalizer_eq_self`

English:
lemma genWeightSpace_zero_normalizer_eq_self
  proof: by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, Module.End.mul_eq_comp]

中文:
引理 genWeightSpace_zero_normalizer_eq_self
  证明: by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, Module.End.mul_eq_comp]

Depends on / 依赖: LieSubmodule, LieSubmodule.le_normalizer, LieSubmodule.mem_normalizer, Module, Module.End.mul_eq_comp, Pi.zero_apply, le_antisymm, le_normalizer, mem_genWeightSpace, mem_normalizer, mul_eq_comp, pow_succ, sub_zero, zero_apply, zero_smul
-/
lemma genWeightSpace_zero_normalizer_eq_self :
    (genWeightSpace M (0 : L -> R)).normalizer = genWeightSpace M 0 := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, Module.End.mul_eq_comp]

/--
lemma `iSup_ucs_le_genWeightSpace_zero` / 引理 `iSup_ucs_le_genWeightSpace_zero`

English:
lemma iSup_ucs_le_genWeightSpace_zero
  proof: by
  simpa using
    LieSubmodule.ucs_le_of_normalizer_eq_self (genWeightSpace_zero_normalizer_eq_self R L M)

中文:
引理 iSup_ucs_le_genWeightSpace_zero
  证明: by
  simpa using
    LieSubmodule.ucs_le_of_normalizer_eq_self (genWeightSpace_zero_normalizer_eq_self R L M)

Depends on / 依赖: LieSubmodule, LieSubmodule.ucs_le_of_normalizer_eq_self, genWeightSpace_zero_normalizer_eq_self, ucs_le_of_normalizer_eq_self
-/
lemma iSup_ucs_le_genWeightSpace_zero :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k <= genWeightSpace M (0 : L -> R) := by
  simpa using
    LieSubmodule.ucs_le_of_normalizer_eq_self (genWeightSpace_zero_normalizer_eq_self R L M)

/--
lemma `iSup_ucs_eq_genWeightSpace_zero` / 引理 `iSup_ucs_eq_genWeightSpace_zero`

English:
lemma iSup_ucs_eq_genWeightSpace_zero
  given: [IsNoetherian R M]
  proof: by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
 genWeightSpace M (0 : L -> R)).mp inferInstance
  refine le_antisymm (iSup_ucs_le_genWeightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k => (⊥ : LieSubmodule R L M).ucs k) k

中文:
引理 iSup_ucs_eq_genWeightSpace_zero
  条件: [IsNoetherian R M]
  证明: by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
 genWeightSpace M (0 : L -> R)).mp inferInstance
  refine le_antisymm (iSup_ucs_le_genWeightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k => (⊥ : LieSubmodule R L M).ucs k) k

Depends on / 依赖: LieSubmodule, LieSubmodule.isNilpotent_iff_exists_self_le_ucs, SetLike, SetLike.ext, SetLike.ext_iff.mp, ext_iff, f.range_localizedMap_eq_localized, genWeightSpace, iSup_ucs_le_genWeightSpace_zero, isNilpotent_iff_exists_self_le_ucs, le_antisymm, le_iSup, le_trans
-/
lemma iSup_ucs_eq_genWeightSpace_zero [IsNoetherian R M] :
    ⨆ k, (⊥ : LieSubmodule R L M).ucs k = genWeightSpace M (0 : L -> R) := by
  obtain ⟨k, hk⟩ := (LieSubmodule.isNilpotent_iff_exists_self_le_ucs
 genWeightSpace M (0 : L -> R)).mp inferInstance
  refine le_antisymm (iSup_ucs_le_genWeightSpace_zero R L M) (le_trans hk ?_)
  exact le_iSup (fun k => (⊥ : LieSubmodule R L M).ucs k) k

variable {L}

/--
Definition of `posFittingCompOf` / `posFittingCompOf` 的定义

English:
definition posFittingCompOf
  signature: (x : L)
  body: { toSubmodule := ⨅ k, LinearMap.range (toEnd R L M x ^ k)
    lie_mem := by
      set φ := toEnd R L M x
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_iInf, LinearMap.mem_range] at hm ⊢
      intr

中文:
定义 posFittingCompOf
  签名: (x : L)
  定义体: { toSubmodule := ⨅ k, LinearMap.range (toEnd R L M x ^ k)
    lie_mem := by
      set φ := toEnd R L M x
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_iInf, LinearMap.mem_range] at hm ⊢
      intr

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, LieAlgebra, LieAlgebra.ad, LieAlgebra.nilpotent_ad_of_nilpotent_algebra, LinearMap, LinearMap.mem_range, LinearMap.range, Module, Module.End, Submodule, Submodule.mem_iInf, Submodule.mem_toAddSubmonoid, lTensor, lie_mem, mem_carrier, mem_iInf, mem_range
-/
def posFittingCompOf (x : L) : LieSubmodule R L M :=
  { toSubmodule := ⨅ k, LinearMap.range (toEnd R L M x ^ k)
    lie_mem := by
      set φ := toEnd R L M x
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Submodule.mem_iInf, LinearMap.mem_range] at hm ⊢
      intro k
      obtain ⟨N, hN⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra R L
      obtain ⟨m, rfl⟩ := hm (N + k)
      let f₁ : Module.End R (L otimes[R] M) := (LieAlgebra.ad R L x).rTensor M
      let f₂ : Module.End R (L otimes[R] M) := φ.lTensor L
      replace hN : f₁ ^ N = 0 := by ext; simp [f₁, hN]
      have h₁ : Commute f₁ f₂ := by ext; simp [f₁, f₂]
      have h₂ : φ ∘ₗ toModuleHom R L M = toModuleHom R L M ∘ₗ (f₁ + f₂) := by ext; simp [φ, f₁, f₂]
      obtain ⟨q, hq⟩ := h₁.add_pow_dvd_pow_of_pow_eq_zero_right (N + k).le_succ hN
      use toModuleHom R L M (q (y otimesₜ m))
      change (φ ^ k).comp ((toModuleHom R L M : L otimes[R] M ->ₗ[R] M)) _ = _
      simp [φ, f₁, f₂, Module.End.commute_pow_left_of_commute h₂,
        LinearMap.comp_apply (g := (f₁ + f₂) ^ k), ← LinearMap.comp_apply (g := q),
        ← Module.End.mul_eq_comp, ← hq] }

variable {M} in
/--
lemma `mem_posFittingCompOf` / 引理 `mem_posFittingCompOf`

English:
lemma mem_posFittingCompOf
  given: (x : L) (m : M)
  proof: by
  simp [posFittingCompOf]

中文:
引理 mem_posFittingCompOf
  条件: (x : L) (m : M)
  证明: by
  simp [posFittingCompOf]

Depends on / 依赖: posFittingCompOf
-/
lemma mem_posFittingCompOf (x : L) (m : M) :
    m in posFittingCompOf R M x ↔ forall (k : Nat), exists n, (toEnd R L M x ^ k) n = m := by
  simp [posFittingCompOf]

/--
lemma `posFittingCompOf_le_lowerCentralSeries` / 引理 `posFittingCompOf_le_lowerCentralSeries`

English:
lemma posFittingCompOf_le_lowerCentralSeries
  given: (x : L) (k : Nat)
  proof: by
  suffices forall m l, (toEnd R L M x ^ l) m in lowerCentralSeries R L M l by
    intro m hm
    obtain ⟨n, rfl⟩ := (mem_posFittingCompOf R x m).mp hm k
    exact this n k
  intro m l
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [lowerCentralSeries_succ, pow_succ', Module.En

中文:
引理 posFittingCompOf_le_lowerCentralSeries
  条件: (x : L) (k : 自然数)
  证明: by
  suffices forall m l, (toEnd R L M x ^ l) m in lowerCentralSeries R L M l by
    intro m hm
    obtain ⟨n, rfl⟩ := (mem_posFittingCompOf R x m).mp hm k
    exact this n k
  intro m l
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [lowerCentralSeries_succ, pow_succ', Module.En
-/
@[simp] lemma posFittingCompOf_le_lowerCentralSeries (x : L) (k : Nat) :
    posFittingCompOf R M x <= lowerCentralSeries R L M k := by
  suffices forall m l, (toEnd R L M x ^ l) m in lowerCentralSeries R L M l by
    intro m hm
    obtain ⟨n, rfl⟩ := (mem_posFittingCompOf R x m).mp hm k
    exact this n k
  intro m l
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [lowerCentralSeries_succ, pow_succ', Module.End.mul_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih

/--
lemma `posFittingCompOf_eq_bot_of_isNilpotent` / 引理 `posFittingCompOf_eq_bot_of_isNilpotent`

English:
lemma posFittingCompOf_eq_bot_of_isNilpotent
  proof: by
  simp_rw [eq_bot_iff, ← iInf_lowerCentralSeries_eq_bot_of_isNilpotent, le_iInf_iff,
    posFittingCompOf_le_lowerCentralSeries, forall_const]

中文:
引理 posFittingCompOf_eq_bot_of_isNilpotent
  证明: by
  simp_rw [eq_bot_iff, ← iInf_lowerCentralSeries_eq_bot_of_isNilpotent, le_iInf_iff,
    posFittingCompOf_le_lowerCentralSeries, forall_const]
-/
@[simp] lemma posFittingCompOf_eq_bot_of_isNilpotent
    [IsNilpotent L M] (x : L) :
    posFittingCompOf R M x = ⊥ := by
  simp_rw [eq_bot_iff, ← iInf_lowerCentralSeries_eq_bot_of_isNilpotent, le_iInf_iff,
    posFittingCompOf_le_lowerCentralSeries, forall_const]

variable (L)

/--
Definition of `posFittingComp` / `posFittingComp` 的定义

English:
definition posFittingComp
  signature: : LieSubmodule R L M
  body: ⨆ x, posFittingCompOf R M x

中文:
定义 posFittingComp
  签名: : LieSubmodule R L M
  定义体: ⨆ x, posFittingCompOf R M x

Depends on / 依赖: posFittingCompOf
-/
def posFittingComp : LieSubmodule R L M :=
  ⨆ x, posFittingCompOf R M x

/--
lemma `mem_posFittingComp` / 引理 `mem_posFittingComp`

English:
lemma mem_posFittingComp
  given: (m : M)
  proof: by
  rfl

中文:
引理 mem_posFittingComp
  条件: (m : M)
  证明: by
  rfl
-/
lemma mem_posFittingComp (m : M) :
    m in posFittingComp R L M ↔ m in ⨆ (x : L), posFittingCompOf R M x := by
  rfl

/--
lemma `posFittingCompOf_le_posFittingComp` / 引理 `posFittingCompOf_le_posFittingComp`

English:
lemma posFittingCompOf_le_posFittingComp
  given: (x : L)
  proof: by
  rw [posFittingComp]; exact le_iSup (posFittingCompOf R M) x

中文:
引理 posFittingCompOf_le_posFittingComp
  条件: (x : L)
  证明: by
  rw [posFittingComp]; exact le_iSup (posFittingCompOf R M) x

Depends on / 依赖: le_iSup, posFittingComp, posFittingCompOf
-/
lemma posFittingCompOf_le_posFittingComp (x : L) :
    posFittingCompOf R M x <= posFittingComp R L M := by
  rw [posFittingComp]; exact le_iSup (posFittingCompOf R M) x

/--
lemma `posFittingComp_le_iInf_lowerCentralSeries` / 引理 `posFittingComp_le_iInf_lowerCentralSeries`

English:
lemma posFittingComp_le_iInf_lowerCentralSeries
  proof: by
  simp [posFittingComp]

中文:
引理 posFittingComp_le_iInf_lowerCentralSeries
  证明: by
  simp [posFittingComp]

Depends on / 依赖: posFittingComp
-/
lemma posFittingComp_le_iInf_lowerCentralSeries :
    posFittingComp R L M <= ⨅ k, lowerCentralSeries R L M k := by
  simp [posFittingComp]

/--
lemma `iInf_lowerCentralSeries_eq_posFittingComp` / 引理 `iInf_lowerCentralSeries_eq_posFittingComp`

English:
lemma iInf_lowerCentralSeries_eq_posFittingComp
  proof: by
  refine le_antisymm ?_ (posFittingComp_le_iInf_lowerCentralSeries R L M)
  apply iInf_lcs_le_of_isNilpotent_quot
  rw [LieModule.isNilpotent_iff_forall' (R := R)]
  intro x
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEnd R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := po

中文:
引理 iInf_lowerCentralSeries_eq_posFittingComp
  证明: by
  refine le_antisymm ?_ (posFittingComp_le_iInf_lowerCentralSeries R L M)
  apply iInf_lcs_le_of_isNilpotent_quot
  rw [LieModule.isNilpotent_iff_forall' (R := R)]
  intro x
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEnd R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := po
-/
@[simp] lemma iInf_lowerCentralSeries_eq_posFittingComp
    [IsNoetherian R M] [IsArtinian R M] :
    ⨅ k, lowerCentralSeries R L M k = posFittingComp R L M := by
  refine le_antisymm ?_ (posFittingComp_le_iInf_lowerCentralSeries R L M)
  apply iInf_lcs_le_of_isNilpotent_quot
  rw [LieModule.isNilpotent_iff_forall' (R := R)]
  intro x
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (toEnd R L M x).eventually_iInf_range_pow_eq
  use k
  ext ⟨m⟩
  set F := posFittingComp R L M
  replace hk : (toEnd R L M x ^ k) m in F := by
    apply posFittingCompOf_le_posFittingComp R L M x
    simp_rw [← LieSubmodule.mem_toSubmodule, posFittingCompOf, hk k (le_refl k)]
    apply LinearMap.mem_range_self
  suffices (toEnd R L (M ⧸ F) x ^ k) (LieSubmodule.Quotient.mk (N := F) m) =
    LieSubmodule.Quotient.mk (N := F) ((toEnd R L M x ^ k) m)
      by simpa [Submodule.Quotient.quot_mk_eq_mk, this]
  have := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute
    (LieSubmodule.Quotient.toEnd_comp_mk' F x) k) m
  simpa using this

/--
lemma `posFittingComp_eq_bot_of_isNilpotent` / 引理 `posFittingComp_eq_bot_of_isNilpotent`

English:
lemma posFittingComp_eq_bot_of_isNilpotent
  proof: by
  simp [posFittingComp]

中文:
引理 posFittingComp_eq_bot_of_isNilpotent
  证明: by
  simp [posFittingComp]
-/
@[simp] lemma posFittingComp_eq_bot_of_isNilpotent
    [IsNilpotent L M] :
    posFittingComp R L M = ⊥ := by
  simp [posFittingComp]

section map_comap

variable {R L M}
variable
  {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  {χ : L -> R} (f : M ->ₗ⁅R,L⁆ M₂)

/--
lemma `map_posFittingComp_le` / 引理 `map_posFittingComp_le`

English:
lemma map_posFittingComp_le
  proof: by
  rw [posFittingComp]; rw [posFittingComp]; rw [LieSubmodule.map_iSup]
  refine iSup_mono fun y => LieSubmodule.map_le_iff_le_comap.mpr fun m hm => ?_
  simp only [mem_posFittingCompOf] at hm
  simp only [LieSubmodule.mem_comap, mem_posFittingCompOf]
  intro k
  obtain ⟨n, hn⟩ := hm k
  use f n
 

中文:
引理 map_posFittingComp_le
  证明: by
  rw [posFittingComp]; rw [posFittingComp]; rw [LieSubmodule.map_iSup]
  refine iSup_mono fun y => LieSubmodule.map_le_iff_le_comap.mpr fun m hm => ?_
  simp only [mem_posFittingCompOf] at hm
  simp only [LieSubmodule.mem_comap, mem_posFittingCompOf]
  intro k
  obtain ⟨n, hn⟩ := hm k
  use f n
 

Depends on / 依赖: LieModule, LieModule.toEnd_pow_apply_map, LieSubmodule, LieSubmodule.map_iSup, LieSubmodule.map_le_iff_le_comap.mpr, LieSubmodule.mem_comap, iSup_mono, map_iSup, map_le_iff_le_comap, mem_comap, mem_posFittingCompOf, posFittingComp, toEnd_pow_apply_map
-/
lemma map_posFittingComp_le :
    (posFittingComp R L M).map f <= posFittingComp R L M₂ := by
  rw [posFittingComp]; rw [posFittingComp]; rw [LieSubmodule.map_iSup]
  refine iSup_mono fun y => LieSubmodule.map_le_iff_le_comap.mpr fun m hm => ?_
  simp only [mem_posFittingCompOf] at hm
  simp only [LieSubmodule.mem_comap, mem_posFittingCompOf]
  intro k
  obtain ⟨n, hn⟩ := hm k
  use f n
  rw [LieModule.toEnd_pow_apply_map]; rw [hn]

/--
lemma `map_genWeightSpace_le` / 引理 `map_genWeightSpace_le`

English:
lemma map_genWeightSpace_le
  proof: by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, mem_genWeightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (mem_genWeightSpace _ _ _).mp hm x
  refine ⟨k, ?_⟩
  simpa [h

中文:
引理 map_genWeightSpace_le
  证明: by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, mem_genWeightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (mem_genWeightSpace _ _ _).mp hm x
  refine ⟨k, ?_⟩
  simpa [h

Depends on / 依赖: LieSubmodule, LieSubmodule.map_le_iff_le_comap, LieSubmodule.mem_comap, LinearMap, LinearMap.congr_fun, Module, Module.End.commute_pow_left_of_commute, commute_pow_left_of_commute, congr_fun, map_le_iff_le_comap, mem_comap, mem_genWeightSpace
-/
lemma map_genWeightSpace_le :
    (genWeightSpace M χ).map f <= genWeightSpace M₂ χ := by
  rw [LieSubmodule.map_le_iff_le_comap]
  intro m hm
  simp only [LieSubmodule.mem_comap, mem_genWeightSpace]
  intro x
  have : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f = f ∘ₗ (toEnd R L M x - χ x • ↑1) := by
    ext; simp
  obtain ⟨k, h⟩ := (mem_genWeightSpace _ _ _).mp hm x
  refine ⟨k, ?_⟩
  simpa [h] using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute this k) m

variable {f}

/--
lemma `comap_genWeightSpace_eq_of_injective` / 引理 `comap_genWeightSpace_eq_of_injective`

English:
lemma comap_genWeightSpace_eq_of_injective
  given: (hf : Injective f)
  proof: by
  refine le_antisymm (fun m hm => ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_genWeightSpace] at hm
    simp only [mem_genWeightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use 

中文:
引理 comap_genWeightSpace_eq_of_injective
  条件: (hf : Injective f)
  证明: by
  refine le_antisymm (fun m hm => ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_genWeightSpace] at hm
    simp only [mem_genWeightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use 

Depends on / 依赖: LieSubmodule, LieSubmodule.map_le_iff_le_comap, LieSubmodule.mem_comap, LinearMap, LinearMap.congr_fun, Module, Module.End.commute_pow_left_of_commute, commute_pow_left_of_commute, congr_fun, le_antisymm, map_le_iff_le_comap, map_zero, mem_comap, mem_genWeightSpace
-/
lemma comap_genWeightSpace_eq_of_injective (hf : Injective f) :
    (genWeightSpace M₂ χ).comap f = genWeightSpace M χ := by
  refine le_antisymm (fun m hm => ?_) ?_
  · simp only [LieSubmodule.mem_comap, mem_genWeightSpace] at hm
    simp only [mem_genWeightSpace]
    intro x
    have h : (toEnd R L M₂ x - χ x • ↑1) ∘ₗ f =
             f ∘ₗ (toEnd R L M x - χ x • ↑1) := by ext; simp
    obtain ⟨k, hk⟩ := hm x
    use k
    suffices f (((toEnd R L M x - χ x • ↑1) ^ k) m) = 0 by
      rw [← map_zero f] at this; exact hf this
    simpa [hk] using (LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h k) m).symm
  · rw [← LieSubmodule.map_le_iff_le_comap]
    exact map_genWeightSpace_le f

/--
lemma `map_genWeightSpace_eq_of_injective` / 引理 `map_genWeightSpace_eq_of_injective`

English:
lemma map_genWeightSpace_eq_of_injective
  given: (hf : Injective f)
  proof: by
  refine le_antisymm (le_inf_iff.mpr ⟨map_genWeightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_genWeightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

中文:
引理 map_genWeightSpace_eq_of_injective
  条件: (hf : Injective f)
  证明: by
  refine le_antisymm (le_inf_iff.mpr ⟨map_genWeightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_genWeightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

Depends on / 依赖: LieSubmodule, LieSubmodule.map_le_range, LieSubmodule.mem_comap, LieSubmodule.mem_map, comap_genWeightSpace_eq_of_injective, le_antisymm, le_inf_iff, le_inf_iff.mpr, map_genWeightSpace_le, map_le_range, mem_comap, mem_map
-/
lemma map_genWeightSpace_eq_of_injective (hf : Injective f) :
    (genWeightSpace M χ).map f = genWeightSpace M₂ χ ⊓ f.range := by
  refine le_antisymm (le_inf_iff.mpr ⟨map_genWeightSpace_le f, LieSubmodule.map_le_range f⟩) ?_
  rintro - ⟨hm, ⟨m, rfl⟩⟩
  simp only [← comap_genWeightSpace_eq_of_injective hf, LieSubmodule.mem_map,
    LieSubmodule.mem_comap]
  exact ⟨m, hm, rfl⟩

/--
lemma `map_genWeightSpace_eq` / 引理 `map_genWeightSpace_eq`

English:
lemma map_genWeightSpace_eq
  given: (e : M ≃ₗ⁅R,L⁆ M₂)
  proof: by
  simp [map_genWeightSpace_eq_of_injective e.injective]

中文:
引理 map_genWeightSpace_eq
  条件: (e : M ≃ₗ⁅R,L⁆ M₂)
  证明: by
  simp [map_genWeightSpace_eq_of_injective e.injective]

Depends on / 依赖: e.injective, injective, map_genWeightSpace_eq_of_injective
-/
lemma map_genWeightSpace_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (genWeightSpace M χ).map e = genWeightSpace M₂ χ := by
  simp [map_genWeightSpace_eq_of_injective e.injective]

/--
lemma `map_posFittingComp_eq` / 引理 `map_posFittingComp_eq`

English:
lemma map_posFittingComp_eq
  given: (e : M ≃ₗ⁅R,L⁆ M₂)
  proof: by
  refine le_antisymm (map_posFittingComp_le _) ?_
  suffices posFittingComp R L M₂ = ((posFittingComp R L M₂).map (e.symm : M₂ ->ₗ⁅R,L⁆ M)).map e by
    rw [this]
    exact LieSubmodule.map_mono (map_posFittingComp_le _)
  rw [← LieSubmodule.map_comp]
  convert! LieSubmodule.map_id
  ext
  simp

中文:
引理 map_posFittingComp_eq
  条件: (e : M ≃ₗ⁅R,L⁆ M₂)
  证明: by
  refine le_antisymm (map_posFittingComp_le _) ?_
  suffices posFittingComp R L M₂ = ((posFittingComp R L M₂).map (e.symm : M₂ ->ₗ⁅R,L⁆ M)).map e by
    rw [this]
    exact LieSubmodule.map_mono (map_posFittingComp_le _)
  rw [← LieSubmodule.map_comp]
  convert! LieSubmodule.map_id
  ext
  simp

Depends on / 依赖: LieSubmodule, LieSubmodule.map_comp, LieSubmodule.map_id, LieSubmodule.map_mono, convert, e.symm, le_antisymm, map_comp, map_id, map_mono, map_posFittingComp_le, posFittingComp
-/
lemma map_posFittingComp_eq (e : M ≃ₗ⁅R,L⁆ M₂) :
    (posFittingComp R L M).map e = posFittingComp R L M₂ := by
  refine le_antisymm (map_posFittingComp_le _) ?_
  suffices posFittingComp R L M₂ = ((posFittingComp R L M₂).map (e.symm : M₂ ->ₗ⁅R,L⁆ M)).map e by
    rw [this]
    exact LieSubmodule.map_mono (map_posFittingComp_le _)
  rw [← LieSubmodule.map_comp]
  convert! LieSubmodule.map_id
  ext
  simp

/--
lemma `posFittingComp_map_incl_sup_of_codisjoint` / 引理 `posFittingComp_map_incl_sup_of_codisjoint`

English:
lemma posFittingComp_map_incl_sup_of_codisjoint
  statement: [IsNoetherian R M] [IsArtinian R M]
  proof: by
obtain ⟨l, hl⟩ := Filter.eventually_atTop.mp
(eventually_iInf_lowerCentralSeries_eq R L N₁).and
    (eventually_iInf_lowerCentralSeries_eq R L N₂).and
    (eventually_iInf_lowerCentralSeries_eq R L M)
  obtain ⟨hl₁, hl₂, hl₃⟩ := hl l (le_refl _)
  simp_rw [← iInf_lowerCentralSeries_eq_posFittingC

中文:
引理 posFittingComp_map_incl_sup_of_codisjoint
  结论: [IsNoetherian R M] [IsArtinian R M]
  证明: by
obtain ⟨l, hl⟩ := Filter.eventually_atTop.mp
(eventually_iInf_lowerCentralSeries_eq R L N₁).and
    (eventually_iInf_lowerCentralSeries_eq R L N₂).and
    (eventually_iInf_lowerCentralSeries_eq R L M)
  obtain ⟨hl₁, hl₂, hl₃⟩ := hl l (le_refl _)
  simp_rw [← iInf_lowerCentralSeries_eq_posFittingC

Depends on / 依赖: Filter, Filter.eventually_atTop.mp, LieSubmodule, LieSubmodule.lcs_sup, LieSubmodule.lowerCentralSeries_map_eq_lcs, eq_top, eventually_atTop, eventually_iInf_lowerCentralSeries_eq, h.eq_top, iInf_lowerCentralSeries_eq_posFittingComp, lcs_sup, le_refl, lowerCentralSeries, lowerCentralSeries_map_eq_lcs, simp_rw
-/
lemma posFittingComp_map_incl_sup_of_codisjoint [IsNoetherian R M] [IsArtinian R M]
    {N₁ N₂ : LieSubmodule R L M} (h : Codisjoint N₁ N₂) :
    (posFittingComp R L N₁).map N₁.incl ⊔ (posFittingComp R L N₂).map N₂.incl =
    posFittingComp R L M := by
obtain ⟨l, hl⟩ := Filter.eventually_atTop.mp
(eventually_iInf_lowerCentralSeries_eq R L N₁).and
    (eventually_iInf_lowerCentralSeries_eq R L N₂).and
    (eventually_iInf_lowerCentralSeries_eq R L M)
  obtain ⟨hl₁, hl₂, hl₃⟩ := hl l (le_refl _)
  simp_rw [← iInf_lowerCentralSeries_eq_posFittingComp, hl₁, hl₂, hl₃,
    LieSubmodule.lowerCentralSeries_map_eq_lcs, ← LieSubmodule.lcs_sup, lowerCentralSeries,
    h.eq_top]

/--
lemma `genWeightSpace_genWeightSpaceOf_map_incl` / 引理 `genWeightSpace_genWeightSpaceOf_map_incl`

English:
lemma genWeightSpace_genWeightSpaceOf_map_incl
  given: (x : L) (χ : L -> R)
  proof: by
  simpa [map_genWeightSpace_eq_of_injective (genWeightSpaceOf M (χ x) x).injective_incl]
    using genWeightSpace_le_genWeightSpaceOf M x χ

中文:
引理 genWeightSpace_genWeightSpaceOf_map_incl
  条件: (x : L) (χ : L -> R)
  证明: by
  simpa [map_genWeightSpace_eq_of_injective (genWeightSpaceOf M (χ x) x).injective_incl]
    using genWeightSpace_le_genWeightSpaceOf M x χ

Depends on / 依赖: genWeightSpaceOf, genWeightSpace_le_genWeightSpaceOf, injective_incl, map_genWeightSpace_eq_of_injective
-/
lemma genWeightSpace_genWeightSpaceOf_map_incl (x : L) (χ : L -> R) :
    (genWeightSpace (genWeightSpaceOf M (χ x) x) χ).map (genWeightSpaceOf M (χ x) x).incl =
    genWeightSpace M χ := by
  simpa [map_genWeightSpace_eq_of_injective (genWeightSpaceOf M (χ x) x).injective_incl]
    using genWeightSpace_le_genWeightSpaceOf M x χ

end map_comap

section fitting_decomposition

variable [IsNoetherian R M] [IsArtinian R M]

/--
lemma `isCompl_genWeightSpaceOf_zero_posFittingCompOf` / 引理 `isCompl_genWeightSpaceOf_zero_posFittingCompOf`

English:
lemma isCompl_genWeightSpaceOf_zero_posFittingCompOf
  given: (x : L)
  proof: by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.toSubmodule_inj,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule,
    LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule, coe_genWeightSpaceOf_zero] using!
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_

中文:
引理 isCompl_genWeightSpaceOf_zero_posFittingCompOf
  条件: (x : L)
  证明: by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.toSubmodule_inj,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule,
    LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule, coe_genWeightSpaceOf_zero] using!
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_

Depends on / 依赖: LieSubmodule, LieSubmodule.bot_toSubmodule, LieSubmodule.inf_toSubmodule, LieSubmodule.sup_toSubmodule, LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule, bot_toSubmodule, codisjoint_iff, coe_genWeightSpaceOf_zero, disjoint_iff, inf_toSubmodule, isCompl_iSup_ker_pow_iInf_range_pow, isCompl_iff, sup_toSubmodule, toSubmodule_inj, top_toSubmodule
-/
lemma isCompl_genWeightSpaceOf_zero_posFittingCompOf (x : L) :
    IsCompl (genWeightSpaceOf M 0 x) (posFittingCompOf R M x) := by
  simpa only [isCompl_iff, codisjoint_iff, disjoint_iff, ← LieSubmodule.toSubmodule_inj,
    LieSubmodule.sup_toSubmodule, LieSubmodule.inf_toSubmodule,
    LieSubmodule.top_toSubmodule, LieSubmodule.bot_toSubmodule, coe_genWeightSpaceOf_zero] using!
    (toEnd R L M x).isCompl_iSup_ker_pow_iInf_range_pow

/--
lemma `isCompl_genWeightSpace_zero_posFittingComp_aux` / 引理 `isCompl_genWeightSpace_zero_posFittingComp_aux`

English:
lemma isCompl_genWeightSpace_zero_posFittingComp_aux
  proof: by
  set M₀ := genWeightSpace M (0 : L -> R)
  set M₁ := posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) => genWeightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : genWeightSpaceOf M (0 : R) x != ⊤⟩
  · suffices IsNilpotent L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤

中文:
引理 isCompl_genWeightSpace_zero_posFittingComp_aux
  证明: by
  set M₀ := genWeightSpace M (0 : L -> R)
  set M₁ := posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) => genWeightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : genWeightSpaceOf M (0 : R) x != ⊤⟩
  · suffices IsNilpotent L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤
-/
private lemma isCompl_genWeightSpace_zero_posFittingComp_aux
    (h : forall N < (⊤ : LieSubmodule R L M), IsCompl (genWeightSpace N 0) (posFittingComp R L N)) :
    IsCompl (genWeightSpace M 0) (posFittingComp R L M) := by
  set M₀ := genWeightSpace M (0 : L -> R)
  set M₁ := posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) => genWeightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : genWeightSpaceOf M (0 : R) x != ⊤⟩
  · suffices IsNilpotent L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤ := by simpa [M₀, genWeightSpace]
    rw [← LieModule.isNilpotent_of_top_iff' (R := R)]; rw [← h]
    infer_instance
  · set M₀ₓ := genWeightSpaceOf M (0 : R) x
    set M₁ₓ := posFittingCompOf R M x
    set M₀ₓ₀ := genWeightSpace M₀ₓ (0 : L -> R)
    set M₀ₓ₁ := posFittingComp R L M₀ₓ
    have h₁ : IsCompl M₀ₓ M₁ₓ := isCompl_genWeightSpaceOf_zero_posFittingCompOf R L M x
    have h₂ : IsCompl M₀ₓ₀ M₀ₓ₁ := h M₀ₓ hx.lt_top
    have h₃ : M₀ₓ₀.map M₀ₓ.incl = M₀ := by
      rw [map_genWeightSpace_eq_of_injective M₀ₓ.injective_incl]; rw [inf_eq_left]; rw [LieSubmodule.range_incl]
      exact iInf_le _ x
    have h₄ : M₀ₓ₁.map M₀ₓ.incl ⊔ M₁ₓ = M₁ := by
apply le_antisymm sup_le_iff.mpr
        ⟨map_posFittingComp_le _, posFittingCompOf_le_posFittingComp R L M x⟩
      rw [← posFittingComp_map_incl_sup_of_codisjoint h₁.codisjoint]
      exact sup_le_sup_left LieSubmodule.map_incl_le _
    rw [← h₃]; rw [← h₄]
    apply Disjoint.isCompl_sup_right_of_isCompl_sup_left
    · rw [disjoint_iff, ← LieSubmodule.map_inf M₀ₓ.injective_incl, h₂.inf_eq_bot,
        LieSubmodule.map_bot]
    · rwa [← LieSubmodule.map_sup, h₂.sup_eq_top, LieModuleHom.map_top, LieSubmodule.range_incl]

/--
lemma `isCompl_genWeightSpace_zero_posFittingComp` / 引理 `isCompl_genWeightSpace_zero_posFittingComp`

English:
lemma isCompl_genWeightSpace_zero_posFittingComp
  proof: by
  let P : LieSubmodule R L M -> Prop := fun N => IsCompl (genWeightSpace N 0) (posFittingComp R L N)
  suffices P ⊤ by
    let e := LieModuleEquiv.ofTop R L M
    rw [← map_genWeightSpace_eq e]; rw [← map_posFittingComp_eq e]
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mp this
  induc

中文:
引理 isCompl_genWeightSpace_zero_posFittingComp
  证明: by
  let P : LieSubmodule R L M -> Prop := fun N => IsCompl (genWeightSpace N 0) (posFittingComp R L N)
  suffices P ⊤ by
    let e := LieModuleEquiv.ofTop R L M
    rw [← map_genWeightSpace_eq e]; rw [← map_posFittingComp_eq e]
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mp this
  induc

Depends on / 依赖: IsCompl, LieModuleEquiv, LieModuleEquiv.ofTop, LieSubmodule, LieSubmodule.orderIsoMapComap, LieSubmodule.wellFoundedLT_of_isArtinian, genWeightSpa, genWeightSpace, isCompl_genWeightSpace_zero_posFittingComp_aux, isCompl_iff, isCompl_iff.mp, map_genWeightSpace_eq, map_posFittingComp_eq, orderIsoMapComap, posFittingComp, wellFoundedLT_of_isArtinian
-/
lemma isCompl_genWeightSpace_zero_posFittingComp :
    IsCompl (genWeightSpace M 0) (posFittingComp R L M) := by
  let P : LieSubmodule R L M -> Prop := fun N => IsCompl (genWeightSpace N 0) (posFittingComp R L N)
  suffices P ⊤ by
    let e := LieModuleEquiv.ofTop R L M
    rw [← map_genWeightSpace_eq e]; rw [← map_posFittingComp_eq e]
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mp this
  induction (⊤ : LieSubmodule R L M) using
    (LieSubmodule.wellFoundedLT_of_isArtinian R L M).induction with | ind N hN
  refine isCompl_genWeightSpace_zero_posFittingComp_aux R L N fun N' hN' => ?_
  suffices IsCompl (genWeightSpace (N'.map N.incl) 0) (posFittingComp R L (N'.map N.incl)) by
    let e := LieSubmodule.equivMapOfInjective N' N.injective_incl
    rw [← map_genWeightSpace_eq e]; rw [← map_posFittingComp_eq e] at this
    exact (LieSubmodule.orderIsoMapComap e).isCompl_iff.mpr this
  exact hN _ (LieSubmodule.map_incl_lt_iff_lt_top.mpr hN')

end fitting_decomposition

section IsTorsionFree
variable [IsDomain R] [Module.IsTorsionFree R M]

/--
lemma `disjoint_genWeightSpaceOf` / 引理 `disjoint_genWeightSpaceOf`

English:
lemma disjoint_genWeightSpaceOf
  given: {x : L} {φ₁ φ₂ : R} (h : φ₁ != φ₂)
  proof: by
  rw [← LieSubmodule.disjoint_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact Module.End.disjoint_genEigenspace _ h _ _

中文:
引理 disjoint_genWeightSpaceOf
  条件: {x : L} {φ₁ φ₂ : R} (h : φ₁ != φ₂)
  证明: by
  rw [← LieSubmodule.disjoint_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact Module.End.disjoint_genEigenspace _ h _ _

Depends on / 依赖: LieSubmodule, LieSubmodule.disjoint_toSubmodule, Module, Module.End.disjoint_genEigenspace, disjoint_genEigenspace, disjoint_toSubmodule, genWeightSpaceOf
-/
lemma disjoint_genWeightSpaceOf {x : L} {φ₁ φ₂ : R} (h : φ₁ != φ₂) :
    Disjoint (genWeightSpaceOf M φ₁ x) (genWeightSpaceOf M φ₂ x) := by
  rw [← LieSubmodule.disjoint_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact Module.End.disjoint_genEigenspace _ h _ _

/--
lemma `disjoint_genWeightSpace` / 引理 `disjoint_genWeightSpace`

English:
lemma disjoint_genWeightSpace
  given: {χ₁ χ₂ : L -> R} (h : χ₁ != χ₂)
  proof: by
  obtain ⟨x, hx⟩ : exists x, χ₁ x != χ₂ x := Function.ne_iff.mp h
  exact (disjoint_genWeightSpaceOf R L M hx).mono
    (genWeightSpace_le_genWeightSpaceOf M x χ₁) (genWeightSpace_le_genWeightSpaceOf M x χ₂)

中文:
引理 disjoint_genWeightSpace
  条件: {χ₁ χ₂ : L -> R} (h : χ₁ != χ₂)
  证明: by
  obtain ⟨x, hx⟩ : exists x, χ₁ x != χ₂ x := Function.ne_iff.mp h
  exact (disjoint_genWeightSpaceOf R L M hx).mono
    (genWeightSpace_le_genWeightSpaceOf M x χ₁) (genWeightSpace_le_genWeightSpaceOf M x χ₂)

Depends on / 依赖: Function, Function.ne_iff.mp, disjoint_genWeightSpaceOf, genWeightSpace_le_genWeightSpaceOf, ne_iff
-/
lemma disjoint_genWeightSpace {χ₁ χ₂ : L -> R} (h : χ₁ != χ₂) :
    Disjoint (genWeightSpace M χ₁) (genWeightSpace M χ₂) := by
  obtain ⟨x, hx⟩ : exists x, χ₁ x != χ₂ x := Function.ne_iff.mp h
  exact (disjoint_genWeightSpaceOf R L M hx).mono
    (genWeightSpace_le_genWeightSpaceOf M x χ₁) (genWeightSpace_le_genWeightSpaceOf M x χ₂)

/--
lemma `injOn_genWeightSpace` / 引理 `injOn_genWeightSpace`

English:
lemma injOn_genWeightSpace
  proof: by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : genWeightSpace M χ₁ = genWeightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_genWeightSpace R L M hχ₂

中文:
引理 injOn_genWeightSpace
  证明: by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : genWeightSpace M χ₁ = genWeightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_genWeightSpace R L M hχ₂

Depends on / 依赖: contrapose, disjoint_genWeightSpace, genWeightSpace
-/
lemma injOn_genWeightSpace :
    InjOn (fun (χ : L -> R) => genWeightSpace M χ) {χ | genWeightSpace M χ != ⊥} := by
  rintro χ₁ _ χ₂ hχ₂ (hχ₁₂ : genWeightSpace M χ₁ = genWeightSpace M χ₂)
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_genWeightSpace R L M hχ₂

/--
lemma `iSupIndep_genWeightSpace` / 引理 `iSupIndep_genWeightSpace`

English:
lemma iSupIndep_genWeightSpace
  statement: iSupIndep fun χ : L -> R => genWeightSpace M χ
  proof: by
  simp only [← LieSubmodule.iSupIndep_toSubmodule, genWeightSpace,
    LieSubmodule.iInf_toSubmodule]
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (toEnd R L M)
    (fun x y φ z => (genWeightSpaceOf M φ y).lie_mem)

中文:
引理 iSupIndep_genWeightSpace
  结论: iSupIndep fun χ : L -> R => genWeightSpace M χ
  证明: by
  simp only [← LieSubmodule.iSupIndep_toSubmodule, genWeightSpace,
    LieSubmodule.iInf_toSubmodule]
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (toEnd R L M)
    (fun x y φ z => (genWeightSpaceOf M φ y).lie_mem)

Depends on / 依赖: LieSubmodule, LieSubmodule.iInf_toSubmodule, LieSubmodule.iSupIndep_toSubmodule, Module, Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo, genWeightSpace, genWeightSpaceOf, iInf_toSubmodule, iSupIndep_toSubmodule, independent_iInf_maxGenEigenspace_of_forall_mapsTo, lie_mem
-/
lemma iSupIndep_genWeightSpace : iSupIndep fun χ : L -> R => genWeightSpace M χ := by
  simp only [← LieSubmodule.iSupIndep_toSubmodule, genWeightSpace,
    LieSubmodule.iInf_toSubmodule]
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (toEnd R L M)
    (fun x y φ z => (genWeightSpaceOf M φ y).lie_mem)

/--
lemma `iSupIndep_genWeightSpace'` / 引理 `iSupIndep_genWeightSpace'`

English:
lemma iSupIndep_genWeightSpace'
  statement: iSupIndep fun χ : Weight R L M => genWeightSpace M χ
  proof: (iSupIndep_genWeightSpace R L M).comp
    Subtype.val_injective.comp (Weight.equivSetOfPred R L M).injective

中文:
引理 iSupIndep_genWeightSpace'
  结论: iSupIndep fun χ : Weight R L M => genWeightSpace M χ
  证明: (iSupIndep_genWeightSpace R L M).comp
    Subtype.val_injective.comp (Weight.equivSetOfPred R L M).injective

Depends on / 依赖: Subtype, Subtype.val_injective.comp, Weight, Weight.equivSetOfPred, equivSetOfPred, iSupIndep_genWeightSpace, injective, val_injective
-/
lemma iSupIndep_genWeightSpace' : iSupIndep fun χ : Weight R L M => genWeightSpace M χ :=
(iSupIndep_genWeightSpace R L M).comp
    Subtype.val_injective.comp (Weight.equivSetOfPred R L M).injective

/--
lemma `iSupIndep_genWeightSpaceOf` / 引理 `iSupIndep_genWeightSpaceOf`

English:
lemma iSupIndep_genWeightSpaceOf
  given: (x : L)
  statement: iSupIndep fun (χ : R) => genWeightSpaceOf M χ x
  proof: by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact (toEnd R L M x).independent_genEigenspace _

中文:
引理 iSupIndep_genWeightSpaceOf
  条件: (x : L)
  结论: iSupIndep fun (χ : R) => genWeightSpaceOf M χ x
  证明: by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact (toEnd R L M x).independent_genEigenspace _

Depends on / 依赖: LieSubmodule, LieSubmodule.iSupIndep_toSubmodule, genWeightSpaceOf, iSupIndep_toSubmodule, independent_genEigenspace
-/
lemma iSupIndep_genWeightSpaceOf (x : L) : iSupIndep fun (χ : R) => genWeightSpaceOf M χ x := by
  rw [← LieSubmodule.iSupIndep_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact (toEnd R L M x).independent_genEigenspace _

/--
lemma `finite_genWeightSpaceOf_ne_bot` / 引理 `finite_genWeightSpaceOf_ne_bot`

English:
lemma finite_genWeightSpaceOf_ne_bot
  given: [IsNoetherian R M] (x : L)
  proof: WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpaceOf R L M x)

中文:
引理 finite_genWeightSpaceOf_ne_bot
  条件: [IsNoetherian R M] (x : L)
  证明: WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpaceOf R L M x)

Depends on / 依赖: WellFoundedGT, WellFoundedGT.finite_ne_bot_of_iSupIndep, finite_ne_bot_of_iSupIndep, iSupIndep_genWeightSpaceOf
-/
lemma finite_genWeightSpaceOf_ne_bot [IsNoetherian R M] (x : L) :
    {χ : R | genWeightSpaceOf M χ x != ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpaceOf R L M x)

/--
lemma `finite_genWeightSpace_ne_bot` / 引理 `finite_genWeightSpace_ne_bot`

English:
lemma finite_genWeightSpace_ne_bot
  given: [IsNoetherian R M]
  proof: WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpace R L M)

中文:
引理 finite_genWeightSpace_ne_bot
  条件: [IsNoetherian R M]
  证明: WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpace R L M)

Depends on / 依赖: WellFoundedGT, WellFoundedGT.finite_ne_bot_of_iSupIndep, finite_ne_bot_of_iSupIndep, iSupIndep_genWeightSpace
-/
lemma finite_genWeightSpace_ne_bot [IsNoetherian R M] :
    {χ : L -> R | genWeightSpace M χ != ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_genWeightSpace R L M)

/--
Instance `Weight.instFinite` / 实例 `Weight.instFinite`

English:
instance Weight.instFinite
  signature: [IsNoetherian R M]
  body: by
  have : Finite {χ : L -> R | genWeightSpace M χ != ⊥} := finite_genWeightSpace_ne_bot R L M
  exact Finite.of_injective (equivSetOfPred R L M) (equivSetOfPred R L M).injective

中文:
实例 Weight.instFinite
  签名: [IsNoetherian R M]
  定义体: by
  have : Finite {χ : L -> R | genWeightSpace M χ != ⊥} := finite_genWeightSpace_ne_bot R L M
  exact Finite.of_injective (equivSetOfPred R L M) (equivSetOfPred R L M).injective

Depends on / 依赖: Finite, Finite.of_injective, equivSetOfPred, finite_genWeightSpace_ne_bot, genWeightSpace, injective, of_injective
-/
instance Weight.instFinite [IsNoetherian R M] : Finite (Weight R L M) := by
  have : Finite {χ : L -> R | genWeightSpace M χ != ⊥} := finite_genWeightSpace_ne_bot R L M
  exact Finite.of_injective (equivSetOfPred R L M) (equivSetOfPred R L M).injective

/--
Instance `Weight.instFintype` / 实例 `Weight.instFintype`

English:
instance Weight.instFintype
  signature: [IsNoetherian R M]
  body: .ofFinite _

中文:
实例 Weight.instFintype
  签名: [IsNoetherian R M]
  定义体: .ofFinite _

Depends on / 依赖: ofFinite
-/
noncomputable instance Weight.instFintype [IsNoetherian R M] : Fintype (Weight R L M) := .ofFinite _

end IsTorsionFree

/--
Definition of `IsTriangularizable` / `IsTriangularizable` 的定义

English:
class IsTriangularizable
  parameters: : Prop where
  axioms and operations (1):
    - maxGenEigenspace_eq_top : forall x, ⨆ φ, (toEnd R L M x).maxGenEigenspace φ = ⊤

中文:
类 IsTriangularizable
  参数: : 命题 where
  公理与运算 (1 个):
    - maxGenEigenspace_eq_top : 对任意 x, ⨆ φ, (toEnd R L M x).maxGenEigenspace φ = ⊤
-/
class IsTriangularizable : Prop where
  maxGenEigenspace_eq_top : forall x, ⨆ φ, (toEnd R L M x).maxGenEigenspace φ = ⊤

instance (L' : LieSubalgebra R L) [IsTriangularizable R L M] : IsTriangularizable R L' M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

instance (I : LieIdeal R L) [IsTriangularizable R L M] : IsTriangularizable R I M where
  maxGenEigenspace_eq_top x := IsTriangularizable.maxGenEigenspace_eq_top (x : L)

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangularizable
  signature: R L M] : IsTriangularizable R (LieModule.toEnd R L M).range M where
  body: by
    rintro ⟨-, x, rfl⟩
    exact IsTriangularizable.maxGenEigenspace_eq_top x

omit [LieRing.IsNilpotent L] in

中文:
实例 [IsTriangularizable
  签名: R L M] : IsTriangularizable R (LieModule.toEnd R L M).range M where
  定义体: by
    rintro ⟨-, x, rfl⟩
    exact IsTriangularizable.maxGenEigenspace_eq_top x

omit [LieRing.IsNilpotent L] in

Depends on / 依赖: IsTriangularizable, IsTriangularizable.maxGenEigenspace_eq_top, maxGenEigenspace_eq_top
-/
instance [IsTriangularizable R L M] : IsTriangularizable R (LieModule.toEnd R L M).range M where
  maxGenEigenspace_eq_top := by
    rintro ⟨-, x, rfl⟩
    exact IsTriangularizable.maxGenEigenspace_eq_top x

omit [LieRing.IsNilpotent L] in
/--
lemma `IsTriangularizable.exists_hasEigenvalue` / 引理 `IsTriangularizable.exists_hasEigenvalue`

English:
lemma IsTriangularizable.exists_hasEigenvalue
  given: [Nontrivial M] [IsTriangularizable R L M] (x : L)
  proof: by
  suffices exists φ, (toEnd R L M x).maxGenEigenspace φ != ⊥ by
    obtain ⟨φ, hφ⟩ := this
    exact ⟨φ, (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one ENat.top_pos).mp hφ⟩
  have := maxGenEigenspace_eq_top (R := R) (L := L) (M := M) x
  contrapose! this
  simp [this]

@[simp]

中文:
引理 IsTriangularizable.exists_hasEigenvalue
  条件: [Nontrivial M] [IsTriangularizable R L M] (x : L)
  证明: by
  suffices exists φ, (toEnd R L M x).maxGenEigenspace φ != ⊥ by
    obtain ⟨φ, hφ⟩ := this
    exact ⟨φ, (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one ENat.top_pos).mp hφ⟩
  have := maxGenEigenspace_eq_top (R := R) (L := L) (M := M) x
  contrapose! this
  simp [this]

@[simp]

Depends on / 依赖: ENat.top_pos, Module, Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, contrapose, hasUnifEigenvalue_iff_hasUnifEigenvalue_one, maxGenEigenspace, maxGenEigenspace_eq_top, top_pos
-/
lemma IsTriangularizable.exists_hasEigenvalue [Nontrivial M] [IsTriangularizable R L M] (x : L) :
    exists φ, (toEnd R L M x).HasEigenvalue φ := by
  suffices exists φ, (toEnd R L M x).maxGenEigenspace φ != ⊥ by
    obtain ⟨φ, hφ⟩ := this
    exact ⟨φ, (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one ENat.top_pos).mp hφ⟩
  have := maxGenEigenspace_eq_top (R := R) (L := L) (M := M) x
  contrapose! this
  simp [this]

@[simp]
/--
lemma `iSup_genWeightSpaceOf_eq_top` / 引理 `iSup_genWeightSpaceOf_eq_top`

English:
lemma iSup_genWeightSpaceOf_eq_top
  given: [IsTriangularizable R L M] (x : L)
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.iSup_toSubmodule]; rw [LieSubmodule.top_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact IsTriangularizable.maxGenEigenspace_eq_top x

中文:
引理 iSup_genWeightSpaceOf_eq_top
  条件: [IsTriangularizable R L M] (x : L)
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.iSup_toSubmodule]; rw [LieSubmodule.top_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact IsTriangularizable.maxGenEigenspace_eq_top x

Depends on / 依赖: IsTriangularizable, IsTriangularizable.maxGenEigenspace_eq_top, LieSubmodule, LieSubmodule.iSup_toSubmodule, LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule, genWeightSpaceOf, iSup_toSubmodule, maxGenEigenspace_eq_top, toSubmodule_inj, top_toSubmodule
-/
lemma iSup_genWeightSpaceOf_eq_top [IsTriangularizable R L M] (x : L) :
    ⨆ (φ : R), genWeightSpaceOf M φ x = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.iSup_toSubmodule]; rw [LieSubmodule.top_toSubmodule]
  dsimp [genWeightSpaceOf]
  exact IsTriangularizable.maxGenEigenspace_eq_top x

open LinearMap Module in
@[simp]
/--
lemma `trace_toEnd_genWeightSpace` / 引理 `trace_toEnd_genWeightSpace`

English:
lemma trace_toEnd_genWeightSpace
  statement: [IsDomain R] [IsPrincipalIdealRing R]
  proof: by
  suffices _root_.IsNilpotent ((toEnd R L (genWeightSpace M χ) x) - χ x • LinearMap.id) by
    replace this := (isNilpotent_trace_of_isNilpotent this).eq_zero
    rwa [map_sub, map_smul, trace_id, sub_eq_zero, smul_eq_mul, mul_comm,
      ← nsmul_eq_mul] at this
  rw [← Module.algebraMap_end_eq_s

中文:
引理 trace_toEnd_genWeightSpace
  结论: [IsDomain R] [IsPrincipalIdealRing R]
  证明: by
  suffices _root_.IsNilpotent ((toEnd R L (genWeightSpace M χ) x) - χ x • LinearMap.id) by
    replace this := (isNilpotent_trace_of_isNilpotent this).eq_zero
    rwa [map_sub, map_smul, trace_id, sub_eq_zero, smul_eq_mul, mul_comm,
      ← nsmul_eq_mul] at this
  rw [← Module.algebraMap_end_eq_s

Depends on / 依赖: IsNilpotent, LinearMap, LinearMap.id, Module, Module.algebraMap_end_eq_smul_id, _root_, _root_.IsNilpotent, algebraMap_end_eq_smul_id, eq_zero, genWeightSpace, isNilpotent_toEnd_sub_algebraMap, isNilpotent_trace_of_isNilpotent, map_smul, map_sub, mul_comm, nsmul_eq_mul, replace, smul_eq_mul, sub_eq_zero, trace_id
-/
lemma trace_toEnd_genWeightSpace [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R M] [Module.Finite R M] (χ : L -> R) (x : L) :
    trace R _ (toEnd R L (genWeightSpace M χ) x) = finrank R (genWeightSpace M χ) • χ x := by
  suffices _root_.IsNilpotent ((toEnd R L (genWeightSpace M χ) x) - χ x • LinearMap.id) by
    replace this := (isNilpotent_trace_of_isNilpotent this).eq_zero
    rwa [map_sub, map_smul, trace_id, sub_eq_zero, smul_eq_mul, mul_comm,
      ← nsmul_eq_mul] at this
  rw [← Module.algebraMap_end_eq_smul_id]
  exact isNilpotent_toEnd_sub_algebraMap M χ x

section field

open Module

variable (K)
variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

/--
Instance `instIsTriangularizableOfIsAlgClosed` / 实例 `instIsTriangularizableOfIsAlgClosed`

English:
instance instIsTriangularizableOfIsAlgClosed
  signature: [IsAlgClosed K]
  body: ⟨fun _ => Module.End.iSup_maxGenEigenspace_eq_top _⟩

中文:
实例 instIsTriangularizableOfIsAlgClosed
  签名: [IsAlgClosed K]
  定义体: ⟨fun _ => Module.End.iSup_maxGenEigenspace_eq_top _⟩

Depends on / 依赖: Module, Module.End.iSup_maxGenEigenspace_eq_top, iSup_maxGenEigenspace_eq_top
-/
instance instIsTriangularizableOfIsAlgClosed [IsAlgClosed K] : IsTriangularizable K L M :=
  ⟨fun _ => Module.End.iSup_maxGenEigenspace_eq_top _⟩

instance (N : LieSubmodule K L M) [IsTriangularizable K L M] : IsTriangularizable K L N := by
  refine ⟨fun y => ?_⟩
  rw [← N.toEnd_restrict_eq_toEnd y]
  exact Module.End.genEigenspace_restrict_eq_top _ (IsTriangularizable.maxGenEigenspace_eq_top y)

/--
lemma `iSup_genWeightSpace_eq_top` / 引理 `iSup_genWeightSpace_eq_top`

English:
lemma iSup_genWeightSpace_eq_top
  given: [IsTriangularizable K L M]
  proof: by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.iInf_toSubmodule, LieSubmodule.top_toSubmodule, genWeightSpace]
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (toEnd K L M)
    (fun x y φ z => (genWeightSpaceOf M φ y).lie_mem) ?

中文:
引理 iSup_genWeightSpace_eq_top
  条件: [IsTriangularizable K L M]
  证明: by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.iInf_toSubmodule, LieSubmodule.top_toSubmodule, genWeightSpace]
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (toEnd K L M)
    (fun x y φ z => (genWeightSpaceOf M φ y).lie_mem) ?

Depends on / 依赖: IsTriangularizable, IsTriangularizable.maxGenEigenspace_eq_top, LieSubmodule, LieSubmodule.iInf_toSubmodule, LieSubmodule.iSup_toSubmodule, LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule, Module, Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo, genWeightSpace, genWeightSpaceOf, iInf_toSubmodule, iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo, iSup_toSubmodule, lie_mem, maxGenEigenspace_eq_top, toSubmodule_inj, top_toSubmodule
-/
lemma iSup_genWeightSpace_eq_top [IsTriangularizable K L M] :
    ⨆ χ : L -> K, genWeightSpace M χ = ⊤ := by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.iInf_toSubmodule, LieSubmodule.top_toSubmodule, genWeightSpace]
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (toEnd K L M)
    (fun x y φ z => (genWeightSpaceOf M φ y).lie_mem) ?_
  apply IsTriangularizable.maxGenEigenspace_eq_top

/--
lemma `iSup_genWeightSpace_eq_top'` / 引理 `iSup_genWeightSpace_eq_top'`

English:
lemma iSup_genWeightSpace_eq_top'
  given: [IsTriangularizable K L M]
  proof: by
  have := iSup_genWeightSpace_eq_top K L M
  erw [← iSup_ne_bot_subtype, ← (Weight.equivSetOfPred K L M).iSup_comp] at this
  exact this

中文:
引理 iSup_genWeightSpace_eq_top'
  条件: [IsTriangularizable K L M]
  证明: by
  have := iSup_genWeightSpace_eq_top K L M
  erw [← iSup_ne_bot_subtype, ← (Weight.equivSetOfPred K L M).iSup_comp] at this
  exact this

Depends on / 依赖: Weight, Weight.equivSetOfPred, equivSetOfPred, iSup_comp, iSup_genWeightSpace_eq_top, iSup_ne_bot_subtype
-/
lemma iSup_genWeightSpace_eq_top' [IsTriangularizable K L M] :
    ⨆ χ : Weight K L M, genWeightSpace M χ = ⊤ := by
  have := iSup_genWeightSpace_eq_top K L M
  erw [← iSup_ne_bot_subtype, ← (Weight.equivSetOfPred K L M).iSup_comp] at this
  exact this

/--
lemma `eq_iSup_inf_genWeightSpace` / 引理 `eq_iSup_inf_genWeightSpace`

English:
lemma eq_iSup_inf_genWeightSpace
  given: [IsTriangularizable K L M] (N : LieSubmodule K L M)
  proof: by
  refine le_antisymm ?_ (iSup_le fun χ => inf_le_left)
  conv_lhs => rw [← N.map_incl_top, ← iSup_genWeightSpace_eq_top' K L N, LieSubmodule.map_iSup]
  refine iSup_le fun χ_N => ?_
  have hN := (LieSubmodule.map_mono (le_top : genWeightSpace N χ_N <= ⊤)).trans N.map_incl_top.le
exact (le_inf hN 

中文:
引理 eq_iSup_inf_genWeightSpace
  条件: [IsTriangularizable K L M] (N : LieSubmodule K L M)
  证明: by
  refine le_antisymm ?_ (iSup_le fun χ => inf_le_left)
  conv_lhs => rw [← N.map_incl_top, ← iSup_genWeightSpace_eq_top' K L N, LieSubmodule.map_iSup]
  refine iSup_le fun χ_N => ?_
  have hN := (LieSubmodule.map_mono (le_top : genWeightSpace N χ_N <= ⊤)).trans N.map_incl_top.le
exact (le_inf hN 

Depends on / 依赖: LieSubmodule, LieSubmodule.map_iSup, LieSubmodule.map_mono, N.map_incl_top, N.map_incl_top.le, conv_lhs, genWeightSpace, iSup_genWeightSpace_eq_top, iSup_le, inf_le_left, le_antisymm, le_iSup_of_le, le_inf, le_rfl, le_top, map_genWeightSpace_le, map_iSup, map_incl_top, map_mono
-/
lemma eq_iSup_inf_genWeightSpace [IsTriangularizable K L M] (N : LieSubmodule K L M) :
    N = ⨆ χ : Weight K L M, N ⊓ genWeightSpace M χ := by
  refine le_antisymm ?_ (iSup_le fun χ => inf_le_left)
  conv_lhs => rw [← N.map_incl_top, ← iSup_genWeightSpace_eq_top' K L N, LieSubmodule.map_iSup]
  refine iSup_le fun χ_N => ?_
  have hN := (LieSubmodule.map_mono (le_top : genWeightSpace N χ_N <= ⊤)).trans N.map_incl_top.le
exact (le_inf hN (map_genWeightSpace_le _)).trans by
    by_cases h : genWeightSpace M (χ_N : L -> K) = ⊥
    · simp [h]
    · exact le_iSup_of_le ⟨_, h⟩ le_rfl

end field

end LieModule
