/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`toDualMap`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element `x`
of the space to `fun y => ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `toDual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `toDualMap`. This is the Fréchet-Riesz representation theorem: every element of the
dual of a Hilbert space `E` has the form `fun u => ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `InnerProductSpace.continuousLinearMapOfBilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `toDual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

@[expose] public section

noncomputable section

open ComplexConjugate Module

namespace InnerProductSpace

open RCLike ContinuousLinearMap

variable (𝕜 E : Type*)

section Seminormed

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

/--
Definition of `toDualMap` / `toDualMap` 的定义

English:
definition toDualMap
  signature: : E ->ₗᵢ⋆[𝕜] StrongDual 𝕜 E
  body: { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }

中文:
定义 toDualMap
  签名: : E ->ₗᵢ⋆[𝕜] StrongDual 𝕜 E
  定义体: { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }

Depends on / 依赖: innerSL, innerSL_apply_norm, norm_map
-/
def toDualMap : E ->ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }

variable {E}

@[simp]
/--
theorem `toContinuousLinearMap_toDualMap` / 定理 `toContinuousLinearMap_toDualMap`

English:
theorem toContinuousLinearMap_toDualMap
  proof: rfl

@[simp]

中文:
定理 toContinuousLinearMap_toDualMap
  证明: rfl

@[simp]
-/
theorem toContinuousLinearMap_toDualMap :
    (toDualMap 𝕜 E).toContinuousLinearMap = innerSL 𝕜 := rfl

@[simp]
/--
theorem `toDualMap_apply_apply` / 定理 `toDualMap_apply_apply`

English:
theorem toDualMap_apply_apply
  given: {x y : E}
  statement: toDualMap 𝕜 E x y = ⟪x, y⟫
  proof: rfl

中文:
定理 toDualMap_apply_apply
  条件: {x y : E}
  结论: toDualMap 𝕜 E x y = ⟪x, y⟫
  证明: rfl
-/
theorem toDualMap_apply_apply {x y : E} : toDualMap 𝕜 E x y = ⟪x, y⟫ := rfl

variable {𝕜} in
@[simp]
/--
theorem `_root_.innerSL_inj` / 定理 `_root_.innerSL_inj`

English:
theorem _root_.innerSL_inj
  given: {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x y : E}
  proof: (toDualMap 𝕜 E).injective.eq_iff

中文:
定理 _root_.innerSL_inj
  条件: {E : 类型} [赋范交换加群 E] [内积空间 𝕜 E] {x y : E}
  证明: (toDualMap 𝕜 E).injective.eq_iff

Depends on / 依赖: eq_iff, injective, injective.eq_iff, toDualMap
-/
theorem _root_.innerSL_inj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x y : E} :
    innerSL 𝕜 x = innerSL 𝕜 y ↔ x = y :=
  (toDualMap 𝕜 E).injective.eq_iff

section NullSubmodule

open LinearMap

/--
lemma `nullSubmodule_le_ker_toDualMap_right` / 引理 `nullSubmodule_le_ker_toDualMap_right`

English:
lemma nullSubmodule_le_ker_toDualMap_right
  given: (x : E)
  statement: nullSubmodule 𝕜 E <= (toDualMap 𝕜 E x).ker
  proof: fun _ hx => inner_eq_zero_of_right x (mem_nullSubmodule_iff.mp hx)

中文:
引理 nullSubmodule_le_ker_toDualMap_right
  条件: (x : E)
  结论: nullSubmodule 𝕜 E <= (toDualMap 𝕜 E x).ker
  证明: fun _ hx => inner_eq_zero_of_right x (mem_nullSubmodule_iff.mp hx)

Depends on / 依赖: inner_eq_zero_of_right, mem_nullSubmodule_iff, mem_nullSubmodule_iff.mp
-/
lemma nullSubmodule_le_ker_toDualMap_right (x : E) : nullSubmodule 𝕜 E <= (toDualMap 𝕜 E x).ker :=
  fun _ hx => inner_eq_zero_of_right x (mem_nullSubmodule_iff.mp hx)

/--
lemma `nullSubmodule_le_ker_toDualMap_left` / 引理 `nullSubmodule_le_ker_toDualMap_left`

English:
lemma nullSubmodule_le_ker_toDualMap_left
  statement: nullSubmodule 𝕜 E <= (toDualMap 𝕜 E).ker
  proof: fun _ hx => ContinuousLinearMap.ext fun y => inner_eq_zero_of_left y hx

中文:
引理 nullSubmodule_le_ker_toDualMap_left
  结论: nullSubmodule 𝕜 E <= (toDualMap 𝕜 E).ker
  证明: fun _ hx => ContinuousLinearMap.ext fun y => inner_eq_zero_of_left y hx

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, inner_eq_zero_of_left
-/
lemma nullSubmodule_le_ker_toDualMap_left : nullSubmodule 𝕜 E <= (toDualMap 𝕜 E).ker :=
fun _ hx => ContinuousLinearMap.ext fun y => inner_eq_zero_of_left y hx

end NullSubmodule

end Seminormed

section Normed
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

/--
theorem `innerSL_norm` / 定理 `innerSL_norm`

English:
theorem innerSL_norm
  given: [Nontrivial E]
  statement: ‖(innerSL 𝕜 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)‖ = 1
  proof: show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _

中文:
定理 innerSL_norm
  条件: [非平凡 E]
  结论: ‖(innerSL 𝕜 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)‖ = 1
  证明: show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _

Depends on / 依赖: LinearIsometry, LinearIsometry.norm_toContinuousLinearMap, norm_toContinuousLinearMap, toContinuousLinearMap, toDualMap
-/
theorem innerSL_norm [Nontrivial E] : ‖(innerSL 𝕜 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)‖ = 1 :=
  show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _

variable {E 𝕜}

/--
theorem `ext_inner_left_basis` / 定理 `ext_inner_left_basis`

English:
theorem ext_inner_left_basis
  statement: {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
  proof: by
  apply (toDualMap 𝕜 E).map_eq_iff.mp
  refine (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (b.ext ?_)
  intro i
  simp only [ContinuousLinearMap.coe_coe, toDualMap_apply_apply]
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

中文:
定理 ext_inner_left_basis
  结论: {ι : 类型} {x y : E} (b : 基 ι 𝕜 E)
  证明: by
  apply (toDualMap 𝕜 E).map_eq_iff.mp
  refine (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (b.ext ?_)
  intro i
  simp only [ContinuousLinearMap.coe_coe, toDualMap_apply_apply]
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_injective, Function, Function.Injective.eq_iff, Injective, b.ext, coe_coe, coe_injective, congr_arg, conv_rhs, eq_iff, inner_conj_symm, map_eq_iff, map_eq_iff.mp, toDualMap, toDualMap_apply_apply
-/
theorem ext_inner_left_basis {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
    (h : forall i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y := by
  apply (toDualMap 𝕜 E).map_eq_iff.mp
  refine (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (b.ext ?_)
  intro i
  simp only [ContinuousLinearMap.coe_coe, toDualMap_apply_apply]
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

/--
theorem `ext_inner_right_basis` / 定理 `ext_inner_right_basis`

English:
theorem ext_inner_right_basis
  statement: {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
  proof: by
  refine ext_inner_left_basis b fun i => ?_
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

中文:
定理 ext_inner_right_basis
  结论: {ι : 类型} {x y : E} (b : 基 ι 𝕜 E)
  证明: by
  refine ext_inner_left_basis b fun i => ?_
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

Depends on / 依赖: congr_arg, conv_rhs, ext_inner_left_basis, inner_conj_symm
-/
theorem ext_inner_right_basis {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
    (h : forall i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y := by
  refine ext_inner_left_basis b fun i => ?_
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

variable (𝕜) (E)
variable [CompleteSpace E]

/--
Definition of `toDual` / `toDual` 的定义

English:
definition toDual
  signature: : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E
  body: LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := ℓ.ker
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := LinearMap.ker_eq_top.mp htriv
          norm_cast at h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ != ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z in Yᗮ, z_ne_0 : z != 0⟩ := htriv
        refine ⟨(starRingEnd (R := 𝕜) (ℓ z) / ⟪z, z⟫) • z, ?_⟩
        apply ContinuousLinearMap.ext
        intro x
        have h₁ : ℓ z • x - ℓ x • z in Y := by
          rw [LinearMap.mem_ker]; rw [map_sub]; rw [map_smul]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
          sub_eq_zero.mp h₃.symm
        calc
          ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left]
          _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
          _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
          _ = ℓ x := by have : ⟪z, z⟫ != 0 := inner_self_ne_zero.mpr z_ne_0; field)

中文:
定义 toDual
  签名: : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E
  定义体: LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := ℓ.ker
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := LinearMap.ker_eq_top.mp htriv
          norm_cast at h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ != ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z in Yᗮ, z_ne_0 : z != 0⟩ := htriv
        refine ⟨(starRingEnd (R := 𝕜) (ℓ z) / ⟪z, z⟫) • z, ?_⟩
        apply ContinuousLinearMap.ext
        intro x
        have h₁ : ℓ z • x - ℓ x • z in Y := by
          rw [LinearMap.mem_ker]; rw [map_sub]; rw [map_smul]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
          sub_eq_zero.mp h₃.symm
        calc
          ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left]
          _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
          _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
          _ = ℓ x := by have : ⟪z, z⟫ != 0 := inner_self_ne_zero.mpr z_ne_0; field)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, LinearIsometryEquiv, LinearIsometryEquiv.ofSurjective, LinearMap, LinearMap.ker_eq_top.mp, Submodule, Submodule.ne_bot_iff, Submodule.orthogonal_eq_bot_iff, ker_eq_top, ne_bot_iff, ofSurjective, orthogonal_eq_bot_iff, starRingEnd, toDualMap, z_ne_0
-/
def toDual : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := ℓ.ker
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := LinearMap.ker_eq_top.mp htriv
          norm_cast at h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ != ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z in Yᗮ, z_ne_0 : z != 0⟩ := htriv
        refine ⟨(starRingEnd (R := 𝕜) (ℓ z) / ⟪z, z⟫) • z, ?_⟩
        apply ContinuousLinearMap.ext
        intro x
        have h₁ : ℓ z • x - ℓ x • z in Y := by
          rw [LinearMap.mem_ker]; rw [map_sub]; rw [map_smul]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
          sub_eq_zero.mp h₃.symm
        calc
          ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left]
          _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
          _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
          _ = ℓ x := by have : ⟪z, z⟫ != 0 := inner_self_ne_zero.mpr z_ne_0; field)

variable {𝕜} {E}

@[simp]
/--
theorem `toDual_apply_apply` / 定理 `toDual_apply_apply`

English:
theorem toDual_apply_apply
  given: {x y : E}
  statement: toDual 𝕜 E x y = ⟪x, y⟫
  proof: rfl

@[simp]

中文:
定理 toDual_apply_apply
  条件: {x y : E}
  结论: toDual 𝕜 E x y = ⟪x, y⟫
  证明: rfl

@[simp]
-/
theorem toDual_apply_apply {x y : E} : toDual 𝕜 E x y = ⟪x, y⟫ := rfl

@[simp]
/--
theorem `toDual_symm_apply` / 定理 `toDual_symm_apply`

English:
theorem toDual_symm_apply
  given: {x : E} {y : StrongDual 𝕜 E}
  statement: ⟪(toDual 𝕜 E).symm y, x⟫ = y x
  proof: by
  rw [← toDual_apply_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]

@[simp]

中文:
定理 toDual_symm_apply
  条件: {x : E} {y : StrongDual 𝕜 E}
  结论: ⟪(toDual 𝕜 E).symm y, x⟫ = y x
  证明: by
  rw [← toDual_apply_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.apply_symm_apply, apply_symm_apply, toDual_apply_apply
-/
theorem toDual_symm_apply {x : E} {y : StrongDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x := by
  rw [← toDual_apply_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]

@[simp]
/--
lemma `toLinearIsometry_toDual` / 引理 `toLinearIsometry_toDual`

English:
lemma toLinearIsometry_toDual
  proof: rfl

中文:
引理 toLinearIsometry_toDual
  证明: rfl
-/
lemma toLinearIsometry_toDual :
    (toDual 𝕜 E).toLinearIsometry = toDualMap 𝕜 E := rfl

/--
lemma `toDual_apply_eq_toDualMap_apply` / 引理 `toDual_apply_eq_toDualMap_apply`

English:
lemma toDual_apply_eq_toDualMap_apply
  given: (x : E)
  proof: rfl

中文:
引理 toDual_apply_eq_toDualMap_apply
  条件: (x : E)
  证明: rfl
-/
lemma toDual_apply_eq_toDualMap_apply (x : E) :
    toDual 𝕜 E x = toDualMap 𝕜 E x := rfl

/--
Definition of `continuousLinearMapOfBilin` / `continuousLinearMapOfBilin` 的定义

English:
definition continuousLinearMapOfBilin
  signature: (B : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)
  body: (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

local postfix:1024 "♯" => continuousLinearMapOfBilin

中文:
定义 continuousLinearMapOfBilin
  签名: (B : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)
  定义体: (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

local postfix:1024 "♯" => continuousLinearMapOfBilin

Depends on / 依赖: symm.toContinuousLinearEquiv.toContinuousLinearMap.comp, toContinuousLinearEquiv, toContinuousLinearMap, toDual
-/
def continuousLinearMapOfBilin (B : E ->L⋆[𝕜] E ->L[𝕜] 𝕜) : E ->L[𝕜] E :=
  (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)

@[simp]
/--
theorem `continuousLinearMapOfBilin_zero` / 定理 `continuousLinearMapOfBilin_zero`

English:
theorem continuousLinearMapOfBilin_zero
  statement: (0 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)♯ = 0
  proof: by
  simp [continuousLinearMapOfBilin]

@[simp]

中文:
定理 continuousLinearMapOfBilin_zero
  结论: (0 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)♯ = 0
  证明: by
  simp [continuousLinearMapOfBilin]

@[simp]

Depends on / 依赖: continuousLinearMapOfBilin
-/
theorem continuousLinearMapOfBilin_zero : (0 : E ->L⋆[𝕜] E ->L[𝕜] 𝕜)♯ = 0 := by
  simp [continuousLinearMapOfBilin]

@[simp]
/--
theorem `continuousLinearMapOfBilin_apply` / 定理 `continuousLinearMapOfBilin_apply`

English:
theorem continuousLinearMapOfBilin_apply
  given: (v w : E)
  statement: ⟪B♯ v, w⟫ = B v w
  proof: by
  simp [continuousLinearMapOfBilin]

中文:
定理 continuousLinearMapOfBilin_apply
  条件: (v w : E)
  结论: ⟪B♯ v, w⟫ = B v w
  证明: by
  simp [continuousLinearMapOfBilin]

Depends on / 依赖: continuousLinearMapOfBilin
-/
theorem continuousLinearMapOfBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w := by
  simp [continuousLinearMapOfBilin]

/--
theorem `unique_continuousLinearMapOfBilin` / 定理 `unique_continuousLinearMapOfBilin`

English:
theorem unique_continuousLinearMapOfBilin
  given: {v f : E} (is_lax_milgram : forall w, ⟪f, w⟫ = B v w)
  proof: by
  refine ext_inner_right 𝕜 ?_
  intro w
  rw [continuousLinearMapOfBilin_apply]
  exact is_lax_milgram w

中文:
定理 unique_continuousLinearMapOfBilin
  条件: {v f : E} (is_lax_milgram : 对任意 w, ⟪f, w⟫ = B v w)
  证明: by
  refine ext_inner_right 𝕜 ?_
  intro w
  rw [continuousLinearMapOfBilin_apply]
  exact is_lax_milgram w

Depends on / 依赖: continuousLinearMapOfBilin_apply, ext_inner_right, is_lax_milgram
-/
theorem unique_continuousLinearMapOfBilin {v f : E} (is_lax_milgram : forall w, ⟪f, w⟫ = B v w) :
    f = B♯ v := by
  refine ext_inner_right 𝕜 ?_
  intro w
  rw [continuousLinearMapOfBilin_apply]
  exact is_lax_milgram w

end Normed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedAddCommGroup
  signature: E] [CompleteSpace E] [InnerProductSpace Real E] :
  body: continuous_inner
  bijective_left := (toDual Real E).bijective
  bijective_right := by
    convert! (toDual Real E).bijective
    ext y
    simp

中文:
实例 [赋范交换加群
  签名: E] [完备空间 E] [内积空间 实数 E] :
  定义体: continuous_inner
  bijective_left := (toDual Real E).bijective
  bijective_right := by
    convert! (toDual Real E).bijective
    ext y
    simp

Depends on / 依赖: continuous_inner
-/
instance [NormedAddCommGroup E] [CompleteSpace E] [InnerProductSpace Real E] :
    (innerₗ E).IsContPerfPair where
  continuous_uncurry := continuous_inner
  bijective_left := (toDual Real E).bijective
  bijective_right := by
    convert! (toDual Real E).bijective
    ext y
    simp

/--
lemma `rank_rankOne` / 引理 `rank_rankOne`

English:
lemma rank_rankOne
  statement: {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  rw [LinearMap.rank]; rw [rankOne_def]; rw [range_smulRight_apply]; rw [Module.rank_eq_one_iff_finrank_eq_one]
  · exact finrank_span_singleton hx
.not.mpr hy · exact map_eq_zero_iff _ (toDualMap 𝕜 F).injective

中文:
引理 rank_rankOne
  结论: {𝕜 E F : 类型} [RCLike 𝕜] [SeminormedAddComm群 E] [赋范空间 𝕜 E]
  证明: by
  rw [LinearMap.rank]; rw [rankOne_def]; rw [range_smulRight_apply]; rw [Module.rank_eq_one_iff_finrank_eq_one]
  · exact finrank_span_singleton hx
.not.mpr hy · exact map_eq_zero_iff _ (toDualMap 𝕜 F).injective

Depends on / 依赖: LinearMap, LinearMap.rank, Module, Module.rank_eq_one_iff_finrank_eq_one, finrank_span_singleton, injective, map_eq_zero_iff, not.mpr, range_smulRight_apply, rankOne_def, rank_eq_one_iff_finrank_eq_one, toDualMap
-/
lemma rank_rankOne {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {x : E} {y : F} (hx : x != 0) (hy : y != 0) :
    (rankOne 𝕜 x y).rank = 1 := by
  rw [LinearMap.rank]; rw [rankOne_def]; rw [range_smulRight_apply]; rw [Module.rank_eq_one_iff_finrank_eq_one]
  · exact finrank_span_singleton hx
.not.mpr hy · exact map_eq_zero_iff _ (toDualMap 𝕜 F).injective

end InnerProductSpace

/--
lemma `OrthonormalBasis.norm_dual` / 引理 `OrthonormalBasis.norm_dual`

English:
lemma OrthonormalBasis.norm_dual
  statement: {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
  proof: by
  have := b.toBasis.finiteDimensional_of_finite
  simp_rw [← (InnerProductSpace.toDual Real E).symm.norm_map, ← b.sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]

中文:
引理 正交标准基.norm_dual
  结论: {ι E : 类型} [有限类型 ι] [赋范交换加群 E]
  证明: by
  have := b.toBasis.finiteDimensional_of_finite
  simp_rw [← (InnerProductSpace.toDual Real E).symm.norm_map, ← b.sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.toDual, InnerProductSpace.toDual_symm_apply, b.sum_sq_inner_left, b.toBasis.finiteDimensional_of_finite, finiteDimensional_of_finite, norm_map, simp_rw, sum_sq_inner_left, symm.norm_map, toBasis, toDual, toDual_symm_apply
-/
lemma OrthonormalBasis.norm_dual {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace Real E] (b : OrthonormalBasis ι Real E) (L : StrongDual Real E) :
    ‖L‖ ^ 2 = ∑ i, L (b i) ^ 2 := by
  have := b.toBasis.finiteDimensional_of_finite
  simp_rw [← (InnerProductSpace.toDual Real E).symm.norm_map, ← b.sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]
