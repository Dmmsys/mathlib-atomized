/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Categorical constructions for `IsSMulRegular`
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Abelian Pointwise

/--
lemma `LinearMap.exact_lsmul_mkQ_smul_top` / 引理 `LinearMap.exact_lsmul_mkQ_smul_top`

English:
lemma LinearMap.exact_lsmul_mkQ_smul_top
  given: (M : Type v) [AddCommGroup M] [Module R M] (r : R)
  proof: by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

@[deprecated (since := "2026-04-13")]
alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_mkQ_smul_top

中文:
引理 LinearMap.exact_lsmul_mkQ_smul_top
  条件: (M : 类型v) [AddCommGroup M] [Module R M] (r : R)
  证明: by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

@[deprecated (since := "2026-04-13")]
alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_mkQ_smul_top

Depends on / 依赖: Submodule, Submodule.mem_smul_pointwise_iff_exists, mem_smul_pointwise_iff_exists
-/
lemma LinearMap.exact_lsmul_mkQ_smul_top (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

@[deprecated (since := "2026-04-13")]
alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_mkQ_smul_top

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps!]
/--
Definition of `smulShortComplex` / `smulShortComplex` 的定义

English:
definition smulShortComplex
  signature: (r : R)
  body: ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]

中文:
定义 smulShortComplex
  签名: (r : R)
  定义体: ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]

Depends on / 依赖: LinearMap, LinearMap.exact_lsmul_mkQ_smul_top, LinearMap.lsmul, ModuleCat, ModuleCat.shortComplexOfCompEqZero, Submodule, exact_lsmul_mkQ_smul_top, linearMap_comp_eq_zero, shortComplexOfCompEqZero
-/
def smulShortComplex (r : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]
/--
lemma `smulShortComplex_f_eq_smul_id` / 引理 `smulShortComplex_f_eq_smul_id`

English:
lemma smulShortComplex_f_eq_smul_id
  given: (r : R)
  statement: (M.smulShortComplex r).f = r • 𝟙 M
  proof: rfl

中文:
引理 smulShortComplex_f_eq_smul_id
  条件: (r : R)
  结论: (M.smulShortComplex r).f = r • 𝟙 M
  证明: rfl
-/
lemma smulShortComplex_f_eq_smul_id (r : R) : (M.smulShortComplex r).f = r • 𝟙 M := rfl

/--
lemma `smulShortComplex_exact` / 引理 `smulShortComplex_exact`

English:
lemma smulShortComplex_exact
  given: (r : R)
  statement: (smulShortComplex M r).Exact
  proof: ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_mkQ_smul_top M r)

中文:
引理 smulShortComplex_exact
  条件: (r : R)
  结论: (smulShortComplex M r).Exact
  证明: ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_mkQ_smul_top M r)

Depends on / 依赖: LinearMap, LinearMap.exact_lsmul_mkQ_smul_top, ModuleCat, ModuleCat.shortComplex_exact, exact_lsmul_mkQ_smul_top, shortComplex_exact
-/
lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact :=
  ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_mkQ_smul_top M r)

/--
Instance `smulShortComplex_g_epi` / 实例 `smulShortComplex_g_epi`

English:
instance smulShortComplex_g_epi
  signature: (r : R)
  body: by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

中文:
实例 smulShortComplex_g_epi
  签名: (r : R)
  定义体: by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, Submodule, Submodule.mkQ_surjective, epi_iff_surjective, mkQ_surjective, smulShortComplex
-/
instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
/--
lemma `IsSMulRegular.smulShortComplex_shortExact` / 引理 `IsSMulRegular.smulShortComplex_shortExact`

English:
lemma IsSMulRegular.smulShortComplex_shortExact
  given: {r : R} (reg : IsSMulRegular M r)
  proof: ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using! reg

中文:
引理 IsSMulRegular.smulShortComplex_shortExact
  条件: {r : R} (reg : IsSMulRegular M r)
  证明: ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using! reg

Depends on / 依赖: ModuleCat, ModuleCat.smulShortComplex_exact, smulShortComplex_exact
-/
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using! reg
