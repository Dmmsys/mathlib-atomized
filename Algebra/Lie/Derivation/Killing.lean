/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Derivations of finite-dimensional Killing Lie algebras

This file establishes that all derivations of finite-dimensional Killing Lie algebras are inner.

## Main statements

- `LieDerivation.Killing.ad_mem_orthogonal_of_mem_orthogonal`: if a derivation `D` is in the Killing
  orthogonal of the range of the adjoint action, then, for any `x : L`, `ad (D x)` is also in this
  orthogonal.
- `LieDerivation.Killing.range_ad_eq_top`: in a finite-dimensional Lie algebra with non-degenerate
  Killing form, the range of the adjoint action is full,
- `LieDerivation.Killing.exists_eq_ad`: in a finite-dimensional Lie algebra with non-degenerate
  Killing form, any derivation is an inner derivation.
-/

@[expose] public section

namespace LieDerivation.IsKilling

section

variable (R L : Type*) [Field R] [LieRing L] [LieAlgebra R L]

/-- A local notation for the set of (Lie) derivations on `L`. -/
local notation "𝔻" => (LieDerivation R L L)

/-- A local notation for the range of `ad`. -/
local notation "𝕀" => (LieHom.range (ad R L))

/-- A local notation for the Killing complement of the ideal range of `ad`. -/
local notation "𝕀ᗮ" => LinearMap.BilinForm.orthogonal (killingForm R 𝔻) 𝕀

/--
lemma `killingForm_restrict_range_ad` / 引理 `killingForm_restrict_range_ad`

English:
lemma killingForm_restrict_range_ad
  given: [Module.Finite R L]
  proof: by
  rw [← (ad_isIdealMorphism R L).eq]; rw [← LieIdeal.killingForm_eq]
  rfl

中文:
引理 killingForm_restrict_range_ad
  条件: [模.有限 R L]
  证明: by
  rw [← (ad_isIdealMorphism R L).eq]; rw [← LieIdeal.killingForm_eq]
  rfl

Depends on / 依赖: LieIdeal, LieIdeal.killingForm_eq, ad_isIdealMorphism, killingForm_eq
-/
lemma killingForm_restrict_range_ad [Module.Finite R L] :
    (killingForm R 𝔻).restrict 𝕀 = killingForm R 𝕀 := by
  rw [← (ad_isIdealMorphism R L).eq]; rw [← LieIdeal.killingForm_eq]
  rfl

/--
Definition of `rangeAdOrthogonal` / `rangeAdOrthogonal` 的定义

English:
definition rangeAdOrthogonal
  signature: : LieSubmodule R L (LieDerivation R L L) where
  body: 𝕀ᗮ
  lie_mem := by
    intro x D hD
    have : 𝕀ᗮ = (ad R L).idealRange.killingCompl := by simp [← (ad_isIdealMorphism R L).eq]
    change D in 𝕀ᗮ at hD
    change ⁅x, D⁆ in 𝕀ᗮ
    rw [this] at hD ⊢
    rw [← lie_ad]
    exact lie_mem_right _ _ (ad R L).idealRange.killingCompl _ _ hD

中文:
定义 rangeAdOrthogonal
  签名: : Lie子模 R L (LieDerivation R L L) where
  定义体: 𝕀ᗮ
  lie_mem := by
    intro x D hD
    have : 𝕀ᗮ = (ad R L).idealRange.killingCompl := by simp [← (ad_isIdealMorphism R L).eq]
    change D in 𝕀ᗮ at hD
    change ⁅x, D⁆ in 𝕀ᗮ
    rw [this] at hD ⊢
    rw [← lie_ad]
    exact lie_mem_right _ _ (ad R L).idealRange.killingCompl _ _ hD
-/
@[simps!] noncomputable def rangeAdOrthogonal : LieSubmodule R L (LieDerivation R L L) where
  __ := 𝕀ᗮ
  lie_mem := by
    intro x D hD
    have : 𝕀ᗮ = (ad R L).idealRange.killingCompl := by simp [← (ad_isIdealMorphism R L).eq]
    change D in 𝕀ᗮ at hD
    change ⁅x, D⁆ in 𝕀ᗮ
    rw [this] at hD ⊢
    rw [← lie_ad]
    exact lie_mem_right _ _ (ad R L).idealRange.killingCompl _ _ hD

variable {R L}

/--
lemma `ad_mem_orthogonal_of_mem_orthogonal` / 引理 `ad_mem_orthogonal_of_mem_orthogonal`

English:
lemma ad_mem_orthogonal_of_mem_orthogonal
  given: {D : LieDerivation R L L} (hD : D in 𝕀ᗮ) (x : L)
  proof: by
  simp only [ad_apply_lieDerivation, LieHom.range_toSubmodule, neg_mem_iff]
  exact (rangeAdOrthogonal R L).lie_mem hD

中文:
引理 ad_mem_orthogonal_of_mem_orthogonal
  条件: {D : LieDerivation R L L} (hD : D in 𝕀ᗮ) (x : L)
  证明: by
  simp only [ad_apply_lieDerivation, LieHom.range_toSubmodule, neg_mem_iff]
  exact (rangeAdOrthogonal R L).lie_mem hD

Depends on / 依赖: LieHom, LieHom.range_toSubmodule, ad_apply_lieDerivation, lie_mem, neg_mem_iff, rangeAdOrthogonal, range_toSubmodule
-/
lemma ad_mem_orthogonal_of_mem_orthogonal {D : LieDerivation R L L} (hD : D in 𝕀ᗮ) (x : L) :
    ad R L (D x) in 𝕀ᗮ := by
  simp only [ad_apply_lieDerivation, LieHom.range_toSubmodule, neg_mem_iff]
  exact (rangeAdOrthogonal R L).lie_mem hD

variable [Module.Finite R L]

/--
lemma `ad_mem_ker_killingForm_ad_range_of_mem_orthogonal` / 引理 `ad_mem_ker_killingForm_ad_range_of_mem_orthogonal`

English:
lemma ad_mem_ker_killingForm_ad_range_of_mem_orthogonal
  proof: by
  rw [← killingForm_restrict_range_ad]
  exact LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl ⟨by simp, ad_mem_orthogonal_of_mem_orthogonal hD x⟩

中文:
引理 ad_mem_ker_killingForm_ad_range_of_mem_orthogonal
  证明: by
  rw [← killingForm_restrict_range_ad]
  exact LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl ⟨by simp, ad_mem_orthogonal_of_mem_orthogonal hD x⟩

Depends on / 依赖: BilinForm, LieModule, LieModule.traceForm_isSymm, LinearMap, LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict, ad_mem_orthogonal_of_mem_orthogonal, inf_orthogonal_self_le_ker_restrict, isRefl, killingForm_restrict_range_ad, traceForm_isSymm
-/
lemma ad_mem_ker_killingForm_ad_range_of_mem_orthogonal
    {D : LieDerivation R L L} (hD : D in 𝕀ᗮ) (x : L) :
    ad R L (D x) in (LinearMap.ker (killingForm R 𝕀)).map (LieHom.range (ad R L)).subtype := by
  rw [← killingForm_restrict_range_ad]
  exact LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl ⟨by simp, ad_mem_orthogonal_of_mem_orthogonal hD x⟩

variable (R L)
variable [LieAlgebra.IsKilling R L]

/--
lemma `ad_apply_eq_zero_iff` / 引理 `ad_apply_eq_zero_iff`

English:
lemma ad_apply_eq_zero_iff
  given: (x : L)
  statement: ad R L x = 0 ↔ x = 0
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rwa [← LieHom.mem_ker, ad_ker_eq_center, LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at h

中文:
引理 ad_apply_eq_zero_iff
  条件: (x : L)
  结论: ad R L x = 0 ↔ x = 0
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rwa [← LieHom.mem_ker, ad_ker_eq_center, LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at h
-/
@[simp] lemma ad_apply_eq_zero_iff (x : L) : ad R L x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rwa [← LieHom.mem_ker, ad_ker_eq_center, LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at h

/--
Instance `instIsKilling_range_ad` / 实例 `instIsKilling_range_ad`

English:
instance instIsKilling_range_ad
  signature: : LieAlgebra.IsKilling R 𝕀
  body: (LieEquiv.ofInjective (ad R L) (injective_ad_of_center_eq_bot <| by simp)).isKilling

中文:
实例 instIsKilling_range_ad
  签名: : Lie代数.是Killing R 𝕀
  定义体: (LieEquiv.ofInjective (ad R L) (injective_ad_of_center_eq_bot <| by simp)).isKilling

Depends on / 依赖: LieEquiv, LieEquiv.ofInjective, injective_ad_of_center_eq_bot, isKilling, ofInjective
-/
instance instIsKilling_range_ad : LieAlgebra.IsKilling R 𝕀 :=
  (LieEquiv.ofInjective (ad R L) (injective_ad_of_center_eq_bot <| by simp)).isKilling

/--
lemma `killingForm_restrict_range_ad_nondegenerate` / 引理 `killingForm_restrict_range_ad_nondegenerate`

English:
lemma killingForm_restrict_range_ad_nondegenerate
  proof: by
  convert! LieAlgebra.IsKilling.killingForm_nondegenerate R 𝕀
  exact killingForm_restrict_range_ad R L

中文:
引理 killingForm_restrict_range_ad_nondegenerate
  证明: by
  convert! LieAlgebra.IsKilling.killingForm_nondegenerate R 𝕀
  exact killingForm_restrict_range_ad R L

Depends on / 依赖: IsKilling, LieAlgebra, LieAlgebra.IsKilling.killingForm_nondegenerate, convert, killingForm_nondegenerate, killingForm_restrict_range_ad
-/
lemma killingForm_restrict_range_ad_nondegenerate :
    ((killingForm R 𝔻).restrict 𝕀).Nondegenerate := by
  convert! LieAlgebra.IsKilling.killingForm_nondegenerate R 𝕀
  exact killingForm_restrict_range_ad R L

set_option backward.isDefEq.respectTransparency false in
/-- The range of the adjoint action on a finite-dimensional Killing Lie algebra is full. -/
@[simp]
/--
lemma `range_ad_eq_top` / 引理 `range_ad_eq_top`

English:
lemma range_ad_eq_top
  statement: 𝕀 = ⊤
  proof: by
  rw [← LieSubalgebra.toSubmodule_inj]
  apply LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl (killingForm_restrict_range_ad_nondegenerate R L)
  refine (Submodule.eq_bot_iff _).mpr fun D hD => ext fun x => ?_
  simpa using 

中文:
引理 range_ad_eq_top
  结论: 𝕀 = ⊤
  证明: by
  rw [← LieSubalgebra.toSubmodule_inj]
  apply LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl (killingForm_restrict_range_ad_nondegenerate R L)
  refine (Submodule.eq_bot_iff _).mpr fun D hD => ext fun x => ?_
  simpa using 

Depends on / 依赖: BilinForm, LieModule, LieModule.traceForm_isSymm, LieSubalgebra, LieSubalgebra.toSubmodule_inj, LinearMap, LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot, Submodule, Submodule.eq_bot_iff, ad_mem_ker_killingForm_ad_range_of_mem_orthogonal, eq_bot_iff, eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot, isRefl, killingForm_restrict_range_ad_nondegenerate, toSubmodule_inj, traceForm_isSymm
-/
lemma range_ad_eq_top : 𝕀 = ⊤ := by
  rw [← LieSubalgebra.toSubmodule_inj]
  apply LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (LieModule.traceForm_isSymm R 𝔻 𝔻).isRefl (killingForm_restrict_range_ad_nondegenerate R L)
  refine (Submodule.eq_bot_iff _).mpr fun D hD => ext fun x => ?_
  simpa using ad_mem_ker_killingForm_ad_range_of_mem_orthogonal hD x

variable {R L} in
/--
lemma `exists_eq_ad` / 引理 `exists_eq_ad`

English:
lemma exists_eq_ad
  given: (D : 𝔻)
  statement: exists x, ad R L x = D
  proof: by
  change D in 𝕀
  rw [range_ad_eq_top R L]
  exact Submodule.mem_top

中文:
引理 存在_eq_ad
  条件: (D : 𝔻)
  结论: 存在 x, ad R L x = D
  证明: by
  change D in 𝕀
  rw [range_ad_eq_top R L]
  exact Submodule.mem_top

Depends on / 依赖: Submodule, Submodule.mem_top, mem_top, range_ad_eq_top
-/
lemma exists_eq_ad (D : 𝔻) : exists x, ad R L x = D := by
  change D in 𝕀
  rw [range_ad_eq_top R L]
  exact Submodule.mem_top

end

end IsKilling

end LieDerivation
