/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Weights.Chain
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Roots of Lie algebras with non-degenerate Killing forms

The file contains definitions and results about roots of Lie algebras with non-degenerate Killing
forms.

## Main definitions
* `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`: if the Killing form of
  a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
* `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`: if the Killing form of a Lie
  algebra is non-singular, then its Cartan subalgebras are Abelian.
* `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`: over a perfect field, if a Lie
  algebra has non-degenerate Killing form, Cartan subalgebras contain only semisimple elements.
* `LieAlgebra.IsKilling.span_weight_eq_top`: given a splitting Cartan subalgebra `H` of a
  finite-dimensional Lie algebra with non-singular Killing form, the corresponding roots span the
  dual space of `H`.
* `LieAlgebra.IsKilling.coroot`: the coroot corresponding to a root.
* `LieAlgebra.IsKilling.isCompl_ker_weight_span_coroot`: given a root `α` with respect to a Cartan
  subalgebra `H`, we have a natural decomposition of `H` as the kernel of `α` and the span of the
  coroot corresponding to `α`.
* `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`: root spaces are one-dimensional.
* `LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`: a Lie ideal decomposes as its
  intersection with the Cartan subalgebra plus a sum of root spaces.

-/

@[expose] public section

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

/--
lemma `restrict_killingForm` / 引理 `restrict_killingForm`

English:
lemma restrict_killingForm
  given: (H : LieSubalgebra R L)
  proof: rfl

中文:
引理 restrict_killingForm
  条件: (H : Lie子代数 R L)
  证明: rfl
-/
lemma restrict_killingForm (H : LieSubalgebra R L) :
    (killingForm R L).restrict H = LieModule.traceForm R H L :=
  rfl

namespace IsKilling

variable [IsKilling R L]

/--
lemma `ker_restrict_eq_bot_of_isCartanSubalgebra` / 引理 `ker_restrict_eq_bot_of_isCartanSubalgebra`

English:
lemma ker_restrict_eq_bot_of_isCartanSubalgebra
  proof: by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmo

中文:
引理 ker_restrict_eq_bot_of_isCartanSubalgebra
  证明: by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmo

Depends on / 依赖: Codisjoint, LieModule, LieModule.isCompl_genWeightSpace_zero_posFittingComp, LieModule.posFi, LieModule.posFittingComp, LieSubalgebra, LieSubalgebra.coe_toLieSubmodule, LieSubmodule, LieSubmodule.sup_toSubmodule, LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule, Submodule, codisjoint, codisjoint_iff, coe_toLieSubmodule, isCompl_genWeightSpace_zero_posFittingComp, posFittingComp, replace, rootSpace, rootSpace_zero_eq
-/
lemma ker_restrict_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker ((killingForm R L).restrict H) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmodule_inj, LieSubmodule.sup_toSubmodule,
      LieSubmodule.top_toSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : forall m₀ in H, forall m₁ in LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁

/--
lemma `ker_traceForm_eq_bot_of_isCartanSubalgebra` / 引理 `ker_traceForm_eq_bot_of_isCartanSubalgebra`

English:
lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
  proof: ker_restrict_eq_bot_of_isCartanSubalgebra R L H

中文:
引理 ker_traceForm_eq_bot_of_isCartanSubalgebra
  证明: ker_restrict_eq_bot_of_isCartanSubalgebra R L H
-/
@[simp] lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (LieModule.traceForm R H L) = ⊥ :=
  ker_restrict_eq_bot_of_isCartanSubalgebra R L H

/--
lemma `traceForm_cartan_nondegenerate` / 引理 `traceForm_cartan_nondegenerate`

English:
lemma traceForm_cartan_nondegenerate
  proof: by
  simp [LinearMap.separatingLeft_iff_ker_eq_bot,
    (LieModule.traceForm_isSymm R H L).isRefl.nondegenerate_iff_separatingLeft]

中文:
引理 traceForm_cartan_nondegenerate
  证明: by
  simp [LinearMap.separatingLeft_iff_ker_eq_bot,
    (LieModule.traceForm_isSymm R H L).isRefl.nondegenerate_iff_separatingLeft]

Depends on / 依赖: LieModule, LieModule.traceForm_isSymm, LinearMap, LinearMap.separatingLeft_iff_ker_eq_bot, isRefl, isRefl.nondegenerate_iff_separatingLeft, nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot, traceForm_isSymm
-/
lemma traceForm_cartan_nondegenerate
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieModule.traceForm R H L).Nondegenerate := by
  simp [LinearMap.separatingLeft_iff_ker_eq_bot,
    (LieModule.traceForm_isSymm R H L).isRefl.nondegenerate_iff_separatingLeft]

variable [Module.Free R L] [Module.Finite R L]

/--
Instance `instIsLieAbelianOfIsCartanSubalgebra` / 实例 `instIsLieAbelianOfIsCartanSubalgebra`

English:
instance instIsLieAbelianOfIsCartanSubalgebra
  body: LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

中文:
实例 instIsLieAbelianOfIsCartanSubalgebra
  定义体: LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

Depends on / 依赖: LieModule, LieModule.isLieAbelian_of_ker_traceForm_eq_bot, isLieAbelian_of_ker_traceForm_eq_bot, ker_restrict_eq_bot_of_isCartanSubalgebra
-/
instance instIsLieAbelianOfIsCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    IsLieAbelian H :=
LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

end IsKilling

section Field

open Module LieModule Set
open Submodule (span subset_span)

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

section
variable [IsTriangularizable K H L]

/--
lemma `killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero` / 引理 `killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero`

English:
lemma killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero
  statement: {α β : H -> K} {x y : L}
  proof: by
  /- If `ad R L z` is semisimple for all `z ∈ H` then writing `⟪x, y⟫ = killingForm K L x y`, there
  is a slick proof of this lemma that requires only invariance of the Killing form as follows.
  For any `z ∈ H`, we have:
  `α z • ⟪x, y⟫ = ⟪α z • x, y⟫ = ⟪⁅z, x⁆, y⟫ = - ⟪x, ⁅z, y⁆⟫ = - ⟪x, β z •

中文:
引理 killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero
  结论: {α β : H -> K} {x y : L}
  证明: by
  /- If `ad R L z` is semisimple for all `z ∈ H` then writing `⟪x, y⟫ = killingForm K L x y`, there
  is a slick proof of this lemma that requires only invariance of the Killing form as follows.
  For any `z ∈ H`, we have:
  `α z • ⟪x, y⟫ = ⟪α z • x, y⟫ = ⟪⁅z, x⁆, y⟫ = - ⟪x, ⁅z, y⁆⟫ = - ⟪x, β z •
-/
lemma killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H -> K} {x y : L}
    (hx : x in rootSpace H α) (hy : y in rootSpace H β) (hαβ : α + β != 0) :
    killingForm K L x y = 0 := by
  /- If `ad R L z` is semisimple for all `z ∈ H` then writing `⟪x, y⟫ = killingForm K L x y`, there
  is a slick proof of this lemma that requires only invariance of the Killing form as follows.
  For any `z ∈ H`, we have:
  `α z • ⟪x, y⟫ = ⟪α z • x, y⟫ = ⟪⁅z, x⁆, y⟫ = - ⟪x, ⁅z, y⁆⟫ = - ⟪x, β z • y⟫ = - β z • ⟪x, y⟫`.
  Since this is true for any `z`, we thus have: `(α + β) • ⟪x, y⟫ = 0`, and hence the result.
  However the semisimplicity of `ad R L z` is (a) non-trivial and (b) requires the assumption
  that `K` is a perfect field and `L` has non-degenerate Killing form. -/
  let σ : (H -> K) -> (H -> K) := fun γ => α + (β + γ)
  have hσ : forall γ, σ γ != γ := fun γ => by simpa only [σ, ← add_assoc] using add_ne_right.mpr hαβ
  let f : Module.End K L := (ad K L x) ∘ₗ (ad K L y)
  have hf : forall γ, MapsTo f (rootSpace H γ) (rootSpace H (σ γ)) := fun γ =>
(mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α (β + γ) hx).comp
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L β γ hy
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace K H L)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top K H L)
  exact LinearMap.trace_eq_zero_of_mapsTo_ne hds σ hσ hf

/--
lemma `mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg` / 引理 `mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg`

English:
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
  proof: by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y in ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | mem β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_a

中文:
引理 mem_ker_killingForm_of_mem_rootSpace_of_对任意_rootSpace_neg
  证明: by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y in ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | mem β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_a

Depends on / 依赖: LieSubmodule, LieSubmodule.iSup_induction, LinearMap, LinearMap.mem_ker, add_eq_zero_iff_neg_eq, add_eq_zero_iff_neg_eq.mp, iSup_genWeightSpace_eq_top, iSup_induction, killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero, mem_ker, rootSpace
-/
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H -> K} {x : L} (hx : x in rootSpace H α)
    (hx' : forall y in rootSpace H (-α), killingForm K L x y = 0) :
    x in LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y in ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | mem β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  | zero => simp
  | add => simp_all
end

end Field

end LieAlgebra

namespace LieModule

namespace Weight

open LieAlgebra IsKilling

variable {K L}

variable [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L] {α : Weight K H L}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveNeg (Weight K H L)
  body: ⟨-α, by
    by_cases hα : α.IsZero
    · convert! α.genWeightSpace_ne_bot; rw [hα, neg_zero]
    · intro e
      obtain ⟨x, hx, x_ne0⟩ := α.exists_ne_zero
      have := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hx
        (fun y hy => by rw [rootSpace, e] at hy; rw [hy, map_

中文:
实例 :
  签名: InvolutiveNeg (Weight K H L)
  定义体: ⟨-α, by
    by_cases hα : α.IsZero
    · convert! α.genWeightSpace_ne_bot; rw [hα, neg_zero]
    · intro e
      obtain ⟨x, hx, x_ne0⟩ := α.exists_ne_zero
      have := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hx
        (fun y hy => by rw [rootSpace, e] at hy; rw [hy, map_

Depends on / 依赖: IsZero, convert, exists_ne_zero, genWeightSpace_ne_bot, ker_killingForm_eq_bot, map_zero, mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg, neg_neg, neg_zero, rootSpace, x_ne0
-/
instance : InvolutiveNeg (Weight K H L) where
  neg α := ⟨-α, by
    by_cases hα : α.IsZero
    · convert! α.genWeightSpace_ne_bot; rw [hα, neg_zero]
    · intro e
      obtain ⟨x, hx, x_ne0⟩ := α.exists_ne_zero
      have := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hx
        (fun y hy => by rw [rootSpace, e] at hy; rw [hy, map_zero])
      rw [ker_killingForm_eq_bot] at this
      exact x_ne0 this⟩
  neg_neg α := by ext; simp

/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  statement: ((-α : Weight K H L) : H -> K) = -α
  proof: rfl

中文:
引理 coe_neg
  结论: ((-α : Weight K H L) : H -> K) = -α
  证明: rfl
-/
@[simp] lemma coe_neg : ((-α : Weight K H L) : H -> K) = -α := rfl

/--
lemma `IsZero.neg` / 引理 `IsZero.neg`

English:
lemma IsZero.neg
  given: (h : α.IsZero)
  statement: (-α).IsZero
  proof: by ext; rw [coe_neg, h, neg_zero]

中文:
引理 是零.neg
  条件: (h : α.是零)
  结论: (-α).是零
  证明: by ext; rw [coe_neg, h, neg_zero]

Depends on / 依赖: coe_neg, neg_zero
-/
lemma IsZero.neg (h : α.IsZero) : (-α).IsZero := by ext; rw [coe_neg, h, neg_zero]

/--
lemma `isZero_neg` / 引理 `isZero_neg`

English:
lemma isZero_neg
  statement: (-α).IsZero ↔ α.IsZero
  proof: ⟨fun h => neg_neg α ▸ h.neg, fun h => h.neg⟩

中文:
引理 isZero_neg
  结论: (-α).是零 ↔ α.是零
  证明: ⟨fun h => neg_neg α ▸ h.neg, fun h => h.neg⟩
-/
@[simp] lemma isZero_neg : (-α).IsZero ↔ α.IsZero := ⟨fun h => neg_neg α ▸ h.neg, fun h => h.neg⟩

/--
lemma `IsNonZero.neg` / 引理 `IsNonZero.neg`

English:
lemma IsNonZero.neg
  given: (h : α.IsNonZero)
  statement: (-α).IsNonZero
  proof: fun e => h (by simpa using e.neg)

中文:
引理 IsNonZero.neg
  条件: (h : α.IsNonZero)
  结论: (-α).IsNonZero
  证明: fun e => h (by simpa using e.neg)

Depends on / 依赖: e.neg
-/
lemma IsNonZero.neg (h : α.IsNonZero) : (-α).IsNonZero := fun e => h (by simpa using e.neg)

/--
lemma `isNonZero_neg` / 引理 `isNonZero_neg`

English:
lemma isNonZero_neg
  given: {α : Weight K H L}
  statement: (-α).IsNonZero ↔ α.IsNonZero
  proof: isZero_neg.not

中文:
引理 isNonZero_neg
  条件: {α : Weight K H L}
  结论: (-α).IsNonZero ↔ α.IsNonZero
  证明: isZero_neg.not
-/
@[simp] lemma isNonZero_neg {α : Weight K H L} : (-α).IsNonZero ↔ α.IsNonZero := isZero_neg.not

/--
lemma `toLinear_neg` / 引理 `toLinear_neg`

English:
lemma toLinear_neg
  given: {α : Weight K H L}
  statement: (-α).toLinear = -α.toLinear
  proof: rfl

中文:
引理 toLinear_neg
  条件: {α : Weight K H L}
  结论: (-α).toLinear = -α.toLinear
  证明: rfl
-/
@[simp] lemma toLinear_neg {α : Weight K H L} : (-α).toLinear = -α.toLinear := rfl

end Weight

end LieModule

namespace LieAlgebra

open Module LieModule Set
open Submodule renaming span -> span
open Submodule renaming subset_span -> subset_span

namespace IsKilling

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
variable [IsKilling K L]
attribute [local instance 100] LieRing.ofAssociativeRing

/--
lemma `eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra` / 引理 `eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra`

English:
lemma eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra
  statement: {x : L} (hx : x in H)
  proof: by
  suffices ⟨x, hx⟩ in LinearMap.ker (traceForm K H L) by
    simp only [ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.mem_bot] at this
    exact (AddSubmonoid.mk_eq_zero H.toAddSubmonoid).mp this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K 

中文:
引理 eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra
  结论: {x : L} (hx : x in H)
  证明: by
  suffices ⟨x, hx⟩ in LinearMap.ker (traceForm K H L) by
    simp only [ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.mem_bot] at this
    exact (AddSubmonoid.mk_eq_zero H.toAddSubmonoid).mp this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mk_eq_zero, Commute, H.toAddSubmonoid, LieHom, LieHom.map_lie, LinearMap, LinearMap.isNilpotent_trac, LinearMap.ker, LinearMap.mem_ker, LinearMap.zero_apply, Module, Module.End.mul_eq_comp, Submodule, Submodule.mem_bot, commute_iff_lie_eq, isNilpotent_trac, ker_traceForm_eq_bot_of_isCartanSubalgebra, map_lie, map_zero
-/
lemma eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x in H)
    (hx' : _root_.IsNilpotent (ad K L x)) : x = 0 := by
  suffices ⟨x, hx⟩ in LinearMap.ker (traceForm K H L) by
    simp only [ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.mem_bot] at this
    exact (AddSubmonoid.mk_eq_zero H.toAddSubmonoid).mp this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K H L y) := by
    rw [commute_iff_lie_eq]; rw [← LieHom.map_lie]; rw [trivial_lie_zero]; rw [map_zero]
  rw [traceForm_apply_apply]; rw [← Module.End.mul_eq_comp]; rw [LinearMap.zero_apply]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (comm.isNilpotent_mul_right hx')).eq_zero

@[simp]
/--
lemma `corootSpace_zero_eq_bot` / 引理 `corootSpace_zero_eq_bot`

English:
lemma corootSpace_zero_eq_bot
  proof: by
  refine eq_bot_iff.mpr fun x hx => ?_
  suffices {x | exists y in H, exists z in H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z,

中文:
引理 corootSpace_zero_eq_bot
  证明: by
  refine eq_bot_iff.mpr fun x hx => ?_
  suffices {x | exists y in H, exists z in H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z,

Depends on / 依赖: H.zero_mem, LieSubalgebra, LieSubalgebra.coe_bracket, Subtype, Subtype.ext_iff, ZeroMemClass, ZeroMemClass.coe_zero, coe_bracket, coe_zero, eq_bot_iff, eq_bot_iff.mpr, eq_singleton_iff_unique_mem, eq_singleton_iff_unique_mem.mpr, ext_iff, mem_corootSpace, trivial_lie_zero, zero_lie, zero_mem
-/
lemma corootSpace_zero_eq_bot :
    corootSpace (0 : H -> K) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  suffices {x | exists y in H, exists z in H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z, hz⟩ : H)⁆ = 0 by
    simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using this
  simp [trivial_lie_zero]

variable {K L} in
/-- The restriction of the Killing form to a Cartan subalgebra, as a linear equivalence to the
dual. -/
@[simps! apply_apply]
/--
Definition of `cartanEquivDual` / `cartanEquivDual` 的定义

English:
definition cartanEquivDual
  signature: :
  body: (traceForm K H L).toDual traceForm_cartan_nondegenerate K L H

中文:
定义 cartanEquivDual
  签名: :
  定义体: (traceForm K H L).toDual traceForm_cartan_nondegenerate K L H

Depends on / 依赖: toDual, traceForm, traceForm_cartan_nondegenerate
-/
noncomputable def cartanEquivDual :
    H ≃ₗ[K] Module.Dual K H :=
(traceForm K H L).toDual traceForm_cartan_nondegenerate K L H

variable {K L H}

/--
Definition of `coroot` / `coroot` 的定义

English:
definition coroot
  signature: (α : Weight K H L)
  body: 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α

中文:
定义 coroot
  签名: (α : Weight K H L)
  定义体: 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α

Depends on / 依赖: cartanEquivDual
-/
noncomputable def coroot (α : Weight K H L) : H :=
  2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α

/--
lemma `traceForm_coroot` / 引理 `traceForm_coroot`

English:
lemma traceForm_coroot
  given: (α : Weight K H L) (x : H)
  proof: by
  have : cartanEquivDual H ((cartanEquivDual H).symm α) x = α x := by
    rw [LinearEquiv.apply_symm_apply]; rw [Weight.toLinear_apply]
  rw [coroot]; rw [map_nsmul]; rw [map_smul]; rw [LinearMap.smul_apply]; rw [LinearMap.smul_apply]
  congr 2

中文:
引理 traceForm_coroot
  条件: (α : Weight K H L) (x : H)
  证明: by
  have : cartanEquivDual H ((cartanEquivDual H).symm α) x = α x := by
    rw [LinearEquiv.apply_symm_apply]; rw [Weight.toLinear_apply]
  rw [coroot]; rw [map_nsmul]; rw [map_smul]; rw [LinearMap.smul_apply]; rw [LinearMap.smul_apply]
  congr 2

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearMap, LinearMap.smul_apply, Weight, Weight.toLinear_apply, apply_symm_apply, cartanEquivDual, coroot, map_nsmul, map_smul, smul_apply, toLinear_apply
-/
lemma traceForm_coroot (α : Weight K H L) (x : H) :
    traceForm K H L (coroot α) x = 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • α x := by
  have : cartanEquivDual H ((cartanEquivDual H).symm α) x = α x := by
    rw [LinearEquiv.apply_symm_apply]; rw [Weight.toLinear_apply]
  rw [coroot]; rw [map_nsmul]; rw [map_smul]; rw [LinearMap.smul_apply]; rw [LinearMap.smul_apply]
  congr 2

/--
lemma `coroot_neg` / 引理 `coroot_neg`

English:
lemma coroot_neg
  given: [IsTriangularizable K H L] (α : Weight K H L)
  proof: by
  simp [coroot]

中文:
引理 coroot_neg
  条件: [是Triangularizable K H L] (α : Weight K H L)
  证明: by
  simp [coroot]
-/
@[simp] lemma coroot_neg [IsTriangularizable K H L] (α : Weight K H L) :
    coroot (-α) = -coroot α := by
  simp [coroot]

variable [IsTriangularizable K H L]

/--
lemma `lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux` / 引理 `lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux`

English:
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux
  proof: by
  set α' := (cartanEquivDual H).symm α
  rw [← sub_eq_zero]; rw [← Submodule.mem_bot (R := K)]; rw [← ker_killingForm_eq_bot]
  apply mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg (α := (0 : H -> K))
  · simp only [rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule]
    refine sub

中文:
引理 lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux
  证明: by
  set α' := (cartanEquivDual H).symm α
  rw [← sub_eq_zero]; rw [← Submodule.mem_bot (R := K)]; rw [← ker_killingForm_eq_bot]
  apply mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg (α := (0 : H -> K))
  · simp only [rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule]
    refine sub

Depends on / 依赖: H.smul_mem, LieSubalgebra, LieSubalgebra.mem_toLieSubmodule, Submodule, Submodule.mem_bot, cartanEquivDual, ker_killingForm_eq_bot, mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace, mem_bot, mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg, mem_toLieSubmodule, property, replace, rootSpace_zero_eq, smul_mem, sub_eq_zero, sub_mem
-/
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux
    {α : Weight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace H (-α))
    (aux : forall (h : H), ⁅h, e⁆ = α h • e) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by
  set α' := (cartanEquivDual H).symm α
  rw [← sub_eq_zero]; rw [← Submodule.mem_bot (R := K)]; rw [← ker_killingForm_eq_bot]
  apply mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg (α := (0 : H -> K))
  · simp only [rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule]
    refine sub_mem ?_ (H.smul_mem _ α'.property)
    simpa using mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α (-α) heα hfα
  · intro z hz
    replace hz : z in H := by simpa using hz
    have he : ⁅z, e⁆ = α ⟨z, hz⟩ • e := aux ⟨z, hz⟩
    have hαz : killingForm K L α' (⟨z, hz⟩ : H) = α ⟨z, hz⟩ :=
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) _ _
    simp [traceForm_comm K L L ⁅e, f⁆, ← traceForm_apply_lie_apply, he, mul_comm _ (α ⟨z, hz⟩), hαz]

/--
lemma `cartanEquivDual_symm_apply_mem_corootSpace` / 引理 `cartanEquivDual_symm_apply_mem_corootSpace`

English:
lemma cartanEquivDual_symm_apply_mem_corootSpace
  given: (α : Weight K H L)
  proof: by
  obtain ⟨e : L, he₀ : e != 0, he : forall x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e in rootSpace H α := (mem_genWeightSpace L α e).mpr fun x => ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : exists f in rootSpace H (-α), killingForm K L e f != 0 := by
    contrapose

中文:
引理 cartanEquivDual_symm_apply_mem_corootSpace
  条件: (α : Weight K H L)
  证明: by
  obtain ⟨e : L, he₀ : e != 0, he : forall x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e in rootSpace H α := (mem_genWeightSpace L α e).mpr fun x => ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : exists f in rootSpace H (-α), killingForm K L e f != 0 := by
    contrapose

Depends on / 依赖: Submodule, Submodule.subse, cartanEquivDual, contrapose, exists_forall_lie_eq_smul, killingForm, mem_corootSpace, mem_genWeightSpace, mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg, rootSpace
-/
lemma cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) :
    (cartanEquivDual H).symm α in corootSpace α := by
  obtain ⟨e : L, he₀ : e != 0, he : forall x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e in rootSpace H α := (mem_genWeightSpace L α e).mpr fun x => ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : exists f in rootSpace H (-α), killingForm K L e f != 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  suffices ⁅e, f⁆ = killingForm K L e f • ((cartanEquivDual H).symm α : L) from
(mem_corootSpace α).mpr Submodule.subset_span ⟨(killingForm K L e f)⁻¹ • e,
      Submodule.smul_mem _ _ heα, f, hfα, by simpa [inv_smul_eq_iff₀ hf]⟩
  exact lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα he

/--
lemma `coroot_mem_corootSpace` / 引理 `coroot_mem_corootSpace`

English:
lemma coroot_mem_corootSpace
  given: (α : Weight K H L)
  proof: nsmul_mem (Submodule.smul_mem _ _ <| cartanEquivDual_symm_apply_mem_corootSpace α) _

中文:
引理 coroot_mem_corootSpace
  条件: (α : Weight K H L)
  证明: nsmul_mem (Submodule.smul_mem _ _ <| cartanEquivDual_symm_apply_mem_corootSpace α) _
-/
@[simp] lemma coroot_mem_corootSpace (α : Weight K H L) :
    coroot α in corootSpace α :=
  nsmul_mem (Submodule.smul_mem _ _ <| cartanEquivDual_symm_apply_mem_corootSpace α) _

/-- Given a splitting Cartan subalgebra `H` of a finite-dimensional Lie algebra with non-singular
Killing form, the corresponding roots span the dual space of `H`. -/
@[simp]
/--
lemma `span_weight_eq_top` / 引理 `span_weight_eq_top`

English:
lemma span_weight_eq_top
  proof: by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L]; rw [← LinearMap.dualAnnihilator_ker_eq_range_flip]; rw [ker_traceForm_eq_bot_of_isCartanSubalgebra]; rw [Submodule.dualAnnihilator_bot]

中文:
引理 span_weight_eq_top
  证明: by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L]; rw [← LinearMap.dualAnnihilator_ker_eq_range_flip]; rw [ker_traceForm_eq_bot_of_isCartanSubalgebra]; rw [Submodule.dualAnnihilator_bot]

Depends on / 依赖: LieModule, LieModule.range_traceForm_le_span_weight, LinearMap, LinearMap.dualAnnihilator_ker_eq_range_flip, Submodule, Submodule.dualAnnihilator_bot, dualAnnihilator_bot, dualAnnihilator_ker_eq_range_flip, eq_top_iff, eq_top_iff.mpr, ker_traceForm_eq_bot_of_isCartanSubalgebra, le_trans, range_traceForm_le_span_weight, traceForm_flip
-/
lemma span_weight_eq_top :
    span K (range (Weight.toLinear K H L)) = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L]; rw [← LinearMap.dualAnnihilator_ker_eq_range_flip]; rw [ker_traceForm_eq_bot_of_isCartanSubalgebra]; rw [Submodule.dualAnnihilator_bot]

variable (K L H) in
@[simp]
/--
lemma `span_weight_isNonZero_eq_top` / 引理 `span_weight_isNonZero_eq_top`

English:
lemma span_weight_isNonZero_eq_top
  proof: by
  rw [← span_weight_eq_top]
  refine le_antisymm (Submodule.span_mono <| by simp) ?_
  suffices range (Weight.toLinear K H L) subseteq
    insert 0 ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) by
    simpa only [Submodule.span_insert_zero] using Submodule.span_mono this
  rint

中文:
引理 span_weight_isNonZero_eq_top
  证明: by
  rw [← span_weight_eq_top]
  refine le_antisymm (Submodule.span_mono <| by simp) ?_
  suffices range (Weight.toLinear K H L) subseteq
    insert 0 ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) by
    simpa only [Submodule.span_insert_zero] using Submodule.span_mono this
  rint

Depends on / 依赖: IsNonZero, Submodule, Submodule.span_insert_zero, Submodule.span_mono, Weight, Weight.coe_toLinear_eq_zero_iff, Weight.toLinear, coe_toLinear_eq_zero_iff, insert, le_antisymm, mem_image, mem_insert_iff, mem_ofPred_eq, span_insert_zero, span_mono, span_weight_eq_top, subseteq, toLinear
-/
lemma span_weight_isNonZero_eq_top :
    span K ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) = ⊤ := by
  rw [← span_weight_eq_top]
  refine le_antisymm (Submodule.span_mono <| by simp) ?_
  suffices range (Weight.toLinear K H L) subseteq
    insert 0 ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) by
    simpa only [Submodule.span_insert_zero] using Submodule.span_mono this
  rintro - ⟨α, rfl⟩
  simp only [mem_insert_iff, Weight.coe_toLinear_eq_zero_iff, mem_image, mem_ofPred_eq]
  tauto

@[simp]
/--
lemma `iInf_ker_weight_eq_bot` / 引理 `iInf_ker_weight_eq_bot`

English:
lemma iInf_ker_weight_eq_bot
  proof: by
  rw [← Subspace.dualAnnihilator_inj]; rw [Subspace.dualAnnihilator_iInf_eq]; rw [Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

中文:
引理 iInf_ker_weight_eq_bot
  证明: by
  rw [← Subspace.dualAnnihilator_inj]; rw [Subspace.dualAnnihilator_iInf_eq]; rw [Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

Depends on / 依赖: LinearMap, LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule, Submodule.dualAnnihilator_bot, Submodule.span_range_eq_iSup, Subspace, Subspace.dualAnnihilator_iInf_eq, Subspace.dualAnnihilator_inj, dualAnnihilator_bot, dualAnnihilator_iInf_eq, dualAnnihilator_inj, range_dualMap_eq_dualAnnihilator_ker, span_range_eq_iSup
-/
lemma iInf_ker_weight_eq_bot :
    ⨅ α : Weight K H L, α.ker = ⊥ := by
  rw [← Subspace.dualAnnihilator_inj]; rw [Subspace.dualAnnihilator_iInf_eq]; rw [Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

section PerfectField

variable [PerfectField K]

open Module.End in
/--
lemma `isSemisimple_ad_of_mem_isCartanSubalgebra` / 引理 `isSemisimple_ad_of_mem_isCartanSubalgebra`

English:
lemma isSemisimple_ad_of_mem_isCartanSubalgebra
  given: {x : L} (hx : x in H)
  proof: by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_o

中文:
引理 isSemisimple_ad_of_mem_isCartanSubalgebra
  条件: {x : L} (hx : x in H)
  证明: by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_o
-/
lemma isSemisimple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x in H) :
    (ad K L x).IsSemisimple := by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_of_add_eq hSN.symm] at hN
  /- Note that the semisimple part `S` is just a scalar action on each root space. -/
  have aux {α : H -> K} {y : L} (hy : y in rootSpace H α) : S y = α x' • y := by
    replace hy : y in (ad K L x).maxGenEigenspace (α x') :=
      (genWeightSpace_le_genWeightSpaceOf L x' α) hy
    rw [maxGenEigenspace_eq] at hy
    set k := maxGenEigenspaceIndex (ad K L x) (α x')
    rw [apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hy hS₀ hS.isFinitelySemisimple hN]
  /- So `S` obeys the derivation axiom if we restrict to root spaces. -/
  have h_der (y z : L) (α β : H -> K) (hy : y in rootSpace H α) (hz : z in rootSpace H β) :
      S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hyz : ⁅y, z⁆ in rootSpace H (α + β) :=
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β hy hz
    rw [aux hy]; rw [aux hz]; rw [aux hyz]; rw [smul_lie]; rw [lie_smul]; rw [← add_smul]; rw [← Pi.add_apply]
  /- Thus `S` is a derivation since root spaces span. -/
  replace h_der (y z : L) : S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hy : y in ⨆ α : H -> K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    have hz : z in ⨆ α : H -> K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      induction hz using LieSubmodule.iSup_induction' with
      | mem β z hz => exact h_der y z α β hy hz
      | zero => simp
      | add _ _ _ _ h h' => simp only [lie_add, map_add, h, h']; abel
    | zero => simp
    | add _ _ _ _ h h' => simp only [add_lie, map_add, h, h']; abel
  /- An equivalent form of the derivation axiom used in `LieDerivation`. -/
  replace h_der : forall y z : L, S ⁅y, z⁆ = ⁅y, S z⁆ - ⁅z, S y⁆ := by
    simp_rw [← lie_skew (S _) _, add_comm, ← sub_eq_add_neg] at h_der; assumption
  /- Bundle `S` as a `LieDerivation`. -/
  let S' : LieDerivation K L L := ⟨S, h_der⟩
  /- Since `L` has non-degenerate Killing form, `S` must be inner, corresponding to some `y : L`. -/
  obtain ⟨y, hy⟩ := LieDerivation.IsKilling.exists_eq_ad S'
  /- `y` commutes with all elements of `H` because `S` has eigenvalue 0 on `H`, `S = ad K L y`. -/
  have hy' (z : L) (hz : z in H) : ⁅y, z⁆ = 0 := by
    rw [← LieSubalgebra.mem_toLieSubmodule]; rw [← rootSpace_zero_eq] at hz
    simp [S', ← ad_apply (R := K), ← LieDerivation.coe_ad_apply_eq_ad_apply, hy, aux hz]
  /- Thus `y` belongs to `H` since `H` is self-normalizing. -/
  replace hy' : y in H := by
    suffices y in H.normalizer by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at this
    exact (H.mem_normalizer_iff y).mpr fun z hz => hy' z hz ▸ LieSubalgebra.zero_mem H
  /- It suffices to show `x = y` since `S = ad K L y` is semisimple. -/
  suffices x = y by rwa [this, ← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rw [← sub_eq_zero]
  /- This will follow if we can show that `ad K L (x - y)` is nilpotent. -/
  apply eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra K L H (H.sub_mem hx hy')
  /- Which is true because `ad K L (x - y) = N`. -/
  replace hy : S = ad K L y := by rw [← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rwa [map_sub, hSN, hy, add_sub_cancel_right, eq_sub_of_add_eq hSN.symm]

/--
lemma `lie_eq_smul_of_mem_rootSpace` / 引理 `lie_eq_smul_of_mem_rootSpace`

English:
lemma lie_eq_smul_of_mem_rootSpace
  given: {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H)
  proof: by
  replace hx : x in (ad K L h).maxGenEigenspace (α h) :=
    genWeightSpace_le_genWeightSpaceOf L h α hx
  rw [(isSemisimple_ad_of_mem_isCartanSubalgebra
    h.property).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]; rw [Module.End.mem_eigenspace_iff] at hx
  simpa using hx

中文:
引理 lie_eq_smul_of_mem_rootSpace
  条件: {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H)
  证明: by
  replace hx : x in (ad K L h).maxGenEigenspace (α h) :=
    genWeightSpace_le_genWeightSpaceOf L h α hx
  rw [(isSemisimple_ad_of_mem_isCartanSubalgebra
    h.property).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]; rw [Module.End.mem_eigenspace_iff] at hx
  simpa using hx

Depends on / 依赖: Module, Module.End.mem_eigenspace_iff, genWeightSpace_le_genWeightSpaceOf, h.property, isFinitelySemisimple, isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, isSemisimple_ad_of_mem_isCartanSubalgebra, maxGenEigenspace, maxGenEigenspace_eq_eigenspace, mem_eigenspace_iff, property, replace
-/
lemma lie_eq_smul_of_mem_rootSpace {α : H -> K} {x : L} (hx : x in rootSpace H α) (h : H) :
    ⁅h, x⁆ = α h • x := by
  replace hx : x in (ad K L h).maxGenEigenspace (α h) :=
    genWeightSpace_le_genWeightSpaceOf L h α hx
  rw [(isSemisimple_ad_of_mem_isCartanSubalgebra
    h.property).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]; rw [Module.End.mem_eigenspace_iff] at hx
  simpa using hx

/--
lemma `lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg` / 引理 `lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg`

English:
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
  proof: by
  apply lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα
  exact lie_eq_smul_of_mem_rootSpace heα

中文:
引理 lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
  证明: by
  apply lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα
  exact lie_eq_smul_of_mem_rootSpace heα

Depends on / 依赖: lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux, lie_eq_smul_of_mem_rootSpace
-/
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    {α : Weight K H L} {e f : L} (heα : e in rootSpace H α) (hfα : f in rootSpace H (-α)) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by
  apply lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα
  exact lie_eq_smul_of_mem_rootSpace heα

/--
lemma `coe_corootSpace_eq_span_singleton'` / 引理 `coe_corootSpace_eq_span_singleton'`

English:
lemma coe_corootSpace_eq_span_singleton'
  given: (α : Weight K H L)
  proof: by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} subseteq
        K ∙ ((cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα]; rw

中文:
引理 coe_corootSpace_eq_span_singleton'
  条件: (α : Weight K H L)
  证明: by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} subseteq
        K ∙ ((cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα]; rw

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_toSubmodule, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_span_singleton, Submodule.span_mono, Submodule.span_span, cartanEquivDual, killingForm, le_antisymm, lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg, mem_coe, mem_corootSpace, mem_span_singleton, mem_toSubmodule, replace, rootSpace, span_mono, span_span
-/
lemma coe_corootSpace_eq_span_singleton' (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ (cartanEquivDual H).symm α := by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y in rootSpace H α) (z in rootSpace H (-α))} subseteq
        K ∙ ((cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα]; rw [SetLike.mem_coe]; rw [Submodule.mem_span_singleton]
      exact ⟨killingForm K L e f, rfl⟩
    simp only [LieSubmodule.mem_toSubmodule, mem_corootSpace] at hx'
    replace this := Submodule.span_mono this hx'
    rw [Submodule.span_span] at this
    rw [Submodule.mem_span_singleton] at this ⊢
    obtain ⟨t, rfl⟩ := this
    solve_by_elim
  · simp only [Submodule.span_singleton_le_iff_mem, LieSubmodule.mem_toSubmodule]
    exact cartanEquivDual_symm_apply_mem_corootSpace α

end PerfectField

section CharZero

variable [CharZero K]

/--
lemma `eq_zero_of_apply_eq_zero_of_mem_corootSpace` / 引理 `eq_zero_of_apply_eq_zero_of_mem_corootSpace`

English:
lemma eq_zero_of_apply_eq_zero_of_mem_corootSpace
  proof: by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x in ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β => ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] u

中文:
引理 eq_zero_of_apply_eq_zero_of_mem_corootSpace
  证明: by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x in ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β => ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] u

Depends on / 依赖: Submodule, Submodule.mem_iInf, Weight, eq_or_ne, exists_forall_mem_corootSpace_smul_add_eq_zero, genWeightSpace_ne_bot, hb.ne, mem_iInf, replace
-/
lemma eq_zero_of_apply_eq_zero_of_mem_corootSpace
    (x : H) (α : H -> K) (hαx : α x = 0) (hx : x in corootSpace α) :
    x = 0 := by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x in ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β => ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx

/--
lemma `disjoint_ker_weight_corootSpace` / 引理 `disjoint_ker_weight_corootSpace`

English:
lemma disjoint_ker_weight_corootSpace
  given: (α : Weight K H L)
  proof: by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ => ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

中文:
引理 disjoint_ker_weight_corootSpace
  条件: (α : Weight K H L)
  证明: by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ => ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

Depends on / 依赖: Submodule, Submodule.eq_bot_iff, disjoint_iff, eq_bot_iff, eq_zero_of_apply_eq_zero_of_mem_corootSpace, replace
-/
lemma disjoint_ker_weight_corootSpace (α : Weight K H L) :
    Disjoint α.ker (corootSpace α) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ => ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

/--
lemma `root_apply_cartanEquivDual_symm_ne_zero` / 引理 `root_apply_cartanEquivDual_symm_ne_zero`

English:
lemma root_apply_cartanEquivDual_symm_ne_zero
  given: {α : Weight K H L} (hα : α.IsNonZero)
  proof: by
  contrapose hα
  suffices (cartanEquivDual H).symm α in α.ker ⊓ corootSpace α by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, cartanEquivDual_symm_apply_mem_corootSpace α⟩

中文:
引理 root_apply_cartanEquivDual_symm_ne_zero
  条件: {α : Weight K H L} (hα : α.IsNonZero)
  证明: by
  contrapose hα
  suffices (cartanEquivDual H).symm α in α.ker ⊓ corootSpace α by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, cartanEquivDual_symm_apply_mem_corootSpace α⟩

Depends on / 依赖: Submodule, Submodule.mem_inf.mp, cartanEquivDual, cartanEquivDual_symm_apply_mem_corootSpace, contrapose, corootSpace, disjoint_ker_weight_corootSpace, eq_bot, mem_inf
-/
lemma root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    α ((cartanEquivDual H).symm α) != 0 := by
  contrapose hα
  suffices (cartanEquivDual H).symm α in α.ker ⊓ corootSpace α by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, cartanEquivDual_symm_apply_mem_corootSpace α⟩

/--
lemma `root_apply_coroot` / 引理 `root_apply_coroot`

English:
lemma root_apply_coroot
  given: {α : Weight K H L} (hα : α.IsNonZero)
  proof: by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel₀ (root_apply_cartanEquivDual_symm_ne_zero hα)

中文:
引理 root_apply_coroot
  条件: {α : Weight K H L} (hα : α.IsNonZero)
  证明: by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel₀ (root_apply_cartanEquivDual_symm_ne_zero hα)

Depends on / 依赖: Weight, Weight.coe_coe, coe_coe, coroot, root_apply_cartanEquivDual_symm_ne_zero
-/
lemma root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) :
    α (coroot α) = 2 := by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel₀ (root_apply_cartanEquivDual_symm_ne_zero hα)

/--
lemma `coroot_eq_zero_iff` / 引理 `coroot_eq_zero_iff`

English:
lemma coroot_eq_zero_iff
  given: {α : Weight K H L}
  proof: by
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

@[simp]

中文:
引理 coroot_eq_zero_iff
  条件: {α : Weight K H L}
  证明: by
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

@[simp]
-/
@[simp] lemma coroot_eq_zero_iff {α : Weight K H L} :
    coroot α = 0 ↔ α.IsZero := by
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

@[simp]
/--
lemma `coroot_zero` / 引理 `coroot_zero`

English:
lemma coroot_zero
  given: [Nontrivial L]
  statement: coroot (0 : Weight K H L) = 0
  proof: by simp [Weight.isZero_zero]

中文:
引理 coroot_zero
  条件: [非平凡 L]
  结论: coroot (0 : Weight K H L) = 0
  证明: by simp [Weight.isZero_zero]

Depends on / 依赖: Weight, Weight.isZero_zero, isZero_zero
-/
lemma coroot_zero [Nontrivial L] : coroot (0 : Weight K H L) = 0 := by simp [Weight.isZero_zero]

/--
lemma `coe_corootSpace_eq_span_singleton` / 引理 `coe_corootSpace_eq_span_singleton`

English:
lemma coe_corootSpace_eq_span_singleton
  given: (α : Weight K H L)
  proof: by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (cartanEquivDual H).symm α
    suffices (K ∙ coroot α) = K ∙ α' by rw [coe_corootSpace_eq_span_singleton']; exact this.symm
    have : IsUnit (2 * (α α')⁻¹) := by simpa using root_apply_cartanEquivDual_symm_n

中文:
引理 coe_corootSpace_eq_span_singleton
  条件: (α : Weight K H L)
  证明: by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (cartanEquivDual H).symm α
    suffices (K ∙ coroot α) = K ∙ α' by rw [coe_corootSpace_eq_span_singleton']; exact this.symm
    have : IsUnit (2 * (α α')⁻¹) := by simpa using root_apply_cartanEquivDual_symm_n

Depends on / 依赖: IsUnit, IsZero, Nat.cast_smul_eq_nsmul, Submodule, Submodule.span_singleton_smul_eq, cartanEquivDual, cast_smul_eq_nsmul, coe_corootSpace_eq_span_singleton, coroot, coroot_eq_zero_iff, coroot_eq_zero_iff.mpr, root_apply_cartanEquivDual_symm_ne_zero, smul_smul, span_singleton_smul_eq, this.symm
-/
lemma coe_corootSpace_eq_span_singleton (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ coroot α := by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (cartanEquivDual H).symm α
    suffices (K ∙ coroot α) = K ∙ α' by rw [coe_corootSpace_eq_span_singleton']; exact this.symm
    have : IsUnit (2 * (α α')⁻¹) := by simpa using root_apply_cartanEquivDual_symm_ne_zero hα
    change (K ∙ (2 • (α α')⁻¹ • α')) = _
    simpa [← Nat.cast_smul_eq_nsmul K, smul_smul] using Submodule.span_singleton_smul_eq this _

/--
lemma `eq_coroot_of_mem_corootSpace_of_two` / 引理 `eq_coroot_of_mem_corootSpace_of_two`

English:
lemma eq_coroot_of_mem_corootSpace_of_two
  statement: (α : Weight K H L) {x : H}
  proof: by
  by_cases h₀ : α.IsZero; · simp [h₀.eq] at h_two
  replace h_mem : x in K ∙ coroot α := by rwa [← coe_corootSpace_eq_span_singleton]
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h_mem
  suffices t = 1 by simp [this]
  simpa [root_apply_coroot h₀] using h_two

@[simp]

中文:
引理 eq_coroot_of_mem_corootSpace_of_two
  结论: (α : Weight K H L) {x : H}
  证明: by
  by_cases h₀ : α.IsZero; · simp [h₀.eq] at h_two
  replace h_mem : x in K ∙ coroot α := by rwa [← coe_corootSpace_eq_span_singleton]
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h_mem
  suffices t = 1 by simp [this]
  simpa [root_apply_coroot h₀] using h_two

@[simp]

Depends on / 依赖: IsZero, Submodule, Submodule.mem_span_singleton.mp, coe_corootSpace_eq_span_singleton, coroot, h_mem, h_two, mem_span_singleton, replace, root_apply_coroot
-/
lemma eq_coroot_of_mem_corootSpace_of_two (α : Weight K H L) {x : H}
    (h_mem : x in corootSpace α) (h_two : α x = 2) :
    x = coroot α := by
  by_cases h₀ : α.IsZero; · simp [h₀.eq] at h_two
  replace h_mem : x in K ∙ coroot α := by rwa [← coe_corootSpace_eq_span_singleton]
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h_mem
  suffices t = 1 by simp [this]
  simpa [root_apply_coroot h₀] using h_two

@[simp]
/--
lemma `corootSpace_eq_bot_iff` / 引理 `corootSpace_eq_bot_iff`

English:
lemma corootSpace_eq_bot_iff
  given: {α : Weight K H L}
  proof: by
  simp [← LieSubmodule.toSubmodule_eq_bot, coe_corootSpace_eq_span_singleton α]

中文:
引理 corootSpace_eq_bot_iff
  条件: {α : Weight K H L}
  证明: by
  simp [← LieSubmodule.toSubmodule_eq_bot, coe_corootSpace_eq_span_singleton α]

Depends on / 依赖: CanLift, LieSubmodule, LieSubmodule.toSubmodule_eq_bot, Submodule, coe_corootSpace_eq_span_singleton, toSubmodule_eq_bot
-/
lemma corootSpace_eq_bot_iff {α : Weight K H L} :
    corootSpace α = ⊥ ↔ α.IsZero := by
  simp [← LieSubmodule.toSubmodule_eq_bot, coe_corootSpace_eq_span_singleton α]

/--
lemma `isCompl_ker_weight_span_coroot` / 引理 `isCompl_ker_weight_span_coroot`

English:
lemma isCompl_ker_weight_span_coroot
  given: (α : Weight K H L)
  proof: by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by simp_all)
      (disjoint_ker_weight_coroot

中文:
引理 isCompl_ker_weight_span_coroot
  条件: (α : Weight K H L)
  证明: by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by simp_all)
      (disjoint_ker_weight_coroot

Depends on / 依赖: IsZero, LieSubmodule, LieSubmodule.toSubmodule_inj, Module, Module.Dual.isCompl_ker_of_disjoint_of_ne_bot, Weight, Weight.coe_toLinear_eq_zero_iff.mpr, Weight.ker, coe_corootSpace_eq_span_singleton, coe_toLinear_eq_zero_iff, corootSpace, coroot_eq_zero_iff, coroot_eq_zero_iff.mpr, disjoint_ker_weight_corootSpace, isCompl_ker_of_disjoint_of_ne_bot, isCompl_top_bot, ne_eq, replace, toSubmodule_inj
-/
lemma isCompl_ker_weight_span_coroot (α : Weight K H L) :
    IsCompl α.ker (K ∙ coroot α) := by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by simp_all)
      (disjoint_ker_weight_corootSpace α)
    replace hα : corootSpace α != ⊥ := by simpa using hα
    rwa [ne_eq, ← LieSubmodule.toSubmodule_inj] at hα

/--
lemma `traceForm_eq_zero_of_mem_ker_of_mem_span_coroot` / 引理 `traceForm_eq_zero_of_mem_ker_of_mem_span_coroot`

English:
lemma traceForm_eq_zero_of_mem_ker_of_mem_span_coroot
  statement: {α : Weight K H L} {x y : H}
  proof: by
  rw [← coe_corootSpace_eq_span_singleton]; rw [LieSubmodule.mem_toSubmodule]; rw [mem_corootSpace'] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, v, -, huv⟩ := hz
    change killingForm K L (x : L) (z : L) = 0
    replace hx : α x = 0 := by simpa usi

中文:
引理 traceForm_eq_zero_of_mem_ker_of_mem_span_coroot
  结论: {α : Weight K H L} {x y : H}
  证明: by
  rw [← coe_corootSpace_eq_span_singleton]; rw [LieSubmodule.mem_toSubmodule]; rw [mem_corootSpace'] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, v, -, huv⟩ := hz
    change killingForm K L (x : L) (z : L) = 0
    replace hx : α x = 0 := by simpa usi

Depends on / 依赖: LieSubalgebra, LieSubalgebra.coe_bracket_of_module, LieSubmodule, LieSubmodule.mem_toSubmodule, LinearMap, LinearMap.zero_apply, Submodule, Submodule.span_induction, coe_bracket_of_module, coe_corootSpace_eq_span_singleton, killingForm, lie_eq_smul_of_mem_rootSpace, map_zero, mem_corootSpace, mem_toSubmodule, replace, span_induction, traceForm_apply_lie_apply, zero_apply, zero_smul
-/
lemma traceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : H}
    (hx : x in α.ker) (hy : y in K ∙ coroot α) :
    traceForm K H L x y = 0 := by
  rw [← coe_corootSpace_eq_span_singleton]; rw [LieSubmodule.mem_toSubmodule]; rw [mem_corootSpace'] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, v, -, huv⟩ := hz
    change killingForm K L (x : L) (z : L) = 0
    replace hx : α x = 0 := by simpa using hx
    rw [← huv]; rw [← traceForm_apply_lie_apply]; rw [← LieSubalgebra.coe_bracket_of_module]; rw [lie_eq_smul_of_mem_rootSpace hu]; rw [hx]; rw [zero_smul]; rw [map_zero]; rw [LinearMap.zero_apply]
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul _ _ _ hz => simp [hz]

/--
lemma `orthogonal_span_coroot_eq_ker` / 引理 `orthogonal_span_coroot_eq_ker`

English:
lemma orthogonal_span_coroot_eq_ker
  given: (α : Weight K H L)
  proof: by
  if hα : α.IsZero then
    have hα' : coroot α = 0 := by simpa
    replace hα : α.ker = ⊤ := by ext; simp [hα]
    simp [hα, hα']
  else
    refine le_antisymm (fun x hx => ?_) (fun x hx y hy => ?_)
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      specialize hx (coroot α) (Su

中文:
引理 orthogonal_span_coroot_eq_ker
  条件: (α : Weight K H L)
  证明: by
  if hα : α.IsZero then
    have hα' : coroot α = 0 := by simpa
    replace hα : α.ker = ⊤ := by ext; simp [hα]
    simp [hα, hα']
  else
    refine le_antisymm (fun x hx => ?_) (fun x hx y hy => ?_)
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      specialize hx (coroot α) (Su
-/
@[simp] lemma orthogonal_span_coroot_eq_ker (α : Weight K H L) :
    (traceForm K H L).orthogonal (K ∙ coroot α) = α.ker := by
  if hα : α.IsZero then
    have hα' : coroot α = 0 := by simpa
    replace hα : α.ker = ⊤ := by ext; simp [hα]
    simp [hα, hα']
  else
    refine le_antisymm (fun x hx => ?_) (fun x hx y hy => ?_)
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      specialize hx (coroot α) (Submodule.mem_span_singleton_self _)
      simp only [traceForm_coroot, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, false_or] at hx
      simpa using hx.resolve_left (root_apply_cartanEquivDual_symm_ne_zero hα)
    · have := traceForm_eq_zero_of_mem_ker_of_mem_span_coroot hx hy
      rwa [traceForm_comm] at this

/--
lemma `coroot_eq_iff` / 引理 `coroot_eq_iff`

English:
lemma coroot_eq_iff
  given: (α β : Weight K H L)
  proof: by
  refine ⟨fun hyp => ?_, fun h => by rw [h]⟩
  if hα : α.IsZero then
    have hβ : β.IsZero := by
      rw [← coroot_eq_zero_iff] at hα ⊢
      rwa [← hyp]
    ext
    simp [hα.eq, hβ.eq]
  else
    have hβ : β.IsNonZero := by
      contrapose hα
      simp only [← coroot_eq_zero_iff] at hα ⊢
   

中文:
引理 coroot_eq_iff
  条件: (α β : Weight K H L)
  证明: by
  refine ⟨fun hyp => ?_, fun h => by rw [h]⟩
  if hα : α.IsZero then
    have hβ : β.IsZero := by
      rw [← coroot_eq_zero_iff] at hα ⊢
      rwa [← hyp]
    ext
    simp [hα.eq, hβ.eq]
  else
    have hβ : β.IsNonZero := by
      contrapose hα
      simp only [← coroot_eq_zero_iff] at hα ⊢
   
-/
@[simp] lemma coroot_eq_iff (α β : Weight K H L) :
    coroot α = coroot β ↔ α = β := by
  refine ⟨fun hyp => ?_, fun h => by rw [h]⟩
  if hα : α.IsZero then
    have hβ : β.IsZero := by
      rw [← coroot_eq_zero_iff] at hα ⊢
      rwa [← hyp]
    ext
    simp [hα.eq, hβ.eq]
  else
    have hβ : β.IsNonZero := by
      contrapose hα
      simp only [← coroot_eq_zero_iff] at hα ⊢
      rwa [hyp]
    have : α.ker = β.ker := by
      rw [← orthogonal_span_coroot_eq_ker α]; rw [hyp]; rw [orthogonal_span_coroot_eq_ker]
    suffices (α : H ->ₗ[K] K) = β by ext x; simpa using LinearMap.congr_fun this x
    apply Module.Dual.eq_of_ker_eq_of_apply_eq (coroot α) this
    · rw [Weight.toLinear_apply, root_apply_coroot hα, hyp, Weight.toLinear_apply,
        root_apply_coroot hβ]
    · simp [root_apply_coroot hα]

/--
lemma `exists_isSl2Triple_of_weight_isNonZero` / 引理 `exists_isSl2Triple_of_weight_isNonZero`

English:
lemma exists_isSl2Triple_of_weight_isNonZero
  given: {α : Weight K H L} (hα : α.IsNonZero)
  proof: by
  obtain ⟨e, heα : e in rootSpace H α, he₀ : e != 0⟩ := α.exists_ne_zero
  obtain ⟨f', hfα, hf⟩ : exists f in rootSpace H (-α), killingForm K L e f != 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  have hef := lie_eq_killin

中文:
引理 存在_isSl2Triple_of_weight_isNonZero
  条件: {α : Weight K H L} (hα : α.IsNonZero)
  证明: by
  obtain ⟨e, heα : e in rootSpace H α, he₀ : e != 0⟩ := α.exists_ne_zero
  obtain ⟨f', hfα, hf⟩ : exists f in rootSpace H (-α), killingForm K L e f != 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  have hef := lie_eq_killin

Depends on / 依赖: Submodule, Submodule.coe_mem, Submodule.smul_mem, cartanEquivDual, coe_mem, contrapose, exists_ne_zero, killingForm, lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg, mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg, rootSpace, smul_mem
-/
lemma exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) :
    exists h e f : L, IsSl2Triple h e f ∧ e in rootSpace H α ∧ f in rootSpace H (-α) := by
  obtain ⟨e, heα : e in rootSpace H α, he₀ : e != 0⟩ := α.exists_ne_zero
  obtain ⟨f', hfα, hf⟩ : exists f in rootSpace H (-α), killingForm K L e f != 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  let h : H := ⟨⁅e, f'⁆, hef ▸ Submodule.smul_mem _ _ (Submodule.coe_mem _)⟩
  have hh : α h != 0 := by
    have : h = killingForm K L e f' • (cartanEquivDual H).symm α := by
      simp only [h, Subtype.ext_iff, hef]
      rw [Submodule.coe_smul_of_tower]
    rw [this]; rw [map_smul]; rw [smul_eq_mul]; rw [ne_eq]; rw [mul_eq_zero]; rw [not_or]
    exact ⟨hf, root_apply_cartanEquivDual_symm_ne_zero hα⟩
  let f := (2 * (α h)⁻¹) • f'
  replace hef : ⁅⁅e, f⁆, e⁆ = 2 • e := by
    have : ⁅⁅e, f'⁆, e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    rw [lie_smul]; rw [smul_lie]; rw [this]; rw [← smul_assoc]; rw [smul_eq_mul]; rw [mul_assoc]; rw [inv_mul_cancel₀ hh]; rw [mul_one]; rw [two_smul]; rw [two_smul]
  refine ⟨⁅e, f⁆, e, f, ⟨fun contra => ?_, rfl, hef, ?_⟩, heα, Submodule.smul_mem _ _ hfα⟩
  · rw [contra] at hef
    have : IsAddTorsionFree L := .of_isTorsionFree K L
    simp only [zero_lie, eq_comm (a := (0 : L)), smul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hef
    contradiction
  · have : ⁅⁅e, f'⁆, f'⁆ = - α h • f' := lie_eq_smul_of_mem_rootSpace hfα h
    rw [lie_smul]; rw [lie_smul]; rw [smul_lie]; rw [this]
    simp [← smul_assoc, f, hh, mul_comm _ (2 * (α h)⁻¹)]

/--
lemma `_root_.IsSl2Triple.h_eq_coroot` / 引理 `_root_.IsSl2Triple.h_eq_coroot`

English:
lemma _root_.IsSl2Triple.h_eq_coroot
  statement: {α : Weight K H L} (hα : α.IsNonZero)
  proof: by
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift h to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  congr 1
  have key : α h = 2 := by
    have := lie_eq_smul_of_mem_rootSpace heα h
    rw [LieSubalgebra.coe_bracket_

中文:
引理 _root_.是Sl2Triple.h_eq_coroot
  结论: {α : Weight K H L} (hα : α.IsNonZero)
  证明: by
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift h to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  congr 1
  have key : α h = 2 := by
    have := lie_eq_smul_of_mem_rootSpace heα h
    rw [LieSubalgebra.coe_bracket_

Depends on / 依赖: H.smul_mem, LieSubalgebra, LieSubalgebra.coe_bracket_of_module, Submodule, Submodule.coe_mem, coe_bracket_of_module, coe_mem, coroot, e_ne_zero, ht.e_ne_zero, ht.lie_e_f, ht.lie_h_e_smul, lie_e_f, lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg, lie_eq_smul_of_mem_rootSpace, lie_h_e_smul, replace, root_apply_coroot, smul_left_injective, smul_mem
-/
lemma _root_.IsSl2Triple.h_eq_coroot {α : Weight K H L} (hα : α.IsNonZero)
    {h e f : L} (ht : IsSl2Triple h e f) (heα : e in rootSpace H α) (hfα : f in rootSpace H (-α)) :
    h = coroot α := by
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift h to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  congr 1
  have key : α h = 2 := by
    have := lie_eq_smul_of_mem_rootSpace heα h
    rw [LieSubalgebra.coe_bracket_of_module]; rw [ht.lie_h_e_smul K] at this
    exact smul_left_injective K ht.e_ne_zero this.symm
  suffices exists s : K, s • h = coroot α by
    obtain ⟨s, hs⟩ := this
    replace this : s = 1 := by simpa [root_apply_coroot hα, key] using congr_arg α hs
    rwa [this, one_smul] at hs
  set α' := (cartanEquivDual H).symm α with hα'
  have h_eq : h = killingForm K L e f • α' := by
    simp only [hα', Subtype.ext_iff, ← ht.lie_e_f, hef]
    rw [Submodule.coe_smul_of_tower]
  use (2 • (α α')⁻¹) * (killingForm K L e f)⁻¹
  have hef₀ : killingForm K L e f != 0 := by
    have := ht.h_ne_zero
    contrapose this
    simpa [this] using h_eq
  rw [h_eq]; rw [smul_smul]; rw [mul_assoc]; rw [inv_mul_cancel₀ hef₀]; rw [mul_one]; rw [smul_assoc]; rw [coroot]

/--
lemma `finrank_rootSpace_eq_one` / 引理 `finrank_rootSpace_eq_one`

English:
lemma finrank_rootSpace_eq_one
  given: (α : Weight K H L) (hα : α.IsNonZero)
  proof: by
  suffices ¬ 1 < finrank K (rootSpace H α) by
    have h₀ : finrank K (rootSpace H α) != 0 := by
      convert_to! finrank K (rootSpace H α).toSubmodule != 0
      simpa using! α.genWeightSpace_ne_bot
    lia
  intro contra
  obtain ⟨h, e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZer

中文:
引理 finrank_rootSpace_eq_one
  条件: (α : Weight K H L) (hα : α.IsNonZero)
  证明: by
  suffices ¬ 1 < finrank K (rootSpace H α) by
    have h₀ : finrank K (rootSpace H α) != 0 := by
      convert_to! finrank K (rootSpace H α).toSubmodule != 0
      simpa using! α.genWeightSpace_ne_bot
    lia
  intro contra
  obtain ⟨h, e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZer

Depends on / 依赖: F.ker_ne_bot_of_finrank_lt, LinearMap, LinearMap.ker, Submodule, Submodule.ne_bot_iff, contra, convert_to, exists_isSl2Triple_of_weight_isNonZero, finrank, finrank_self, genWeightSpace_ne_bot, ker_ne_bot_of_finrank_lt, killingForm, ne_bot_iff, rootSpace, subtype, toSubmodule
-/
lemma finrank_rootSpace_eq_one (α : Weight K H L) (hα : α.IsNonZero) :
    finrank K (rootSpace H α) = 1 := by
  suffices ¬ 1 < finrank K (rootSpace H α) by
    have h₀ : finrank K (rootSpace H α) != 0 := by
      convert_to! finrank K (rootSpace H α).toSubmodule != 0
      simpa using! α.genWeightSpace_ne_bot
    lia
  intro contra
  obtain ⟨h, e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  let F : rootSpace H α ->ₗ[K] K := killingForm K L f ∘ₗ (rootSpace H α).subtype
have hF : LinearMap.ker F != ⊥ := F.ker_ne_bot_of_finrank_lt by rwa [finrank_self]
  obtain ⟨⟨y, hyα⟩, hy, hy₀⟩ := (Submodule.ne_bot_iff _).mp hF
  replace hy : ⁅y, f⁆ = 0 := by
    have : killingForm K L y f = 0 := by simpa [F, traceForm_comm] using! hy
    simpa [this] using! lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg hyα hfα
  have P : ht.symm.HasPrimitiveVectorWith y (-2 : K) :=
    { ne_zero := by simpa [LieSubmodule.mk_eq_zero] using! hy₀
      lie_h := by simp only [neg_smul, neg_lie, ht.h_eq_coroot hα heα hfα,
        ← H.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace hyα (coroot α),
        root_apply_coroot hα]
      lie_e := by rw [← lie_skew, hy, neg_zero] }
  obtain ⟨n, hn⟩ := P.exists_nat
  assumption_mod_cast

/--
Definition of `sl2SubalgebraOfRoot` / `sl2SubalgebraOfRoot` 的定义

English:
definition sl2SubalgebraOfRoot
  signature: {α : Weight K H L} (hα : α.IsNonZero)
  body: by
  choose h e f t ht using exists_isSl2Triple_of_weight_isNonZero hα
  exact t.toLieSubalgebra K

中文:
定义 sl2SubalgebraOfRoot
  签名: {α : Weight K H L} (hα : α.IsNonZero)
  定义体: by
  choose h e f t ht using exists_isSl2Triple_of_weight_isNonZero hα
  exact t.toLieSubalgebra K

Depends on / 依赖: exists_isSl2Triple_of_weight_isNonZero, t.toLieSubalgebra, toLieSubalgebra
-/
noncomputable def sl2SubalgebraOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubalgebra K L := by
  choose h e f t ht using exists_isSl2Triple_of_weight_isNonZero hα
  exact t.toLieSubalgebra K

/--
lemma `mem_sl2SubalgebraOfRoot_iff` / 引理 `mem_sl2SubalgebraOfRoot_iff`

English:
lemma mem_sl2SubalgebraOfRoot_iff
  statement: {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
  proof: by
  simp only [sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : exists c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨

中文:
引理 mem_sl2SubalgebraOfRoot_iff
  结论: {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
  证明: by
  simp only [sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : exists c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨

Depends on / 依赖: IsSl2Triple, IsSl2Triple.mem_toLieSubalgebra_iff, choose_spec, e_ne_zero, f_ne_zero, finrank_eq_one_iff_of_nonzero, finrank_rootSpace_eq_one, generalize_proofs, hc.symm, he.choose, he.choose_spec.choose_spec, hf.choose, mem_toLieSubalgebra_iff, sl2SubalgebraOfRoot, t.e_ne_zero, t.f_ne_zero
-/
lemma mem_sl2SubalgebraOfRoot_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
    (t : IsSl2Triple h e f) (hte : e in rootSpace H α) (htf : f in rootSpace H (-α)) {x : L} :
    x in sl2SubalgebraOfRoot hα ↔ exists c₁ c₂ c₃ : K, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp only [sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : exists c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨_, he.choose_spec.choose_spec.2.1⟩
    exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨cf, hcf⟩ : exists c : K, hf.choose = c • f := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, htf⟩ (by simpa using t.f_ne_zero)).mp
      (finrank_rootSpace_eq_one (-α) (by simpa)) ⟨_, hf.choose_spec.2.2⟩
    exact ⟨c, by simpa using hc.symm⟩
  have hce₀ : ce != 0 := by
    rintro rfl
    simp only [zero_smul] at hce
    exact he.choose_spec.choose_spec.1.e_ne_zero hce
  have hcf₀ : cf != 0 := by
    rintro rfl
    simp only [zero_smul] at hcf
    exact he.choose_spec.choose_spec.1.f_ne_zero hcf
  simp_rw [hcf, hce]
  refine ⟨fun ⟨c₁, c₂, c₃, hx⟩ => ⟨c₁ * ce, c₂ * cf, c₃ * cf * ce, ?_⟩,
    fun ⟨c₁, c₂, c₃, hx⟩ => ⟨c₁ * ce⁻¹, c₂ * cf⁻¹, c₃ * ce⁻¹ * cf⁻¹, ?_⟩⟩
  · simp [hx, mul_smul]
  · simp [hx, mul_smul, hce₀, hcf₀]

/--
Definition of `sl2SubmoduleOfRoot` / `sl2SubmoduleOfRoot` 的定义

English:
definition sl2SubmoduleOfRoot
  signature: {α : Weight K H L} (hα : α.IsNonZero)
  body: sl2SubalgebraOfRoot hα
  lie_mem {h} x hx := by
    suffices ⁅(h : L), x⁆ in sl2SubalgebraOfRoot hα by simpa
    obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    replace hx : x in sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_if

中文:
定义 sl2SubmoduleOfRoot
  签名: {α : Weight K H L} (hα : α.IsNonZero)
  定义体: sl2SubalgebraOfRoot hα
  lie_mem {h} x hx := by
    suffices ⁅(h : L), x⁆ in sl2SubalgebraOfRoot hα by simpa
    obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    replace hx : x in sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_if

Depends on / 依赖: sl2SubalgebraOfRoot
-/
noncomputable def sl2SubmoduleOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubmodule K H L where
  __ := sl2SubalgebraOfRoot hα
  lie_mem {h} x hx := by
    suffices ⁅(h : L), x⁆ in sl2SubalgebraOfRoot hα by simpa
    obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    replace hx : x in sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]; rw [lie_add]; rw [lie_add]; rw [lie_smul]; rw [lie_smul]; rw [lie_smul]
    have he_wt : ⁅(h : L), e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    have hf_wt : ⁅(h : L), f⁆ = (-α) h • f := lie_eq_smul_of_mem_rootSpace hfα h
    have hef_zero : ⁅(h : L), ⁅e, f⁆⁆ = 0 := by
      suffices h_coroot_in_zero : ⁅e, f⁆ in rootSpace H (0 : H -> K) from
        lie_eq_smul_of_mem_rootSpace h_coroot_in_zero h ▸ (zero_smul K ⁅e, f⁆)
      rw [ht.lie_e_f]; rw [IsSl2Triple.h_eq_coroot hα ht heα hfα]; rw [rootSpace_zero_eq K L H]
      exact (coroot α).property
    exact ⟨c₁ * α h, c₂ * (-α h), 0, by simp [he_wt, hf_wt, hef_zero, smul_smul]⟩

/--
Definition of `corootSubmodule` / `corootSubmodule` 的定义

English:
abbreviation corootSubmodule
  signature: (α : Weight K H L)
  body: LieSubmodule.map H.toLieSubmodule.incl (corootSpace α)

omit [CharZero K] in

中文:
缩写 corootSubmodule
  签名: (α : Weight K H L)
  定义体: LieSubmodule.map H.toLieSubmodule.incl (corootSpace α)

omit [CharZero K] in

Depends on / 依赖: H.toLieSubmodule.incl, LieSubmodule, LieSubmodule.map, corootSpace, toLieSubmodule
-/
noncomputable abbrev corootSubmodule (α : Weight K H L) : LieSubmodule K H L :=
  LieSubmodule.map H.toLieSubmodule.incl (corootSpace α)

omit [CharZero K] in
/--
lemma `coe_coroot_mem_corootSubmodule` / 引理 `coe_coroot_mem_corootSubmodule`

English:
lemma coe_coroot_mem_corootSubmodule
  given: (α : Weight K H L)
  proof: (LieSubmodule.mem_map _).mpr
    ⟨⟨coroot α, (coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩

中文:
引理 coe_coroot_mem_corootSubmodule
  条件: (α : Weight K H L)
  证明: (LieSubmodule.mem_map _).mpr
    ⟨⟨coroot α, (coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_map, coroot, coroot_mem_corootSpace, mem_map, property
-/
lemma coe_coroot_mem_corootSubmodule (α : Weight K H L) :
    (coroot α : L) in corootSubmodule α :=
  (LieSubmodule.mem_map _).mpr
    ⟨⟨coroot α, (coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
open Submodule in
/--
lemma `sl2SubmoduleOfRoot_eq_sup` / 引理 `sl2SubmoduleOfRoot_eq_sup`

English:
lemma sl2SubmoduleOfRoot_eq_sup
  given: (α : Weight K H L) (hα : α.IsNonZero)
  proof: by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · replace hx : x in sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
·

中文:
引理 sl2SubmoduleOfRoot_eq_sup
  条件: (α : Weight K H L) (hα : α.IsNonZero)
  证明: by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · replace hx : x in sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
·

Depends on / 依赖: H.subtype, Subtype, Subtype.exis, add_mem, corootSpace, exists_isSl2Triple_of_weight_isNonZero, ht.lie_e_f, lie_e_f, mem_sl2SubalgebraOfRoot_iff, mem_sup_left, mem_sup_right, replace, sl2SubalgebraOfRoot, smul_mem, subtype
-/
lemma sl2SubmoduleOfRoot_eq_sup (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα = genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α := by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · replace hx : x in sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
· exact mem_sup_left mem_sup_left smul_mem _ _ heα
· exact mem_sup_left mem_sup_right smul_mem _ _ hfα
    · suffices exists y in corootSpace α, H.subtype y = c₃ • h' from
mem_sup_right by simpa [ht.lie_e_f, -Subtype.exists]
refine ⟨c₃ • coroot α, smul_mem _ _ by simp, ?_⟩
      rw [IsSl2Triple.h_eq_coroot hα ht heα hfα]; rw [map_smul]; rw [subtype_apply]
  · have aux {β : Weight K H L} (hβ : β.IsNonZero) {y g : L}
        (hy : y in genWeightSpace L β) (hg : g in rootSpace H β) (hg_ne_zero : g != 0) :
        exists c : K, y = c • g := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨g, hg⟩
        (by rwa [ne_eq, LieSubmodule.mk_eq_zero])).mp (finrank_rootSpace_eq_one β hβ) ⟨y, hy⟩
      exact ⟨c, by simpa using hc.symm⟩
    obtain ⟨x_αneg, hx_αneg, x_h, ⟨y, hy_coroot, rfl⟩, rfl⟩ := mem_sup.mp hx
    obtain ⟨x_pos, hx_pos, x_neg, hx_neg, rfl⟩ := mem_sup.mp hx_αneg
    obtain ⟨c₁, rfl⟩ := aux hα hx_pos heα ht.e_ne_zero
    obtain ⟨c₂, rfl⟩ := aux (Weight.IsNonZero.neg hα) hx_neg hfα ht.f_ne_zero
    obtain ⟨c₃, rfl⟩ : exists c₃ : K, c₃ • coroot α = y := by
      simpa [← mem_span_singleton, ← coe_corootSpace_eq_span_singleton α]
    change _ in sl2SubalgebraOfRoot hα
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
    use c₁, c₂, c₃
    simp [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, -LieSubmodule.incl_coe]

/--
lemma `sl2SubmoduleOfRoot_ne_bot` / 引理 `sl2SubmoduleOfRoot_ne_bot`

English:
lemma sl2SubmoduleOfRoot_ne_bot
  given: (α : Weight K H L) (hα : α.IsNonZero)
  proof: by
  rw [sl2SubmoduleOfRoot_eq_sup]
  exact ne_bot_of_le_ne_bot α.genWeightSpace_ne_bot (le_sup_of_le_left le_sup_left)

中文:
引理 sl2SubmoduleOfRoot_ne_bot
  条件: (α : Weight K H L) (hα : α.IsNonZero)
  证明: by
  rw [sl2SubmoduleOfRoot_eq_sup]
  exact ne_bot_of_le_ne_bot α.genWeightSpace_ne_bot (le_sup_of_le_left le_sup_left)

Depends on / 依赖: genWeightSpace_ne_bot, le_sup_left, le_sup_of_le_left, ne_bot_of_le_ne_bot, sl2SubmoduleOfRoot_eq_sup
-/
lemma sl2SubmoduleOfRoot_ne_bot (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα != ⊥ := by
  rw [sl2SubmoduleOfRoot_eq_sup]
  exact ne_bot_of_le_ne_bot α.genWeightSpace_ne_bot (le_sup_of_le_left le_sup_left)

/--
Definition of `_root_.LieSubalgebra.root` / `_root_.LieSubalgebra.root` 的定义

English:
abbreviation _root_.LieSubalgebra.root
  signature: : Finset (Weight K H L)
  body: {α | α.IsNonZero}

omit [IsKilling K L] [IsTriangularizable K H L] [CharZero K] in
@[simp]

中文:
缩写 _root_.Lie子代数.root
  签名: : 有限集 (Weight K H L)
  定义体: {α | α.IsNonZero}

omit [IsKilling K L] [IsTriangularizable K H L] [CharZero K] in
@[simp]

Depends on / 依赖: IsNonZero
-/
noncomputable abbrev _root_.LieSubalgebra.root : Finset (Weight K H L) := {α | α.IsNonZero}

omit [IsKilling K L] [IsTriangularizable K H L] [CharZero K] in
@[simp]
/--
lemma `_root_.LieSubalgebra.isNonZero_coe_root` / 引理 `_root_.LieSubalgebra.isNonZero_coe_root`

English:
lemma _root_.LieSubalgebra.isNonZero_coe_root
  given: (α : H.root)
  statement: (α : Weight K H L).IsNonZero
  proof: by
  aesop

中文:
引理 _root_.Lie子代数.isNonZero_coe_root
  条件: (α : H.root)
  结论: (α : Weight K H L).IsNonZero
  证明: by
  aesop

Depends on / 依赖: Module, fast_instance, toModule
-/
lemma _root_.LieSubalgebra.isNonZero_coe_root (α : H.root) : (α : Weight K H L).IsNonZero := by
  aesop

/--
lemma `restrict_killingForm_eq_sum` / 引理 `restrict_killingForm_eq_sum`

English:
lemma restrict_killingForm_eq_sum
  proof: by
  rw [restrict_killingForm]; rw [traceForm_eq_sum_finrank_nsmul' K H L]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  replace hχ : χ.IsNonZero := by simpa [LieSubalgebra.root] using hχ
  simp [finrank_rootSpace_eq_one _ hχ]

中文:
引理 restrict_killingForm_eq_sum
  证明: by
  rw [restrict_killingForm]; rw [traceForm_eq_sum_finrank_nsmul' K H L]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  replace hχ : χ.IsNonZero := by simpa [LieSubalgebra.root] using hχ
  simp [finrank_rootSpace_eq_one _ hχ]

Depends on / 依赖: Finset, Finset.sum_congr, IsNonZero, LieSubalgebra, LieSubalgebra.root, finrank_rootSpace_eq_one, replace, restrict_killingForm, sum_congr, traceForm_eq_sum_finrank_nsmul
-/
lemma restrict_killingForm_eq_sum :
    (killingForm K L).restrict H = ∑ α in H.root, (α : H ->ₗ[K] K).smulRight (α : H ->ₗ[K] K) := by
  rw [restrict_killingForm]; rw [traceForm_eq_sum_finrank_nsmul' K H L]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  replace hχ : χ.IsNonZero := by simpa [LieSubalgebra.root] using hχ
  simp [finrank_rootSpace_eq_one _ hχ]

/--
lemma `lieIdeal_eq_inf_cartan_sup_biSup_rootSpace` / 引理 `lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`

English:
lemma lieIdeal_eq_inf_cartan_sup_biSup_rootSpace
  given: (I : LieIdeal K L)
  proof: by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ hα => hα))
  conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace]
  refine sup_le_sup_left (iSup₂_le fun α hα => ?_) _
  by_cases h : rootSpace H α <= I.restr H
  · exact le_iSup₂_of_le ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_un

中文:
引理 lieIdeal_eq_inf_cartan_sup_biSup_rootSpace
  条件: (I : LieIdeal K L)
  证明: by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ hα => hα))
  conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace]
  refine sup_le_sup_left (iSup₂_le fun α hα => ?_) _
  by_cases h : rootSpace H α <= I.restr H
  · exact le_iSup₂_of_le ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_un

Depends on / 依赖: Finset, Finset.mem_filter.mpr, Finset.mem_univ, I.restr, LieSubmodule, LieSubmodule.toSubmodule_injective, Submodule, Submodule.isAtom_iff_finrank_eq_one.mpr, conv_lhs, finrank_rootSpace_eq_one, ha.not_le_i, inf_le_left, inf_le_right, isAtom_iff_finrank_eq_one, le_antisymm, lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace, mem_filter, mem_univ, not_le_i, rootSpace
-/
lemma lieIdeal_eq_inf_cartan_sup_biSup_rootSpace (I : LieIdeal K L) :
    I.restr H = (I.restr H ⊓ H.toLieSubmodule) ⊔
      ⨆ (α : H.root) (_ : rootSpace H α.val <= I.restr H), rootSpace H α.val := by
  refine le_antisymm ?_ (sup_le inf_le_left (iSup₂_le fun _ hα => hα))
  conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace]
  refine sup_le_sup_left (iSup₂_le fun α hα => ?_) _
  by_cases h : rootSpace H α <= I.restr H
  · exact le_iSup₂_of_le ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩ h inf_le_right
  · have ha := Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_rootSpace_eq_one α hα)
    have : I.restr H ⊓ rootSpace H (α : H -> K) = ⊥ :=
      LieSubmodule.toSubmodule_injective ((ha.not_le_iff_disjoint.mp h).symm.eq_bot)
    simp only [this, bot_le]

end CharZero

end IsKilling

end LieAlgebra
