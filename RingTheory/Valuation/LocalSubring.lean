/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring

-- The copyright notice exceeds the maximum column width, but the `linter.style.header` linter
-- flags the copyright notice if "All rights reserved." is not on the same line as "Copyright".
set_option linter.style.header false

/-!

# Valuation subrings are exactly the maximal local subrings

See `LocalSubring.isMax_iff`.
Note that the order on local subrings is not merely inclusion but domination.

-/

@[expose] public section

open IsLocalRing Algebra

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]

instance (V : ValuationSubring K) : IsIntegrallyClosed V.toSubring := by
  rw [← V.integer_valuation]; infer_instance

instance (V : ValuationSubring K) : IsIntegrallyClosed V :=
  inferInstanceAs (IsIntegrallyClosed V.toSubring)

/--
Definition of `ValuationSubring.toLocalSubring` / `ValuationSubring.toLocalSubring` 的定义

English:
definition ValuationSubring.toLocalSubring
  signature: (A : ValuationSubring K)
  body: A.toSubring
  isLocalRing := A.isLocalRing

中文:
定义 赋值子环.toLocalSubring
  签名: (A : 赋值子环 K)
  定义体: A.toSubring
  isLocalRing := A.isLocalRing

Depends on / 依赖: A.toSubring, toSubring
-/
def ValuationSubring.toLocalSubring (A : ValuationSubring K) : LocalSubring K where
  toSubring := A.toSubring
  isLocalRing := A.isLocalRing

/--
lemma `ValuationSubring.toLocalSubring_injective` / 引理 `ValuationSubring.toLocalSubring_injective`

English:
lemma ValuationSubring.toLocalSubring_injective
  proof: fun _ _ h => ValuationSubring.toSubring_injective congr(($h).toSubring)

中文:
引理 赋值子环.toLocalSubring_injective
  证明: fun _ _ h => ValuationSubring.toSubring_injective congr(($h).toSubring)
-/
lemma ValuationSubring.toLocalSubring_injective :
    Function.Injective (ValuationSubring.toLocalSubring (K := K)) :=
  fun _ _ h => ValuationSubring.toSubring_injective congr(($h).toSubring)

/--
lemma `LocalSubring.map_maximalIdeal_eq_top_of_isMax` / 引理 `LocalSubring.map_maximalIdeal_eq_top_of_isMax`

English:
lemma LocalSubring.map_maximalIdeal_eq_top_of_isMax
  statement: {R : LocalSubring K}
  proof: by
  set mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R <= fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
    refine .trans ?_ (Ideal.map_mono h_incl)
    rw [Ideal.map_map]; rfl
  exact (hR.eq_of_le h_RleSₘ ▸ hS).not_ge (LocalSubring.le_ofPrime ..)

@[stacks 00IC]

中文:
引理 Local子环.map_maximalIdeal_eq_top_of_isMax
  结论: {R : Local子环 K}
  证明: by
  set mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R <= fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
    refine .trans ?_ (Ideal.map_mono h_incl)
    rw [Ideal.map_map]; rfl
  exact (hR.eq_of_le h_RleSₘ ▸ hS).not_ge (LocalSubring.le_ofPrime ..)

@[stacks 00IC]

Depends on / 依赖: AtPrime, Ideal.exists_le_maximal, Ideal.map_map, Ideal.map_mono, IsLocalization, IsLocalization.AtPrime.map_eq_maximalIdeal, LocalSubring, LocalSubring.le_ofPrime, LocalSubring.ofPrime, R.toSubring, Subring, Subring.inclusion, conv_rhs, eq_of_le, exists_le_maximal, hR.eq_of_le, hS.le, hS.le.trans, h_incl, h_is_max
-/
lemma LocalSubring.map_maximalIdeal_eq_top_of_isMax {R : LocalSubring K}
    (hR : IsMax R) {S : Subring K} (hS : R.toSubring < S) :
    (maximalIdeal R.toSubring).map (Subring.inclusion hS.le) = ⊤ := by
  set mR := (maximalIdeal R.toSubring).map (Subring.inclusion hS.le)
  by_contra h_is_not_top
  obtain ⟨M, h_is_max, h_incl⟩ := Ideal.exists_le_maximal _ h_is_not_top
  let fSₘ : LocalSubring K := LocalSubring.ofPrime S M
  have h_RleSₘ : R <= fSₘ := by
    refine ⟨hS.le.trans (LocalSubring.le_ofPrime ..), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]
    refine .trans ?_ (Ideal.map_mono h_incl)
    rw [Ideal.map_map]; rfl
  exact (hR.eq_of_le h_RleSₘ ▸ hS).not_ge (LocalSubring.le_ofPrime ..)

@[stacks 00IC]
-- the conclusion could be `IsIntegrallyClosedIn R.toSubring K`, which has slightly worse defeq.
/--
lemma `LocalSubring.mem_of_isMax_of_isIntegral` / 引理 `LocalSubring.mem_of_isMax_of_isIntegral`

English:
lemma LocalSubring.mem_of_isMax_of_isIntegral
  statement: {R : LocalSubring K}
  proof: by
  let S := R.toSubring[x]
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := S) (maximalIdeal R.toSubring) (le_maximalIdeal (by simp))
  have : R = .ofPrime S.toSubring Q := by
    have hRS : R.toSubring <= S.toSubring := fun r hr => algebraMap_mem S ⟨r, hr⟩
    refine hR.eq_of_le ⟨hRS.trans (LocalSubring.le_ofPrime _ _), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
    refine .trans ?_ (Ideal.map_mono <| Ideal.map_le_iff_le_comap.mpr e.ge)
    rw [Ideal.map_map]; rfl
  rw [this]
  exact LocalSubring.le_ofPrime _ _ (self_mem_adjoin_singleton _ _)

@[stacks 052K]

中文:
引理 Local子环.mem_of_isMax_of_is整数egral
  结论: {R : Local子环 K}
  证明: by
  let S := R.toSubring[x]
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := S) (maximalIdeal R.toSubring) (le_maximalIdeal (by simp))
  have : R = .ofPrime S.toSubring Q := by
    have hRS : R.toSubring <= S.toSubring := fun r hr => algebraMap_mem S ⟨r, hr⟩
    refine hR.eq_of_le ⟨hRS.trans (LocalSubring.le_ofPrime _ _), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
    refine .trans ?_ (Ideal.map_mono <| Ideal.map_le_iff_le_comap.mpr e.ge)
    rw [Ideal.map_map]; rfl
  rw [this]
  exact LocalSubring.le_ofPrime _ _ (self_mem_adjoin_singleton _ _)

@[stacks 052K]

Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.IsIntegral.adjoin, Ideal.exists_ideal_over_maximal_of_isIntegral, IsIntegral, IsLocaliz, LocalSubring, LocalSubring.le_ofPrime, R.toSubring, S.toSubring, adjoin, algebraMap_mem, conv_rhs, eq_of_le, exists_ideal_over_maximal_of_isIntegral, hR.eq_of_le, hRS.trans, le_maximalIdeal, le_ofPrime, local_hom_TFAE
-/
lemma LocalSubring.mem_of_isMax_of_isIntegral {R : LocalSubring K}
    (hR : IsMax R) {x : K} (hx : IsIntegral R.toSubring x) : x in R.toSubring := by
  let S := R.toSubring[x]
  have : Algebra.IsIntegral R.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
  obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := S) (maximalIdeal R.toSubring) (le_maximalIdeal (by simp))
  have : R = .ofPrime S.toSubring Q := by
    have hRS : R.toSubring <= S.toSubring := fun r hr => algebraMap_mem S ⟨r, hr⟩
    refine hR.eq_of_le ⟨hRS.trans (LocalSubring.le_ofPrime _ _), ((local_hom_TFAE _).out 2 0).mp ?_⟩
    conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
    refine .trans ?_ (Ideal.map_mono <| Ideal.map_le_iff_le_comap.mpr e.ge)
    rw [Ideal.map_map]; rfl
  rw [this]
  exact LocalSubring.le_ofPrime _ _ (self_mem_adjoin_singleton _ _)

@[stacks 052K]
/--
lemma `ValuationSubring.isMax_toLocalSubring` / 引理 `ValuationSubring.isMax_toLocalSubring`

English:
lemma ValuationSubring.isMax_toLocalSubring
  given: (R : ValuationSubring K)
  proof: by
  intro S hS
  refine (LocalSubring.toSubring_injective (hS.1.antisymm fun x hx => (R.2 x).elim id fun h => ?_)).ge
  by_contra h'
  have hx0 : x != 0 := by rintro rfl; exact h' R.zero_mem
  have : IsUnit (Subring.inclusion hS.1 ⟨x⁻¹, h⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨x', hx'⟩ := isUnit_iff_exists_inv.mp (hS.2.1 _ this)
  have : x' = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hx'
  exact h' (this ▸ x'.2)

中文:
引理 赋值子环.isMax_toLocalSubring
  条件: (R : 赋值子环 K)
  证明: by
  intro S hS
  refine (LocalSubring.toSubring_injective (hS.1.antisymm fun x hx => (R.2 x).elim id fun h => ?_)).ge
  by_contra h'
  have hx0 : x != 0 := by rintro rfl; exact h' R.zero_mem
  have : IsUnit (Subring.inclusion hS.1 ⟨x⁻¹, h⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨x', hx'⟩ := isUnit_iff_exists_inv.mp (hS.2.1 _ this)
  have : x' = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hx'
  exact h' (this ▸ x'.2)

Depends on / 依赖: IsUnit, LocalSubring, LocalSubring.toSubring_injective, R.zero_mem, Subring, Subring.inclusion, Subtype, Subtype.ext, Subtype.ext_iff, antisymm, ext_iff, inclusion, isUnit_iff_exists_inv, isUnit_iff_exists_inv.mp, isUnit_iff_exists_inv.mpr, toSubring_injective, zero_mem
-/
lemma ValuationSubring.isMax_toLocalSubring (R : ValuationSubring K) :
    IsMax R.toLocalSubring := by
  intro S hS
  refine (LocalSubring.toSubring_injective (hS.1.antisymm fun x hx => (R.2 x).elim id fun h => ?_)).ge
  by_contra h'
  have hx0 : x != 0 := by rintro rfl; exact h' R.zero_mem
  have : IsUnit (Subring.inclusion hS.1 ⟨x⁻¹, h⟩) :=
    isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨x', hx'⟩ := isUnit_iff_exists_inv.mp (hS.2.1 _ this)
  have : x' = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hx'
  exact h' (this ▸ x'.2)

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 00IB]
/--
lemma `LocalSubring.exists_valuationRing_of_isMax` / 引理 `LocalSubring.exists_valuationRing_of_isMax`

English:
lemma LocalSubring.exists_valuationRing_of_isMax
  given: {R : LocalSubring K} (hR : IsMax R)
  proof: by
  suffices forall x ∉ R.toSubring, x⁻¹ in R.toSubring from
    ⟨⟨R.toSubring, fun x => or_iff_not_imp_left.mpr (this x)⟩, rfl⟩
  refine fun x hx => mem_of_isMax_of_isIntegral hR ?_
  have hx0 : x != 0 := fun e => hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  let S := R.toSubring[x]
  have : R.toSubring < S.toSubring := SetLike.lt_iff_le_and_exists.mpr
    ⟨fun r hr => algebraMap_mem S ⟨r, hr⟩, ⟨x, self_mem_adjoin_singleton _ _, hx⟩⟩
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal R.toSubring).ne_top
    (top_unique <| (map_maximalIdeal_eq_top_of_isMax hR this).ge.trans le_self_add)
  have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

中文:
引理 Local子环.存在_valuationRing_of_isMax
  条件: {R : Local子环 K} (hR : IsMax R)
  证明: by
  suffices forall x ∉ R.toSubring, x⁻¹ in R.toSubring from
    ⟨⟨R.toSubring, fun x => or_iff_not_imp_left.mpr (this x)⟩, rfl⟩
  refine fun x hx => mem_of_isMax_of_isIntegral hR ?_
  have hx0 : x != 0 := fun e => hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  let S := R.toSubring[x]
  have : R.toSubring < S.toSubring := SetLike.lt_iff_le_and_exists.mpr
    ⟨fun r hr => algebraMap_mem S ⟨r, hr⟩, ⟨x, self_mem_adjoin_singleton _ _, hx⟩⟩
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal R.toSubring).ne_top
    (top_unique <| (map_maximalIdeal_eq_top_of_isMax hR this).ge.trans le_self_add)
  have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

Depends on / 依赖: R.toSubring, S.toSubring, SetLike, SetLike.lt_iff_le_and_exists.mpr, algebraMap_mem, exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_, invertibleOfNonzero, lt_iff_le_and_exists, mem_of_isMax_of_isIntegral, or_iff_not_imp_left, or_iff_not_imp_left.mpr, self_mem_adjoin_singleton, toSubring, zero_mem
-/
lemma LocalSubring.exists_valuationRing_of_isMax {R : LocalSubring K} (hR : IsMax R) :
    exists R' : ValuationSubring K, R'.toLocalSubring = R := by
  suffices forall x ∉ R.toSubring, x⁻¹ in R.toSubring from
    ⟨⟨R.toSubring, fun x => or_iff_not_imp_left.mpr (this x)⟩, rfl⟩
  refine fun x hx => mem_of_isMax_of_isIntegral hR ?_
  have hx0 : x != 0 := fun e => hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  let S := R.toSubring[x]
  have : R.toSubring < S.toSubring := SetLike.lt_iff_le_and_exists.mpr
    ⟨fun r hr => algebraMap_mem S ⟨r, hr⟩, ⟨x, self_mem_adjoin_singleton _ _, hx⟩⟩
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal R.toSubring).ne_top
    (top_unique <| (map_maximalIdeal_eq_top_of_isMax hR this).ge.trans le_self_add)
  have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

/--
lemma `LocalSubring.isMax_iff` / 引理 `LocalSubring.isMax_iff`

English:
lemma LocalSubring.isMax_iff
  given: {A : LocalSubring K}
  proof: ⟨exists_valuationRing_of_isMax, fun ⟨B, e⟩ => e ▸ B.isMax_toLocalSubring⟩

@[stacks 00IA]

中文:
引理 Local子环.isMax_iff
  条件: {A : Local子环 K}
  证明: ⟨exists_valuationRing_of_isMax, fun ⟨B, e⟩ => e ▸ B.isMax_toLocalSubring⟩

@[stacks 00IA]

Depends on / 依赖: B.isMax_toLocalSubring, exists_valuationRing_of_isMax, isMax_toLocalSubring
-/
lemma LocalSubring.isMax_iff {A : LocalSubring K} :
    IsMax A ↔ exists B : ValuationSubring K, B.toLocalSubring = A :=
  ⟨exists_valuationRing_of_isMax, fun ⟨B, e⟩ => e ▸ B.isMax_toLocalSubring⟩

@[stacks 00IA]
/--
lemma `LocalSubring.exists_le_valuationSubring` / 引理 `LocalSubring.exists_le_valuationSubring`

English:
lemma LocalSubring.exists_le_valuationSubring
  given: (A : LocalSubring K)
  proof: by
  suffices exists B, A <= B ∧ IsMax B by
    obtain ⟨B, hB, hB'⟩ := this
    obtain ⟨B, rfl⟩ := B.exists_valuationRing_of_isMax hB'
    exact ⟨B, hB⟩
  refine zorn_le_nonempty_Ici₀ _ ?_ _ le_rfl
  intro s hs H y hys
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a in A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b in B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h => h.map (Subring.inclusion (le_iSup (fun i : s => i.1.toSubring) C))
    · exact fun h => h.map (Subring.inclusion (le_iSup (fun i : s => i.1.toSubring) C))
  · intro A hA
    refine ⟨le_iSup (fun i : s => i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b in B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

中文:
引理 Local子环.存在_le_valuationSubring
  条件: (A : Local子环 K)
  证明: by
  suffices exists B, A <= B ∧ IsMax B by
    obtain ⟨B, hB, hB'⟩ := this
    obtain ⟨B, rfl⟩ := B.exists_valuationRing_of_isMax hB'
    exact ⟨B, hB⟩
  refine zorn_le_nonempty_Ici₀ _ ?_ _ le_rfl
  intro s hs H y hys
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a in A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b in B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h => h.map (Subring.inclusion (le_iSup (fun i : s => i.1.toSubring) C))
    · exact fun h => h.map (Subring.inclusion (le_iSup (fun i : s => i.1.toSubring) C))
  · intro A hA
    refine ⟨le_iSup (fun i : s => i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b in B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

Depends on / 依赖: B.exists_valuationRing_of_isMax, H.directed.mono_comp, LocalSubring, LocalSubring.mk, LocalSubring.toSubring_mono, Nonempty, Subring, Subring.mem_iSup_of_directed, directed, exists_valuationRing_of_isMax, le_rfl, mem_iSup_of_directed, mono_comp, toSubring, toSubring_mono
-/
lemma LocalSubring.exists_le_valuationSubring (A : LocalSubring K) :
    exists B : ValuationSubring K, A <= B.toLocalSubring := by
  suffices exists B, A <= B ∧ IsMax B by
    obtain ⟨B, hB, hB'⟩ := this
    obtain ⟨B, rfl⟩ := B.exists_valuationRing_of_isMax hB'
    exact ⟨B, hB⟩
  refine zorn_le_nonempty_Ici₀ _ ?_ _ le_rfl
  intro s hs H y hys
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a in A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b in B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h => h.map (Subring.inclusion (le_iSup (fun i : s => i.1.toSubring) C))
    · exact fun h => h.map (Subring.inclusion (le_iSup (fun i : s => i.1.toSubring) C))
  · intro A hA
    refine ⟨le_iSup (fun i : s => i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b in B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

/--
lemma `Ideal.image_subset_nonunits_valuationSubring` / 引理 `Ideal.image_subset_nonunits_valuationSubring`

English:
lemma Ideal.image_subset_nonunits_valuationSubring
  given: {A : Subring K} (I : Ideal A) (hI : I != ⊤)
  proof: by
  have ⟨M, hM, le⟩ := I.exists_le_maximal hI
  have ⟨V, hV⟩ := (LocalSubring.ofPrime A M).exists_le_valuationSubring
  refine ⟨V, (LocalSubring.le_ofPrime ..).trans hV.1, ?_⟩
  rw [← V.image_maximalIdeal]
  refine .trans ?_ (Set.image_mono <| ((local_hom_TFAE _).out 0 2).mp hV.2)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]; rw [map_map]
  refine .trans ?_ (Set.image_mono <| map_mono le)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨_, mem_map_of_mem _ ha, rfl⟩

中文:
引理 理想.image_subset_nonunits_valuationSubring
  条件: {A : 子环 K} (I : 理想 A) (hI : I != ⊤)
  证明: by
  have ⟨M, hM, le⟩ := I.exists_le_maximal hI
  have ⟨V, hV⟩ := (LocalSubring.ofPrime A M).exists_le_valuationSubring
  refine ⟨V, (LocalSubring.le_ofPrime ..).trans hV.1, ?_⟩
  rw [← V.image_maximalIdeal]
  refine .trans ?_ (Set.image_mono <| ((local_hom_TFAE _).out 0 2).mp hV.2)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]; rw [map_map]
  refine .trans ?_ (Set.image_mono <| map_mono le)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨_, mem_map_of_mem _ ha, rfl⟩

Depends on / 依赖: AtPrime, I.exists_le_maximal, IsLocalization, IsLocalization.AtPrime.map_eq_maximalIdeal, LocalSubring, LocalSubring.le_ofPrime, LocalSubring.ofPrime, Set.image_mono, V.image_maximalIdeal, exists_le_maximal, exists_le_valuationSubring, image_maximalIdeal, image_mono, le_ofPrime, local_hom_TFAE, map_eq_maximalIdeal, map_map, map_mono, mem_map_of_mem, ofPrime
-/
lemma Ideal.image_subset_nonunits_valuationSubring {A : Subring K} (I : Ideal A) (hI : I != ⊤) :
    exists B : ValuationSubring K, A <= B.toSubring ∧ A.subtype '' I subseteq B.nonunits := by
  have ⟨M, hM, le⟩ := I.exists_le_maximal hI
  have ⟨V, hV⟩ := (LocalSubring.ofPrime A M).exists_le_valuationSubring
  refine ⟨V, (LocalSubring.le_ofPrime ..).trans hV.1, ?_⟩
  rw [← V.image_maximalIdeal]
  refine .trans ?_ (Set.image_mono <| ((local_hom_TFAE _).out 0 2).mp hV.2)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M]; rw [map_map]
  refine .trans ?_ (Set.image_mono <| map_mono le)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨_, mem_map_of_mem _ ha, rfl⟩

open Polynomial Algebra in
/--
lemma `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` / 引理 `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`

English:
lemma Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
  proof: by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
have : Ideal.span {xinv} != ⊤ := fun eq => hxR
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _
      (⊥ : Ideal R) bot_ne_top (top_unique <| eq.ge.trans le_add_self)
    (Subring.isIntegrallyClosedIn_iff).mp ‹_› ⟨p, by simpa [Monic, sub_eq_zero] using hp, hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ this
  exact ⟨V, fun r hr => hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    (V.inv_mem_nonunits_iff.mp <| hV.2 ⟨_, Ideal.subset_span rfl, rfl⟩).resolve_left hx0⟩

中文:
引理 子环.存在_le_valuationSubring_of_is整数egrallyClosedIn
  证明: by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
have : Ideal.span {xinv} != ⊤ := fun eq => hxR
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _
      (⊥ : Ideal R) bot_ne_top (top_unique <| eq.ge.trans le_add_self)
    (Subring.isIntegrallyClosedIn_iff).mp ‹_› ⟨p, by simpa [Monic, sub_eq_zero] using hp, hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ this
  exact ⟨V, fun r hr => hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    (V.inv_mem_nonunits_iff.mp <| hV.2 ⟨_, Ideal.subset_span rfl, rfl⟩).resolve_left hx0⟩
-/
@[stacks 090P "part (1)"] lemma Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    {x : K} {R : Subring K} (hxR : x ∉ R) [IsIntegrallyClosedIn R K] :
    exists V : ValuationSubring K, R <= V.toSubring ∧ x ∉ V := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
have : Ideal.span {xinv} != ⊤ := fun eq => hxR
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _
      (⊥ : Ideal R) bot_ne_top (top_unique <| eq.ge.trans le_add_self)
    (Subring.isIntegrallyClosedIn_iff).mp ‹_› ⟨p, by simpa [Monic, sub_eq_zero] using hp, hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ this
  exact ⟨V, fun r hr => hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    (V.inv_mem_nonunits_iff.mp <| hV.2 ⟨_, Ideal.subset_span rfl, rfl⟩).resolve_left hx0⟩

set_option backward.isDefEq.respectTransparency.types false in
open Polynomial Algebra in
/--
lemma `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn` / 引理 `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn`

English:
lemma LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
  proof: by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.toSubring.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R.toSubring[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
have : (maximalIdeal R.toSubring).map (algebraMap _ B) + .span {xinv} != ⊤ := fun eq => hxR
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _ _
      (maximalIdeal.isMaximal R.toSubring).ne_top eq
    have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
    (Subring.isIntegrallyClosedIn_iff).mp ‹_›
      ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ this
  refine ⟨V, ⟨fun r hr => hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    ((local_hom_TFAE _).out 3 0).mp fun r hr => ?_⟩, (V.inv_mem_nonunits_iff.mp <|
      hV.2 ⟨_, le_add_self (α := Ideal B) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0⟩
  rw [← V.image_maximalIdeal] at hV
  obtain ⟨⟨r, _⟩, hr, rfl⟩ := hV.2 ⟨_, le_self_add (α := Ideal B) (Ideal.mem_map_of_mem _ hr), rfl⟩
  exact hr

中文:
引理 Local子环.存在_le_valuationSubring_of_is整数egrallyClosedIn
  证明: by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.toSubring.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R.toSubring[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
have : (maximalIdeal R.toSubring).map (algebraMap _ B) + .span {xinv} != ⊤ := fun eq => hxR
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _ _
      (maximalIdeal.isMaximal R.toSubring).ne_top eq
    have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
    (Subring.isIntegrallyClosedIn_iff).mp ‹_›
      ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ this
  refine ⟨V, ⟨fun r hr => hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    ((local_hom_TFAE _).out 3 0).mp fun r hr => ?_⟩, (V.inv_mem_nonunits_iff.mp <|
      hV.2 ⟨_, le_add_self (α := Ideal B) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0⟩
  rw [← V.image_maximalIdeal] at hV
  obtain ⟨⟨r, _⟩, hr, rfl⟩ := hV.2 ⟨_, le_self_add (α := Ideal B) (Ideal.mem_map_of_mem _ hr), rfl⟩
  exact hr
-/
@[stacks 090P "part (2)"] lemma LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    {x : K} {R : LocalSubring K} (hxR : x ∉ R.toSubring) [IsIntegrallyClosedIn R.toSubring K] :
    exists V : ValuationSubring K, R <= V.toLocalSubring ∧ x ∉ V := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact (hxR R.toSubring.zero_mem).elim
  let := invertibleOfNonzero hx0
  let B := R.toSubring[x⁻¹]
  let xinv : B.toSubring := ⟨x⁻¹, subset_adjoin rfl⟩
have : (maximalIdeal R.toSubring).map (algebraMap _ B) + .span {xinv} != ⊤ := fun eq => hxR
    have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top _ _
      (maximalIdeal.isMaximal R.toSubring).ne_top eq
    have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
    (Subring.isIntegrallyClosedIn_iff).mp ‹_›
      ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩
  have ⟨V, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ this
  refine ⟨V, ⟨fun r hr => hV.1 (B.algebraMap_mem ⟨r, hr⟩),
    ((local_hom_TFAE _).out 3 0).mp fun r hr => ?_⟩, (V.inv_mem_nonunits_iff.mp <|
      hV.2 ⟨_, le_add_self (α := Ideal B) (Ideal.subset_span rfl), rfl⟩).resolve_left hx0⟩
  rw [← V.image_maximalIdeal] at hV
  obtain ⟨⟨r, _⟩, hr, rfl⟩ := hV.2 ⟨_, le_self_add (α := Ideal B) (Ideal.mem_map_of_mem _ hr), rfl⟩
  exact hr

/--
lemma `Subring.eq_iInf_of_isIntegrallyClosedIn` / 引理 `Subring.eq_iInf_of_isIntegrallyClosedIn`

English:
lemma Subring.eq_iInf_of_isIntegrallyClosedIn
  given: {R : Subring K} [IsIntegrallyClosedIn R K]
  proof: le_antisymm (le_iInf fun V => V.2) fun _ h => of_not_not fun hxR =>
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

中文:
引理 子环.eq_iInf_of_is整数egrallyClosedIn
  条件: {R : 子环 K} [Is整数egrallyClosedIn R K]
  证明: le_antisymm (le_iInf fun V => V.2) fun _ h => of_not_not fun hxR =>
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

Depends on / 依赖: R.exists_le_valuationSubring_of_isIntegrallyClosedIn, Subring, exists_le_valuationSubring_of_isIntegrallyClosedIn, iInf_le_of_le, le_antisymm, le_iInf, le_rfl, of_not_not
-/
lemma Subring.eq_iInf_of_isIntegrallyClosedIn {R : Subring K} [IsIntegrallyClosedIn R K] :
    R = ⨅ V : {V : ValuationSubring K // R <= V.toSubring}, V.1.toSubring :=
  le_antisymm (le_iInf fun V => V.2) fun _ h => of_not_not fun hxR =>
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

/--
lemma `LocalSubring.eq_iInf_of_isIntegrallyClosedIn` / 引理 `LocalSubring.eq_iInf_of_isIntegrallyClosedIn`

English:
lemma LocalSubring.eq_iInf_of_isIntegrallyClosedIn
  statement: {R : LocalSubring K}
  proof: le_antisymm (le_iInf fun V => V.2.1) fun _ h => of_not_not fun hxR =>
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

中文:
引理 Local子环.eq_iInf_of_is整数egrallyClosedIn
  结论: {R : Local子环 K}
  证明: le_antisymm (le_iInf fun V => V.2.1) fun _ h => of_not_not fun hxR =>
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

Depends on / 依赖: R.exists_le_valuationSubring_of_isIntegrallyClosedIn, Subring, exists_le_valuationSubring_of_isIntegrallyClosedIn, iInf_le_of_le, le_antisymm, le_iInf, le_rfl, of_not_not
-/
lemma LocalSubring.eq_iInf_of_isIntegrallyClosedIn {R : LocalSubring K}
    [IsIntegrallyClosedIn R.toSubring K] :
    R.toSubring = ⨅ V : {V : ValuationSubring K // R <= V.toLocalSubring}, V.1.toSubring :=
  le_antisymm (le_iInf fun V => V.2.1) fun _ h => of_not_not fun hxR =>
    have ⟨V, hV⟩ := R.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
    hV.2 (iInf_le_of_le (α := Subring K) ⟨V, hV.1⟩ le_rfl h)

/--
lemma `iInf_valuationSubring_superset` / 引理 `iInf_valuationSubring_superset`

English:
lemma iInf_valuationSubring_superset
  given: {s : Set K}
  proof: by
  refine .trans ?_ Subring.eq_iInf_of_isIntegrallyClosedIn.symm
  simp_rw [iInf_subtype]
  congr! with V
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  rw [Subring.integralClosure_subring_le_iff]
  exact Subring.closure_le.symm

中文:
引理 iInf_valuationSubring_superset
  条件: {s : 集合 K}
  证明: by
  refine .trans ?_ Subring.eq_iInf_of_isIntegrallyClosedIn.symm
  simp_rw [iInf_subtype]
  congr! with V
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  rw [Subring.integralClosure_subring_le_iff]
  exact Subring.closure_le.symm

Depends on / 依赖: IsIntegrallyClosedIn, Subring, Subring.closure_le.symm, Subring.eq_iInf_of_isIntegrallyClosedIn.symm, Subring.integralClosure_subring_le_iff, V.toSubring, closure_le, eq_iInf_of_isIntegrallyClosedIn, iInf_subtype, integralClosure_subring_le_iff, simp_rw, toSubring
-/
lemma iInf_valuationSubring_superset {s : Set K} :
    (⨅ V : {V : ValuationSubring K // s subseteq V.toSubring}, V.1.toSubring) =
    (integralClosure (Subring.closure s) K).toSubring := by
  refine .trans ?_ Subring.eq_iInf_of_isIntegrallyClosedIn.symm
  simp_rw [iInf_subtype]
  congr! with V
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  rw [Subring.integralClosure_subring_le_iff]
  exact Subring.closure_le.symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `bijective_rangeRestrict_comp_of_valuationRing` / 引理 `bijective_rangeRestrict_comp_of_valuationRing`

English:
lemma bijective_rangeRestrict_comp_of_valuationRing
  statement: [IsDomain R] [ValuationRing R]
  proof: by
  refine ⟨?_, ?_⟩
  · exact .of_comp (f := Subtype.val) (by convert! (IsFractionRing.injective R K); rw [← h]; rfl)
  · let V : ValuationSubring K :=
      ⟨(algebraMap R K).range, ValuationRing.isInteger_or_isInteger R⟩
    suffices LocalSubring.range g <= V.toLocalSubring by
      rintro ⟨_, x, rfl⟩
      obtain ⟨y, hy⟩ := this.1 ⟨x, rfl⟩
      exact ⟨y, Subtype.ext (by simpa [← h] using hy)⟩
    apply V.isMax_toLocalSubring
    have H : (algebraMap R K).range <= g.range := fun x ⟨a, ha⟩ => ⟨f a, by simp [← ha, ← h]⟩
    refine ⟨H, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ (ha : IsUnit (M := g.range) ⟨algebraMap R K a, _⟩)
    suffices IsUnit a from this.map (algebraMap R K).rangeRestrict
    apply IsUnit.of_map f
    apply (IsLocalHom.of_surjective g.rangeRestrict g.rangeRestrict_surjective).1
    convert! ha
    simp [← h]

中文:
引理 bijective_rangeRestrict_comp_of_valuationRing
  结论: [是整环 R] [赋值环 R]
  证明: by
  refine ⟨?_, ?_⟩
  · exact .of_comp (f := Subtype.val) (by convert! (IsFractionRing.injective R K); rw [← h]; rfl)
  · let V : ValuationSubring K :=
      ⟨(algebraMap R K).range, ValuationRing.isInteger_or_isInteger R⟩
    suffices LocalSubring.range g <= V.toLocalSubring by
      rintro ⟨_, x, rfl⟩
      obtain ⟨y, hy⟩ := this.1 ⟨x, rfl⟩
      exact ⟨y, Subtype.ext (by simpa [← h] using hy)⟩
    apply V.isMax_toLocalSubring
    have H : (algebraMap R K).range <= g.range := fun x ⟨a, ha⟩ => ⟨f a, by simp [← ha, ← h]⟩
    refine ⟨H, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ (ha : IsUnit (M := g.range) ⟨algebraMap R K a, _⟩)
    suffices IsUnit a from this.map (algebraMap R K).rangeRestrict
    apply IsUnit.of_map f
    apply (IsLocalHom.of_surjective g.rangeRestrict g.rangeRestrict_surjective).1
    convert! ha
    simp [← h]

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, LocalSubring, LocalSubring.range, Subtype, Subtype.ext, Subtype.val, V.isMax_toLocalSubring, V.toLocalSubring, ValuationRing, ValuationRing.isInteger_or_isInteger, ValuationSubring, algebraMap, convert, g.range, injective, isInteger_or_isInteger, isMax_toLocalSubring, of_comp, toLocalSubring
-/
lemma bijective_rangeRestrict_comp_of_valuationRing [IsDomain R] [ValuationRing R]
    [IsLocalRing S] [Algebra R K] [IsFractionRing R K]
    (f : R ->+* S) (g : S ->+* K) (h : g.comp f = algebraMap R K) [IsLocalHom f] :
    Function.Bijective (g.rangeRestrict.comp f) := by
  refine ⟨?_, ?_⟩
  · exact .of_comp (f := Subtype.val) (by convert! (IsFractionRing.injective R K); rw [← h]; rfl)
  · let V : ValuationSubring K :=
      ⟨(algebraMap R K).range, ValuationRing.isInteger_or_isInteger R⟩
    suffices LocalSubring.range g <= V.toLocalSubring by
      rintro ⟨_, x, rfl⟩
      obtain ⟨y, hy⟩ := this.1 ⟨x, rfl⟩
      exact ⟨y, Subtype.ext (by simpa [← h] using hy)⟩
    apply V.isMax_toLocalSubring
    have H : (algebraMap R K).range <= g.range := fun x ⟨a, ha⟩ => ⟨f a, by simp [← ha, ← h]⟩
    refine ⟨H, ⟨?_⟩⟩
    rintro ⟨_, a, rfl⟩ (ha : IsUnit (M := g.range) ⟨algebraMap R K a, _⟩)
    suffices IsUnit a from this.map (algebraMap R K).rangeRestrict
    apply IsUnit.of_map f
    apply (IsLocalHom.of_surjective g.rangeRestrict g.rangeRestrict_surjective).1
    convert! ha
    simp [← h]

/--
lemma `IsLocalRing.exists_factor_valuationRing` / 引理 `IsLocalRing.exists_factor_valuationRing`

English:
lemma IsLocalRing.exists_factor_valuationRing
  given: [IsLocalRing R] (f : R ->+* K)
  proof: by
  obtain ⟨B, hB⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨B, fun x => hB.1 ⟨x, rfl⟩, ?_⟩
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hB.2 (.of_surjective _ f.rangeRestrict_surjective)

中文:
引理 是局部环.存在_factor_valuationRing
  条件: [是局部环 R] (f : R ->+* K)
  证明: by
  obtain ⟨B, hB⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨B, fun x => hB.1 ⟨x, rfl⟩, ?_⟩
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hB.2 (.of_surjective _ f.rangeRestrict_surjective)

Depends on / 依赖: LocalSubring, LocalSubring.range, RingHom, RingHom.isLocalHom_comp, exists_le_valuationSubring, f.rangeRestrict_surjective, isLocalHom_comp, of_surjective, rangeRestrict_surjective
-/
lemma IsLocalRing.exists_factor_valuationRing [IsLocalRing R] (f : R ->+* K) :
    exists (A : ValuationSubring K) (h : _), IsLocalHom (f.codRestrict A.toSubring h) := by
  obtain ⟨B, hB⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨B, fun x => hB.1 ⟨x, rfl⟩, ?_⟩
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ hB.2 (.of_surjective _ f.rangeRestrict_surjective)
