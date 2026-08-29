/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!

# Compact Hausdorff Rings

## Main results
- `IsArtinianRing.finite_of_compactSpace_of_t2Space`:
  Compact Hausdorff Artinian rings are finite (and thus discrete).
- `Ideal.isOpen_of_isMaximal`:
  Maximal ideals are open in compact Hausdorff Noetherian rings.
- `IsLocalRing.isOpen_iff_finite_quotient`:
  An ideal in a compact Hausdorff Noetherian local ring is open iff it has finite index.
- `IsDedekindDomain.isOpen_iff`:
  An ideal in a compact Hausdorff Dedekind domain (that is not a field) is open iff it is non-zero.

## Future projects
Show that compact Hausdorff rings are totally disconnected and linearly topologized.
See https://ncatlab.org/nlab/show/compact+Hausdorff+rings+are+profinite

-/

public section

attribute [local instance] Ideal.Quotient.field Fintype.ofFinite finite_of_compact_of_discrete
  DivisionRing.finite_of_compactSpace_of_t2Space

variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R] [CompactSpace R] [T2Space R]

namespace IsArtinianRing

/--
theorem `finite_of_compactSpace_of_t2Space` / 定理 `finite_of_compactSpace_of_t2Space`

English:
theorem finite_of_compactSpace_of_t2Space
  given: [IsArtinianRing R]
  proof: by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff]; rw [← Ideal.zero_eq_bot]; rw [← hn]
    gcongr
    rw [Ideal.jacobson_bot]; rw [Ring.jacobson_eq_sInf_isMaximal]; rw [le_sInf_iff]
    exact fun I hI => Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ => IsNoetherian.noetherian _) (fun _ _ => inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

中文:
定理 finite_of_compactSpace_of_t2Space
  条件: [是Artin环 R]
  证明: by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff]; rw [← Ideal.zero_eq_bot]; rw [← hn]
    gcongr
    rw [Ideal.jacobson_bot]; rw [Ring.jacobson_eq_sInf_isMaximal]; rw [le_sInf_iff]
    exact fun I hI => Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ => IsNoetherian.noetherian _) (fun _ _ => inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

Depends on / 依赖: Finset, Finset.inf_le, Finset.univ, Ideal.finite_quotient_prod, Ideal.jacobson_bot, Ideal.prod_le_inf.trans, Ideal.zero_eq_bot, IsArtinianRing, IsArtinianRing.isNilpotent_jacobson_bot, IsNoetherian, IsNoetherian.noetherian, PrimeSpectrum, PrimeSpectrum.asIdeal, PrimeSpectrum.mk, Ring.jacobson_eq_sInf_isMaximal, asIdeal, finite_quotient_prod, hI.isPrime, inf_le, isNilpotent_jacobson_bot
-/
theorem finite_of_compactSpace_of_t2Space [IsArtinianRing R] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff]; rw [← Ideal.zero_eq_bot]; rw [← hn]
    gcongr
    rw [Ideal.jacobson_bot]; rw [Ring.jacobson_eq_sInf_isMaximal]; rw [le_sInf_iff]
    exact fun I hI => Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ => IsNoetherian.noetherian _) (fun _ _ => inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

end IsArtinianRing

section IsNoetherianRing

variable [IsNoetherianRing R]

/--
lemma `Ideal.isOpen_of_isMaximal` / 引理 `Ideal.isOpen_of_isMaximal`

English:
lemma Ideal.isOpen_of_isMaximal
  given: (I : Ideal R) [I.IsMaximal]
  statement: IsOpen (X := R) I
  proof: have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))

中文:
引理 理想.isOpen_of_isMaximal
  条件: (I : 理想 R) [I.是极大]
  结论: 是开集 (X := R) I
  证明: have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))
-/
lemma Ideal.isOpen_of_isMaximal (I : Ideal R) [I.IsMaximal] : IsOpen (X := R) I :=
  have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))

/--
lemma `Ideal.isOpen_pow_of_isMaximal` / 引理 `Ideal.isOpen_pow_of_isMaximal`

English:
lemma Ideal.isOpen_pow_of_isMaximal
  given: (I : Ideal R) [I.IsMaximal] (n : Nat)
  proof: have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed

中文:
引理 理想.isOpen_pow_of_isMaximal
  条件: (I : 理想 R) [I.是极大] (n : 自然数)
  证明: have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed
-/
lemma Ideal.isOpen_pow_of_isMaximal (I : Ideal R) [I.IsMaximal] (n : Nat) :
    IsOpen (X := R) ↑(I ^ n) :=
  have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed

-- Note: this is only by infer_instance because of the opened local instances.
instance (priority := low) (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := inferInstance

end IsNoetherianRing

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/--
lemma `isOpen_maximalIdeal_pow` / 引理 `isOpen_maximalIdeal_pow`

English:
lemma isOpen_maximalIdeal_pow
  given: (n : Nat)
  proof: Ideal.isOpen_pow_of_isMaximal _ _

中文:
引理 isOpen_maximalIdeal_pow
  条件: (n : 自然数)
  证明: Ideal.isOpen_pow_of_isMaximal _ _

Depends on / 依赖: maximalIdeal
-/
lemma isOpen_maximalIdeal_pow (n : Nat) :
    IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  Ideal.isOpen_pow_of_isMaximal _ _

variable (R) in
/--
lemma `isOpen_maximalIdeal` / 引理 `isOpen_maximalIdeal`

English:
lemma isOpen_maximalIdeal
  statement: IsOpen (X := R) ↑(maximalIdeal R)
  proof: Ideal.isOpen_of_isMaximal _

中文:
引理 isOpen_maximalIdeal
  结论: 是开集 (X := R) ↑(maximalIdeal R)
  证明: Ideal.isOpen_of_isMaximal _

Depends on / 依赖: maximalIdeal
-/
lemma isOpen_maximalIdeal : IsOpen (X := R) ↑(maximalIdeal R) :=
  Ideal.isOpen_of_isMaximal _

/--
Instance `finite_residueField_of_compactSpace` / 实例 `finite_residueField_of_compactSpace`

English:
instance finite_residueField_of_compactSpace
  signature: : Finite (ResidueField R)
  body: inferInstanceAs (Finite (R ⧸ _))

中文:
实例 finite_residueField_of_compactSpace
  签名: : 有限 (ResidueField R)
  定义体: inferInstanceAs (Finite (R ⧸ _))

Depends on / 依赖: Finite
-/
instance finite_residueField_of_compactSpace : Finite (ResidueField R) :=
  inferInstanceAs (Finite (R ⧸ _))

/--
lemma `isOpen_iff_finite_quotient` / 引理 `isOpen_iff_finite_quotient`

English:
lemma isOpen_iff_finite_quotient
  given: {I : Ideal R}
  proof: by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H => ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

中文:
引理 isOpen_iff_finite_quotient
  条件: {I : 理想 R}
  证明: by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H => ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

Depends on / 依赖: AddSubgroup, AddSubgroup.isOpen_mono, AddSubgroup.quotient_finite_of_isOpen, Finite, I.toAddSubgroup, exists_maximalIdeal_pow_le_of_isArtinianRing_quotient, isOpen_maximalIdeal_pow, isOpen_mono, maximalIdeal, quotient_finite_of_isOpen, toAddSubgroup
-/
lemma isOpen_iff_finite_quotient {I : Ideal R} :
    IsOpen (X := R) I ↔ Finite (R ⧸ I) := by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H => ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

end IsLocalRing

section IsDedekindDomain

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsDedekindDomain.isOpen_of_ne_bot` / 引理 `IsDedekindDomain.isOpen_of_ne_bot`

English:
lemma IsDedekindDomain.isOpen_of_ne_bot
  proof: by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI]; rw [finprod_eq_finsetProd_of_mulSupport_subset _
      (s := (Ideal.hasFiniteMulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ => IsNoetherian.noetherian _) fun _ _ => ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _

中文:
引理 是Dedekind整环.isOpen_of_ne_bot
  证明: by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI]; rw [finprod_eq_finsetProd_of_mulSupport_subset _
      (s := (Ideal.hasFiniteMulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ => IsNoetherian.noetherian _) fun _ _ => ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _

Depends on / 依赖: AddSubgroup, AddSubgroup.finiteIndex_of_finite_quotient, AddSubgroup.isOpen_of_isClosed_of_finiteIndex, Ideal.finite_quotient_pow, Ideal.finite_quotient_prod, Ideal.finprod_heightOneSpectrum_factorization, Ideal.hasFiniteMulSupport, IsNoetherian, IsNoetherian.noetherian, IsNoetherianRing, IsNoetherianRing.isClosed_ideal, Submodule, Submodule.toAddSubgroup, finiteIndex_of_finite_quotient, finite_quotient_pow, finite_quotient_prod, finprod_eq_finsetProd_of_mulSupport_subset, finprod_heightOneSpectrum_factorization, hasFiniteMulSupport, isClosed_ideal
-/
lemma IsDedekindDomain.isOpen_of_ne_bot
    [IsDedekindDomain R] {I : Ideal R} (hI : I != ⊥) :
    IsOpen (X := R) I := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI]; rw [finprod_eq_finsetProd_of_mulSupport_subset _
      (s := (Ideal.hasFiniteMulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ => IsNoetherian.noetherian _) fun _ _ => ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _

/--
lemma `IsDedekindDomain.isOpen_iff` / 引理 `IsDedekindDomain.isOpen_iff`

English:
lemma IsDedekindDomain.isOpen_iff
  proof: by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)

中文:
引理 是Dedekind整环.isOpen_iff
  证明: by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)

Depends on / 依赖: Finite, Finite.isField_of_domain, IsDedekindDomain, IsDedekindDomain.isOpen_of_ne_bot, discreteTopology_iff_isOpen_singleton_zero, discreteTopology_iff_isOpen_singleton_zero.mpr, isField_of_domain, isOpen_of_ne_bot
-/
lemma IsDedekindDomain.isOpen_iff
    [IsDedekindDomain R] (hR : ¬ IsField R) {I : Ideal R} :
    IsOpen (X := R) I ↔ I != ⊥ := by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)

/--
lemma `IsDiscreteValuationRing.isOpen_iff` / 引理 `IsDiscreteValuationRing.isOpen_iff`

English:
lemma IsDiscreteValuationRing.isOpen_iff
  proof: IsDedekindDomain.isOpen_iff (not_isField R)

中文:
引理 是离散赋值环.isOpen_iff
  证明: IsDedekindDomain.isOpen_iff (not_isField R)
-/
lemma IsDiscreteValuationRing.isOpen_iff
    [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} :
    IsOpen (X := R) I ↔ I != ⊥ :=
  IsDedekindDomain.isOpen_iff (not_isField R)

end IsDedekindDomain
