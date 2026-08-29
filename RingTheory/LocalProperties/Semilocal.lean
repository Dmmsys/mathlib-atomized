/-
Copyright (c) 2025 Yiming Fu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiming Fu
-/
module

public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# Local properties for semilocal rings

This file proves some local properties for a semilocal ring `R` (a ring with
finitely many maximal ideals).

## Main results

* `Module.Finite.of_isLocalized_maximal`: A module `M` over a semilocal ring `R` is finite if its
  localization at every maximal ideal is finite.
* `IsNoetherianRing.of_isLocalization_maximal`: A semilocal ring `R` is Noetherian if its
  localization at every maximal ideal is a Noetherian ring.
* `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal`: A semilocal
  integral domain `A` is a PID if its localization at every maximal ideal is a PID.
-/

public section

section CommSemiring

variable {R : Type*} [CommSemiring R] [Finite (MaximalSpectrum R)]
variable (M : Type*) [AddCommMonoid M] [Module R M]

variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : forall (P : Ideal R) [P.IsMaximal], M ->ₗ[R] Mₚ P)
  [forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

section IsLocalized

include f in
/--
theorem `Module.Finite.of_isLocalized_maximal` / 定理 `Module.Finite.of_isLocalized_maximal`

English:
theorem Module.Finite.of_isLocalized_maximal
  proof: by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose s hs using fun P : MaximalSpectrum R => (H P.1).fg_top
  choose frac hfrac using fun P : MaximalSpectrum R => IsLocalizedModule.surj P.1.primeCompl (f P.1)
  use Finset.biUnion Finset.univ fun P => Finset.image (frac 

中文:
定理 Module.Finite.of_isLocalized_maximal
  证明: by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose s hs using fun P : MaximalSpectrum R => (H P.1).fg_top
  choose frac hfrac using fun P : MaximalSpectrum R => IsLocalizedModule.surj P.1.primeCompl (f P.1)
  use Finset.biUnion Finset.univ fun P => Finset.image (frac 

Depends on / 依赖: Finset, Finset.biUnion, Finset.image, Finset.univ, Fintype, Fintype.ofFinite, IsLocalizedModule, IsLocalizedModule.surj, MaximalSpectrum, Submodule, Submodule.eq_top_of_localization_maximal, Submodule.localized, Submodule.span_le, _span, biUnion, classical, eq_top_iff, eq_top_of_localization_maximal, fg_top, localized
-/
theorem Module.Finite.of_isLocalized_maximal
    (H : forall (P : Ideal R) [P.IsMaximal], Module.Finite (Rₚ P) (Mₚ P)) :
    Module.Finite R M := by
  classical
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose s hs using fun P : MaximalSpectrum R => (H P.1).fg_top
  choose frac hfrac using fun P : MaximalSpectrum R => IsLocalizedModule.surj P.1.primeCompl (f P.1)
  use Finset.biUnion Finset.univ fun P => Finset.image (frac P · |>.1) (s P)
  refine Submodule.eq_top_of_localization_maximal Rₚ Mₚ f _ fun P hP => ?_
  rw [eq_top_iff]; rw [← hs ⟨P]; rw [hP⟩]; rw [Submodule.localized'_span]; rw [Submodule.span_le]
  intro x hx
  lift x to s ⟨P, hP⟩ using hx
  rw [SetLike.mem_coe]; rw [← IsLocalization.smul_mem_iff (s := (frac ⟨P]; rw [hP⟩ x).2)]; rw [hfrac]
  exact Submodule.subset_span ⟨_, by simpa using ⟨_, _, x.2, rfl⟩, rfl⟩

variable {M} in
/--
theorem `Submodule.fg_of_isLocalized_maximal` / 定理 `Submodule.fg_of_isLocalized_maximal`

English:
theorem Submodule.fg_of_isLocalized_maximal
  statement: (N : Submodule R M)
  proof: by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  exact .of_isLocalized_maximal _ _ _ (fun P => N.toLocalized' (Rₚ P) P.primeCompl (f P)) H

中文:
定理 Submodule.fg_of_isLocalized_maximal
  结论: (N : Submodule R M)
  证明: by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  exact .of_isLocalized_maximal _ _ _ (fun P => N.toLocalized' (Rₚ P) P.primeCompl (f P)) H

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, N.toLocalized, P.primeCompl, iff_fg, of_isLocalized_maximal, primeCompl, simp_rw, toLocalized
-/
theorem Submodule.fg_of_isLocalized_maximal (N : Submodule R M)
    (H : forall (P : Ideal R) [P.IsMaximal], (Submodule.localized' (Rₚ P) P.primeCompl (f P) N).FG) :
    N.FG := by
  simp_rw [← Module.Finite.iff_fg] at ⊢ H
  exact .of_isLocalized_maximal _ _ _ (fun P => N.toLocalized' (Rₚ P) P.primeCompl (f P)) H

end IsLocalized

section Localized

/--
theorem `Module.Finite.of_localized_maximal` / 定理 `Module.Finite.of_localized_maximal`

English:
theorem Module.Finite.of_localized_maximal
  proof: .of_isLocalized_maximal M _ _ (fun _ _ => LocalizedModule.mkLinearMap _ _) H

中文:
定理 Module.Finite.of_localized_maximal
  证明: .of_isLocalized_maximal M _ _ (fun _ _ => LocalizedModule.mkLinearMap _ _) H

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, mkLinearMap, of_isLocalized_maximal
-/
theorem Module.Finite.of_localized_maximal
    (H : forall (P : Ideal R) [P.IsMaximal],
      Module.Finite (Localization P.primeCompl) (LocalizedModule P.primeCompl M)) :
    Module.Finite R M :=
  .of_isLocalized_maximal M _ _ (fun _ _ => LocalizedModule.mkLinearMap _ _) H

variable {M} in
/--
theorem `Submodule.fg_of_localized_maximal` / 定理 `Submodule.fg_of_localized_maximal`

English:
theorem Submodule.fg_of_localized_maximal
  statement: (N : Submodule R M)
  proof: N.fg_of_isLocalized_maximal _ _ _ H

中文:
定理 Submodule.fg_of_localized_maximal
  结论: (N : Submodule R M)
  证明: N.fg_of_isLocalized_maximal _ _ _ H

Depends on / 依赖: ContinuousConstSMul, ContinuousSMul, ContinuousSMul.continuousConstSMul, N.fg_of_isLocalized_maximal, continuousConstSMul, fg_of_isLocalized_maximal
-/
theorem Submodule.fg_of_localized_maximal (N : Submodule R M)
    (H : forall (P : Ideal R) [P.IsMaximal], (N.localized P.primeCompl).FG) :
    N.FG := N.fg_of_isLocalized_maximal _ _ _ H

end Localized

section IsLocalization

/--
theorem `IsNoetherianRing.of_isLocalization_maximal` / 定理 `IsNoetherianRing.of_isLocalization_maximal`

English:
theorem IsNoetherianRing.of_isLocalization_maximal
  proof: Submodule.fg_of_isLocalized_maximal
    Rₚ Rₚ (fun P _ => Algebra.linearMap R (Rₚ P)) N fun _ _ => IsNoetherian.noetherian _

中文:
定理 IsNoetherianRing.of_isLocalization_maximal
  证明: Submodule.fg_of_isLocalized_maximal
    Rₚ Rₚ (fun P _ => Algebra.linearMap R (Rₚ P)) N fun _ _ => IsNoetherian.noetherian _

Depends on / 依赖: Submodule, Submodule.fg_of_isLocalized_maximal, fg_of_isLocalized_maximal
-/
theorem IsNoetherianRing.of_isLocalization_maximal
    (H : forall (P : Ideal R) [P.IsMaximal], IsNoetherianRing (Rₚ P)) :
    IsNoetherianRing R where
  noetherian N := Submodule.fg_of_isLocalized_maximal
    Rₚ Rₚ (fun P _ => Algebra.linearMap R (Rₚ P)) N fun _ _ => IsNoetherian.noetherian _

end IsLocalization

end CommSemiring

section CommRing

section IsLocalization

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]

/--
theorem `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal` / 定理 `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal`

English:
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal
  statement: [IsDomain R]
  proof: by
  have : IsNoetherianRing R :=
    IsNoetherianRing.of_isLocalization_maximal Rₚ fun P _ => inferInstance
  have : IsIntegrallyClosed R := by
    refine IsIntegrallyClosed.of_isLocalization_maximal Rₚ fun P hP => ?_
    have : IsDomain (Rₚ P) := IsLocalization.isDomain_of_atPrime (Rₚ P) P
    inf

中文:
定理 isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal
  结论: [IsDomain R]
  证明: by
  have : IsNoetherianRing R :=
    IsNoetherianRing.of_isLocalization_maximal Rₚ fun P _ => inferInstance
  have : IsIntegrallyClosed R := by
    refine IsIntegrallyClosed.of_isLocalization_maximal Rₚ fun P hP => ?_
    have : IsDomain (Rₚ P) := IsLocalization.isDomain_of_atPrime (Rₚ P) P
    inf

Depends on / 依赖: IsDedekindDomain, IsDomain, IsIntegrallyClosed, IsIntegrallyClosed.of_isLocalization_maximal, IsLocalization, IsLocalization.isDomain_of_atPrime, IsNoetherianRing, IsNoetherianRing.of_isLocalization_maximal, KrullDimLE, Ring.KrullDimLE, Ring.krullDimLE_of_isLocalization_maximal, Ring.krullDimLE_one_iff_of_noZeroDivisors, dedekind, infer_instance, isDomain_of_atPrime, krullDimLE_of_isLocalization_maximal, krullDimLE_one_iff_of_noZeroDivisors, maximalOfPrim, of_isLocalization_maximal
-/
theorem isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal [IsDomain R]
    (hpid : forall (P : Ideal R) [P.IsMaximal], IsPrincipalIdealRing (Rₚ P)) :
    IsPrincipalIdealRing R := by
  have : IsNoetherianRing R :=
    IsNoetherianRing.of_isLocalization_maximal Rₚ fun P _ => inferInstance
  have : IsIntegrallyClosed R := by
    refine IsIntegrallyClosed.of_isLocalization_maximal Rₚ fun P hP => ?_
    have : IsDomain (Rₚ P) := IsLocalization.isDomain_of_atPrime (Rₚ P) P
    infer_instance
  have : Ring.KrullDimLE 1 R :=
    Ring.krullDimLE_of_isLocalization_maximal Rₚ fun P _ => inferInstance
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors] at this
  have dedekind : IsDedekindDomain R := { maximalOfPrime := this _ }
  have hp_finite : {P : Ideal R | P.IsMaximal}.Finite := by
    rw [← MaximalSpectrum.range_asIdeal]
    exact Set.finite_range MaximalSpectrum.asIdeal
  exact IsPrincipalIdealRing.of_finite_maximals hp_finite

end IsLocalization

end CommRing
