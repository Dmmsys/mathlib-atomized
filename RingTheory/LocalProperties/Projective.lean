/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!

# Being projective is a local property

## Main results
- `LinearMap.split_surjective_of_localization_maximal`
  If `N` is finitely presented, then `f : M →ₗ[R] N`
  being split injective can be checked on stalks (of maximal ideals).
- `Module.projective_of_localization_maximal` If `M` is finitely presented,
  then `M` being projective can be checked on stalks (of maximal ideals).

## TODO
- Show that being projective is Zariski-local (very hard)

-/

public section

universe uM

variable {R N N' : Type*} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
variable [Module R N] [AddCommGroup N'] [Module R N'] (S : Submonoid R)

/--
theorem `Module.free_of_isLocalizedModule` / 定理 `Module.free_of_isLocalizedModule`

English:
theorem Module.free_of_isLocalizedModule
  statement: {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
  proof: Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

universe uR' uM' in

中文:
定理 Module.free_of_isLocalizedModule
  结论: {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
  证明: Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

universe uR' uM' in

Depends on / 依赖: Free.of_equiv, IsLocalizedModule, IsLocalizedModule.isBaseChange, isBaseChange, of_equiv
-/
theorem Module.free_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M ->ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M] :
    Module.Free Rₛ Mₛ :=
  Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

universe uR' uM' in
/--
theorem `Module.lift_rank_of_isLocalizedModule_of_free` / 定理 `Module.lift_rank_of_isLocalizedModule_of_free`

English:
theorem Module.lift_rank_of_isLocalizedModule_of_free
  proof: by
  apply Cardinal.lift_injective.{max uM' uR'}
  have := (algebraMap R Rₛ).domain_nontrivial
  have := (IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
  simp only [rank_tensorProduct, rank_self,
    Cardinal.lift_one, one_mul, Cardinal.lift_lift] at this ⊢
  convert! this
  exact C

中文:
定理 Module.lift_rank_of_isLocalizedModule_of_free
  证明: by
  apply Cardinal.lift_injective.{max uM' uR'}
  have := (algebraMap R Rₛ).domain_nontrivial
  have := (IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
  simp only [rank_tensorProduct, rank_self,
    Cardinal.lift_one, one_mul, Cardinal.lift_lift] at this ⊢
  convert! this
  exact C

Depends on / 依赖: Cardinal, Cardinal.lift_injective, Cardinal.lift_lift, Cardinal.lift_one, Cardinal.lift_umax, IsLocalizedModule, IsLocalizedModule.isBaseChange, algebraMap, convert, domain_nontrivial, equiv.lift_rank_eq.symm, isBaseChange, lift_injective, lift_lift, lift_one, lift_rank_eq, lift_umax, one_mul, rank_self, rank_tensorProduct
-/
theorem Module.lift_rank_of_isLocalizedModule_of_free
    (Rₛ : Type uR') {Mₛ : Type uM'} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M ->ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
    Cardinal.lift.{uM} (Module.rank Rₛ Mₛ) = Cardinal.lift.{uM'} (Module.rank R M) := by
  apply Cardinal.lift_injective.{max uM' uR'}
  have := (algebraMap R Rₛ).domain_nontrivial
  have := (IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
  simp only [rank_tensorProduct, rank_self,
    Cardinal.lift_one, one_mul, Cardinal.lift_lift] at this ⊢
  convert! this
  exact Cardinal.lift_umax

/--
theorem `Module.finrank_of_isLocalizedModule_of_free` / 定理 `Module.finrank_of_isLocalizedModule_of_free`

English:
theorem Module.finrank_of_isLocalizedModule_of_free
  proof: by
  simpa using! congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))

中文:
定理 Module.finrank_of_isLocalizedModule_of_free
  证明: by
  simpa using! congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))

Depends on / 依赖: Cardinal, Cardinal.toNat, Module, Module.lift_rank_of_isLocalizedModule_of_free, lift_rank_of_isLocalizedModule_of_free
-/
theorem Module.finrank_of_isLocalizedModule_of_free
    (Rₛ : Type*) {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M ->ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
    Module.finrank Rₛ Mₛ = Module.finrank R M := by
  simpa using! congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))

/--
theorem `Module.projective_of_isLocalizedModule` / 定理 `Module.projective_of_isLocalizedModule`

English:
theorem Module.projective_of_isLocalizedModule
  statement: {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
  proof: Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

中文:
定理 Module.projective_of_isLocalizedModule
  结论: {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
  证明: Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.isBaseChange, Projective, Projective.of_equiv, isBaseChange, of_equiv
-/
theorem Module.projective_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M ->ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Projective R M] :
    Module.Projective Rₛ Mₛ :=
  Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Projective
  signature: R M] : Module.Projective (Localization S) (LocalizedModule S M)
  body: Module.projective_of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

中文:
实例 [Module.Projective
  签名: R M] : Module.Projective (Localization S) (LocalizedModule S M)
  定义体: Module.projective_of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.projective_of_isLocalizedModule, mkLinearMap, projective_of_isLocalizedModule
-/
instance [Module.Projective R M] : Module.Projective (Localization S) (LocalizedModule S M) :=
  Module.projective_of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

instance {A : Type*} [CommRing A] [Algebra R A] [Module.Projective R A] :
    Module.Projective (Localization S) (Localization (Algebra.algebraMapSubmonoid A S)) :=
  Module.projective_of_isLocalizedModule S (IsScalarTower.toAlgHom R A _).toLinearMap

/--
theorem `LinearMap.split_surjective_of_localization_maximal` / 定理 `LinearMap.split_surjective_of_localization_maximal`

English:
theorem LinearMap.split_surjective_of_localization_maximal
  proof: by
  change LinearMap.id in LinearMap.range (LinearMap.llcomp R N M N f)
  refine Submodule.mem_of_localization_maximal _ (fun P _ => LocalizedModule.map P.primeCompl) _ _
    fun I hI => ?_
  rw [LocalizedModule.map_id]
  have : LinearMap.id in LinearMap.range (LinearMap.llcomp _
    (LocalizedModu

中文:
定理 LinearMap.split_surjective_of_localization_maximal
  证明: by
  change LinearMap.id in LinearMap.range (LinearMap.llcomp R N M N f)
  refine Submodule.mem_of_localization_maximal _ (fun P _ => LocalizedModule.map P.primeCompl) _ _
    fun I hI => ?_
  rw [LocalizedModule.map_id]
  have : LinearMap.id in LinearMap.range (LinearMap.llcomp _
    (LocalizedModu

Depends on / 依赖: I.primeCompl, IsLocalizedModule, IsLocalizedModule.mk, LinearMap, LinearMap.id, LinearMap.llcomp, LinearMap.range, LocalizedModule, LocalizedModule.map, LocalizedModule.map_id, P.primeCompl, Submodule, Submodule.mem_of_localization_maximal, convert, llcomp, map_id, mem_of_localization_maximal, primeCompl
-/
theorem LinearMap.split_surjective_of_localization_maximal
    (f : M ->ₗ[R] N) [Module.FinitePresentation R N]
    (H : forall (I : Ideal R) (_ : I.IsMaximal),
    exists (g : _ ->ₗ[Localization.AtPrime I] _),
      (LocalizedModule.map I.primeCompl f).comp g = LinearMap.id) :
    exists (g : N ->ₗ[R] M), f.comp g = LinearMap.id := by
  change LinearMap.id in LinearMap.range (LinearMap.llcomp R N M N f)
  refine Submodule.mem_of_localization_maximal _ (fun P _ => LocalizedModule.map P.primeCompl) _ _
    fun I hI => ?_
  rw [LocalizedModule.map_id]
  have : LinearMap.id in LinearMap.range (LinearMap.llcomp _
    (LocalizedModule I.primeCompl N) _ _ (LocalizedModule.map I.primeCompl f)) := H I hI
  convert! this
  · ext f
    constructor
    · intro hf
      obtain ⟨a, ha, c, rfl⟩ := hf
      obtain ⟨g, rfl⟩ := ha
      use IsLocalizedModule.mk' (LocalizedModule.map I.primeCompl) g c
      apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
        (LocalizedModule.map I.primeCompl) c).injective
      dsimp
      conv_rhs => rw [← Submonoid.smul_def]
      conv_lhs => rw [← LinearMap.map_smul_of_tower]
      rw [← Submonoid.smul_def]; rw [IsLocalizedModule.mk'_cancel']; rw [IsLocalizedModule.mk'_cancel']
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [LocalizedModule.map_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearMap.llcomp_apply,
        LocalizedModule.map_mk]
    · rintro ⟨g, rfl⟩
      obtain ⟨⟨g, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective I.primeCompl (LocalizedModule.map I.primeCompl) g
      simp only [Function.uncurry_apply_pair]
      refine ⟨f.comp g, ⟨g, rfl⟩, s, ?_⟩
      apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
         (LocalizedModule.map I.primeCompl) s).injective
      simp only [Module.algebraMap_end_apply, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
        ← LinearMap.map_smul_of_tower]
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [coe_comp, coe_restrictScalars, Function.comp_apply,
        LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, llcomp_apply]

/--
theorem `Module.projective_of_localization_maximal` / 定理 `Module.projective_of_localization_maximal`

English:
theorem Module.projective_of_localization_maximal
  statement: (H : forall (I : Ideal R) (_ : I.IsMaximal),
  proof: by
  have : Module.Finite R M := by infer_instance
  obtain ⟨s, hs⟩ := this
  let N := s ->₀ R
  let f : N ->ₗ[R] M := Finsupp.linearCombination R (Subtype.val : s -> M)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]; rw [Subtype.range

中文:
定理 Module.projective_of_localization_maximal
  结论: (H : 对任意 (I : Ideal R) (_ : I.IsMaximal),
  证明: by
  have : Module.Finite R M := by infer_instance
  obtain ⟨s, hs⟩ := this
  let N := s ->₀ R
  let f : N ->ₗ[R] M := Finsupp.linearCombination R (Subtype.val : s -> M)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]; rw [Subtype.range

Depends on / 依赖: Finite, Finsupp, Finsupp.linearCombination, Finsupp.range_linearCombination, Function, Function.Surjective, I.IsMaximal, I.primeCompl, IsMaximal, LinearMap, LinearMap.id, LinearMap.range_eq_top, LocalizedModule, LocalizedModule.map, LocalizedModule.map_surjective, Module, Module.Finite, Module.projective_lifting_property, Subtype, Subtype.range_val
-/
theorem Module.projective_of_localization_maximal (H : forall (I : Ideal R) (_ : I.IsMaximal),
    Module.Projective (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  have : Module.Finite R M := by infer_instance
  obtain ⟨s, hs⟩ := this
  let N := s ->₀ R
  let f : N ->ₗ[R] M := Finsupp.linearCombination R (Subtype.val : s -> M)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]; rw [Subtype.range_val]
    convert! hs
  have (I : Ideal R) (hI : I.IsMaximal) :=
    letI := H I hI
    Module.projective_lifting_property (LocalizedModule.map I.primeCompl f) LinearMap.id
    (LocalizedModule.map_surjective _ _ hf)
  obtain ⟨g, hg⟩ := LinearMap.split_surjective_of_localization_maximal _ this
  exact Module.Projective.of_split _ _ hg

variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : forall (P : Ideal R) [P.IsMaximal], M ->ₗ[R] Mₚ P)
  [inst : forall (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
include f in
/--
theorem `Module.projective_of_localization_maximal'` / 定理 `Module.projective_of_localization_maximal'`

English:
theorem Module.projective_of_localization_maximal'
  proof: by
  apply Module.projective_of_localization_maximal
  intro P hP
  set e := (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
  refine Module.Projective.of_equiv (M := Mₚ P) (R := Rₚ P)
    (σ := e)
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
      

中文:
定理 Module.projective_of_localization_maximal'
  证明: by
  apply Module.projective_of_localization_maximal
  intro P hP
  set e := (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
  refine Module.Projective.of_equiv (M := Mₚ P) (R := Rₚ P)
    (σ := e)
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
      

Depends on / 依赖: AtPrime, IsLocalization, IsLocalization.algEquiv, IsLocalization.exists_mk, IsLocalizedModule, IsLocalizedModule.linearEquiv, IsLocalizedModule.map_units, Localization, Localization.AtPrime, LocalizedModule, LocalizedModule.mkLinearMap, Module, Module.End.isUnit_iff, Module.Projective.of_equiv, Module.projective_of_localization_maximal, P.primeCompl, Projective, algEquiv, exists_mk, isUnit_iff
-/
theorem Module.projective_of_localization_maximal'
    (H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Rₚ I) (Mₚ I))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  apply Module.projective_of_localization_maximal
  intro P hP
  set e := (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
  refine Module.Projective.of_equiv (M := Mₚ P) (R := Rₚ P)
    (σ := e)
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
        (LocalizedModule.mkLinearMap P.primeCompl M)
      map_smul' := ?_ }
  · intro r m
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl r
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P.primeCompl M) s)).1
    dsimp [e]
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
      IsLocalization.map_id_mk']
