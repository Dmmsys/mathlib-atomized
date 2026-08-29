/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.DedekindDomain
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Structure of finitely generated modules over a PID

## Main statements

* `Module.equiv_directSum_of_isTorsion` : A finitely generated torsion module over a PID is
  isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
* `Module.equiv_free_prod_directSum` : A finitely generated module over a PID is isomorphic to the
  product of a free module (its torsion free part) and a direct sum of the form above (its torsion
  submodule).

## Notation

* `R` is a PID and `M` is a (finitely generated for main statements) `R`-module, with additional
  torsion hypotheses in the intermediate lemmas.
* `p` is an irreducible element of `R` or a tuple of these.

## Implementation details

We first prove (`Submodule.isInternal_prime_power_torsion_of_pid`) that a finitely generated
torsion module is the internal direct sum of its `p i ^ e i`-torsion submodules for some
(finitely many) prime powers `p i ^ e i`. This is proved in more generality for a Dedekind domain
at `Submodule.isInternal_prime_power_torsion`.

Then we treat the case of a `p ^ ∞`-torsion module (that is, a module where all elements are
cancelled by scalar multiplication by some power of `p`) and apply it to the `p i ^ e i`-torsion
submodules (that are `p i ^ ∞`-torsion) to get the result for torsion modules.

Then we get the general result using that a torsion free module is free (which has been proved at
`Module.free_of_finite_type_torsion_free'` at `LinearAlgebra.FreeModule.PID`.)

## Tags

Finitely generated module, principal ideal domain, classification, structure theorem
-/

public section

-- We shouldn't need to know about topology to prove
-- the structure theorem for finitely generated modules over a PID.
assert_not_exists TopologicalSpace

universe u v

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

open Submodule

open UniqueFactorizationMonoid

/--
theorem `Submodule.isSemisimple_torsionBy_of_irreducible` / 定理 `Submodule.isSemisimple_torsionBy_of_irreducible`

English:
theorem Submodule.isSemisimple_torsionBy_of_irreducible
  given: {a : R} (h : Irreducible a)
  proof: haveI := PrincipalIdealRing.isMaximal_of_irreducible h
  letI := Ideal.Quotient.field (R ∙ a)
  (isSemisimpleModule_iff ..).mpr (submodule_torsionBy_orderIso a).complementedLattice

中文:
定理 子模.isSemisimple_torsionBy_of_irreducible
  条件: {a : R} (h : 不可约 a)
  证明: haveI := PrincipalIdealRing.isMaximal_of_irreducible h
  letI := Ideal.Quotient.field (R ∙ a)
  (isSemisimpleModule_iff ..).mpr (submodule_torsionBy_orderIso a).complementedLattice

Depends on / 依赖: Ideal.Quotient.field, PrincipalIdealRing, PrincipalIdealRing.isMaximal_of_irreducible, Quotient, complementedLattice, isMaximal_of_irreducible, isSemisimpleModule_iff, submodule_torsionBy_orderIso
-/
theorem Submodule.isSemisimple_torsionBy_of_irreducible {a : R} (h : Irreducible a) :
    IsSemisimpleModule R (torsionBy R M a) :=
  haveI := PrincipalIdealRing.isMaximal_of_irreducible h
  letI := Ideal.Quotient.field (R ∙ a)
  (isSemisimpleModule_iff ..).mpr (submodule_torsionBy_orderIso a).complementedLattice

variable [IsDomain R]

/--
theorem `Submodule.isInternal_prime_power_torsion_of_pid` / 定理 `Submodule.isInternal_prime_power_torsion_of_pid`

English:
theorem Submodule.isInternal_prime_power_torsion_of_pid
  statement: [Module.Finite R M]
  proof: by
  convert! isInternal_prime_power_torsion hM
  rw [← torsionBySet_span_singleton_eq]; rw [Ideal.submodule_span_eq]; rw [← Ideal.span_singleton_pow]; rw [Ideal.span_singleton_generator]

中文:
定理 子模.is整数ernal_prime_power_torsion_of_pid
  结论: [模.有限 R M]
  证明: by
  convert! isInternal_prime_power_torsion hM
  rw [← torsionBySet_span_singleton_eq]; rw [Ideal.submodule_span_eq]; rw [← Ideal.span_singleton_pow]; rw [Ideal.span_singleton_generator]

Depends on / 依赖: Ideal.span_singleton_generator, Ideal.span_singleton_pow, Ideal.submodule_span_eq, convert, isInternal_prime_power_torsion, span_singleton_generator, span_singleton_pow, submodule_span_eq, torsionBySet_span_singleton_eq
-/
theorem Submodule.isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBy R M
        (IsPrincipal.generator (p : Ideal R) ^
          (factors (⊤ : Submodule R M).annihilator).count ↑p) := by
  convert! isInternal_prime_power_torsion hM
  rw [← torsionBySet_span_singleton_eq]; rw [Ideal.submodule_span_eq]; rw [← Ideal.span_singleton_pow]; rw [Ideal.span_singleton_generator]

/--
theorem `Submodule.exists_isInternal_prime_power_torsion_of_pid` / 定理 `Submodule.exists_isInternal_prime_power_torsion_of_pid`

English:
theorem Submodule.exists_isInternal_prime_power_torsion_of_pid
  statement: [Module.Finite R M]
  proof: by
  refine ⟨_, ?_, _, _, ?_, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  · exact Finset.fintypeCoeSort _
  · rintro ⟨p, hp⟩
    have hP := prime_of_factor p (Multiset.mem_toFinset.mp hp)
    have := Ideal.isPrime_of_prime hP
    exact (IsPrincipal.prime_generator_of_isPrime p hP.ne_zer

中文:
定理 子模.存在_is整数ernal_prime_power_torsion_of_pid
  结论: [模.有限 R M]
  证明: by
  refine ⟨_, ?_, _, _, ?_, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  · exact Finset.fintypeCoeSort _
  · rintro ⟨p, hp⟩
    have hP := prime_of_factor p (Multiset.mem_toFinset.mp hp)
    have := Ideal.isPrime_of_prime hP
    exact (IsPrincipal.prime_generator_of_isPrime p hP.ne_zer

Depends on / 依赖: Finset, Finset.fintypeCoeSort, Ideal.isPrime_of_prime, IsPrincipal, IsPrincipal.prime_generator_of_isPrime, Multiset, Multiset.mem_toFinset.mp, Submodule, Submodule.isInternal_prime_power_torsion_of_pid, fintypeCoeSort, hP.ne_zero, irreducible, isInternal_prime_power_torsion_of_pid, isPrime_of_prime, mem_toFinset, ne_zero, prime_generator_of_isPrime, prime_of_factor
-/
theorem Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    exists (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι -> R) (_ : forall i, Irreducible <| p i)
(e : ι -> Nat), DirectSum.IsInternal fun i => torsionBy R M p i ^ e i := by
  refine ⟨_, ?_, _, _, ?_, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  · exact Finset.fintypeCoeSort _
  · rintro ⟨p, hp⟩
    have hP := prime_of_factor p (Multiset.mem_toFinset.mp hp)
    have := Ideal.isPrime_of_prime hP
    exact (IsPrincipal.prime_generator_of_isPrime p hP.ne_zero).irreducible

namespace Module

section PTorsion

variable {p : R} (hp : Irreducible p) (hM : Module.IsTorsion' M (Submonoid.powers p))
variable [dec : forall x : M, Decidable (x = 0)]

open Ideal Submodule.IsPrincipal

include hp

/--
theorem `_root_.Ideal.torsionOf_eq_span_pow_pOrder` / 定理 `_root_.Ideal.torsionOf_eq_span_pow_pOrder`

English:
theorem _root_.Ideal.torsionOf_eq_span_pow_pOrder
  given: (x : M)
  proof: by
  classical
  dsimp only [pOrder]
  rw [← (torsionOf R M x).span_singleton_generator]; rw [Ideal.span_singleton_eq_span_singleton]; rw [←
    Associates.mk_eq_mk_iff_associated]; rw [Associates.mk_pow]
  have prop :
    (fun n : Nat => p ^ n • x = 0) = fun n : Nat =>
      (Associates.mk <| gener

中文:
定理 _root_.理想.torsionOf_eq_span_pow_pOrder
  条件: (x : M)
  证明: by
  classical
  dsimp only [pOrder]
  rw [← (torsionOf R M x).span_singleton_generator]; rw [Ideal.span_singleton_eq_span_singleton]; rw [←
    Associates.mk_eq_mk_iff_associated]; rw [Associates.mk_pow]
  have prop :
    (fun n : Nat => p ^ n • x = 0) = fun n : Nat =>
      (Associates.mk <| gener

Depends on / 依赖: Associates, Associates.eq_p, Associates.mk, Associates.mk_dvd_mk, Associates.mk_eq_mk_iff_associated, Associates.mk_pow, Ideal.span_singleton_eq_span_singleton, _powers_iff, classical, convert, eq_p, generator, isTorsion, mem_iff_generator_dvd, mk_dvd_mk, mk_eq_mk_iff_associated, mk_pow, pOrder, span_singleton_eq_span_singleton, span_singleton_generator
-/
theorem _root_.Ideal.torsionOf_eq_span_pow_pOrder (x : M) :
    torsionOf R M x = span {p ^ pOrder hM x} := by
  classical
  dsimp only [pOrder]
  rw [← (torsionOf R M x).span_singleton_generator]; rw [Ideal.span_singleton_eq_span_singleton]; rw [←
    Associates.mk_eq_mk_iff_associated]; rw [Associates.mk_pow]
  have prop :
    (fun n : Nat => p ^ n • x = 0) = fun n : Nat =>
      (Associates.mk <| generator <| torsionOf R M x) ∣ Associates.mk p ^ n := by
    ext n; rw [← Associates.mk_pow, Associates.mk_dvd_mk, ← mem_iff_generator_dvd]; rfl
  have := (isTorsion'_powers_iff p).mp hM x; rw [prop] at this
  convert!
    Associates.eq_pow_find_of_dvd_irreducible_pow (Associates.irreducible_mk.mpr hp)
      this.choose_spec

/--
theorem `p_pow_smul_lift` / 定理 `p_pow_smul_lift`

English:
theorem p_pow_smul_lift
  statement: {x y : M} {k : Nat} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
  proof: by
  by_cases! hk : k <= pOrder hM y
  · let f :=
      ((R ∙ p ^ (pOrder hM y - k) * p ^ k).quotEquivOfEq _ ?_).trans
        (quotTorsionOfEquivSpanSingleton R M y)
    · have : f.symm ⟨p ^ k • x, h⟩ in
          R ∙ Ideal.Quotient.mk (R ∙ p ^ (pOrder hM y - k) * p ^ k) (p ^ k) := by
        rw [←

中文:
定理 p_pow_smul_lift
  结论: {x y : M} {k : 自然数} (hM' : 模.IsTorsionBy R M (p ^ pOrder hM y))
  证明: by
  by_cases! hk : k <= pOrder hM y
  · let f :=
      ((R ∙ p ^ (pOrder hM y - k) * p ^ k).quotEquivOfEq _ ?_).trans
        (quotTorsionOfEquivSpanSingleton R M y)
    · have : f.symm ⟨p ^ k • x, h⟩ in
          R ∙ Ideal.Quotient.mk (R ∙ p ^ (pOrder hM y - k) * p ^ k) (p ^ k) := by
        rw [←

Depends on / 依赖: Ideal.Quotient.mk, Nat.sub_add_cancel, Quotient, Quotient.torsionBy_eq_span_singleton, coe_mk, coe_smul_of_tower, coe_zero, convert, f.symm, f.symm.map_smul, f.symm.map_zero, map_smul, map_zero, mem_torsionBy_iff, pOrder, pow_add, quotEquivOfEq, quotTorsionOfEquivSpanSingleton, smul_smul, sub_add_cancel
-/
theorem p_pow_smul_lift {x y : M} {k : Nat} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
    (h : p ^ k • x in R ∙ y) : exists a : R, p ^ k • x = p ^ k • a • y := by
  by_cases! hk : k <= pOrder hM y
  · let f :=
      ((R ∙ p ^ (pOrder hM y - k) * p ^ k).quotEquivOfEq _ ?_).trans
        (quotTorsionOfEquivSpanSingleton R M y)
    · have : f.symm ⟨p ^ k • x, h⟩ in
          R ∙ Ideal.Quotient.mk (R ∙ p ^ (pOrder hM y - k) * p ^ k) (p ^ k) := by
        rw [← Quotient.torsionBy_eq_span_singleton]; rw [mem_torsionBy_iff]; rw [← f.symm.map_smul]
        · convert! f.symm.map_zero; ext
          rw [coe_smul_of_tower]; rw [coe_mk]; rw [coe_zero]; rw [smul_smul]; rw [← pow_add]; rw [Nat.sub_add_cancel hk]; rw [@hM' x]
        · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp.ne_zero)
      rw [Submodule.mem_span_singleton] at this; obtain ⟨a, ha⟩ := this; use a
      rw [f.eq_symm_apply]; rw [← Ideal.Quotient.mk_eq_mk]; rw [← Quotient.mk_smul] at ha
      dsimp only [smul_eq_mul, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
        quotTorsionOfEquivSpanSingleton_apply_mk] at ha
      rw [smul_smul]; rw [mul_comm]; exact congr_arg ((↑) : _ -> M) ha.symm
    · symm; convert! Ideal.torsionOf_eq_span_pow_pOrder hp hM y
      rw [← pow_add]; rw [Nat.sub_add_cancel hk]
  · use 0
    rw [zero_smul]; rw [smul_zero]; rw [← Nat.sub_add_cancel hk.le]; rw [pow_add]; rw [mul_smul]; rw [hM']; rw [smul_zero]

open Submodule.Quotient

/--
theorem `exists_smul_eq_zero_and_mk_eq` / 定理 `exists_smul_eq_zero_and_mk_eq`

English:
theorem exists_smul_eq_zero_and_mk_eq
  statement: {z : M} (hz : Module.IsTorsionBy R M (p ^ pOrder hM z))
  proof: by
  have f1 := mk_surjective (R ∙ z) (f 1)
  have : p ^ k • f1.choose in R ∙ z := by
    rw [← Quotient.mk_eq_zero]; rw [mk_smul]; rw [f1.choose_spec]; rw [← f.map_smul]
    convert! f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul]; rw [Quotient.mk_eq_zero]; rw [smul_eq_mul]; r

中文:
定理 存在_smul_eq_zero_and_mk_eq
  结论: {z : M} (hz : 模.IsTorsionBy R M (p ^ pOrder hM z))
  证明: by
  have f1 := mk_surjective (R ∙ z) (f 1)
  have : p ^ k • f1.choose in R ∙ z := by
    rw [← Quotient.mk_eq_zero]; rw [mk_smul]; rw [f1.choose_spec]; rw [← f.map_smul]
    convert! f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul]; rw [Quotient.mk_eq_zero]; rw [smul_eq_mul]; r

Depends on / 依赖: Quotient, Quotient.mk_eq_zero, Submodule, Submodule.Quotient.mk, Submodule.mem_span_singleton_self, choose_spec, convert, f.map_smul, f.map_zero, f1.choose, f1.choose_spec, map_smul, map_zero, mem_span_singleton_self, mk_eq_zero, mk_smul, mk_sub, mk_surjective, mul_one, p_pow_smul_lift
-/
theorem exists_smul_eq_zero_and_mk_eq {z : M} (hz : Module.IsTorsionBy R M (p ^ pOrder hM z))
    {k : Nat} (f : (R ⧸ R ∙ p ^ k) ->ₗ[R] M ⧸ R ∙ z) :
    exists x : M, p ^ k • x = 0 ∧ Submodule.Quotient.mk (p := span R {z}) x = f 1 := by
  have f1 := mk_surjective (R ∙ z) (f 1)
  have : p ^ k • f1.choose in R ∙ z := by
    rw [← Quotient.mk_eq_zero]; rw [mk_smul]; rw [f1.choose_spec]; rw [← f.map_smul]
    convert! f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul]; rw [Quotient.mk_eq_zero]; rw [smul_eq_mul]; rw [mul_one]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := p_pow_smul_lift hp hM hz this
  refine ⟨f1.choose - a • z, by rw [smul_sub, sub_eq_zero, ha], ?_⟩
  rw [mk_sub]; rw [mk_smul]; rw [(Quotient.mk_eq_zero _).mpr <| Submodule.mem_span_singleton_self _]; rw [smul_zero]; rw [sub_zero]; rw [f1.choose_spec]

open Finset Multiset

set_option backward.isDefEq.respectTransparency.types false in
omit dec in
/--
theorem `torsion_by_prime_power_decomposition` / 定理 `torsion_by_prime_power_decomposition`

English:
theorem torsion_by_prime_power_decomposition
  statement: (hM : Module.IsTorsion' M (Submonoid.powers p))
  proof: by
  obtain ⟨d, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ h'; use d; clear h'
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty]; rw [Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact

中文:
定理 torsion_by_prime_power_decomposition
  结论: (hM : 模.是挠' M (子幺半群.powers p))
  证明: by
  obtain ⟨d, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ h'; use d; clear h'
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty]; rw [Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact

Depends on / 依赖: Decidable, Finite, Module, Module.Finite.exists_fin, Set.range_eq_empty, Submodule, Submodule.mem_bot, Submodule.mem_top, Submodule.span_empty, Unique, classical, d.succ, d.succ_ne_zero, exists_fin, exists_isTorsionBy, finZeroElim, generalizing, infer_instance, mem_bot, mem_top
-/
theorem torsion_by_prime_power_decomposition (hM : Module.IsTorsion' M (Submonoid.powers p))
    [h' : Module.Finite R M] :
exists (d : Nat) (k : Fin d -> Nat), Nonempty M ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ (k i : Nat) := by
  obtain ⟨d, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ h'; use d; clear h'
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty]; rw [Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact Submodule.mem_top⟩
    exact ⟨0⟩
  | succ d IH =>
    have : forall x : M, Decidable (x = 0) := fun _ => by classical infer_instance
    obtain ⟨j, hj⟩ := exists_isTorsionBy hM d.succ d.succ_ne_zero s hs
    let s' : Fin d -> M ⧸ R ∙ s j := Submodule.Quotient.mk ∘ s ∘ j.succAbove
    -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
    -- `obtain` doesn't work with placeholders.
    have := IH ?_ s' ?_
    · obtain ⟨k, ⟨f⟩⟩ := this
      clear IH
      have : forall i : Fin d,
          exists x : M, p ^ k i • x = 0 ∧ f (Submodule.Quotient.mk x) = DirectSum.lof R _ _ i 1 := by
        intro i
        let fi := f.symm.toLinearMap.comp (DirectSum.lof _ _ _ i)
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hM hj fi; refine ⟨x, h0, ?_⟩; rw [h1]
        simp only [fi, LinearMap.coe_comp, f.symm.coe_toLinearMap, f.apply_symm_apply,
          Function.comp_apply]
      refine ⟨?_, ⟨?_⟩⟩
      · exact fun a => (fun i => (Option.rec (pOrder hM (s j)) k i : Nat)) (finSuccEquiv d a)
      · refine
          (lequivProdOfRightSplitExact
            (g := f.toLinearMap.comp <| mkQ _)
            (f := (DirectSum.toModule _ _ _ fun i => (liftQSpanSingleton (p ^ k i)
                (LinearMap.toSpanSingleton _ _ _) (this i).choose_spec.left : R ⧸ _ ->ₗ[R] _)))
              (R ∙ s j).injective_subtype ?_ ?_).symm ≪≫ₗ
          (((quotTorsionOfEquivSpanSingleton R M (s j)).symm ≪≫ₗ
            (quotEquivOfEq (torsionOf R M (s j)) _
              (Ideal.torsionOf_eq_span_pow_pOrder hp hM (s j)))).prodCongr (.refl _ _)) ≪≫ₗ
          (@DirectSum.lequivProdDirectSum R _ _
            (fun i => R ⧸ R ∙ p ^ @Option.rec _ (fun _ => Nat) (pOrder hM <| s j) k i) _ _).symm ≪≫ₗ
          (DirectSum.lequivCongrLeft R (finSuccEquiv d).symm)
        · rw [range_subtype, LinearEquiv.ker_comp, ker_mkQ]
        · rw [LinearMap.comp_assoc]
          ext i : 3
          simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply]
          rw [LinearEquiv.coe_toLinearMap]; rw [LinearMap.id_apply]; rw [DirectSum.toModule_lof]; rw [liftQSpanSingleton_apply]; rw [LinearMap.toSpanSingleton_apply_one]; rw [Ideal.Quotient.mk_eq_mk]; rw [map_one (Ideal.Quotient.mk _)]; rw [(this i).choose_spec.right]
    · exact (mk_surjective _).forall.mpr fun x =>
        ⟨(@hM x).choose, by rw [← Quotient.mk_smul, (@hM x).choose_spec, Quotient.mk_zero]⟩
    · have hs' := congr_arg (Submodule.map <| mkQ <| R ∙ s j) hs
      rw [Submodule.map_span]; rw [Submodule.map_top]; rw [range_mkQ] at hs'; simp only [mkQ_apply] at hs'
      simp only [s']; rw [← Function.comp_assoc, Set.range_comp (_ ∘ s), Fin.range_succAbove]
      rw [← Set.range_comp]; rw [← Set.insert_image_compl_eq_range _ j]; rw [Function.comp_apply]; rw [(Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)]; rw [Submodule.span_insert_zero] at hs'
      exact hs'

end PTorsion

/--
theorem `equiv_directSum_of_isTorsion` / 定理 `equiv_directSum_of_isTorsion`

English:
theorem equiv_directSum_of_isTorsion
  given: [h' : Module.Finite R M] (hM : Module.IsTorsion R M)
  proof: by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hM
  have :
    forall i,
      exists (d : Nat) (k : Fin d -> Nat),
Nonempty torsionBy R M (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j := by
    exact fun i =>
      torsion_by_prime_power_decomposition.{u, v

中文:
定理 equiv_directSum_of_isTorsion
  条件: [h' : 模.有限 R M] (hM : 模.是挠 R M)
  证明: by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hM
  have :
    forall i,
      exists (d : Nat) (k : Fin d -> Nat),
Nonempty torsionBy R M (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j := by
    exact fun i =>
      torsion_by_prime_power_decomposition.{u, v

Depends on / 依赖: LinearEq, Nonempty, Submodule, Submodule.exists_isInternal_prime_power_torsion_of_pid, _powers_iff, choose_spec, choose_spec.choose, exists_isInternal_prime_power_torsion_of_pid, isTorsion, smul_torsionBy, torsionBy, torsion_by_prime_power_decomposition
-/
theorem equiv_directSum_of_isTorsion [h' : Module.Finite R M] (hM : Module.IsTorsion R M) :
    exists (ι : Type u) (_ : Fintype ι) (p : ι -> R) (_ : forall i, Irreducible <| p i) (e : ι -> Nat),
Nonempty M ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hM
  have :
    forall i,
      exists (d : Nat) (k : Fin d -> Nat),
Nonempty torsionBy R M (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j := by
    exact fun i =>
      torsion_by_prime_power_decomposition.{u, v} (hp i)
        ((isTorsion'_powers_iff <| p i).mpr fun x => ⟨e i, smul_torsionBy _ _⟩)
  refine
    ⟨Σ i, Fin (this i).choose, inferInstance, fun ⟨i, _⟩ => p i, fun ⟨i, _⟩ => hp i, fun ⟨i, j⟩ =>
      (this i).choose_spec.choose j,
⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h).symm.trans
(DFinsupp.mapRange.linearEquiv fun i => (this i).choose_spec.choose_spec.some).trans
            (DirectSum.sigmaLcurryEquiv R).symm.trans
              (DFinsupp.mapRange.linearEquiv fun i => quotEquivOfEq _ _ ?_)⟩⟩
  simp only

variable (R M)

/--
theorem `equiv_free_prod_directSum` / 定理 `equiv_free_prod_directSum`

English:
theorem equiv_free_prod_directSum
  given: [h' : Module.Finite R M]
  proof: by
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R M _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ (M ⧸ torsion R M) _ _ _ _ _ _
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R M).mkQ_surjective

中文:
定理 equiv_free_prod_directSum
  条件: [h' : 模.有限 R M]
  证明: by
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R M _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ (M ⧸ torsion R M) _ _ _ _ _ _
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R M).mkQ_surjective

Depends on / 依赖: LinearEquiv, LinearEquiv.prodComm, LinearMap, LinearMap.id, Module, Module.basisOfFiniteTypeTorsionFree, Module.projective_lifting_property, basisOfFiniteTypeTorsionFree, equiv_directSum_of_isTorsion, h.prodCongr, injective_subtype, ker_mk, lequivProdOfRightSplitExact, mkQ_surjective, prodComm, prodCongr, projective_lifting_property, range_subtype, symm.trans, torsion
-/
theorem equiv_free_prod_directSum [h' : Module.Finite R M] :
    exists (n : Nat) (ι : Type u) (_ : Fintype ι) (p : ι -> R) (_ : forall i, Irreducible <| p i) (e : ι -> Nat),
Nonempty M ≃ₗ[R] (Fin n ->₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R M _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ (M ⧸ torsion R M) _ _ _ _ _ _
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R M).mkQ_surjective
  refine
    ⟨n, I, fI, p, hp, e,
⟨(lequivProdOfRightSplitExact (torsion R M).injective_subtype ?_ hf).symm.trans
(h.prodCongr g).trans LinearEquiv.prodComm.{u, u} R _ (Fin n ->₀ R) ⟩⟩
  rw [range_subtype]; rw [ker_mkQ]

set_option backward.isDefEq.respectTransparency false in
open LinearMap in
/--
theorem `exists_ker_toSpanSingleton_eq_annihilator` / 定理 `exists_ker_toSpanSingleton_eq_annihilator`

English:
theorem exists_ker_toSpanSingleton_eq_annihilator
  given: [Module.Finite R M]
  proof: by
  have ⟨m, ι, _, p, irr, n, ⟨e⟩⟩ := equiv_free_prod_directSum (R := R) (M := M)
  refine ⟨e.symm (Finsupp.equivFunOnFinite.symm fun _ => 1, DFinsupp.equivFunOnFintype.symm
    fun _ => mkQ _ 1), le_antisymm (fun x h => ?_) fun x h => mem_annihilator.mp h _⟩
  rw [mem_ker]; rw [toSpanSingleton_app

中文:
定理 存在_ker_toSpanSingleton_eq_annihilator
  条件: [模.有限 R M]
  证明: by
  have ⟨m, ι, _, p, irr, n, ⟨e⟩⟩ := equiv_free_prod_directSum (R := R) (M := M)
  refine ⟨e.symm (Finsupp.equivFunOnFinite.symm fun _ => 1, DFinsupp.equivFunOnFintype.symm
    fun _ => mkQ _ 1), le_antisymm (fun x h => ?_) fun x h => mem_annihilator.mp h _⟩
  rw [mem_ker]; rw [toSpanSingleton_app

Depends on / 依赖: DFinsupp, DFinsupp.equivFunOnFintype.symm, DFinsupp.ext_iff, Finsupp, Finsupp.equivFunOnFinite.symm, Finsupp.ext_iff, Prod.ext_iff, annihilator_eq, annihilator_prod, e.annihilator_eq, e.symm, e.symm.map_eq_zero_iff, equivFunOnFinite, equivFunOnFintype, equiv_free_prod_directSum, ext_iff, le_antisymm, map_eq_zero_iff, map_smul, mem_annihilator
-/
theorem exists_ker_toSpanSingleton_eq_annihilator [Module.Finite R M] :
    exists x : M, ker (toSpanSingleton R _ x) = annihilator R M := by
  have ⟨m, ι, _, p, irr, n, ⟨e⟩⟩ := equiv_free_prod_directSum (R := R) (M := M)
  refine ⟨e.symm (Finsupp.equivFunOnFinite.symm fun _ => 1, DFinsupp.equivFunOnFintype.symm
    fun _ => mkQ _ 1), le_antisymm (fun x h => ?_) fun x h => mem_annihilator.mp h _⟩
  rw [mem_ker]; rw [toSpanSingleton_apply]; rw [← map_smul]; rw [e.symm.map_eq_zero_iff]; rw [Prod.ext_iff]; rw [Finsupp.ext_iff]; rw [DFinsupp.ext_iff] at h
  obtain _ | m := m
  · rw [← mul_one x, ← smul_eq_mul, e.annihilator_eq, annihilator_prod]
    simp_rw [annihilator_eq_top_iff.mpr inferInstance, DirectSum, annihilator_dfinsupp,
      top_inf_eq, mem_iInf, Ideal.annihilator_quotient, ← Quotient.mk_eq_zero]
    exact h.2
  · rw [show x = 0 by simpa using h.1 0]
    exact zero_mem _

end Module
