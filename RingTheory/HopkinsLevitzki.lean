/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
## The Hopkins–Levitzki theorem

## Main results

* `IsSemiprimaryRing.isNoetherian_iff_isArtinian`: the Hopkins–Levitzki theorem, which states
  that for a module over a semiprimary ring (in particular, an Artinian ring),
  `IsNoetherian` is equivalent to `IsArtinian` (and therefore also to `IsFiniteLength`).

* In particular, for a module over an Artinian ring, `Module.Finite`, `IsNoetherian`, `IsArtinian`,
  and `IsFiniteLength` are all equivalent (`IsArtinianRing.tfae`),
  and a (left) Artinian ring is also (left) Noetherian.

* `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`: a commutative ring is Artinian iff
  it is Noetherian with Krull dimension at most 0.

## Reference

* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

public section

universe u

variable (R₀ R : Type*) (M : Type u) [Ring R₀] [Ring R] [Module R₀ R]
  [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]

namespace IsSemiprimaryRing

variable [IsSemiprimaryRing R]

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  proof: by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n <= Module.annihilator R M := hn ▸ bot_le
  have {M} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M] :
      Jac <= Module.annihilator R M -> P M := by
    rw [← SetLike.co

中文:
定理 induction
  证明: by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n <= Module.annihilator R M := hn ▸ bot_le
  have {M} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M] :
      Jac <= Module.annihilator R M -> P M := by
    rw [← SetLike.co
-/
@[elab_as_elim] protected theorem induction
    {P : forall (M : Type u) [AddCommGroup M] [Module R₀ M] [Module R M], Prop}
    (h0 : forall (M) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
      [IsSemisimpleModule R M], Module.IsTorsionBySet R M (Ring.jacobson R) -> P M)
    (h1 : forall (M) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M],
      let N := Ring.jacobson R • (⊤ : Submodule R M); P N -> P (M ⧸ N) -> P M) :
    P M := by
  have ⟨ss, n, hn⟩ := (isSemiprimaryRing_iff R).mp ‹_›
  set Jac := Ring.jacobson R
  replace hn : Jac ^ n <= Module.annihilator R M := hn ▸ bot_le
  have {M} [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M] :
      Jac <= Module.annihilator R M -> P M := by
    rw [← SetLike.coe_subset_coe]; rw [← Module.isTorsionBySet_iff_subset_annihilator]
    intro h
    let _ := h.module
    have := (h.semilinearMap.isSemisimpleModule_iff_of_bijective Function.bijective_id).2
      inferInstance
    exact h0 _ h
  induction n generalizing M with
  | zero => rw [Jac.pow_zero, Ideal.one_eq_top] at hn; exact this (le_top.trans hn)
  | succ n ih => ?_
  obtain _ | n := n
  · rw [Jac.pow_one] at hn; exact this hn
  refine h1 _ (ih _ ?_) (ih _ ?_)
  · rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff, Jac.pow_succ,
      Submodule.mul_smul, ← Submodule.le_annihilator_iff] at hn
  · rw [← SetLike.coe_subset_coe, ← Module.isTorsionBySet_iff_subset_annihilator,
      Module.isTorsionBySet_quotient_iff]
    exact fun m i hi => Submodule.smul_mem_smul (Ideal.pow_le_self n.succ_ne_zero hi) trivial

section

variable [IsScalarTower R₀ R R] [Module.Finite R₀ (R ⧸ Ring.jacobson R)]

/--
theorem `finite_of_isNoetherian_or_isArtinian` / 定理 `finite_of_isNoetherian_or_isArtinian`

English:
theorem finite_of_isNoetherian_or_isArtinian
  proof: by
  refine IsSemiprimaryRing.induction R₀ R M (P := fun M => IsNoetherian R M ∨ IsArtinian R M ->
    Module.Finite R₀ M) (fun M _ _ _ _ _ hJ h => ?_) (fun M _ _ _ _ hs hq h => ?_)
  · let _ := hJ.module
    have := IsSemisimpleModule.finite_tfae (R := R) (M := M)
    simp_rw [this.out 1 0, this.ou

中文:
定理 finite_of_isNoetherian_or_isArtinian
  证明: by
  refine IsSemiprimaryRing.induction R₀ R M (P := fun M => IsNoetherian R M ∨ IsArtinian R M ->
    Module.Finite R₀ M) (fun M _ _ _ _ _ hJ h => ?_) (fun M _ _ _ _ hs hq h => ?_)
  · let _ := hJ.module
    have := IsSemisimpleModule.finite_tfae (R := R) (M := M)
    simp_rw [this.out 1 0, this.ou
-/
private theorem finite_of_isNoetherian_or_isArtinian :
    IsNoetherian R M ∨ IsArtinian R M -> Module.Finite R₀ M := by
  refine IsSemiprimaryRing.induction R₀ R M (P := fun M => IsNoetherian R M ∨ IsArtinian R M ->
    Module.Finite R₀ M) (fun M _ _ _ _ _ hJ h => ?_) (fun M _ _ _ _ hs hq h => ?_)
  · let _ := hJ.module
    have := IsSemisimpleModule.finite_tfae (R := R) (M := M)
    simp_rw [this.out 1 0, this.out 2 0, or_self,
      hJ.semilinearMap.finite_iff_of_bijective Function.bijective_id] at h
    exact .trans (R ⧸ Ring.jacobson R) M
  · let N := (Ring.jacobson R • ⊤ : Submodule R M).restrictScalars R₀
    have : Module.Finite R₀ N := by refine hs (h.imp ?_ ?_) <;> (intro; infer_instance)
    have : Module.Finite R₀ (M ⧸ N) := by refine hq (h.imp ?_ ?_) <;> (intro; infer_instance)
    exact .of_submodule_quotient N

/--
theorem `finite_of_isNoetherian` / 定理 `finite_of_isNoetherian`

English:
theorem finite_of_isNoetherian
  given: [IsNoetherian R M]
  statement: Module.Finite R₀ M
  proof: finite_of_isNoetherian_or_isArtinian R₀ R M (.inl ‹_›)

中文:
定理 finite_of_isNoetherian
  条件: [是Noether R M]
  结论: 模.有限 R₀ M
  证明: finite_of_isNoetherian_or_isArtinian R₀ R M (.inl ‹_›)

Depends on / 依赖: finite_of_isNoetherian_or_isArtinian
-/
theorem finite_of_isNoetherian [IsNoetherian R M] : Module.Finite R₀ M :=
  finite_of_isNoetherian_or_isArtinian R₀ R M (.inl ‹_›)

/--
theorem `finite_of_isArtinian` / 定理 `finite_of_isArtinian`

English:
theorem finite_of_isArtinian
  given: [IsArtinian R M]
  statement: Module.Finite R₀ M
  proof: finite_of_isNoetherian_or_isArtinian R₀ R M (.inr ‹_›)

中文:
定理 finite_of_isArtinian
  条件: [是Artin R M]
  结论: 模.有限 R₀ M
  证明: finite_of_isNoetherian_or_isArtinian R₀ R M (.inr ‹_›)

Depends on / 依赖: finite_of_isNoetherian_or_isArtinian
-/
theorem finite_of_isArtinian [IsArtinian R M] : Module.Finite R₀ M :=
  finite_of_isNoetherian_or_isArtinian R₀ R M (.inr ‹_›)

end

variable {R M}

/--
theorem `isNoetherian_iff_isArtinian` / 定理 `isNoetherian_iff_isArtinian`

English:
theorem isNoetherian_iff_isArtinian
  statement: IsNoetherian R M ↔ IsArtinian R M
  proof: IsSemiprimaryRing.induction R R M (P := fun M => IsNoetherian R M ↔ IsArtinian R M)
    (fun M _ _ _ _ _ _ => IsSemisimpleModule.finite_tfae.out 1 2)
    fun M _ _ _ _ h h' => let N : Submodule R M := Ring.jacobson R • ⊤; by
      simp_rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submod

中文:
定理 isNoetherian_iff_isArtinian
  结论: 是Noether R M ↔ 是Artin R M
  证明: IsSemiprimaryRing.induction R R M (P := fun M => IsNoetherian R M ↔ IsArtinian R M)
    (fun M _ _ _ _ _ _ => IsSemisimpleModule.finite_tfae.out 1 2)
    fun M _ _ _ _ h h' => let N : Submodule R M := Ring.jacobson R • ⊤; by
      simp_rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submod

Depends on / 依赖: IsArtinian, IsNoetherian, IsSemiprimaryRing, IsSemiprimaryRing.induction, IsSemisimpleModule, IsSemisimpleModule.finite_tfae.out, Ring.jacobson, Submodule, finite_tfae, isArtinian_iff_submodule_quotient, isNoetherian_iff_submodule_quotient, jacobson, simp_rw
-/
theorem isNoetherian_iff_isArtinian : IsNoetherian R M ↔ IsArtinian R M :=
  IsSemiprimaryRing.induction R R M (P := fun M => IsNoetherian R M ↔ IsArtinian R M)
    (fun M _ _ _ _ _ _ => IsSemisimpleModule.finite_tfae.out 1 2)
    fun M _ _ _ _ h h' => let N : Submodule R M := Ring.jacobson R • ⊤; by
      simp_rw [isNoetherian_iff_submodule_quotient N, isArtinian_iff_submodule_quotient N, N, h, h']

/--
theorem `isNoetherian_iff_finite_of_jacobson_fg` / 定理 `isNoetherian_iff_finite_of_jacobson_fg`

English:
theorem isNoetherian_iff_finite_of_jacobson_fg
  given: (fg : (Ring.jacobson R).FG)
  proof: ⟨fun _ => inferInstance, IsSemiprimaryRing.induction R R M
    (P := fun M => Module.Finite R M -> IsNoetherian R M)
    (fun M _ _ _ _ _ _ => (IsSemisimpleModule.finite_tfae.out 0 1).mp)
    fun M _ _ _ _ hs hq fin => (isNoetherian_iff_submodule_quotient (Ring.jacobson R • ⊤)).mpr
      ⟨hs (.of_fg

中文:
定理 isNoetherian_iff_finite_of_jacobson_fg
  条件: (fg : (环.jacobson R).FG)
  证明: ⟨fun _ => inferInstance, IsSemiprimaryRing.induction R R M
    (P := fun M => Module.Finite R M -> IsNoetherian R M)
    (fun M _ _ _ _ _ _ => (IsSemisimpleModule.finite_tfae.out 0 1).mp)
    fun M _ _ _ _ hs hq fin => (isNoetherian_iff_submodule_quotient (Ring.jacobson R • ⊤)).mpr
      ⟨hs (.of_fg

Depends on / 依赖: Finite, IsNoetherian, IsSemiprimaryRing, IsSemiprimaryRing.induction, IsSemisimpleModule, IsSemisimpleModule.finite_tfae.out, Module, Module.Finite, Ring.jacobson, finite_tfae, isNoetherian_iff_submodule_quotient, jacobson, of_fg
-/
theorem isNoetherian_iff_finite_of_jacobson_fg (fg : (Ring.jacobson R).FG) :
    IsNoetherian R M ↔ Module.Finite R M :=
  ⟨fun _ => inferInstance, IsSemiprimaryRing.induction R R M
    (P := fun M => Module.Finite R M -> IsNoetherian R M)
    (fun M _ _ _ _ _ _ => (IsSemisimpleModule.finite_tfae.out 0 1).mp)
    fun M _ _ _ _ hs hq fin => (isNoetherian_iff_submodule_quotient (Ring.jacobson R • ⊤)).mpr
      ⟨hs (.of_fg (.smul fg fin.1)), hq inferInstance⟩⟩

/--
theorem `isNoetherianRing_iff_jacobson_fg` / 定理 `isNoetherianRing_iff_jacobson_fg`

English:
theorem isNoetherianRing_iff_jacobson_fg
  statement: IsNoetherianRing R ↔ (Ring.jacobson R).FG
  proof: ⟨fun _ => IsNoetherian.noetherian .., fun fg =>
    (IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg fg).mpr inferInstance⟩

中文:
定理 isNoetherianRing_iff_jacobson_fg
  结论: 是Noether环 R ↔ (环.jacobson R).FG
  证明: ⟨fun _ => IsNoetherian.noetherian .., fun fg =>
    (IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg fg).mpr inferInstance⟩

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, IsSemiprimaryRing, IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg, isNoetherian_iff_finite_of_jacobson_fg, noetherian
-/
theorem isNoetherianRing_iff_jacobson_fg : IsNoetherianRing R ↔ (Ring.jacobson R).FG :=
  ⟨fun _ => IsNoetherian.noetherian .., fun fg =>
    (IsSemiprimaryRing.isNoetherian_iff_finite_of_jacobson_fg fg).mpr inferInstance⟩

end IsSemiprimaryRing

/--
theorem `IsArtinianRing.tfae` / 定理 `IsArtinianRing.tfae`

English:
theorem IsArtinianRing.tfae
  given: [IsArtinianRing R]
  proof: by
  tfae_have 2 ↔ 3 := IsSemiprimaryRing.isNoetherian_iff_isArtinian
  tfae_have 2 -> 1 := fun _ => inferInstance
  tfae_have 1 -> 3 := fun _ => inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tfae_have 4 -> 2 := And.left
  tfae_have 2 -> 4 := fun h => ⟨h, tfae_2_iff_3.mp h⟩
  tfa

中文:
定理 是Artin环.tfae
  条件: [是Artin环 R]
  证明: by
  tfae_have 2 ↔ 3 := IsSemiprimaryRing.isNoetherian_iff_isArtinian
  tfae_have 2 -> 1 := fun _ => inferInstance
  tfae_have 1 -> 3 := fun _ => inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tfae_have 4 -> 2 := And.left
  tfae_have 2 -> 4 := fun h => ⟨h, tfae_2_iff_3.mp h⟩
  tfa

Depends on / 依赖: And.left, IsSemiprimaryRing, IsSemiprimaryRing.isNoetherian_iff_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff_isArtinian, tfae_2_iff_3, tfae_2_iff_3.mp, tfae_finish, tfae_have
-/
theorem IsArtinianRing.tfae [IsArtinianRing R] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M] := by
  tfae_have 2 ↔ 3 := IsSemiprimaryRing.isNoetherian_iff_isArtinian
  tfae_have 2 -> 1 := fun _ => inferInstance
  tfae_have 1 -> 3 := fun _ => inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tfae_have 4 -> 2 := And.left
  tfae_have 2 -> 4 := fun h => ⟨h, tfae_2_iff_3.mp h⟩
  tfae_finish

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself."]
/--
theorem `isArtinianRing_iff_isFiniteLength` / 定理 `isArtinianRing_iff_isFiniteLength`

English:
theorem isArtinianRing_iff_isFiniteLength
  statement: IsArtinianRing R ↔ IsFiniteLength R R
  proof: ⟨fun h => ((IsArtinianRing.tfae R R).out 2 3).mp h,
    fun h => (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2⟩

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself.
**Any such ring is both Artinian and Noetherian.**"]

中文:
定理 isArtinianRing_iff_isFiniteLength
  结论: 是Artin环 R ↔ 是FiniteLength R R
  证明: ⟨fun h => ((IsArtinianRing.tfae R R).out 2 3).mp h,
    fun h => (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2⟩

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself.
**Any such ring is both Artinian and Noetherian.**"]

Depends on / 依赖: IsArtinianRing, IsArtinianRing.tfae, isFiniteLength_iff_isNoetherian_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian.mp
-/
theorem isArtinianRing_iff_isFiniteLength : IsArtinianRing R ↔ IsFiniteLength R R :=
  ⟨fun h => ((IsArtinianRing.tfae R R).out 2 3).mp h,
    fun h => (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2⟩

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself.
**Any such ring is both Artinian and Noetherian.**"]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsArtinianRing
  signature: R] : IsNoetherianRing R
  body: ((IsArtinianRing.tfae R R).out 2 1).mp ‹_›

中文:
实例 [是Artin环
  签名: R] : 是Noether环 R
  定义体: ((IsArtinianRing.tfae R R).out 2 1).mp ‹_›

Depends on / 依赖: IsArtinianRing, IsArtinianRing.tfae
-/
instance [IsArtinianRing R] : IsNoetherianRing R := ((IsArtinianRing.tfae R R).out 2 1).mp ‹_›

/--
theorem `isNoetherian_of_finite_isArtinian` / 定理 `isNoetherian_of_finite_isArtinian`

English:
theorem isNoetherian_of_finite_isArtinian
  statement: {R} [CommRing R] [Module R M]
  proof: by
  obtain ⟨s, fin, span⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  rw [← s.iUnion_of_singleton_coe]; rw [Submodule.span_iUnion] at span
  rw [← Set.finite_coe_iff] at fin
  rw [← isNoetherian_top_iff]; rw [← span]
  have _ (i : M) : IsNoetherian R (Submodule.span R {i}) := by
    rw [Lin

中文:
定理 isNoetherian_of_finite_isArtinian
  结论: {R} [交换环 R] [模 R M]
  证明: by
  obtain ⟨s, fin, span⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  rw [← s.iUnion_of_singleton_coe]; rw [Submodule.span_iUnion] at span
  rw [← Set.finite_coe_iff] at fin
  rw [← isNoetherian_top_iff]; rw [← span]
  have _ (i : M) : IsNoetherian R (Submodule.span R {i}) := by
    rw [Lin

Depends on / 依赖: Ideal.Quotient.mk, IsNoetherian, LinearMap, LinearMap.quotKerEquivRange, LinearMap.span_singleton_eq_range, Module, Module.finite_def.mp, Quotient, Set.finite_coe_iff, Submodule, Submodule.fg_def.mp, Submodule.span, Submodule.span_iUnion, fg_def, finite_coe_iff, finite_def, iUnion_of_singleton_coe, isNoetherian_iff, isNoetherian_iff_of_bijectiv, isNoetherian_top_iff
-/
theorem isNoetherian_of_finite_isArtinian {R} [CommRing R] [Module R M]
    [Module.Finite R M] [IsArtinian R M] : IsNoetherian R M := by
  obtain ⟨s, fin, span⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹_›)
  rw [← s.iUnion_of_singleton_coe]; rw [Submodule.span_iUnion] at span
  rw [← Set.finite_coe_iff] at fin
  rw [← isNoetherian_top_iff]; rw [← span]
  have _ (i : M) : IsNoetherian R (Submodule.span R {i}) := by
    rw [LinearMap.span_singleton_eq_range]; rw [← (LinearMap.quotKerEquivRange _).isNoetherian_iff]
    let e (I : Ideal R) : R ⧸ I ->ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨.id _, fun _ _ => rfl⟩
    rw [(e _).isNoetherian_iff_of_bijective Function.bijective_id]
    refine @instIsNoetherianRingOfIsArtinianRing _ _ ?_
    rw [IsArtinianRing]; rw [← (e _).isArtinian_iff_of_bijective Function.bijective_id]; rw [(LinearMap.quotKerEquivRange _).isArtinian_iff]
    infer_instance
  infer_instance

/--
theorem `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero` / 定理 `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`

English:
theorem IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  statement: {R} [CommRing R]
  proof: have eq := Ring.jacobson_eq_nilradical_of_krullDimLE_zero R
  let Spec := {I : Ideal R | I.IsPrime}
  have : Finite Spec :=
    (minimalPrimes.finite_of_isNoetherianRing R).subset Ideal.mem_minimalPrimes_of_krullDimLE_zero
  have (I : Spec) : I.1.IsPrime := I.2
  have (I : Spec) : IsSemisimpleRing (

中文:
定理 是Noether环.isArtinianRing_of_krullDimLE_zero
  结论: {R} [交换环 R]
  证明: have eq := Ring.jacobson_eq_nilradical_of_krullDimLE_zero R
  let Spec := {I : Ideal R | I.IsPrime}
  have : Finite Spec :=
    (minimalPrimes.finite_of_isNoetherianRing R).subset Ideal.mem_minimalPrimes_of_krullDimLE_zero
  have (I : Spec) : I.1.IsPrime := I.2
  have (I : Spec) : IsSemisimpleRing (

Depends on / 依赖: Finite, I.IsPrime, Ideal.Quotient.field, Ideal.mem_minimalPrimes_of_krullDimLE_zero, Ideal.quotientInfRingEquivPiQuotient, IsPrime, IsSemisimpleRing, Quotient, Ring.jacobson, Ring.jacobson_eq_nilradical_of_krullDimLE_zero, finite_of_isNoetherianRing, jacobson, jacobson_eq_nilradical_of_krullDimLE_zero, mem_minimalPrimes_of_krullDimLE_zero, minimalPrimes, minimalPrimes.finite_of_isNoetherianRing, nilradical_eq_sInf, quotientInfRingEquivPiQuotient, sInf_eq_iInf, subset
-/
theorem IsNoetherianRing.isArtinianRing_of_krullDimLE_zero {R} [CommRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 0 R] : IsArtinianRing R :=
  have eq := Ring.jacobson_eq_nilradical_of_krullDimLE_zero R
  let Spec := {I : Ideal R | I.IsPrime}
  have : Finite Spec :=
    (minimalPrimes.finite_of_isNoetherianRing R).subset Ideal.mem_minimalPrimes_of_krullDimLE_zero
  have (I : Spec) : I.1.IsPrime := I.2
  have (I : Spec) : IsSemisimpleRing (R ⧸ I.1) := let _ := Ideal.Quotient.field I.1; inferInstance
  have : IsSemisimpleRing (R ⧸ Ring.jacobson R) := by
    rw [eq]; rw [nilradical_eq_sInf]; rw [sInf_eq_iInf']
    exact (Ideal.quotientInfRingEquivPiQuotient _ fun I J ne =>
Ideal.isCoprime_of_isMaximal Subtype.coe_ne_coe.mpr ne).symm.isSemisimpleRing
  have : IsSemiprimaryRing R := ⟨this, eq ▸ IsNoetherianRing.isNilpotent_nilradical R⟩
  IsSemiprimaryRing.isNoetherian_iff_isArtinian.mp ‹_›

/--
theorem `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero` / 定理 `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`

English:
theorem isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
  given: {R} [CommRing R]
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨h, _⟩ => h.isArtinianRing_of_krullDimLE_zero⟩

中文:
定理 isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
  条件: {R} [交换环 R]
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨h, _⟩ => h.isArtinianRing_of_krullDimLE_zero⟩
-/
@[stacks 00KH] theorem isArtinianRing_iff_isNoetherianRing_krullDimLE_zero {R} [CommRing R] :
    IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨h, _⟩ => h.isArtinianRing_of_krullDimLE_zero⟩

/--
theorem `isArtinianRing_iff_krullDimLE_zero` / 定理 `isArtinianRing_iff_krullDimLE_zero`

English:
theorem isArtinianRing_iff_krullDimLE_zero
  given: {R : Type*} [CommRing R] [IsNoetherianRing R]
  proof: by
  rwa [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, and_iff_right]

中文:
定理 isArtinianRing_iff_krullDimLE_zero
  条件: {R : 类型} [交换环 R] [是Noether环 R]
  证明: by
  rwa [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, and_iff_right]

Depends on / 依赖: and_iff_right, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
-/
theorem isArtinianRing_iff_krullDimLE_zero {R : Type*} [CommRing R] [IsNoetherianRing R] :
    IsArtinianRing R ↔ Ring.KrullDimLE 0 R := by
  rwa [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero, and_iff_right]

/--
lemma `isArtinianRing_iff_isNilpotent_maximalIdeal` / 引理 `isArtinianRing_iff_isNilpotent_maximalIdeal`

English:
lemma isArtinianRing_iff_isNilpotent_maximalIdeal
  statement: (R : Type*) [CommRing R] [IsNoetherianRing R]
  proof: by
  rw [isArtinianRing_iff_krullDimLE_zero]; rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]; rw [← and_iff_left (a := Ring.KrullDimLE 0 R) ‹IsLocalRing R›]; rw [(Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 3 rfl rfl]; rw [IsLocalRing.isMaximal_iff]; rw [le_antisymm_i

中文:
引理 isArtinianRing_iff_isNilpotent_maximalIdeal
  结论: (R : 类型) [交换环 R] [是Noether环 R]
  证明: by
  rw [isArtinianRing_iff_krullDimLE_zero]; rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]; rw [← and_iff_left (a := Ring.KrullDimLE 0 R) ‹IsLocalRing R›]; rw [(Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 3 rfl rfl]; rw [IsLocalRing.isMaximal_iff]; rw [le_antisymm_i

Depends on / 依赖: Ideal.FG.isNilpotent_iff_le_nilradical, Ideal.radical_eq_top, IsLocalRing, IsLocalRing.isMaximal_iff, IsLocalRing.le_maximalIdeal, IsNoetherian, IsNoetherian.noetherian, KrullDimLE, Ring.KrullDimLE, Ring.krullDimLE_zero_and_isLocalRing_tfae, and_iff_left, and_iff_right, isArtinianRing_iff_krullDimLE_zero, isMaximal_iff, isNilpotent_iff_le_nilradical, krullDimLE_zero_and_isLocalRing_tfae, le_antisymm_iff, le_maximalIdeal, nilradical, noetherian
-/
lemma isArtinianRing_iff_isNilpotent_maximalIdeal (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : IsArtinianRing R ↔ IsNilpotent (IsLocalRing.maximalIdeal R) := by
  rw [isArtinianRing_iff_krullDimLE_zero]; rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]; rw [← and_iff_left (a := Ring.KrullDimLE 0 R) ‹IsLocalRing R›]; rw [(Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 3 rfl rfl]; rw [IsLocalRing.isMaximal_iff]; rw [le_antisymm_iff]; rw [and_iff_right]
  exact IsLocalRing.le_maximalIdeal (by simp [nilradical, Ideal.radical_eq_top])
