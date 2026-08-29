/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Finitely generated ideals

Lemmas about finiteness of ideal operations.
-/

public section

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `FG.map` / 定理 `FG.map`

English:
theorem FG.map
  given: {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R ->+* S)
  proof: by
  classical
    obtain ⟨s, hs⟩ := h
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image]; rw [← map_span]; rw [hs]

中文:
定理 FG.map
  条件: {R S : 类型} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R ->+* S)
  证明: by
  classical
    obtain ⟨s, hs⟩ := h
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image]; rw [← map_span]; rw [hs]
-/
theorem FG.map {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R ->+* S) :
    (I.map f).FG := by
  classical
    obtain ⟨s, hs⟩ := h
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image]; rw [← map_span]; rw [hs]

/--
theorem `fg_ker_comp` / 定理 `fg_ker_comp`

English:
theorem fg_ker_comp
  statement: {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R ->+* S)
  proof: by
  let : Algebra R S := RingHom.toAlgebra f
  let : Algebra R A := RingHom.toAlgebra (g.comp f)
  let : Algebra S A := RingHom.toAlgebra g
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinea

中文:
定理 fg_ker_comp
  结论: {R S A : 类型} [CommRing R] [CommRing S] [CommRing A] (f : R ->+* S)
  证明: by
  let : Algebra R S := RingHom.toAlgebra f
  let : Algebra R A := RingHom.toAlgebra (g.comp f)
  let : Algebra S A := RingHom.toAlgebra g
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinea

Depends on / 依赖: Algebra, Algebra.linearMap, IsScalarTower, IsScalarTower.of_algebraMap_eq, IsScalarTower.toAlgHom, RingHom, RingHom.toAlgebra, Submodule, Submodule.FG.restrictScalars_of_surjective, Submodule.fg_ker_comp, fg_ker_comp, g.comp, linearMap, of_algebraMap_eq, restrictScalars_of_surjective, toAlgHom, toAlgebra, toLinearMap
-/
theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R ->+* S)
    (g : S ->+* A) (hf : (RingHom.ker f).FG) (hg : (RingHom.ker g).FG)
    (hsur : Function.Surjective f) :
    (RingHom.ker (g.comp f)).FG := by
  let : Algebra R S := RingHom.toAlgebra f
  let : Algebra R A := RingHom.toAlgebra (g.comp f)
  let : Algebra S A := RingHom.toAlgebra g
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fg_ker_comp f₁ g₁ hf
    (Submodule.FG.restrictScalars_of_surjective hg hsur) hsur

/--
theorem `fg_of_fg_map_of_fg_inf_ker_of_surjective` / 定理 `fg_of_fg_map_of_fg_inf_ker_of_surjective`

English:
theorem fg_of_fg_map_of_fg_inf_ker_of_surjective
  statement: {R S : Type*} [CommRing R] [CommRing S]
  proof: by
  algebraize [f]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Module.compHom.toLinearMap f) ?_ hk
  have : RingHomSurjective f := ⟨hf⟩
  simpa [Ideal.map_eq_submodule_map] using! Submodule.FG.restrictScalars_of_surjective hmap hf

中文:
定理 fg_of_fg_map_of_fg_inf_ker_of_surjective
  结论: {R S : 类型} [CommRing R] [CommRing S]
  证明: by
  algebraize [f]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Module.compHom.toLinearMap f) ?_ hk
  have : RingHomSurjective f := ⟨hf⟩
  simpa [Ideal.map_eq_submodule_map] using! Submodule.FG.restrictScalars_of_surjective hmap hf

Depends on / 依赖: Ideal.map_eq_submodule_map, Module, Module.compHom.toLinearMap, RingHomSurjective, Submodule, Submodule.FG.restrictScalars_of_surjective, Submodule.fg_of_fg_map_of_fg_inf_ker, algebraize, compHom, fg_of_fg_map_of_fg_inf_ker, map_eq_submodule_map, restrictScalars_of_surjective, toLinearMap
-/
theorem fg_of_fg_map_of_fg_inf_ker_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R ->+* S} {I : Ideal R} (hmap : (I.map f).FG) (hk : (I ⊓ (RingHom.ker f)).FG)
    (hf : Function.Surjective f) : I.FG := by
  algebraize [f]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Module.compHom.toLinearMap f) ?_ hk
  have : RingHomSurjective f := ⟨hf⟩
  simpa [Ideal.map_eq_submodule_map] using! Submodule.FG.restrictScalars_of_surjective hmap hf

/--
theorem `exists_radical_pow_le_of_fg` / 定理 `exists_radical_pow_le_of_fg`

English:
theorem exists_radical_pow_le_of_fg
  given: {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG)
  proof: by
  suffices hJ : forall J : Ideal R, J.FG -> J <= I.radical -> exists n : Nat, J ^ n <= I by
    simpa using hJ I.radical h
  intro J hJ hJK
  induction J, hJ using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := hJK (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← 

中文:
定理 exists_radical_pow_le_of_fg
  条件: {R : 类型} [CommSemiring R] (I : Ideal R) (h : I.radical.FG)
  证明: by
  suffices hJ : forall J : Ideal R, J.FG -> J <= I.radical -> exists n : Nat, J ^ n <= I by
    simpa using hJ I.radical h
  intro J hJ hJK
  induction J, hJ using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := hJK (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← 

Depends on / 依赖: I.radical, J.FG, Set.mem_singleton, Set.singleton_subset_iff, Submodule, Submodule.fg_induction, add_eq_sup, fg_induction, mem_singleton, mem_sup_left, mem_sup_right, radical, singleton, singleton_subset_iff, span_le, span_singleton_pow, subset_span
-/
theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    exists n : Nat, I.radical ^ n <= I := by
  suffices hJ : forall J : Ideal R, J.FG -> J <= I.radical -> exists n : Nat, J ^ n <= I by
    simpa using hJ I.radical h
  intro J hJ hJK
  induction J, hJ using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := hJK (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  | sup J K _ _ hJ hK =>
obtain ⟨n, hn⟩ := hJ fun x hx => hJK mem_sup_left hx
obtain ⟨m, hm⟩ := hK fun x hx => hJK mem_sup_right hx
    use n + m
    rw [← add_eq_sup]; rw [add_pow]; rw [sum_eq_sup]; rw [Finset.sup_le_iff]
    refine fun i _ => mul_le_left.trans ?_
    obtain h | h := le_or_gt n i
    · exact mul_le_left.trans ((pow_le_pow_right h).trans hn)
    · exact mul_le_right.trans ((pow_le_pow_right (by lia)).trans hm)

/--
theorem `exists_pow_le_of_le_radical_of_fg_radical` / 定理 `exists_pow_le_of_le_radical_of_fg_radical`

English:
theorem exists_pow_le_of_le_radical_of_fg_radical
  statement: {R : Type*} [CommSemiring R] {I J : Ideal R}
  proof: by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  exact ⟨k, (pow_right_mono hIJ k).trans hk⟩

中文:
定理 exists_pow_le_of_le_radical_of_fg_radical
  结论: {R : 类型} [CommSemiring R] {I J : Ideal R}
  证明: by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  exact ⟨k, (pow_right_mono hIJ k).trans hk⟩

Depends on / 依赖: J.exists_radical_pow_le_of_fg, exists_radical_pow_le_of_fg, pow_right_mono
-/
theorem exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I J : Ideal R}
    (hIJ : I <= J.radical) (hJ : J.radical.FG) :
    exists k : Nat, I ^ k <= J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  exact ⟨k, (pow_right_mono hIJ k).trans hk⟩

/--
lemma `exists_pow_le_of_le_radical_of_fg` / 引理 `exists_pow_le_of_le_radical_of_fg`

English:
lemma exists_pow_le_of_le_radical_of_fg
  statement: {R : Type*} [CommSemiring R] {I J : Ideal R}
  proof: by
  induction I, h using Submodule.fg_induction with
  | singleton x =>
    simp only [submodule_span_eq, span_le, Set.singleton_subset_iff, SetLike.mem_coe] at h'
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, by simpa [span_singleton_pow, span_le]⟩
  | sup I₁ I₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁ (

中文:
引理 exists_pow_le_of_le_radical_of_fg
  结论: {R : 类型} [CommSemiring R] {I J : Ideal R}
  证明: by
  induction I, h using Submodule.fg_induction with
  | singleton x =>
    simp only [submodule_span_eq, span_le, Set.singleton_subset_iff, SetLike.mem_coe] at h'
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, by simpa [span_singleton_pow, span_le]⟩
  | sup I₁ I₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁ (

Depends on / 依赖: Set.singleton_subset_iff, SetLike, SetLike.mem_coe, Submodule, Submodule.fg_induction, fg_induction, le_sup_left, le_sup_left.trans, le_sup_right, le_sup_right.trans, mem_coe, singleton, singleton_subset_iff, span_le, span_singleton_pow, submodule_span_eq, sup_le, sup_pow_add_le_pow_sup_pow, sup_pow_add_le_pow_sup_pow.trans
-/
lemma exists_pow_le_of_le_radical_of_fg {R : Type*} [CommSemiring R] {I J : Ideal R}
    (h' : I <= J.radical) (h : I.FG) :
    exists n : Nat, I ^ n <= J := by
  induction I, h using Submodule.fg_induction with
  | singleton x =>
    simp only [submodule_span_eq, span_le, Set.singleton_subset_iff, SetLike.mem_coe] at h'
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, by simpa [span_singleton_pow, span_le]⟩
  | sup I₁ I₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁ (le_sup_left.trans h')
    obtain ⟨n₂, hn₂⟩ := h₂ (le_sup_right.trans h')
    use n₁ + n₂
    exact sup_pow_add_le_pow_sup_pow.trans (sup_le hn₁ hn₂)

/--
theorem `_root_.Submodule.FG.smul` / 定理 `_root_.Submodule.FG.smul`

English:
theorem _root_.Submodule.FG.smul
  statement: {I : Ideal R} [I.IsTwoSided] {N : Submodule R M}
  proof: by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, rfl⟩ := hN
  classical rw [Submodule.span_smul_span, ← s.coe_smul]
  exact ⟨_, rfl⟩

中文:
定理 _root_.Submodule.FG.smul
  结论: {I : Ideal R} [I.IsTwoSided] {N : Submodule R M}
  证明: by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, rfl⟩ := hN
  classical rw [Submodule.span_smul_span, ← s.coe_smul]
  exact ⟨_, rfl⟩

Depends on / 依赖: Submodule, Submodule.span_smul_span, classical, coe_smul, s.coe_smul, span_smul_span
-/
theorem _root_.Submodule.FG.smul {I : Ideal R} [I.IsTwoSided] {N : Submodule R M}
    (hI : I.FG) (hN : N.FG) : (I • N).FG := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, rfl⟩ := hN
  classical rw [Submodule.span_smul_span, ← s.coe_smul]
  exact ⟨_, rfl⟩

/--
theorem `FG.mul` / 定理 `FG.mul`

English:
theorem FG.mul
  given: {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG)
  statement: (I * J).FG
  proof: Submodule.FG.smul hI hJ

中文:
定理 FG.mul
  条件: {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG)
  结论: (I * J).FG
  证明: Submodule.FG.smul hI hJ

Depends on / 依赖: Submodule, Submodule.FG.smul
-/
theorem FG.mul {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG) : (I * J).FG :=
  Submodule.FG.smul hI hJ

/--
theorem `FG.pow` / 定理 `FG.pow`

English:
theorem FG.pow
  given: {I : Ideal R} [I.IsTwoSided] {n : Nat} (hI : I.FG)
  statement: (I ^ n).FG
  proof: n.rec (by rw [I.pow_zero, one_eq_top]; exact fg_top R) fun n ih => by
    rw [IsTwoSided.pow_succ]
    exact hI.mul ih

中文:
定理 FG.pow
  条件: {I : Ideal R} [I.IsTwoSided] {n : 自然数} (hI : I.FG)
  结论: (I ^ n).FG
  证明: n.rec (by rw [I.pow_zero, one_eq_top]; exact fg_top R) fun n ih => by
    rw [IsTwoSided.pow_succ]
    exact hI.mul ih

Depends on / 依赖: I.pow_zero, IsTwoSided, IsTwoSided.pow_succ, fg_top, hI.mul, n.rec, one_eq_top, pow_succ, pow_zero
-/
theorem FG.pow {I : Ideal R} [I.IsTwoSided] {n : Nat} (hI : I.FG) : (I ^ n).FG :=
  n.rec (by rw [I.pow_zero, one_eq_top]; exact fg_top R) fun n ih => by
    rw [IsTwoSided.pow_succ]
    exact hI.mul ih

end Ideal
