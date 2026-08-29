/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Functoriality of the prime spectrum

In this file we define the induced map on prime spectra induced by a ring homomorphism.

## Main definitions

* `PrimeSpectrum.comap`: The induced map on prime spectra by a ring homomorphism. The proof that
  it is continuous is in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

-/

@[expose] public section

universe u v

variable (R : Type u) (S : Type v)

open PrimeSpectrum

/--
Definition of `PrimeSpectrum.comap` / `PrimeSpectrum.comap` 的定义

English:
definition PrimeSpectrum.comap
  signature: {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R ->+* S)
  body: ⟨Ideal.comap f p.asIdeal, inferInstance⟩

中文:
定义 PrimeSpectrum.comap
  签名: {R S : 类型} [CommSemiring R] [CommSemiring S] (f : R ->+* S)
  定义体: ⟨Ideal.comap f p.asIdeal, inferInstance⟩

Depends on / 依赖: Ideal.comap, asIdeal, p.asIdeal
-/
def PrimeSpectrum.comap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R ->+* S)
    (p : PrimeSpectrum S) : PrimeSpectrum R :=
  ⟨Ideal.comap f p.asIdeal, inferInstance⟩

namespace PrimeSpectrum

open RingHom

variable {R S} {S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring S']

variable (f : R ->+* S)

@[simp]
/--
theorem `comap_asIdeal` / 定理 `comap_asIdeal`

English:
theorem comap_asIdeal
  given: (y : PrimeSpectrum S)
  proof: rfl

@[simp]

中文:
定理 comap_asIdeal
  条件: (y : PrimeSpectrum S)
  证明: rfl

@[simp]
-/
theorem comap_asIdeal (y : PrimeSpectrum S) :
    (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: comap (RingHom.id R) = fun x => x
  proof: rfl

@[simp]

中文:
定理 comap_id
  结论: comap (RingHom.id R) = fun x => x
  证明: rfl

@[simp]
-/
theorem comap_id : comap (RingHom.id R) = fun x => x :=
  rfl

@[simp]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (f : R ->+* S) (g : S ->+* S')
  proof: rfl

中文:
定理 comap_comp
  条件: (f : R ->+* S) (g : S ->+* S')
  证明: rfl
-/
theorem comap_comp (f : R ->+* S) (g : S ->+* S') :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl

/--
theorem `comap_comp_apply` / 定理 `comap_comp_apply`

English:
theorem comap_comp_apply
  given: (f : R ->+* S) (g : S ->+* S') (x : PrimeSpectrum S')
  proof: rfl

中文:
定理 comap_comp_apply
  条件: (f : R ->+* S) (g : S ->+* S') (x : PrimeSpectrum S')
  证明: rfl
-/
theorem comap_comp_apply (f : R ->+* S) (g : S ->+* S') (x : PrimeSpectrum S') :
    comap (g.comp f) x = comap f (comap g x) :=
  rfl

/--
theorem `preimage_comap_zeroLocus_aux` / 定理 `preimage_comap_zeroLocus_aux`

English:
theorem preimage_comap_zeroLocus_aux
  given: (f : R ->+* S) (s : Set R)
  proof: by
  ext x
  simp [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus]

@[simp]

中文:
定理 preimage_comap_zeroLocus_aux
  条件: (f : R ->+* S) (s : Set R)
  证明: by
  ext x
  simp [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus]

@[simp]

Depends on / 依赖: Set.image_subset_iff, Set.mem_preimage, image_subset_iff, mem_preimage, mem_zeroLocus
-/
theorem preimage_comap_zeroLocus_aux (f : R ->+* S) (s : Set R) :
    comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) := by
  ext x
  simp [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus]

@[simp]
/--
theorem `preimage_comap_zeroLocus` / 定理 `preimage_comap_zeroLocus`

English:
theorem preimage_comap_zeroLocus
  given: (s : Set R)
  proof: preimage_comap_zeroLocus_aux f s

中文:
定理 preimage_comap_zeroLocus
  条件: (s : Set R)
  证明: preimage_comap_zeroLocus_aux f s

Depends on / 依赖: preimage_comap_zeroLocus_aux
-/
theorem preimage_comap_zeroLocus (s : Set R) :
    comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_comap_zeroLocus_aux f s

/--
theorem `comap_injective_of_surjective` / 定理 `comap_injective_of_surjective`

English:
theorem comap_injective_of_surjective
  given: (f : R ->+* S) (hf : Function.Surjective f)
  proof: fun x y h =>
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))

中文:
定理 comap_injective_of_surjective
  条件: (f : R ->+* S) (hf : Function.Surjective f)
  证明: fun x y h =>
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))
-/
theorem comap_injective_of_surjective (f : R ->+* S) (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun x y h =>
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: R S] (p
  body: rfl

中文:
实例 [Algebra
  签名: R S] (p
  定义体: rfl
-/
instance [Algebra R S] (p : PrimeSpectrum S) :
    p.asIdeal.LiesOver (p.comap <| algebraMap R S).asIdeal where
  over := rfl

/-- `RingHom.comap` of an isomorphism of rings as an equivalence of their prime spectra. -/
@[simps apply]
/--
Definition of `comapEquiv` / `comapEquiv` 的定义

English:
definition comapEquiv
  signature: (e : R ≃+* S)
  body: comap e.symm.toRingHom
  invFun := comap e.toRingHom
  left_inv x := by
    rw [← comap_comp_apply]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]
    rfl
  right_inv x := by
    rw [← comap_comp_apply]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRi

中文:
定义 comapEquiv
  签名: (e : R ≃+* S)
  定义体: comap e.symm.toRingHom
  invFun := comap e.toRingHom
  left_inv x := by
    rw [← comap_comp_apply]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]
    rfl
  right_inv x := by
    rw [← comap_comp_apply]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRi

Depends on / 依赖: e.symm.toRingHom, toRingHom
-/
def comapEquiv (e : R ≃+* S) : PrimeSpectrum R ≃o PrimeSpectrum S where
  toFun := comap e.symm.toRingHom
  invFun := comap e.toRingHom
  left_inv x := by
    rw [← comap_comp_apply]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.symm_comp]
    rfl
  right_inv x := by
    rw [← comap_comp_apply]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.toRingHom_eq_coe]; rw [RingEquiv.comp_symm]
    rfl
  map_rel_iff' {I J} := Ideal.comap_le_comap_iff_of_surjective _ e.symm.surjective ..

/--
lemma `comapEquiv_symm` / 引理 `comapEquiv_symm`

English:
lemma comapEquiv_symm
  given: (e : R ≃+* S)
  statement: (comapEquiv e).symm = comapEquiv e.symm
  proof: rfl

中文:
引理 comapEquiv_symm
  条件: (e : R ≃+* S)
  结论: (comapEquiv e).symm = comapEquiv e.symm
  证明: rfl
-/
@[simp] lemma comapEquiv_symm (e : R ≃+* S) : (comapEquiv e).symm = comapEquiv e.symm := rfl

section Pi

variable {ι} (R : ι -> Type*) [forall i, CommSemiring (R i)]

/--
Definition of `sigmaToPi` / `sigmaToPi` 的定义

English:
definition sigmaToPi
  signature: : (Σ i, PrimeSpectrum (R i)) -> PrimeSpectrum (Π i, R i)

中文:
定义 sigmaToPi
  签名: : (Σ i, PrimeSpectrum (R i)) -> PrimeSpectrum (Π i, R i)
-/
def sigmaToPi : (Σ i, PrimeSpectrum (R i)) -> PrimeSpectrum (Π i, R i)
  | ⟨i, p⟩ => comap (Pi.evalRingHom R i) p

@[simp]
/--
lemma `sigmaToPi_apply` / 引理 `sigmaToPi_apply`

English:
lemma sigmaToPi_apply
  given: (i : ι) (p : PrimeSpectrum (R i))
  proof: rfl

@[deprecated (since := "2026-04-17")]
alias coe_sigmaToPi_asIdeal := sigmaToPi_apply

中文:
引理 sigmaToPi_apply
  条件: (i : ι) (p : PrimeSpectrum (R i))
  证明: rfl

@[deprecated (since := "2026-04-17")]
alias coe_sigmaToPi_asIdeal := sigmaToPi_apply
-/
lemma sigmaToPi_apply (i : ι) (p : PrimeSpectrum (R i)) :
    sigmaToPi R ⟨i, p⟩ = comap (Pi.evalRingHom R i) p :=
  rfl

@[deprecated (since := "2026-04-17")]
alias coe_sigmaToPi_asIdeal := sigmaToPi_apply

/--
theorem `sigmaToPi_injective` / 定理 `sigmaToPi_injective`

English:
theorem sigmaToPi_injective
  statement: (sigmaToPi R).Injective
  proof: fun ⟨i, p⟩ ⟨j, q⟩ eq => by
  classical
  obtain rfl | ne := eq_or_ne i j
  · congr; ext x
    simpa using congr_arg (Function.update (0 : forall i, R i) i x in ·.asIdeal) eq
  · refine (p.1.ne_top_iff_one.mp p.2.ne_top ?_).elim
    have : Function.update (1 : forall i, R i) j 0 in (sigmaToPi R ⟨j, q

中文:
定理 sigmaToPi_injective
  结论: (sigmaToPi R).Injective
  证明: fun ⟨i, p⟩ ⟨j, q⟩ eq => by
  classical
  obtain rfl | ne := eq_or_ne i j
  · congr; ext x
    simpa using congr_arg (Function.update (0 : forall i, R i) i x in ·.asIdeal) eq
  · refine (p.1.ne_top_iff_one.mp p.2.ne_top ?_).elim
    have : Function.update (1 : forall i, R i) j 0 in (sigmaToPi R ⟨j, q

Depends on / 依赖: Function, Function.update, Function.update_of_ne, asIdeal, classical, congr_arg, eq_or_ne, ne_top, ne_top_iff_one, ne_top_iff_one.mp, sigmaToPi, update, update_of_ne
-/
theorem sigmaToPi_injective : (sigmaToPi R).Injective := fun ⟨i, p⟩ ⟨j, q⟩ eq => by
  classical
  obtain rfl | ne := eq_or_ne i j
  · congr; ext x
    simpa using congr_arg (Function.update (0 : forall i, R i) i x in ·.asIdeal) eq
  · refine (p.1.ne_top_iff_one.mp p.2.ne_top ?_).elim
    have : Function.update (1 : forall i, R i) j 0 in (sigmaToPi R ⟨j, q⟩).asIdeal := by simp
    simpa [← eq, Function.update_of_ne ne]

variable [Infinite ι] [forall i, Nontrivial (R i)]

/--
theorem `exists_maximal_notMem_range_sigmaToPi_of_infinite` / 定理 `exists_maximal_notMem_range_sigmaToPi_of_infinite`

English:
theorem exists_maximal_notMem_range_sigmaToPi_of_infinite
  proof: by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i => r i * x i, funext fun i => show dite _ _ _ = _ from ?_⟩
      simp_rw

中文:
定理 exists_maximal_notMem_range_sigmaToPi_of_infinite
  证明: by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i => r i * x i, funext fun i => show dite _ _ _ = _ from ?_⟩
      simp_rw

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mrange, DFinsupp, DFinsupp.coeFnAddMonoidHom, DFinsupp.notMem_support_iff.mp, Ideal.ne_top_iff_one, J.exists_le_maximal, classical, coeFnAddMonoidHom, dite_eq_left_iff, dite_eq_left_iff.mpr, exists_le_maximal, instances, mrange, mul_zero, ne_top_iff_one, notMem_support_iff, simp_rw, smul_mem, support
-/
theorem exists_maximal_notMem_range_sigmaToPi_of_infinite :
    exists (I : Ideal (Π i, R i)) (_ : I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaToPi R) := by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i => r i * x i, funext fun i => show dite _ _ _ = _ from ?_⟩
      simp_rw +instances [DFinsupp.coeFnAddMonoidHom]
      refine dite_eq_left_iff.mpr fun h => ?_
      rw [DFinsupp.notMem_support_iff.mp h]; rw [mul_zero] }
have ⟨I, max, le⟩ := J.exists_le_maximal (Ideal.ne_top_iff_one _).mpr by
    -- take a maximal ideal I containing J
    rintro ⟨x, hx⟩
    have ⟨i, hi⟩ := x.support.exists_notMem
    simpa [DFinsupp.coeFnAddMonoidHom, DFinsupp.notMem_support_iff.mp hi] using congr_fun hx i
  refine ⟨I, max, fun ⟨⟨i, p⟩, eq⟩ => ?_⟩
  -- then I is not in the range of `sigmaToPi`
  have : ⇑(DFinsupp.single i 1) ∉ (sigmaToPi R ⟨i, p⟩).asIdeal := by
    simpa using p.1.ne_top_iff_one.mp p.2.ne_top
  rw [eq] at this
  exact this (le ⟨.single i 1, rfl⟩)

/--
theorem `sigmaToPi_not_surjective_of_infinite` / 定理 `sigmaToPi_not_surjective_of_infinite`

English:
theorem sigmaToPi_not_surjective_of_infinite
  statement: ¬ (sigmaToPi R).Surjective
  proof: fun surj =>
  have ⟨_, _, notMem⟩ := exists_maximal_notMem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ notMem) ⟨⟩

中文:
定理 sigmaToPi_not_surjective_of_infinite
  结论: ¬ (sigmaToPi R).Surjective
  证明: fun surj =>
  have ⟨_, _, notMem⟩ := exists_maximal_notMem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ notMem) ⟨⟩

Depends on / 依赖: PathConnectedSpace, PathConnectedSpace.connectedSpace, connectedSpace
-/
theorem sigmaToPi_not_surjective_of_infinite : ¬ (sigmaToPi R).Surjective := fun surj =>
  have ⟨_, _, notMem⟩ := exists_maximal_notMem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ notMem) ⟨⟩

/--
lemma `exists_comap_evalRingHom_eq` / 引理 `exists_comap_evalRingHom_eq`

English:
lemma exists_comap_evalRingHom_eq
  proof: by
  classical
  cases nonempty_fintype ι
  let e (i) : Π i, R i := Function.update 1 i 0
  have H : ∏ i, e i = 0 := by
    ext j
    rw [Finset.prod_apply]; rw [Pi.zero_apply]; rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    simp [e]
  obtain ⟨i, hi⟩ : exists i, e i in p.asIdeal := by
    simpa [←

中文:
引理 exists_comap_evalRingHom_eq
  证明: by
  classical
  cases nonempty_fintype ι
  let e (i) : Π i, R i := Function.update 1 i 0
  have H : ∏ i, e i = 0 := by
    ext j
    rw [Finset.prod_apply]; rw [Pi.zero_apply]; rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    simp [e]
  obtain ⟨i, hi⟩ : exists i, e i in p.asIdeal := by
    simpa [←

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_apply, Finset.prod_eq_zero, Function, Function.Surjective, Function.update, Ideal.IsPrime.prod_mem_iff, IsPrime, Pi.evalRingHom, Pi.zero_apply, RingHom, RingHom.ker, RingHomSurjective, RingHomSurjective.is_surjective, Surjective, asIdeal, classical, convert, evalRingHom
-/
lemma exists_comap_evalRingHom_eq
    {ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)] [Finite ι]
    (p : PrimeSpectrum (Π i, R i)) :
    exists (i : ι) (q : PrimeSpectrum (R i)), comap (Pi.evalRingHom R i) q = p := by
  classical
  cases nonempty_fintype ι
  let e (i) : Π i, R i := Function.update 1 i 0
  have H : ∏ i, e i = 0 := by
    ext j
    rw [Finset.prod_apply]; rw [Pi.zero_apply]; rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    simp [e]
  obtain ⟨i, hi⟩ : exists i, e i in p.asIdeal := by
    simpa [← H, Ideal.IsPrime.prod_mem_iff] using p.asIdeal.zero_mem
  let h₁ : Function.Surjective (Pi.evalRingHom R i) := RingHomSurjective.is_surjective
  have h₂ : RingHom.ker (Pi.evalRingHom R i) <= p.asIdeal := by
    intro x hx
    convert! p.asIdeal.mul_mem_left x hi
    ext j
    by_cases hj : i = j
    · subst hj; simpa [e]
    · simp [e, Function.update_of_ne (.symm hj)]
  have : (p.asIdeal.map (Pi.evalRingHom R i)).comap (Pi.evalRingHom R i) = p.asIdeal := by
    rwa [Ideal.comap_map_of_surjective _ h₁, sup_eq_left]
  exact ⟨i, ⟨_, Ideal.map_isPrime_of_surjective h₁ h₂⟩, PrimeSpectrum.ext this⟩

/--
lemma `sigmaToPi_bijective` / 引理 `sigmaToPi_bijective`

English:
lemma sigmaToPi_bijective
  given: {ι : Type*} (R : ι -> Type*) [forall i, CommRing (R i)] [Finite ι]
  proof: by
  refine ⟨sigmaToPi_injective R, ?_⟩
  intro q
  obtain ⟨i, q, rfl⟩ := exists_comap_evalRingHom_eq q
  exact ⟨⟨i, q⟩, rfl⟩

中文:
引理 sigmaToPi_bijective
  条件: {ι : 类型} (R : ι -> 类型) [对任意 i, CommRing (R i)] [Finite ι]
  证明: by
  refine ⟨sigmaToPi_injective R, ?_⟩
  intro q
  obtain ⟨i, q, rfl⟩ := exists_comap_evalRingHom_eq q
  exact ⟨⟨i, q⟩, rfl⟩

Depends on / 依赖: exists_comap_evalRingHom_eq, sigmaToPi_injective
-/
lemma sigmaToPi_bijective {ι : Type*} (R : ι -> Type*) [forall i, CommRing (R i)] [Finite ι] :
    Function.Bijective (sigmaToPi R) := by
  refine ⟨sigmaToPi_injective R, ?_⟩
  intro q
  obtain ⟨i, q, rfl⟩ := exists_comap_evalRingHom_eq q
  exact ⟨⟨i, q⟩, rfl⟩

/--
lemma `iUnion_range_comap_comp_evalRingHom` / 引理 `iUnion_range_comap_comp_evalRingHom`

English:
lemma iUnion_range_comap_comp_evalRingHom
  proof: by
  simp_rw [comap_comp]
  apply subset_antisymm
  · exact Set.iUnion_subset fun _ => Set.range_comp_subset_range _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, p, rfl⟩ := exists_comap_evalRingHom_eq p
    exact Set.mem_iUnion_of_mem i ⟨p, rfl⟩

中文:
引理 iUnion_range_comap_comp_evalRingHom
  证明: by
  simp_rw [comap_comp]
  apply subset_antisymm
  · exact Set.iUnion_subset fun _ => Set.range_comp_subset_range _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, p, rfl⟩ := exists_comap_evalRingHom_eq p
    exact Set.mem_iUnion_of_mem i ⟨p, rfl⟩

Depends on / 依赖: Set.iUnion_subset, Set.mem_iUnion_of_mem, Set.range_comp_subset_range, comap_comp, exists_comap_evalRingHom_eq, iUnion_subset, mem_iUnion_of_mem, range_comp_subset_range, simp_rw, subset_antisymm
-/
lemma iUnion_range_comap_comp_evalRingHom
    {ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)] [Finite ι]
    {S : Type*} [CommRing S] (f : S ->+* Π i, R i) :
    ⋃ i, Set.range (comap ((Pi.evalRingHom R i).comp f)) = Set.range (comap f) := by
  simp_rw [comap_comp]
  apply subset_antisymm
  · exact Set.iUnion_subset fun _ => Set.range_comp_subset_range _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, p, rfl⟩ := exists_comap_evalRingHom_eq p
    exact Set.mem_iUnion_of_mem i ⟨p, rfl⟩

end Pi

end PrimeSpectrum

section SpecOfSurjective

open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R ->+* S)
variable {R}

/--
theorem `image_comap_zeroLocus_eq_zeroLocus_comap` / 定理 `image_comap_zeroLocus_eq_zeroLocus_comap`

English:
theorem image_comap_zeroLocus_eq_zeroLocus_comap
  given: (hf : Surjective f) (I : Ideal S)
  proof: by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f <= p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surject

中文:
定理 image_comap_zeroLocus_eq_zeroLocus_comap
  条件: (hf : Surjective f) (I : Ideal S)
  证明: by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f <= p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surject

Depends on / 依赖: Ideal.comap_mono, Ideal.map_isPrime_of_surjective, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective, Ideal.mem_map_of_mem, Set.ext_iff, Set.mem_image, SetLike, SetLike.coe_subset_coe, asIdeal, bot_le, coe_subset_coe, comap_asIdeal, comap_mono, ext_iff, h_I_p, map_isPrime_of_surjective, mem_comap, mem_image, mem_map_iff_of_surjective
-/
theorem image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) := by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f <= p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      rw [comap_asIdeal]; rw [Ideal.mem_comap]; rw [Ideal.mem_map_iff_of_surjective f hf]
      refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine p.asIdeal.sub_mem hx' (hp ?_)
      rwa [mem_ker, map_sub, sub_eq_zero]

/--
theorem `range_comap_of_surjective` / 定理 `range_comap_of_surjective`

English:
theorem range_comap_of_surjective
  given: (hf : Surjective f)
  proof: by
  rw [← Set.image_univ]
  convert! image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

中文:
定理 range_comap_of_surjective
  条件: (hf : Surjective f)
  证明: by
  rw [← Set.image_univ]
  convert! image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

Depends on / 依赖: Set.image_univ, convert, image_comap_zeroLocus_eq_zeroLocus_comap, image_univ, zeroLocus_bot
-/
theorem range_comap_of_surjective (hf : Surjective f) :
    Set.range (comap f) = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  convert! image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

variable {S}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Ideal.primeSpectrumOrderIsoZeroLocusOfSurj` / `Ideal.primeSpectrumOrderIsoZeroLocusOfSurj` 的定义

English:
definition Ideal.primeSpectrumOrderIsoZeroLocusOfSurj
  signature: (hf : Surjective f) {I : Ideal R}
  body: ⟨p.comap f, hI.symm.trans_le (Ideal.ker_le_comap f)⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ => ⟨p.map f, p.map_isPrime_of_surjective hf (hI.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective f hf
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
 

中文:
定义 Ideal.primeSpectrumOrderIsoZeroLocusOfSurj
  签名: (hf : Surjective f) {I : Ideal R}
  定义体: ⟨p.comap f, hI.symm.trans_le (Ideal.ker_le_comap f)⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ => ⟨p.map f, p.map_isPrime_of_surjective hf (hI.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective f hf
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
 
-/
noncomputable def Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (hf : Surjective f) {I : Ideal R}
    (hI : RingHom.ker f = I) : PrimeSpectrum S ≃o (PrimeSpectrum.zeroLocus (R := R) I) where
  toFun p := ⟨p.comap f, hI.symm.trans_le (Ideal.ker_le_comap f)⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ => ⟨p.map f, p.map_isPrime_of_surjective hf (hI.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective f hf
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
    simp only [Subtype.mk.injEq, PrimeSpectrum.ext_iff, comap_asIdeal]
exact (p.comap_map_of_surjective f hf).trans sup_eq_left.mpr (hI.trans_le hp)
  map_rel_iff' {a b} := by
    change a.asIdeal.comap _ <= b.asIdeal.comap _ ↔ a <= b
    rw [← Ideal.map_le_iff_le_comap]; rw [Ideal.map_comap_of_surjective f hf]; rw [PrimeSpectrum.asIdeal_le_asIdeal]

/--
Definition of `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` / `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` 的定义

English:
definition Ideal.primeSpectrumQuotientOrderIsoZeroLocus
  signature: (I : Ideal R)
  body: primeSpectrumOrderIsoZeroLocusOfSurj (Quotient.mk I) Quotient.mk_surjective I.mk_ker

中文:
定义 Ideal.primeSpectrumQuotientOrderIsoZeroLocus
  签名: (I : Ideal R)
  定义体: primeSpectrumOrderIsoZeroLocusOfSurj (Quotient.mk I) Quotient.mk_surjective I.mk_ker
-/
noncomputable def Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R := R) I) :=
  primeSpectrumOrderIsoZeroLocusOfSurj (Quotient.mk I) Quotient.mk_surjective I.mk_ker

/--
lemma `PrimeSpectrum.mem_range_comap_iff` / 引理 `PrimeSpectrum.mem_range_comap_iff`

English:
lemma PrimeSpectrum.mem_range_comap_iff
  given: {p : PrimeSpectrum R}
  proof: by
  refine ⟨fun ⟨q, hq⟩ => by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

中文:
引理 PrimeSpectrum.mem_range_comap_iff
  条件: {p : PrimeSpectrum R}
  证明: by
  refine ⟨fun ⟨q, hq⟩ => by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

Depends on / 依赖: Ideal.comap_map_eq_self_iff_of_isPrime, PrimeSpectrum, PrimeSpectrum.ext, comap_map_eq_self_iff_of_isPrime
-/
lemma PrimeSpectrum.mem_range_comap_iff {p : PrimeSpectrum R} :
    p in Set.range (comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨fun ⟨q, hq⟩ => by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

open TensorProduct

/--
lemma `PrimeSpectrum.nontrivial_iff_mem_rangeComap` / 引理 `PrimeSpectrum.nontrivial_iff_mem_rangeComap`

English:
lemma PrimeSpectrum.nontrivial_iff_mem_rangeComap
  statement: {S : Type*} [CommRing S]
  proof: by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k otimes[R] S)
    use PrimeSpectrum.comap (Algebra.TensorProduct.includeRight).toRingHom ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.comap_comp_apply]; rw [← Algebra.TensorPr

中文:
引理 PrimeSpectrum.nontrivial_iff_mem_rangeComap
  结论: {S : 类型} [CommRing S]
  证明: by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k otimes[R] S)
    use PrimeSpectrum.comap (Algebra.TensorProduct.includeRight).toRingHom ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.comap_comp_apply]; rw [← Algebra.TensorPr

Depends on / 依赖: Algebra, Algebra.TensorP, Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, Algebra.TensorProduct.includeRight, Ideal.eq_bot_of_prime, Ideal.exists_maximal, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.comap_comp_apply, ResidueField, RingHom, RingHom.ker_eq_comap_bot, TensorP, TensorProduct, asIdeal, comap_comp_apply, eq_bot_of_prime, exists_maximal, hm.isPrime, includeLeftRingHom_comp_algebraMap
-/
lemma PrimeSpectrum.nontrivial_iff_mem_rangeComap {S : Type*} [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Nontrivial (p.asIdeal.ResidueField otimes[R] S) ↔ p in Set.range (comap (algebraMap R S)) := by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k otimes[R] S)
    use PrimeSpectrum.comap (Algebra.TensorProduct.includeRight).toRingHom ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.comap_comp_apply]; rw [← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]; rw [comap_comp_apply]
    simp [Ideal.eq_bot_of_prime, k, ← RingHom.ker_eq_comap_bot]
  · obtain ⟨q, rfl⟩ := h
    let f : k otimes[R] S ->ₐ[R] q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) rfl)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ => Commute.all ..)
    exact RingHom.domain_nontrivial f.toRingHom

/--
lemma `RingHom.strictMono_comap_of_surjective` / 引理 `RingHom.strictMono_comap_of_surjective`

English:
lemma RingHom.strictMono_comap_of_surjective
  statement: {S : Type*} [CommRing S]
  proof: fun _ _ h => (Ideal.relIsoOfSurjective _ hf).strictMono h

中文:
引理 RingHom.strictMono_comap_of_surjective
  结论: {S : 类型} [CommRing S]
  证明: fun _ _ h => (Ideal.relIsoOfSurjective _ hf).strictMono h

Depends on / 依赖: Ideal.relIsoOfSurjective, relIsoOfSurjective, strictMono
-/
lemma RingHom.strictMono_comap_of_surjective {S : Type*} [CommRing S]
    {f : R ->+* S} (hf : Function.Surjective f) : StrictMono (comap f) :=
  fun _ _ h => (Ideal.relIsoOfSurjective _ hf).strictMono h

end SpecOfSurjective

section ResidueField

variable {R : Type*} [CommRing R]

/--
lemma `PrimeSpectrum.residueField_comap` / 引理 `PrimeSpectrum.residueField_comap`

English:
lemma PrimeSpectrum.residueField_comap
  given: (I : PrimeSpectrum R)
  proof: by
  rw [Set.range_unique]; rw [Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x => Ideal.algebraMap_residueField_eq_zero)

中文:
引理 PrimeSpectrum.residueField_comap
  条件: (I : PrimeSpectrum R)
  证明: by
  rw [Set.range_unique]; rw [Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x => Ideal.algebraMap_residueField_eq_zero)

Depends on / 依赖: Ideal.algebraMap_residueField_eq_zero, Ideal.ext, PrimeSpectrum, PrimeSpectrum.ext, Set.range_unique, Set.singleton_eq_singleton_iff, algebraMap_residueField_eq_zero, range_unique, singleton_eq_singleton_iff
-/
lemma PrimeSpectrum.residueField_comap (I : PrimeSpectrum R) :
    Set.range (comap (algebraMap R I.asIdeal.ResidueField)) = {I} := by
  rw [Set.range_unique]; rw [Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x => Ideal.algebraMap_residueField_eq_zero)

end ResidueField

variable {R S} in
/--
theorem `IsLocalHom.of_comap_surjective` / 定理 `IsLocalHom.of_comap_surjective`

English:
theorem IsLocalHom.of_comap_surjective
  statement: [CommSemiring R] [CommSemiring S] (f : R ->+* S)
  proof: by
    by_contra hx
    obtain ⟨p, hp, _⟩ := exists_max_ideal_of_mem_nonunits hx
    obtain ⟨⟨q, hqp⟩, hq⟩ := hf ⟨p, hp.isPrime⟩
    simp only [PrimeSpectrum.ext_iff, comap_asIdeal] at hq
    exact hqp.ne_top (q.eq_top_of_isUnit_mem (q.mem_comap.mp (by rwa [hq])) hfx)

中文:
定理 IsLocalHom.of_comap_surjective
  结论: [CommSemiring R] [CommSemiring S] (f : R ->+* S)
  证明: by
    by_contra hx
    obtain ⟨p, hp, _⟩ := exists_max_ideal_of_mem_nonunits hx
    obtain ⟨⟨q, hqp⟩, hq⟩ := hf ⟨p, hp.isPrime⟩
    simp only [PrimeSpectrum.ext_iff, comap_asIdeal] at hq
    exact hqp.ne_top (q.eq_top_of_isUnit_mem (q.mem_comap.mp (by rwa [hq])) hfx)

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.ext_iff, comap_asIdeal, eq_top_of_isUnit_mem, exists_max_ideal_of_mem_nonunits, ext_iff, hp.isPrime, hqp.ne_top, isPrime, mem_comap, ne_top, q.eq_top_of_isUnit_mem, q.mem_comap.mp
-/
theorem IsLocalHom.of_comap_surjective [CommSemiring R] [CommSemiring S] (f : R ->+* S)
    (hf : Function.Surjective (comap f)) : IsLocalHom f where
  map_nonunit x hfx := by
    by_contra hx
    obtain ⟨p, hp, _⟩ := exists_max_ideal_of_mem_nonunits hx
    obtain ⟨⟨q, hqp⟩, hq⟩ := hf ⟨p, hp.isPrime⟩
    simp only [PrimeSpectrum.ext_iff, comap_asIdeal] at hq
    exact hqp.ne_top (q.eq_top_of_isUnit_mem (q.mem_comap.mp (by rwa [hq])) hfx)
