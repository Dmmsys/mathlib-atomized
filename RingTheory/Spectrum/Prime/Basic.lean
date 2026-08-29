/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Prime spectrum of a commutative (semi)ring

For the Zariski topology, see `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `AlgebraicGeometry.StructureSheaf`.)

## Main definitions

* `zeroLocus s`: The zero locus of a subset `s` of `R`
  is the subset of `PrimeSpectrum R` consisting of all prime ideals that contain `s`.
* `vanishingIdeal t`: The vanishing ideal of a subset `t` of `PrimeSpectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of (semi)rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from <https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

## References
* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]
-/

@[expose] public section

-- A dividing line between this file and `Mathlib/RingTheory/Spectrum/Prime/Topology.lean` is
-- that we should not depend on the Zariski topology here
assert_not_exists TopologicalSpace

noncomputable section

open scoped Pointwise

universe u v

variable (R : Type u) (S : Type v)

namespace PrimeSpectrum

section CommSemiRing

variable [CommSemiring R] [CommSemiring S]
variable {R S}

/--
lemma `nonempty_iff_nontrivial` / 引理 `nonempty_iff_nontrivial`

English:
lemma nonempty_iff_nontrivial
  statement: Nonempty (PrimeSpectrum R) ↔ Nontrivial R
  proof: by
  refine ⟨fun ⟨p⟩ => ⟨0, 1, fun h => p.2.ne_top ?_⟩, fun h => ?_⟩
  · simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  · obtain ⟨I, hI⟩ := Ideal.exists_maximal R
    exact ⟨⟨I, hI.isPrime⟩⟩

中文:
引理 nonempty_iff_nontrivial
  结论: Nonempty (PrimeSpectrum R) ↔ Nontrivial R
  证明: by
  refine ⟨fun ⟨p⟩ => ⟨0, 1, fun h => p.2.ne_top ?_⟩, fun h => ?_⟩
  · simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  · obtain ⟨I, hI⟩ := Ideal.exists_maximal R
    exact ⟨⟨I, hI.isPrime⟩⟩

Depends on / 依赖: Ideal.eq_top_iff_one, Ideal.exists_maximal, asIdeal, eq_top_iff_one, exists_maximal, hI.isPrime, isPrime, ne_top, p.asIdeal
-/
lemma nonempty_iff_nontrivial : Nonempty (PrimeSpectrum R) ↔ Nontrivial R := by
  refine ⟨fun ⟨p⟩ => ⟨0, 1, fun h => p.2.ne_top ?_⟩, fun h => ?_⟩
  · simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  · obtain ⟨I, hI⟩ := Ideal.exists_maximal R
    exact ⟨⟨I, hI.isPrime⟩⟩

/--
lemma `isEmpty_iff_subsingleton` / 引理 `isEmpty_iff_subsingleton`

English:
lemma isEmpty_iff_subsingleton
  statement: IsEmpty (PrimeSpectrum R) ↔ Subsingleton R
  proof: by
  contrapose!; exact nonempty_iff_nontrivial

中文:
引理 isEmpty_iff_subsingleton
  结论: IsEmpty (PrimeSpectrum R) ↔ Subsingleton R
  证明: by
  contrapose!; exact nonempty_iff_nontrivial

Depends on / 依赖: contrapose, nonempty_iff_nontrivial
-/
lemma isEmpty_iff_subsingleton : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  contrapose!; exact nonempty_iff_nontrivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nonempty PrimeSpectrum R
  body: nonempty_iff_nontrivial.mpr inferInstance

中文:
实例 [Nontrivial
  签名: R] : Nonempty PrimeSpectrum R
  定义体: nonempty_iff_nontrivial.mpr inferInstance

Depends on / 依赖: nonempty_iff_nontrivial, nonempty_iff_nontrivial.mpr
-/
instance [Nontrivial R] : Nonempty PrimeSpectrum R :=
  nonempty_iff_nontrivial.mpr inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : IsEmpty (PrimeSpectrum R)
  body: isEmpty_iff_subsingleton.mpr inferInstance

中文:
实例 [Subsingleton
  签名: R] : IsEmpty (PrimeSpectrum R)
  定义体: isEmpty_iff_subsingleton.mpr inferInstance

Depends on / 依赖: isEmpty_iff_subsingleton, isEmpty_iff_subsingleton.mpr
-/
instance [Subsingleton R] : IsEmpty (PrimeSpectrum R) :=
  isEmpty_iff_subsingleton.mpr inferInstance

/--
lemma `nontrivial` / 引理 `nontrivial`

English:
lemma nontrivial
  given: (p : PrimeSpectrum R)
  statement: Nontrivial R
  proof: nonempty_iff_nontrivial.mp ⟨p⟩

中文:
引理 nontrivial
  条件: (p : PrimeSpectrum R)
  结论: Nontrivial R
  证明: nonempty_iff_nontrivial.mp ⟨p⟩

Depends on / 依赖: nonempty_iff_nontrivial, nonempty_iff_nontrivial.mp
-/
lemma nontrivial (p : PrimeSpectrum R) : Nontrivial R :=
  nonempty_iff_nontrivial.mp ⟨p⟩

variable (R S)

/--
theorem `range_asIdeal` / 定理 `range_asIdeal`

English:
theorem range_asIdeal
  statement: Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime}
  proof: Set.ext fun J =>
⟨fun hJ => let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr hj ▸ j.isPrime,
      fun hJ => Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

中文:
定理 range_asIdeal
  结论: Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime}
  证明: Set.ext fun J =>
⟨fun hJ => let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr hj ▸ j.isPrime,
      fun hJ => Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

Depends on / 依赖: Set.ext, Set.mem_ofPred.mp, Set.mem_ofPred.mpr, Set.mem_range.mp, Set.mem_range.mpr, isPrime, j.isPrime, mem_ofPred, mem_range
-/
theorem range_asIdeal : Set.range PrimeSpectrum.asIdeal = {J : Ideal R | J.IsPrime} :=
  Set.ext fun J =>
⟨fun hJ => let ⟨j, hj⟩ := Set.mem_range.mp hJ; Set.mem_ofPred.mpr hj ▸ j.isPrime,
      fun hJ => Set.mem_range.mpr ⟨⟨J, Set.mem_ofPred.mp hJ⟩, rfl⟩⟩

/-- The map from the direct sum of prime spectra to the prime spectrum of a direct product. -/
@[simp]
/--
Definition of `primeSpectrumProdOfSum` / `primeSpectrumProdOfSum` 的定义

English:
definition primeSpectrumProdOfSum
  signature: : PrimeSpectrum R oplus PrimeSpectrum S -> PrimeSpectrum (R × S)

中文:
定义 primeSpectrumProdOfSum
  签名: : PrimeSpectrum R oplus PrimeSpectrum S -> PrimeSpectrum (R × S)
-/
def primeSpectrumProdOfSum : PrimeSpectrum R oplus PrimeSpectrum S -> PrimeSpectrum (R × S)
  | Sum.inl ⟨I, _⟩ => ⟨Ideal.prod I ⊤, Ideal.isPrime_ideal_prod_top⟩
  | Sum.inr ⟨J, _⟩ => ⟨Ideal.prod ⊤ J, Ideal.isPrime_ideal_prod_top'⟩

/--
Definition of `primeSpectrumProd` / `primeSpectrumProd` 的定义

English:
definition primeSpectrumProd
  signature: :
  body: Equiv.symm
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod_inj, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.lef

中文:
定义 primeSpectrumProd
  签名: :
  定义体: Equiv.symm
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod_inj, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.lef

Depends on / 依赖: Equiv.ofBijective, Equiv.symm, False.elim, Ideal.ideal_prod_prime, Ideal.prod_inj, Sum.inl, Sum.inr, h.left, h.right, hI.ne_top, hJ.ne_top, ideal_prod_prime, mk.injEq, ne_top, ofBijective, primeSpectrumProdOfSum, prod_inj
-/
noncomputable def primeSpectrumProd :
    PrimeSpectrum (R × S) ≃ PrimeSpectrum R oplus PrimeSpectrum S :=
Equiv.symm
    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
        constructor
        · rintro (⟨I, hI⟩ | ⟨J, hJ⟩) (⟨I', hI'⟩ | ⟨J', hJ'⟩) h <;>
          simp only [mk.injEq, Ideal.prod_inj, primeSpectrumProdOfSum] at h
          · simp only [h]
          · exact False.elim (hI.ne_top h.left)
          · exact False.elim (hJ.ne_top h.right)
          · simp only [h]
        · rintro ⟨I, hI⟩
          rcases (Ideal.ideal_prod_prime I).mp hI with (⟨p, ⟨hp, rfl⟩⟩ | ⟨p, ⟨hp, rfl⟩⟩)
          · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
          · exact ⟨Sum.inr ⟨p, hp⟩, rfl⟩)

variable {R S}

@[simp]
/--
theorem `primeSpectrumProd_symm_inl_asIdeal` / 定理 `primeSpectrumProd_symm_inl_asIdeal`

English:
theorem primeSpectrumProd_symm_inl_asIdeal
  given: (x : PrimeSpectrum R)
  proof: by
  cases x
  rfl

@[simp]

中文:
定理 primeSpectrumProd_symm_inl_asIdeal
  条件: (x : PrimeSpectrum R)
  证明: by
  cases x
  rfl

@[simp]
-/
theorem primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) :
    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ := by
  cases x
  rfl

@[simp]
/--
theorem `primeSpectrumProd_symm_inr_asIdeal` / 定理 `primeSpectrumProd_symm_inr_asIdeal`

English:
theorem primeSpectrumProd_symm_inr_asIdeal
  given: (x : PrimeSpectrum S)
  proof: by
  cases x
  rfl

中文:
定理 primeSpectrumProd_symm_inr_asIdeal
  条件: (x : PrimeSpectrum S)
  证明: by
  cases x
  rfl
-/
theorem primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) :
    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal := by
  cases x
  rfl

/--
Definition of `zeroLocus` / `zeroLocus` 的定义

English:
definition zeroLocus
  signature: (s : Set R)
  body: { x | s subseteq x.asIdeal }

@[simp]

中文:
定义 zeroLocus
  签名: (s : Set R)
  定义体: { x | s subseteq x.asIdeal }

@[simp]

Depends on / 依赖: asIdeal, subseteq, x.asIdeal
-/
def zeroLocus (s : Set R) : Set (PrimeSpectrum R) :=
  { x | s subseteq x.asIdeal }

@[simp]
/--
theorem `mem_zeroLocus` / 定理 `mem_zeroLocus`

English:
theorem mem_zeroLocus
  given: (x : PrimeSpectrum R) (s : Set R)
  statement: x in zeroLocus s ↔ s subseteq x.asIdeal
  proof: Iff.rfl

@[simp]

中文:
定理 mem_zeroLocus
  条件: (x : PrimeSpectrum R) (s : Set R)
  结论: x in zeroLocus s ↔ s subseteq x.asIdeal
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_zeroLocus (x : PrimeSpectrum R) (s : Set R) : x in zeroLocus s ↔ s subseteq x.asIdeal :=
  Iff.rfl

@[simp]
/--
theorem `zeroLocus_span` / 定理 `zeroLocus_span`

English:
theorem zeroLocus_span
  given: (s : Set R)
  statement: zeroLocus (Ideal.span s : Set R) = zeroLocus s
  proof: by
  ext x
  exact (Submodule.gi R R).gc s x.asIdeal

中文:
定理 zeroLocus_span
  条件: (s : Set R)
  结论: zeroLocus (Ideal.span s : Set R) = zeroLocus s
  证明: by
  ext x
  exact (Submodule.gi R R).gc s x.asIdeal

Depends on / 依赖: Submodule, Submodule.gi, asIdeal, x.asIdeal
-/
theorem zeroLocus_span (s : Set R) : zeroLocus (Ideal.span s : Set R) = zeroLocus s := by
  ext x
  exact (Submodule.gi R R).gc s x.asIdeal

/--
Definition of `vanishingIdeal` / `vanishingIdeal` 的定义

English:
definition vanishingIdeal
  signature: (t : Set (PrimeSpectrum R))
  body: ⨅ x in t, x.asIdeal

中文:
定义 vanishingIdeal
  签名: (t : Set (PrimeSpectrum R))
  定义体: ⨅ x in t, x.asIdeal

Depends on / 依赖: asIdeal, x.asIdeal
-/
def vanishingIdeal (t : Set (PrimeSpectrum R)) : Ideal R :=
  ⨅ x in t, x.asIdeal

/--
theorem `coe_vanishingIdeal` / 定理 `coe_vanishingIdeal`

English:
theorem coe_vanishingIdeal
  given: (t : Set (PrimeSpectrum R))
  proof: by
  ext f
  rw [vanishingIdeal]; rw [SetLike.mem_coe]; rw [Submodule.mem_iInf]
  apply forall_congr'; intro x
  rw [Submodule.mem_iInf]

中文:
定理 coe_vanishingIdeal
  条件: (t : Set (PrimeSpectrum R))
  证明: by
  ext f
  rw [vanishingIdeal]; rw [SetLike.mem_coe]; rw [Submodule.mem_iInf]
  apply forall_congr'; intro x
  rw [Submodule.mem_iInf]

Depends on / 依赖: SetLike, SetLike.mem_coe, Submodule, Submodule.mem_iInf, forall_congr, mem_coe, mem_iInf, vanishingIdeal
-/
theorem coe_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    (vanishingIdeal t : Set R) = { f : R | forall x in t, f in x.asIdeal } := by
  ext f
  rw [vanishingIdeal]; rw [SetLike.mem_coe]; rw [Submodule.mem_iInf]
  apply forall_congr'; intro x
  rw [Submodule.mem_iInf]

/--
theorem `mem_vanishingIdeal` / 定理 `mem_vanishingIdeal`

English:
theorem mem_vanishingIdeal
  given: (t : Set (PrimeSpectrum R)) (f : R)
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_vanishingIdeal]; rw [Set.mem_ofPred_eq]

@[simp]

中文:
定理 mem_vanishingIdeal
  条件: (t : Set (PrimeSpectrum R)) (f : R)
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_vanishingIdeal]; rw [Set.mem_ofPred_eq]

@[simp]

Depends on / 依赖: Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, coe_vanishingIdeal, mem_coe, mem_ofPred_eq
-/
theorem mem_vanishingIdeal (t : Set (PrimeSpectrum R)) (f : R) :
    f in vanishingIdeal t ↔ forall x in t, f in x.asIdeal := by
  rw [← SetLike.mem_coe]; rw [coe_vanishingIdeal]; rw [Set.mem_ofPred_eq]

@[simp]
/--
theorem `vanishingIdeal_singleton` / 定理 `vanishingIdeal_singleton`

English:
theorem vanishingIdeal_singleton
  given: (x : PrimeSpectrum R)
  proof: by simp [vanishingIdeal]

中文:
定理 vanishingIdeal_singleton
  条件: (x : PrimeSpectrum R)
  证明: by simp [vanishingIdeal]

Depends on / 依赖: vanishingIdeal
-/
theorem vanishingIdeal_singleton (x : PrimeSpectrum R) :
    vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal := by simp [vanishingIdeal]

/--
theorem `subset_zeroLocus_iff_le_vanishingIdeal` / 定理 `subset_zeroLocus_iff_le_vanishingIdeal`

English:
theorem subset_zeroLocus_iff_le_vanishingIdeal
  given: (t : Set (PrimeSpectrum R)) (I : Ideal R)
  proof: ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _).mpr (h j) k, fun h =>
    fun x j => (mem_zeroLocus _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

中文:
定理 subset_zeroLocus_iff_le_vanishingIdeal
  条件: (t : Set (PrimeSpectrum R)) (I : Ideal R)
  证明: ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _).mpr (h j) k, fun h =>
    fun x j => (mem_zeroLocus _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

Depends on / 依赖: le_trans, mem_vanishingIdeal, mem_zeroLocus
-/
theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (PrimeSpectrum R)) (I : Ideal R) :
    t subseteq zeroLocus I ↔ I <= vanishingIdeal t :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _).mpr (h j) k, fun h =>
    fun x j => (mem_zeroLocus _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

section Gc

variable (R)

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  proof: fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

中文:
定理 gc
  证明: fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

Depends on / 依赖: subset_zeroLocus_iff_le_vanishingIdeal
-/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>
      vanishingIdeal t :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

set_option backward.isDefEq.respectTransparency false in
/--
theorem `gc_set` / 定理 `gc_set`

English:
theorem gc_set
  proof: by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp_def] using ideal_gc.compose (gc R)

中文:
定理 gc_set
  证明: by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp_def] using ideal_gc.compose (gc R)

Depends on / 依赖: Function, Function.comp_def, GaloisConnection, Ideal.span, Submodule, Submodule.gi, comp_def, compose, ideal_gc, ideal_gc.compose, zeroLocus_span
-/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>
      vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp_def] using ideal_gc.compose (gc R)

/--
theorem `subset_zeroLocus_iff_subset_vanishingIdeal` / 定理 `subset_zeroLocus_iff_subset_vanishingIdeal`

English:
theorem subset_zeroLocus_iff_subset_vanishingIdeal
  given: (t : Set (PrimeSpectrum R)) (s : Set R)
  proof: (gc_set R) s t

中文:
定理 subset_zeroLocus_iff_subset_vanishingIdeal
  条件: (t : Set (PrimeSpectrum R)) (s : Set R)
  证明: (gc_set R) s t

Depends on / 依赖: gc_set
-/
theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t subseteq zeroLocus s ↔ s subseteq vanishingIdeal t :=
  (gc_set R) s t

end Gc

/--
theorem `subset_vanishingIdeal_zeroLocus` / 定理 `subset_vanishingIdeal_zeroLocus`

English:
theorem subset_vanishingIdeal_zeroLocus
  given: (s : Set R)
  statement: s subseteq vanishingIdeal (zeroLocus s)
  proof: (gc_set R).le_u_l s

中文:
定理 subset_vanishingIdeal_zeroLocus
  条件: (s : Set R)
  结论: s subseteq vanishingIdeal (zeroLocus s)
  证明: (gc_set R).le_u_l s

Depends on / 依赖: gc_set, le_u_l
-/
theorem subset_vanishingIdeal_zeroLocus (s : Set R) : s subseteq vanishingIdeal (zeroLocus s) :=
  (gc_set R).le_u_l s

/--
theorem `le_vanishingIdeal_zeroLocus` / 定理 `le_vanishingIdeal_zeroLocus`

English:
theorem le_vanishingIdeal_zeroLocus
  given: (I : Ideal R)
  statement: I <= vanishingIdeal (zeroLocus I)
  proof: (gc R).le_u_l I

@[simp]

中文:
定理 le_vanishingIdeal_zeroLocus
  条件: (I : Ideal R)
  结论: I <= vanishingIdeal (zeroLocus I)
  证明: (gc R).le_u_l I

@[simp]

Depends on / 依赖: le_u_l
-/
theorem le_vanishingIdeal_zeroLocus (I : Ideal R) : I <= vanishingIdeal (zeroLocus I) :=
  (gc R).le_u_l I

@[simp]
/--
theorem `vanishingIdeal_zeroLocus_eq_radical` / 定理 `vanishingIdeal_zeroLocus_eq_radical`

English:
theorem vanishingIdeal_zeroLocus_eq_radical
  given: (I : Ideal R)
  proof: Ideal.ext fun f => by
    rw [mem_vanishingIdeal]; rw [Ideal.radical_eq_sInf]; rw [Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

中文:
定理 vanishingIdeal_zeroLocus_eq_radical
  条件: (I : Ideal R)
  证明: Ideal.ext fun f => by
    rw [mem_vanishingIdeal]; rw [Ideal.radical_eq_sInf]; rw [Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

Depends on / 依赖: Ideal.ext, Ideal.radical_eq_sInf, Submodule, Submodule.mem_sInf, mem_sInf, mem_vanishingIdeal, radical_eq_sInf
-/
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f => by
    rw [mem_vanishingIdeal]; rw [Ideal.radical_eq_sInf]; rw [Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

/--
theorem `nilradical_eq_iInf` / 定理 `nilradical_eq_iInf`

English:
theorem nilradical_eq_iInf
  statement: nilradical R = iInf asIdeal
  proof: by
  apply range_asIdeal R ▸ nilradical_eq_sInf R

中文:
定理 nilradical_eq_iInf
  结论: nilradical R = iInf asIdeal
  证明: by
  apply range_asIdeal R ▸ nilradical_eq_sInf R

Depends on / 依赖: nilradical_eq_sInf, range_asIdeal
-/
theorem nilradical_eq_iInf : nilradical R = iInf asIdeal := by
  apply range_asIdeal R ▸ nilradical_eq_sInf R

/--
theorem `vanishingIdeal_univ` / 定理 `vanishingIdeal_univ`

English:
theorem vanishingIdeal_univ
  statement: vanishingIdeal Set.univ = nilradical R
  proof: by
  rw [vanishingIdeal]; rw [iInf_univ]; rw [nilradical_eq_iInf]

@[simp]

中文:
定理 vanishingIdeal_univ
  结论: vanishingIdeal Set.univ = nilradical R
  证明: by
  rw [vanishingIdeal]; rw [iInf_univ]; rw [nilradical_eq_iInf]

@[simp]
-/
@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
  rw [vanishingIdeal]; rw [iInf_univ]; rw [nilradical_eq_iInf]

@[simp]
/--
theorem `zeroLocus_radical` / 定理 `zeroLocus_radical`

English:
theorem zeroLocus_radical
  given: (I : Ideal R)
  statement: zeroLocus (I.radical : Set R) = zeroLocus I
  proof: vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I

中文:
定理 zeroLocus_radical
  条件: (I : Ideal R)
  结论: zeroLocus (I.radical : Set R) = zeroLocus I
  证明: vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I

Depends on / 依赖: l_u_l_eq_l, vanishingIdeal_zeroLocus_eq_radical
-/
theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
  vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I

/--
theorem `subset_zeroLocus_vanishingIdeal` / 定理 `subset_zeroLocus_vanishingIdeal`

English:
theorem subset_zeroLocus_vanishingIdeal
  given: (t : Set (PrimeSpectrum R))
  proof: (gc R).l_u_le t

中文:
定理 subset_zeroLocus_vanishingIdeal
  条件: (t : Set (PrimeSpectrum R))
  证明: (gc R).l_u_le t

Depends on / 依赖: l_u_le
-/
theorem subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    t subseteq zeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t

/--
theorem `zeroLocus_anti_mono` / 定理 `zeroLocus_anti_mono`

English:
theorem zeroLocus_anti_mono
  given: {s t : Set R} (h : s subseteq t)
  statement: zeroLocus t subseteq zeroLocus s
  proof: (gc_set R).monotone_l h

中文:
定理 zeroLocus_anti_mono
  条件: {s t : Set R} (h : s subseteq t)
  结论: zeroLocus t subseteq zeroLocus s
  证明: (gc_set R).monotone_l h

Depends on / 依赖: gc_set, monotone_l
-/
theorem zeroLocus_anti_mono {s t : Set R} (h : s subseteq t) : zeroLocus t subseteq zeroLocus s :=
  (gc_set R).monotone_l h

/--
theorem `zeroLocus_anti_mono_ideal` / 定理 `zeroLocus_anti_mono_ideal`

English:
theorem zeroLocus_anti_mono_ideal
  given: {s t : Ideal R} (h : s <= t)
  proof: (gc R).monotone_l h

中文:
定理 zeroLocus_anti_mono_ideal
  条件: {s t : Ideal R} (h : s <= t)
  证明: (gc R).monotone_l h

Depends on / 依赖: monotone_l
-/
theorem zeroLocus_anti_mono_ideal {s t : Ideal R} (h : s <= t) :
    zeroLocus (t : Set R) subseteq zeroLocus (s : Set R) :=
  (gc R).monotone_l h

/--
theorem `vanishingIdeal_anti_mono` / 定理 `vanishingIdeal_anti_mono`

English:
theorem vanishingIdeal_anti_mono
  given: {s t : Set (PrimeSpectrum R)} (h : s subseteq t)
  proof: (gc R).monotone_u h

中文:
定理 vanishingIdeal_anti_mono
  条件: {s t : Set (PrimeSpectrum R)} (h : s subseteq t)
  证明: (gc R).monotone_u h

Depends on / 依赖: monotone_u
-/
theorem vanishingIdeal_anti_mono {s t : Set (PrimeSpectrum R)} (h : s subseteq t) :
    vanishingIdeal t <= vanishingIdeal s :=
  (gc R).monotone_u h

/--
theorem `zeroLocus_subset_zeroLocus_iff` / 定理 `zeroLocus_subset_zeroLocus_iff`

English:
theorem zeroLocus_subset_zeroLocus_iff
  given: (I J : Ideal R)
  proof: by
  rw [subset_zeroLocus_iff_le_vanishingIdeal]; rw [vanishingIdeal_zeroLocus_eq_radical]

中文:
定理 zeroLocus_subset_zeroLocus_iff
  条件: (I J : Ideal R)
  证明: by
  rw [subset_zeroLocus_iff_le_vanishingIdeal]; rw [vanishingIdeal_zeroLocus_eq_radical]

Depends on / 依赖: subset_zeroLocus_iff_le_vanishingIdeal, vanishingIdeal_zeroLocus_eq_radical
-/
theorem zeroLocus_subset_zeroLocus_iff (I J : Ideal R) :
    zeroLocus (I : Set R) subseteq zeroLocus (J : Set R) ↔ J <= I.radical := by
  rw [subset_zeroLocus_iff_le_vanishingIdeal]; rw [vanishingIdeal_zeroLocus_eq_radical]

/--
theorem `zeroLocus_subset_zeroLocus_singleton_iff` / 定理 `zeroLocus_subset_zeroLocus_singleton_iff`

English:
theorem zeroLocus_subset_zeroLocus_singleton_iff
  given: (f g : R)
  proof: by
  rw [← zeroLocus_span {f}]; rw [← zeroLocus_span {g}]; rw [zeroLocus_subset_zeroLocus_iff]; rw [Ideal.span_le]; rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]

中文:
定理 zeroLocus_subset_zeroLocus_singleton_iff
  条件: (f g : R)
  证明: by
  rw [← zeroLocus_span {f}]; rw [← zeroLocus_span {g}]; rw [zeroLocus_subset_zeroLocus_iff]; rw [Ideal.span_le]; rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]

Depends on / 依赖: Ideal.span_le, Quotient, Quotient.mk, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, mem_coe, singleton_subset_iff, span_le, zeroLocus_span, zeroLocus_subset_zeroLocus_iff
-/
theorem zeroLocus_subset_zeroLocus_singleton_iff (f g : R) :
    zeroLocus ({f} : Set R) subseteq zeroLocus {g} ↔ g in (Ideal.span ({f} : Set R)).radical := by
  rw [← zeroLocus_span {f}]; rw [← zeroLocus_span {g}]; rw [zeroLocus_subset_zeroLocus_iff]; rw [Ideal.span_le]; rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]

/--
theorem `zeroLocus_bot` / 定理 `zeroLocus_bot`

English:
theorem zeroLocus_bot
  statement: zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ
  proof: (gc R).l_bot

@[simp]

中文:
定理 zeroLocus_bot
  结论: zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ
  证明: (gc R).l_bot

@[simp]

Depends on / 依赖: l_bot
-/
theorem zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ :=
  (gc R).l_bot

@[simp]
/--
lemma `zeroLocus_nilradical` / 引理 `zeroLocus_nilradical`

English:
lemma zeroLocus_nilradical
  statement: zeroLocus (nilradical R : Set R) = Set.univ
  proof: by
  rw [nilradical]; rw [zeroLocus_radical]; rw [Ideal.zero_eq_bot]; rw [zeroLocus_bot]

@[simp]

中文:
引理 zeroLocus_nilradical
  结论: zeroLocus (nilradical R : Set R) = Set.univ
  证明: by
  rw [nilradical]; rw [zeroLocus_radical]; rw [Ideal.zero_eq_bot]; rw [zeroLocus_bot]

@[simp]

Depends on / 依赖: Ideal.zero_eq_bot, nilradical, zeroLocus_bot, zeroLocus_radical, zero_eq_bot
-/
lemma zeroLocus_nilradical : zeroLocus (nilradical R : Set R) = Set.univ := by
  rw [nilradical]; rw [zeroLocus_radical]; rw [Ideal.zero_eq_bot]; rw [zeroLocus_bot]

@[simp]
/--
theorem `zeroLocus_singleton_zero` / 定理 `zeroLocus_singleton_zero`

English:
theorem zeroLocus_singleton_zero
  statement: zeroLocus ({0} : Set R) = Set.univ
  proof: zeroLocus_bot

@[simp]

中文:
定理 zeroLocus_singleton_zero
  结论: zeroLocus ({0} : Set R) = Set.univ
  证明: zeroLocus_bot

@[simp]

Depends on / 依赖: zeroLocus_bot
-/
theorem zeroLocus_singleton_zero : zeroLocus ({0} : Set R) = Set.univ :=
  zeroLocus_bot

@[simp]
/--
theorem `zeroLocus_empty` / 定理 `zeroLocus_empty`

English:
theorem zeroLocus_empty
  statement: zeroLocus (∅ : Set R) = Set.univ
  proof: (gc_set R).l_bot

@[simp]

中文:
定理 zeroLocus_empty
  结论: zeroLocus (∅ : Set R) = Set.univ
  证明: (gc_set R).l_bot

@[simp]

Depends on / 依赖: gc_set, l_bot
-/
theorem zeroLocus_empty : zeroLocus (∅ : Set R) = Set.univ :=
  (gc_set R).l_bot

@[simp]
/--
theorem `vanishingIdeal_empty` / 定理 `vanishingIdeal_empty`

English:
theorem vanishingIdeal_empty
  statement: vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤
  proof: by
  simpa using! (gc R).u_top

中文:
定理 vanishingIdeal_empty
  结论: vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤
  证明: by
  simpa using! (gc R).u_top

Depends on / 依赖: u_top
-/
theorem vanishingIdeal_empty : vanishingIdeal (∅ : Set (PrimeSpectrum R)) = ⊤ := by
  simpa using! (gc R).u_top

/--
theorem `zeroLocus_empty_of_one_mem` / 定理 `zeroLocus_empty_of_one_mem`

English:
theorem zeroLocus_empty_of_one_mem
  given: {s : Set R} (h : (1 : R) in s)
  statement: zeroLocus s = ∅
  proof: by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_zeroLocus] at hx
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top

@[simp]

中文:
定理 zeroLocus_empty_of_one_mem
  条件: {s : Set R} (h : (1 : R) in s)
  结论: zeroLocus s = ∅
  证明: by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_zeroLocus] at hx
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top

@[simp]

Depends on / 依赖: Ideal.eq_top_iff_one, IsPrime, Set.eq_empty_iff_forall_notMem, asIdeal, eq_empty_iff_forall_notMem, eq_top, eq_top_iff_one, infer_instance, mem_zeroLocus, ne_top, x.asIdeal, x.asIdeal.IsPrime, x_prime, x_prime.ne_top
-/
theorem zeroLocus_empty_of_one_mem {s : Set R} (h : (1 : R) in s) : zeroLocus s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_zeroLocus] at hx
  have x_prime : x.asIdeal.IsPrime := by infer_instance
  have eq_top : x.asIdeal = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hx h
  apply x_prime.ne_top eq_top

@[simp]
/--
theorem `zeroLocus_singleton_one` / 定理 `zeroLocus_singleton_one`

English:
theorem zeroLocus_singleton_one
  statement: zeroLocus ({1} : Set R) = ∅
  proof: zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))

中文:
定理 zeroLocus_singleton_one
  结论: zeroLocus ({1} : Set R) = ∅
  证明: zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))

Depends on / 依赖: Set.mem_singleton, mem_singleton, zeroLocus_empty_of_one_mem
-/
theorem zeroLocus_singleton_one : zeroLocus ({1} : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_singleton (1 : R))

/--
theorem `zeroLocus_empty_iff_eq_top` / 定理 `zeroLocus_empty_iff_eq_top`

English:
theorem zeroLocus_empty_iff_eq_top
  given: {I : Ideal R}
  statement: zeroLocus (I : Set R) = ∅ ↔ I = ⊤
  proof: by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.isPrime⟩, hIM⟩
  · rintro rfl
    apply zeroLocus_empty_of_one_mem
    trivial

@[simp]

中文:
定理 zeroLocus_empty_iff_eq_top
  条件: {I : Ideal R}
  结论: zeroLocus (I : Set R) = ∅ ↔ I = ⊤
  证明: by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.isPrime⟩, hIM⟩
  · rintro rfl
    apply zeroLocus_empty_of_one_mem
    trivial

@[simp]

Depends on / 依赖: Ideal.exists_le_maximal, contrapose, exists_le_maximal, hM.isPrime, isPrime, zeroLocus_empty_of_one_mem
-/
theorem zeroLocus_empty_iff_eq_top {I : Ideal R} : zeroLocus (I : Set R) = ∅ ↔ I = ⊤ := by
  constructor
  · contrapose!
    intro h
    rcases Ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩
    exact ⟨⟨M, hM.isPrime⟩, hIM⟩
  · rintro rfl
    apply zeroLocus_empty_of_one_mem
    trivial

@[simp]
/--
theorem `zeroLocus_univ` / 定理 `zeroLocus_univ`

English:
theorem zeroLocus_univ
  statement: zeroLocus (Set.univ : Set R) = ∅
  proof: zeroLocus_empty_of_one_mem (Set.mem_univ 1)

中文:
定理 zeroLocus_univ
  结论: zeroLocus (Set.univ : Set R) = ∅
  证明: zeroLocus_empty_of_one_mem (Set.mem_univ 1)

Depends on / 依赖: Set.mem_univ, mem_univ, zeroLocus_empty_of_one_mem
-/
theorem zeroLocus_univ : zeroLocus (Set.univ : Set R) = ∅ :=
  zeroLocus_empty_of_one_mem (Set.mem_univ 1)

/--
theorem `vanishingIdeal_eq_top_iff` / 定理 `vanishingIdeal_eq_top_iff`

English:
theorem vanishingIdeal_eq_top_iff
  given: {s : Set (PrimeSpectrum R)}
  statement: vanishingIdeal s = ⊤ ↔ s = ∅
  proof: by
  rw [← top_le_iff]; rw [← subset_zeroLocus_iff_le_vanishingIdeal]; rw [Submodule.top_coe]; rw [zeroLocus_univ]; rw [Set.subset_empty_iff]

中文:
定理 vanishingIdeal_eq_top_iff
  条件: {s : Set (PrimeSpectrum R)}
  结论: vanishingIdeal s = ⊤ ↔ s = ∅
  证明: by
  rw [← top_le_iff]; rw [← subset_zeroLocus_iff_le_vanishingIdeal]; rw [Submodule.top_coe]; rw [zeroLocus_univ]; rw [Set.subset_empty_iff]

Depends on / 依赖: Set.subset_empty_iff, Submodule, Submodule.top_coe, subset_empty_iff, subset_zeroLocus_iff_le_vanishingIdeal, top_coe, top_le_iff, zeroLocus_univ
-/
theorem vanishingIdeal_eq_top_iff {s : Set (PrimeSpectrum R)} : vanishingIdeal s = ⊤ ↔ s = ∅ := by
  rw [← top_le_iff]; rw [← subset_zeroLocus_iff_le_vanishingIdeal]; rw [Submodule.top_coe]; rw [zeroLocus_univ]; rw [Set.subset_empty_iff]

/--
theorem `zeroLocus_eq_univ_iff` / 定理 `zeroLocus_eq_univ_iff`

English:
theorem zeroLocus_eq_univ_iff
  given: (s : Set R)
  proof: by
  rw [← Set.univ_subset_iff]; rw [subset_zeroLocus_iff_subset_vanishingIdeal]; rw [vanishingIdeal_univ]

中文:
定理 zeroLocus_eq_univ_iff
  条件: (s : Set R)
  证明: by
  rw [← Set.univ_subset_iff]; rw [subset_zeroLocus_iff_subset_vanishingIdeal]; rw [vanishingIdeal_univ]

Depends on / 依赖: Set.univ_subset_iff, subset_zeroLocus_iff_subset_vanishingIdeal, univ_subset_iff, vanishingIdeal_univ
-/
theorem zeroLocus_eq_univ_iff (s : Set R) :
    zeroLocus s = Set.univ ↔ s subseteq nilradical R := by
  rw [← Set.univ_subset_iff]; rw [subset_zeroLocus_iff_subset_vanishingIdeal]; rw [vanishingIdeal_univ]

/--
theorem `zeroLocus_sup` / 定理 `zeroLocus_sup`

English:
theorem zeroLocus_sup
  given: (I J : Ideal R)
  proof: (gc R).l_sup

中文:
定理 zeroLocus_sup
  条件: (I J : Ideal R)
  证明: (gc R).l_sup

Depends on / 依赖: l_sup
-/
theorem zeroLocus_sup (I J : Ideal R) :
    zeroLocus ((I ⊔ J : Ideal R) : Set R) = zeroLocus I inter zeroLocus J :=
  (gc R).l_sup

/--
theorem `zeroLocus_union` / 定理 `zeroLocus_union`

English:
theorem zeroLocus_union
  given: (s s' : Set R)
  statement: zeroLocus (s union s') = zeroLocus s inter zeroLocus s'
  proof: (gc_set R).l_sup

中文:
定理 zeroLocus_union
  条件: (s s' : Set R)
  结论: zeroLocus (s union s') = zeroLocus s inter zeroLocus s'
  证明: (gc_set R).l_sup

Depends on / 依赖: gc_set, l_sup
-/
theorem zeroLocus_union (s s' : Set R) : zeroLocus (s union s') = zeroLocus s inter zeroLocus s' :=
  (gc_set R).l_sup

/--
theorem `vanishingIdeal_union` / 定理 `vanishingIdeal_union`

English:
theorem vanishingIdeal_union
  given: (t t' : Set (PrimeSpectrum R))
  proof: (gc R).u_inf

中文:
定理 vanishingIdeal_union
  条件: (t t' : Set (PrimeSpectrum R))
  证明: (gc R).u_inf

Depends on / 依赖: u_inf
-/
theorem vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t union t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
  (gc R).u_inf

/--
theorem `zeroLocus_iSup` / 定理 `zeroLocus_iSup`

English:
theorem zeroLocus_iSup
  given: {ι : Sort*} (I : ι -> Ideal R)
  proof: (gc R).l_iSup

中文:
定理 zeroLocus_iSup
  条件: {ι : Sort*} (I : ι -> Ideal R)
  证明: (gc R).l_iSup

Depends on / 依赖: l_iSup
-/
theorem zeroLocus_iSup {ι : Sort*} (I : ι -> Ideal R) :
    zeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, zeroLocus (I i) :=
  (gc R).l_iSup

/--
theorem `zeroLocus_iUnion` / 定理 `zeroLocus_iUnion`

English:
theorem zeroLocus_iUnion
  given: {ι : Sort*} (s : ι -> Set R)
  proof: (gc_set R).l_iSup

中文:
定理 zeroLocus_iUnion
  条件: {ι : Sort*} (s : ι -> Set R)
  证明: (gc_set R).l_iSup

Depends on / 依赖: gc_set, l_iSup
-/
theorem zeroLocus_iUnion {ι : Sort*} (s : ι -> Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) :=
  (gc_set R).l_iSup

/--
theorem `zeroLocus_iUnion₂` / 定理 `zeroLocus_iUnion₂`

English:
theorem zeroLocus_iUnion₂
  given: {ι : Sort*} {κ : (i : ι) -> Sort*} (s : forall i, κ i -> Set R)
  proof: (gc_set R).l_iSup₂

中文:
定理 zeroLocus_iUnion₂
  条件: {ι : Sort*} {κ : (i : ι) -> Sort*} (s : 对任意 i, κ i -> Set R)
  证明: (gc_set R).l_iSup₂

Depends on / 依赖: gc_set
-/
theorem zeroLocus_iUnion₂ {ι : Sort*} {κ : (i : ι) -> Sort*} (s : forall i, κ i -> Set R) :
    zeroLocus (⋃ (i) (j), s i j) = ⋂ (i) (j), zeroLocus (s i j) :=
  (gc_set R).l_iSup₂

/--
theorem `zeroLocus_bUnion` / 定理 `zeroLocus_bUnion`

English:
theorem zeroLocus_bUnion
  given: (s : Set (Set R))
  proof: by simp only [zeroLocus_iUnion]

中文:
定理 zeroLocus_bUnion
  条件: (s : Set (Set R))
  证明: by simp only [zeroLocus_iUnion]

Depends on / 依赖: zeroLocus_iUnion
-/
theorem zeroLocus_bUnion (s : Set (Set R)) :
    zeroLocus (⋃ s' in s, s' : Set R) = ⋂ s' in s, zeroLocus s' := by simp only [zeroLocus_iUnion]

/--
theorem `vanishingIdeal_iUnion` / 定理 `vanishingIdeal_iUnion`

English:
theorem vanishingIdeal_iUnion
  given: {ι : Sort*} (t : ι -> Set (PrimeSpectrum R))
  proof: (gc R).u_iInf

中文:
定理 vanishingIdeal_iUnion
  条件: {ι : Sort*} (t : ι -> Set (PrimeSpectrum R))
  证明: (gc R).u_iInf

Depends on / 依赖: u_iInf
-/
theorem vanishingIdeal_iUnion {ι : Sort*} (t : ι -> Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_iInf

/--
theorem `zeroLocus_inf` / 定理 `zeroLocus_inf`

English:
theorem zeroLocus_inf
  given: (I J : Ideal R)
  proof: Set.ext fun x => x.2.inf_le

中文:
定理 zeroLocus_inf
  条件: (I J : Ideal R)
  证明: Set.ext fun x => x.2.inf_le

Depends on / 依赖: Set.ext, inf_le
-/
theorem zeroLocus_inf (I J : Ideal R) :
    zeroLocus ((I ⊓ J : Ideal R) : Set R) = zeroLocus I union zeroLocus J :=
  Set.ext fun x => x.2.inf_le

/--
theorem `union_zeroLocus` / 定理 `union_zeroLocus`

English:
theorem union_zeroLocus
  given: (s s' : Set R)
  proof: by
  rw [zeroLocus_inf]
  simp

中文:
定理 union_zeroLocus
  条件: (s s' : Set R)
  证明: by
  rw [zeroLocus_inf]
  simp

Depends on / 依赖: zeroLocus_inf
-/
theorem union_zeroLocus (s s' : Set R) :
    zeroLocus s union zeroLocus s' = zeroLocus (Ideal.span s ⊓ Ideal.span s' : Ideal R) := by
  rw [zeroLocus_inf]
  simp

/--
theorem `zeroLocus_mul` / 定理 `zeroLocus_mul`

English:
theorem zeroLocus_mul
  given: (I J : Ideal R)
  proof: Set.ext fun x => x.2.mul_le

中文:
定理 zeroLocus_mul
  条件: (I J : Ideal R)
  证明: Set.ext fun x => x.2.mul_le

Depends on / 依赖: Set.ext, mul_le
-/
theorem zeroLocus_mul (I J : Ideal R) :
    zeroLocus ((I * J : Ideal R) : Set R) = zeroLocus I union zeroLocus J :=
  Set.ext fun x => x.2.mul_le

/--
theorem `zeroLocus_singleton_mul` / 定理 `zeroLocus_singleton_mul`

English:
theorem zeroLocus_singleton_mul
  given: (f g : R)
  proof: Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]

中文:
定理 zeroLocus_singleton_mul
  条件: (f g : R)
  证明: Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]

Depends on / 依赖: Set.ext, mul_mem_iff_mem_or_mem
-/
theorem zeroLocus_singleton_mul (f g : R) :
    zeroLocus ({f * g} : Set R) = zeroLocus {f} union zeroLocus {g} :=
  Set.ext fun x => by simpa using x.2.mul_mem_iff_mem_or_mem

@[simp]
/--
theorem `zeroLocus_pow` / 定理 `zeroLocus_pow`

English:
theorem zeroLocus_pow
  given: (I : Ideal R) {n : Nat} (hn : n != 0)
  proof: zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I

@[simp]

中文:
定理 zeroLocus_pow
  条件: (I : Ideal R) {n : 自然数} (hn : n != 0)
  证明: zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I

@[simp]

Depends on / 依赖: I.radical_pow, radical_pow, zeroLocus_radical
-/
theorem zeroLocus_pow (I : Ideal R) {n : Nat} (hn : n != 0) :
    zeroLocus ((I ^ n : Ideal R) : Set R) = zeroLocus I :=
  zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I

@[simp]
/--
theorem `zeroLocus_singleton_pow` / 定理 `zeroLocus_singleton_pow`

English:
theorem zeroLocus_singleton_pow
  given: (f : R) (n : Nat) (hn : 0 < n)
  proof: Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn

中文:
定理 zeroLocus_singleton_pow
  条件: (f : R) (n : 自然数) (hn : 0 < n)
  证明: Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn

Depends on / 依赖: Set.ext, pow_mem_iff_mem
-/
theorem zeroLocus_singleton_pow (f : R) (n : Nat) (hn : 0 < n) :
    zeroLocus ({f ^ n} : Set R) = zeroLocus {f} :=
  Set.ext fun x => by simpa using x.2.pow_mem_iff_mem n hn

/--
theorem `sup_vanishingIdeal_le` / 定理 `sup_vanishingIdeal_le`

English:
theorem sup_vanishingIdeal_le
  given: (t t' : Set (PrimeSpectrum R))
  proof: by
  intro r
  rw [Submodule.mem_sup]; rw [mem_vanishingIdeal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

中文:
定理 sup_vanishingIdeal_le
  条件: (t t' : Set (PrimeSpectrum R))
  证明: by
  intro r
  rw [Submodule.mem_sup]; rw [mem_vanishingIdeal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

Depends on / 依赖: Submodule, Submodule.add_mem, Submodule.mem_sup, add_mem, mem_sup, mem_vanishingIdeal, solve_by_elim
-/
theorem sup_vanishingIdeal_le (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal t ⊔ vanishingIdeal t' <= vanishingIdeal (t inter t') := by
  intro r
  rw [Submodule.mem_sup]; rw [mem_vanishingIdeal]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

/--
theorem `mem_compl_zeroLocus_iff_notMem` / 定理 `mem_compl_zeroLocus_iff_notMem`

English:
theorem mem_compl_zeroLocus_iff_notMem
  given: {f : R} {I : PrimeSpectrum R}
  proof: by
  rw [Set.mem_compl_iff]; rw [mem_zeroLocus]; rw [Set.singleton_subset_iff]; rfl

@[simp]

中文:
定理 mem_compl_zeroLocus_iff_notMem
  条件: {f : R} {I : PrimeSpectrum R}
  证明: by
  rw [Set.mem_compl_iff]; rw [mem_zeroLocus]; rw [Set.singleton_subset_iff]; rfl

@[simp]

Depends on / 依赖: Set.mem_compl_iff, Set.singleton_subset_iff, mem_compl_iff, mem_zeroLocus, singleton_subset_iff
-/
theorem mem_compl_zeroLocus_iff_notMem {f : R} {I : PrimeSpectrum R} :
    I in (zeroLocus {f} : Set (PrimeSpectrum R))ᶜ ↔ f ∉ I.asIdeal := by
  rw [Set.mem_compl_iff]; rw [mem_zeroLocus]; rw [Set.singleton_subset_iff]; rfl

@[simp]
/--
lemma `zeroLocus_insert_zero` / 引理 `zeroLocus_insert_zero`

English:
lemma zeroLocus_insert_zero
  given: (s : Set R)
  statement: zeroLocus (insert 0 s) = zeroLocus s
  proof: by
  rw [← Set.union_singleton]; rw [zeroLocus_union]; rw [zeroLocus_singleton_zero]; rw [Set.inter_univ]

@[simp]

中文:
引理 zeroLocus_insert_zero
  条件: (s : Set R)
  结论: zeroLocus (insert 0 s) = zeroLocus s
  证明: by
  rw [← Set.union_singleton]; rw [zeroLocus_union]; rw [zeroLocus_singleton_zero]; rw [Set.inter_univ]

@[simp]

Depends on / 依赖: Set.inter_univ, Set.union_singleton, inter_univ, union_singleton, zeroLocus_singleton_zero, zeroLocus_union
-/
lemma zeroLocus_insert_zero (s : Set R) : zeroLocus (insert 0 s) = zeroLocus s := by
  rw [← Set.union_singleton]; rw [zeroLocus_union]; rw [zeroLocus_singleton_zero]; rw [Set.inter_univ]

@[simp]
/--
lemma `zeroLocus_sdiff_singleton_zero` / 引理 `zeroLocus_sdiff_singleton_zero`

English:
lemma zeroLocus_sdiff_singleton_zero
  given: (s : Set R)
  statement: zeroLocus (s \ {0}) = zeroLocus s
  proof: by
  rw [← zeroLocus_insert_zero]; rw [← zeroLocus_insert_zero (s := s)]; simp

@[deprecated (since := "2026-06-03")]
alias zeroLocus_diff_singleton_zero := zeroLocus_sdiff_singleton_zero

中文:
引理 zeroLocus_sdiff_singleton_zero
  条件: (s : Set R)
  结论: zeroLocus (s \ {0}) = zeroLocus s
  证明: by
  rw [← zeroLocus_insert_zero]; rw [← zeroLocus_insert_zero (s := s)]; simp

@[deprecated (since := "2026-06-03")]
alias zeroLocus_diff_singleton_zero := zeroLocus_sdiff_singleton_zero

Depends on / 依赖: zeroLocus_insert_zero
-/
lemma zeroLocus_sdiff_singleton_zero (s : Set R) : zeroLocus (s \ {0}) = zeroLocus s := by
  rw [← zeroLocus_insert_zero]; rw [← zeroLocus_insert_zero (s := s)]; simp

@[deprecated (since := "2026-06-03")]
alias zeroLocus_diff_singleton_zero := zeroLocus_sdiff_singleton_zero

/--
lemma `zeroLocus_smul_of_isUnit` / 引理 `zeroLocus_smul_of_isUnit`

English:
lemma zeroLocus_smul_of_isUnit
  given: {r : R} (hr : IsUnit r) (s : Set R)
  proof: by
  ext; simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

中文:
引理 zeroLocus_smul_of_isUnit
  条件: {r : R} (hr : IsUnit r) (s : Set R)
  证明: by
  ext; simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

Depends on / 依赖: Ideal.unit_mul_mem_iff_mem, Set.image_smul, Set.subset_def, image_smul, subset_def, unit_mul_mem_iff_mem
-/
lemma zeroLocus_smul_of_isUnit {r : R} (hr : IsUnit r) (s : Set R) :
    zeroLocus (r • s) = zeroLocus s := by
  ext; simp [Set.subset_def, ← Set.image_smul, Ideal.unit_mul_mem_iff_mem _ hr]

section Order

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] : OrderBot (PrimeSpectrum R) where
  body: ⟨⊥, Ideal.isPrime_bot⟩
  bot_le I := @bot_le _ _ _ I.asIdeal

@[simp]

中文:
实例 [IsDomain
  签名: R] : OrderBot (PrimeSpectrum R) where
  定义体: ⟨⊥, Ideal.isPrime_bot⟩
  bot_le I := @bot_le _ _ _ I.asIdeal

@[simp]

Depends on / 依赖: DiscreteTopology, DiscreteTopology.toLocallyConnectedSpace, Ideal.isPrime_bot, TopologicalSpace, isPrime_bot, toLocallyConnectedSpace
-/
instance [IsDomain R] : OrderBot (PrimeSpectrum R) where
  bot := ⟨⊥, Ideal.isPrime_bot⟩
  bot_le I := @bot_le _ _ _ I.asIdeal

@[simp]
/--
theorem `asIdeal_bot` / 定理 `asIdeal_bot`

English:
theorem asIdeal_bot
  given: [IsDomain R]
  statement: (⊥ : PrimeSpectrum R).asIdeal = ⊥
  proof: rfl

中文:
定理 asIdeal_bot
  条件: [IsDomain R]
  结论: (⊥ : PrimeSpectrum R).asIdeal = ⊥
  证明: rfl
-/
theorem asIdeal_bot [IsDomain R] : (⊥ : PrimeSpectrum R).asIdeal = ⊥ := rfl

instance {R : Type*} [Field R] : Unique (PrimeSpectrum R) where
  default := ⊥
  uniq x := PrimeSpectrum.ext ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right x.2.ne_top)

/--
lemma `isMax_iff` / 引理 `isMax_iff`

English:
lemma isMax_iff
  given: {x : PrimeSpectrum R}
  proof: by
  refine ⟨fun hx => ⟨⟨x.2.ne_top, fun I hI => ?_⟩⟩, fun hx y e => (hx.eq_of_le y.2.ne_top e).ge⟩
  by_contra e
  obtain ⟨m, hm, hm'⟩ := Ideal.exists_le_maximal I e
  exact hx.not_lt (show x < ⟨m, hm.isPrime⟩ from hI.trans_le hm')

中文:
引理 isMax_iff
  条件: {x : PrimeSpectrum R}
  证明: by
  refine ⟨fun hx => ⟨⟨x.2.ne_top, fun I hI => ?_⟩⟩, fun hx y e => (hx.eq_of_le y.2.ne_top e).ge⟩
  by_contra e
  obtain ⟨m, hm, hm'⟩ := Ideal.exists_le_maximal I e
  exact hx.not_lt (show x < ⟨m, hm.isPrime⟩ from hI.trans_le hm')

Depends on / 依赖: Ideal.exists_le_maximal, eq_of_le, exists_le_maximal, hI.trans_le, hm.isPrime, hx.eq_of_le, hx.not_lt, isPrime, ne_top, not_lt, trans_le
-/
lemma isMax_iff {x : PrimeSpectrum R} :
    IsMax x ↔ x.asIdeal.IsMaximal := by
  refine ⟨fun hx => ⟨⟨x.2.ne_top, fun I hI => ?_⟩⟩, fun hx y e => (hx.eq_of_le y.2.ne_top e).ge⟩
  by_contra e
  obtain ⟨m, hm, hm'⟩ := Ideal.exists_le_maximal I e
  exact hx.not_lt (show x < ⟨m, hm.isPrime⟩ from hI.trans_le hm')

/--
lemma `zeroLocus_eq_singleton` / 引理 `zeroLocus_eq_singleton`

English:
lemma zeroLocus_eq_singleton
  given: (m : Ideal R) [m.IsMaximal]
  proof: by
  ext I
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [mem_zeroLocus, SetLike.coe_subset_coe] at h
    simpa using PrimeSpectrum.ext_iff.mpr (Ideal.IsMaximal.eq_of_le ‹_› I.2.ne_top h).symm
  · simp [Set.mem_singleton_iff.mp h]

中文:
引理 zeroLocus_eq_singleton
  条件: (m : Ideal R) [m.IsMaximal]
  证明: by
  ext I
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [mem_zeroLocus, SetLike.coe_subset_coe] at h
    simpa using PrimeSpectrum.ext_iff.mpr (Ideal.IsMaximal.eq_of_le ‹_› I.2.ne_top h).symm
  · simp [Set.mem_singleton_iff.mp h]

Depends on / 依赖: Ideal.IsMaximal.eq_of_le, IsMaximal, PrimeSpectrum, PrimeSpectrum.ext_iff.mpr, Set.mem_singleton_iff.mp, SetLike, SetLike.coe_subset_coe, coe_subset_coe, eq_of_le, ext_iff, mem_singleton_iff, mem_zeroLocus, ne_top
-/
lemma zeroLocus_eq_singleton (m : Ideal R) [m.IsMaximal] :
    zeroLocus m = {⟨m, inferInstance⟩} := by
  ext I
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [mem_zeroLocus, SetLike.coe_subset_coe] at h
    simpa using PrimeSpectrum.ext_iff.mpr (Ideal.IsMaximal.eq_of_le ‹_› I.2.ne_top h).symm
  · simp [Set.mem_singleton_iff.mp h]

/--
lemma `isMin_iff` / 引理 `isMin_iff`

English:
lemma isMin_iff
  given: {x : PrimeSpectrum R}
  proof: by
  change IsMin _ ↔ Minimal (fun q : Ideal R => q.IsPrime ∧ ⊥ <= q) _
  simp only [IsMin, Minimal, x.2, bot_le, and_self, and_true, true_and]
  exact ⟨fun H y hy e => @H ⟨y, hy⟩ e, fun H y e => H y.2 e⟩

中文:
引理 isMin_iff
  条件: {x : PrimeSpectrum R}
  证明: by
  change IsMin _ ↔ Minimal (fun q : Ideal R => q.IsPrime ∧ ⊥ <= q) _
  simp only [IsMin, Minimal, x.2, bot_le, and_self, and_true, true_and]
  exact ⟨fun H y hy e => @H ⟨y, hy⟩ e, fun H y e => H y.2 e⟩

Depends on / 依赖: IsPrime, Minimal, and_self, and_true, bot_le, q.IsPrime, true_and
-/
lemma isMin_iff {x : PrimeSpectrum R} :
    IsMin x ↔ x.asIdeal in minimalPrimes R := by
  change IsMin _ ↔ Minimal (fun q : Ideal R => q.IsPrime ∧ ⊥ <= q) _
  simp only [IsMin, Minimal, x.2, bot_le, and_self, and_true, true_and]
  exact ⟨fun H y hy e => @H ⟨y, hy⟩ e, fun H y e => H y.2 e⟩

end Order

section Noetherian

open Submodule

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/--
theorem `exists_primeSpectrum_prod_le` / 定理 `exists_primeSpectrum_prod_le`

English:
theorem exists_primeSpectrum_prod_le
  given: (I : Ideal R)
  proof: by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal R at M
  by_cases h_prM : M.IsPrime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton]; rw [Multiset.prod_singleton]
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : forall z ∉ M, M < M + sp

中文:
定理 exists_primeSpectrum_prod_le
  条件: (I : Ideal R)
  证明: by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal R at M
  by_cases h_prM : M.IsPrime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton]; rw [Multiset.prod_singleton]
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : forall z ∉ M, M < M + sp

Depends on / 依赖: Ideal.mem_sup_right, Ideal.not_isPrime_iff.mp, IsNoetherian, IsNoetherian.induction, IsPrime, M.IsPrime, Multiset, Multiset.map_singleton, Multiset.prod_singleton, h_prM, le_sup_left, le_top, lt_add, lt_of_le_of_ne, m_eq, map_singleton, mem_span_singleton_self, mem_sup_right, not_isPrime_iff, prod_singleton
-/
theorem exists_primeSpectrum_prod_le (I : Ideal R) :
    exists Z : Multiset (PrimeSpectrum R), Multiset.prod (Z.map asIdeal) <= I := by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal R at M
  by_cases h_prM : M.IsPrime
  · use {⟨M, h_prM⟩}
    rw [Multiset.map_singleton]; rw [Multiset.prod_singleton]
  by_cases htop : M = ⊤
  · rw [htop]
    exact ⟨0, le_top⟩
  have lt_add : forall z ∉ M, M < M + span R {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact Ideal.mem_sup_right (mem_span_singleton_self z)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left htop
  obtain ⟨Wx, h_Wx⟩ := hgt (M + span R {x}) (lt_add _ hx)
  obtain ⟨Wy, h_Wy⟩ := hgt (M + span R {y}) (lt_add _ hy)
  use Wx + Wy
  rw [Multiset.map_add]; rw [Multiset.prod_add]
  apply le_trans (mul_le_mul' h_Wx h_Wy)
  rw [add_mul]
  apply sup_le (show M * (M + span R {y}) <= M from Ideal.mul_le_left)
  rw [mul_add]
  apply sup_le (show span R {x} * M <= M from Ideal.mul_le_right)
  rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]

/--
theorem `exists_primeSpectrum_prod_le_and_ne_bot_of_domain` / 定理 `exists_primeSpectrum_prod_le_and_ne_bot_of_domain`

English:
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain
  statement: (h_fA : ¬IsField A) {I : Ideal A}
  proof: by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal A at M
  have hA_nont : Nontrivial A := IsDomain.toNontrivial
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : exists p : Ideal A, p != ⊥ ∧ p.IsPrime := by
      apply Ring.not_isFie

中文:
定理 exists_primeSpectrum_prod_le_and_ne_bot_of_domain
  结论: (h_fA : ¬IsField A) {I : Ideal A}
  证明: by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal A at M
  have hA_nont : Nontrivial A := IsDomain.toNontrivial
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : exists p : Ideal A, p != ⊥ ∧ p.IsPrime := by
      apply Ring.not_isFie

Depends on / 依赖: IsDomain, IsDomain.toNontrivial, IsNoetherian, IsNoetherian.induction, IsPrime, M.IsPrime, Multiset, Multiset.map_singleton, Multiset.prod_singleton, Nontrivial, PrimeSpectrum, Ring.not_isField_iff_exists_prime.mp, hA_nont, h_fA, h_nzp, h_pp, h_prM, h_topM, le_top, map_singleton
-/
theorem exists_primeSpectrum_prod_le_and_ne_bot_of_domain (h_fA : ¬IsField A) {I : Ideal A}
    (h_nzI : I != ⊥) :
    exists Z : Multiset (PrimeSpectrum A),
      Multiset.prod (Z.map asIdeal) <= I ∧ Multiset.prod (Z.map asIdeal) != ⊥ := by
  induction I using IsNoetherian.induction with | hgt M hgt =>
  change Ideal A at M
  have hA_nont : Nontrivial A := IsDomain.toNontrivial
  by_cases h_topM : M = ⊤
  · rcases h_topM with rfl
    obtain ⟨p_id, h_nzp, h_pp⟩ : exists p : Ideal A, p != ⊥ ∧ p.IsPrime := by
      apply Ring.not_isField_iff_exists_prime.mp h_fA
    use ({⟨p_id, h_pp⟩} : Multiset (PrimeSpectrum A)), le_top
    rwa [Multiset.map_singleton, Multiset.prod_singleton]
  by_cases h_prM : M.IsPrime
  · use ({⟨M, h_prM⟩} : Multiset (PrimeSpectrum A))
    rw [Multiset.map_singleton]; rw [Multiset.prod_singleton]
    exact ⟨le_rfl, h_nzI⟩
  obtain ⟨x, hx, y, hy, h_xy⟩ := (Ideal.not_isPrime_iff.mp h_prM).resolve_left h_topM
  have lt_add : forall z ∉ M, M < M + span A {z} := by
    intro z hz
    refine lt_of_le_of_ne le_sup_left fun m_eq => hz ?_
    rw [m_eq]
    exact mem_sup_right (mem_span_singleton_self z)
  obtain ⟨Wx, h_Wx_le, h_Wx_ne⟩ := hgt (M + span A {x}) (lt_add _ hx) (ne_bot_of_gt (lt_add _ hx))
  obtain ⟨Wy, h_Wy_le, h_Wx_ne⟩ := hgt (M + span A {y}) (lt_add _ hy) (ne_bot_of_gt (lt_add _ hy))
  use Wx + Wy
  rw [Multiset.map_add]; rw [Multiset.prod_add]
  refine ⟨le_trans (mul_le_mul' h_Wx_le h_Wy_le) ?_, mt Ideal.mul_eq_bot.mp ?_⟩
  · rw [add_mul]
    apply sup_le (show M * (M + span A {y}) <= M from Ideal.mul_le_left)
    rw [mul_add]
    apply sup_le (show span A {x} * M <= M from Ideal.mul_le_right)
    rwa [span_mul_span, Set.singleton_mul_singleton, span_singleton_le_iff_mem]
  · rintro (hx | hy) <;> contradiction

end Noetherian

end CommSemiRing

end PrimeSpectrum
