/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import Mathlib.Algebra.Ring.Torsion

/-!
# Structural lemmas about finite crystallographic root pairings

In this file we gather basic lemmas necessary for the classification of finite crystallographic
root pairings.

## Main results:

* `RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`: the Coxeter weights of a finite
  crystallographic root pairing belong to the set `{0, 1, 2, 3, 4}`.
* `RootPairing.root_sub_root_mem_of_pairingIn_pos`: if `α ≠ β` are both roots of a finite
  crystallographic root pairing, and the pairing of `α` with `β` is positive, then `α - β` is also
  a root.
* `RootPairing.root_add_root_mem_of_pairingIn_neg`: if `α ≠ -β` are both roots of a finite
  crystallographic root pairing, and the pairing of `α` with `β` is negative, then `α + β` is also
  a root.

-/

public section

noncomputable section

open Function Set
open Submodule (span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable (P : RootPairing ι R M N) [Finite ι]

local notation "Φ" => range P.root
local notation "α" => P.root

/--
lemma `coxeterWeightIn_le_four` / 引理 `coxeterWeightIn_le_four`

English:
lemma coxeterWeightIn_le_four
  statement: (S : Type*)
  proof: by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).rootLength i
  set lj := (P.posRootForm S).rootLength j
  set lij := (P.posRootForm S).posForm ri rj
  obtain ⟨si, hsi, hsi'⟩ := (P.posRootForm S).exists_pos_eq i
  obtain ⟨sj, hsj, hsj'⟩ := (P.posRootForm S).exists_pos_eq j
replace hsi' : si = li := algebraMap_injective S R by simpa [li] using hsi'
replace hsj' : sj = lj := algebraMap_injective S R by simpa [lj] using hsj'
  rw [hsi'] at hsi
  rw [hsj'] at hsj
  have cs : 4 * lij ^ 2 <= 4 * (li * lj) := by
    rw [mul_le_mul_iff_right₀ four_pos]
    exact (P.posRootForm S).posForm.apply_sq_le_of_symm (zero_le_posForm _ _ ·)
      (P.posRootForm S).isSymm_posForm ri rj
  have key : 4 • lij ^ 2 = P.coxeterWeightIn S i j • (li * lj) := by
    apply algebraMap_injective S R
    simpa [map_ofNat, lij, posRootForm, ri, rj, li, lj] using
       P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_iff_left₀ (by positivity)] at cs

中文:
引理 coxeterWeightIn_le_four
  结论: (S : 类型)
  证明: by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).rootLength i
  set lj := (P.posRootForm S).rootLength j
  set lij := (P.posRootForm S).posForm ri rj
  obtain ⟨si, hsi, hsi'⟩ := (P.posRootForm S).exists_pos_eq i
  obtain ⟨sj, hsj, hsj'⟩ := (P.posRootForm S).exists_pos_eq j
replace hsi' : si = li := algebraMap_injective S R by simpa [li] using hsi'
replace hsj' : sj = lj := algebraMap_injective S R by simpa [lj] using hsj'
  rw [hsi'] at hsi
  rw [hsj'] at hsj
  have cs : 4 * lij ^ 2 <= 4 * (li * lj) := by
    rw [mul_le_mul_iff_right₀ four_pos]
    exact (P.posRootForm S).posForm.apply_sq_le_of_symm (zero_le_posForm _ _ ·)
      (P.posRootForm S).isSymm_posForm ri rj
  have key : 4 • lij ^ 2 = P.coxeterWeightIn S i j • (li * lj) := by
    apply algebraMap_injective S R
    simpa [map_ofNat, lij, posRootForm, ri, rj, li, lj] using
       P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_iff_left₀ (by positivity)] at cs

Depends on / 依赖: Fintype, Fintype.ofFinite, P.posRootForm, Submodule, Submodule.subset_span, algebraMap_injective, exists_pos_eq, mem_range_self, ofFinite, posForm, posRootForm, replace, rootLength, subset_span
-/
lemma coxeterWeightIn_le_four (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] (i j : ι) :
    P.coxeterWeightIn S i j <= 4 := by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).rootLength i
  set lj := (P.posRootForm S).rootLength j
  set lij := (P.posRootForm S).posForm ri rj
  obtain ⟨si, hsi, hsi'⟩ := (P.posRootForm S).exists_pos_eq i
  obtain ⟨sj, hsj, hsj'⟩ := (P.posRootForm S).exists_pos_eq j
replace hsi' : si = li := algebraMap_injective S R by simpa [li] using hsi'
replace hsj' : sj = lj := algebraMap_injective S R by simpa [lj] using hsj'
  rw [hsi'] at hsi
  rw [hsj'] at hsj
  have cs : 4 * lij ^ 2 <= 4 * (li * lj) := by
    rw [mul_le_mul_iff_right₀ four_pos]
    exact (P.posRootForm S).posForm.apply_sq_le_of_symm (zero_le_posForm _ _ ·)
      (P.posRootForm S).isSymm_posForm ri rj
  have key : 4 • lij ^ 2 = P.coxeterWeightIn S i j • (li * lj) := by
    apply algebraMap_injective S R
    simpa [map_ofNat, lij, posRootForm, ri, rj, li, lj] using
       P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_iff_left₀ (by positivity)] at cs

variable [CharZero R] [P.IsCrystallographic] (i j : ι)

/--
lemma `coxeterWeightIn_mem_set_of_isCrystallographic` / 引理 `coxeterWeightIn_mem_set_of_isCrystallographic`

English:
lemma coxeterWeightIn_mem_set_of_isCrystallographic
  proof: by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hcn⟩ : exists n : Nat, P.coxeterWeightIn Int i j = n := by
    have : 0 <= P.coxeterWeightIn Int i j := by
      simpa only [P.algebraMap_coxeterWeightIn] using P.coxeterWeight_nonneg (P.posRootForm Int) i j
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le this
    exact ⟨n, by simp [hn]⟩
  have : P.coxeterWeightIn Int i j <= 4 := P.coxeterWeightIn_le_four Int i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  lia

中文:
引理 coxeterWeightIn_mem_set_of_isCrystallographic
  证明: by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hcn⟩ : exists n : Nat, P.coxeterWeightIn Int i j = n := by
    have : 0 <= P.coxeterWeightIn Int i j := by
      simpa only [P.algebraMap_coxeterWeightIn] using P.coxeterWeight_nonneg (P.posRootForm Int) i j
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le this
    exact ⟨n, by simp [hn]⟩
  have : P.coxeterWeightIn Int i j <= 4 := P.coxeterWeightIn_le_four Int i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  lia

Depends on / 依赖: Fintype, Fintype.ofFinite, Int.eq_ofNat_of_zero_le, P.algebraMap_coxeterWeightIn, P.coxeterWeightIn, P.coxeterWeightIn_le_four, P.coxeterWeight_nonneg, P.posRootForm, algebraMap_coxeterWeightIn, coxeterWeightIn, coxeterWeightIn_le_four, coxeterWeight_nonneg, eq_ofNat_of_zero_le, mem_insert_iff, mem_singleton_iff, ofFinite, posRootForm
-/
lemma coxeterWeightIn_mem_set_of_isCrystallographic :
    P.coxeterWeightIn Int i j in ({0, 1, 2, 3, 4} : Set Int) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hcn⟩ : exists n : Nat, P.coxeterWeightIn Int i j = n := by
    have : 0 <= P.coxeterWeightIn Int i j := by
      simpa only [P.algebraMap_coxeterWeightIn] using P.coxeterWeight_nonneg (P.posRootForm Int) i j
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le this
    exact ⟨n, by simp [hn]⟩
  have : P.coxeterWeightIn Int i j <= 4 := P.coxeterWeightIn_le_four Int i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  lia

variable [IsDomain R]
-- This makes an `IsAddTorsionFree R` instance available, which `grind` needs below.
open scoped IsDomain

/--
lemma `pairingIn_pairingIn_mem_set_of_isCrystallographic` / 引理 `pairingIn_pairingIn_mem_set_of_isCrystallographic`

English:
lemma pairingIn_pairingIn_mem_set_of_isCrystallographic
  proof: by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  simpa [← P.algebraMap_pairingIn Int] using P.pairing_eq_zero_iff' (i := i) (j := j)

中文:
引理 pairingIn_pairingIn_mem_set_of_isCrystallographic
  证明: by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  simpa [← P.algebraMap_pairingIn Int] using P.pairing_eq_zero_iff' (i := i) (j := j)

Depends on / 依赖: Int.mul_mem_zero_one_two_three_four_iff, P.algebraMap_pairingIn, P.coxeterWeightIn_mem_set_of_isCrystallographic, P.pairing_eq_zero_iff, algebraMap_pairingIn, coxeterWeightIn_mem_set_of_isCrystallographic, mul_mem_zero_one_two_three_four_iff, pairing_eq_zero_iff
-/
lemma pairingIn_pairingIn_mem_set_of_isCrystallographic :
    (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (Int × Int)) := by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  simpa [← P.algebraMap_pairingIn Int] using P.pairing_eq_zero_iff' (i := i) (j := j)

/--
lemma `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed` / 引理 `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`

English:
lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed
  given: [P.IsReduced]
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (α i) (-α j) with h₂ | h₂; · simp_all
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn Int i j * P.pairingIn Int j i != 4 := P.coxeterWeightIn_ne_four Int h₁ h₂
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

中文:
引理 pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed
  条件: [P.是既约]
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (α i) (-α j) with h₂ | h₂; · simp_all
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn Int i j * P.pairingIn Int j i != 4 := P.coxeterWeightIn_ne_four Int h₁ h₂
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.coxeterWeightIn_ne_four, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystallographic, P.toLinearMap, community, coxeterWeightIn_ne_four, eq_or_ne, faster, github, github.com, issues, leanprover, mathlib4, of_isPerfPair, pairingIn, pairingIn_pairingIn_mem_set_of_isCrystallographic, should
-/
lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] :
    (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (2, 2), (-2, -2)} : Set (Int × Int)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (α i) (-α j) with h₂ | h₂; · simp_all
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn Int i j * P.pairingIn Int j i != 4 := P.coxeterWeightIn_ne_four Int h₁ h₂
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

/--
lemma `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'` / 引理 `pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'`

English:
lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'
  statement: [P.IsReduced]
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  simp_all

中文:
引理 pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'
  结论: [P.是既约]
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  simp_all

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, P.toLinearMap, of_isPerfPair, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, toLinearMap
-/
lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced]
    (hij : α i != α j) (hij' : α i != -α j) :
    (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1)} : Set (Int × Int)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  simp_all

variable {P} in
/--
lemma `RootPositiveForm.rootLength_le_of_pairingIn_eq` / 引理 `RootPositiveForm.rootLength_le_of_pairingIn_eq`

English:
lemma RootPositiveForm.rootLength_le_of_pairingIn_eq
  statement: (B : P.RootPositiveForm Int) {i j : ι}
  proof: by
  have h : (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(1, 1), (1, 2), (1, 3), (1, 4), (-1, -1), (-1, -2), (-1, -3), (-1, -4)} : Set (Int × Int)) := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at h
  have h' := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases h with hij' | hij' | hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hij'.1]; rw [hij'.2] at h' <;> lia

中文:
引理 RootPositiveForm.rootLength_le_of_pairingIn_eq
  结论: (B : P.RootPositiveForm 整数) {i j : ι}
  证明: by
  have h : (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(1, 1), (1, 2), (1, 3), (1, 4), (-1, -1), (-1, -2), (-1, -3), (-1, -4)} : Set (Int × Int)) := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at h
  have h' := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases h with hij' | hij' | hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hij'.1]; rw [hij'.2] at h' <;> lia

Depends on / 依赖: B.pairingIn_mul_eq_pairingIn_mul_swap, B.rootLength_pos, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystallographic, Prod.mk.injEq, Prod.mk_eq_one, Prod.mk_one_one, community, faster, github, github.com, issues, leanprover, mathlib4, mem_insert_iff, mem_singleton_iff, mk_eq_one, mk_one_one, pairingIn, pairingIn_mul_eq_pairingIn_mul_swap
-/
lemma RootPositiveForm.rootLength_le_of_pairingIn_eq (B : P.RootPositiveForm Int) {i j : ι}
    (hij : P.pairingIn Int i j = -1 ∨ P.pairingIn Int i j = 1) :
    B.rootLength i <= B.rootLength j := by
  have h : (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(1, 1), (1, 2), (1, 3), (1, 4), (-1, -1), (-1, -2), (-1, -3), (-1, -4)} : Set (Int × Int)) := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at h
  have h' := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases h with hij' | hij' | hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hij'.1]; rw [hij'.2] at h' <;> lia

variable {P} in
/--
lemma `RootPositiveForm.rootLength_lt_of_pairingIn_notMem` / 引理 `RootPositiveForm.rootLength_lt_of_pairingIn_notMem`

English:
lemma RootPositiveForm.rootLength_lt_of_pairingIn_notMem
  proof: by
  have hij' : P.pairingIn Int i j = -3 ∨ P.pairingIn Int i j = -2 ∨ P.pairingIn Int i j = 2 ∨
      P.pairingIn Int i j = 3 ∨ P.pairingIn Int i j = -4 ∨ P.pairingIn Int i j = 4 := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₁ : P.pairingIn Int j i = -1 ∨ P.pairingIn Int j i = 1 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₂ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases aux₁ with hji | hji <;> rcases hij' with hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hji]; rw [hij'] at aux₂ <;> lia

中文:
引理 RootPositiveForm.rootLength_lt_of_pairingIn_notMem
  证明: by
  have hij' : P.pairingIn Int i j = -3 ∨ P.pairingIn Int i j = -2 ∨ P.pairingIn Int i j = 2 ∨
      P.pairingIn Int i j = 3 ∨ P.pairingIn Int i j = -4 ∨ P.pairingIn Int i j = 4 := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₁ : P.pairingIn Int j i = -1 ∨ P.pairingIn Int j i = 1 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₂ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases aux₁ with hji | hji <;> rcases hij' with hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hji]; rw [hij'] at aux₂ <;> lia

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.pairingIn, P.pairingIn_pairingIn_me, P.pairingIn_pairingIn_mem_set_of_isCrystallographic, P.toLinearMap, community, faster, github, github.com, issues, leanprover, mathlib4, of_isPerfPair, pairingIn, pairingIn_pairingIn_me, pairingIn_pairingIn_mem_set_of_isCrystallographic, should, toLinearMap
-/
lemma RootPositiveForm.rootLength_lt_of_pairingIn_notMem
    (B : P.RootPositiveForm Int) {i j : ι}
    (hne : α i != α j) (hne' : α i != -α j)
    (hij : P.pairingIn Int i j ∉ ({-1, 0, 1} : Set Int)) :
    B.rootLength j < B.rootLength i := by
  have hij' : P.pairingIn Int i j = -3 ∨ P.pairingIn Int i j = -2 ∨ P.pairingIn Int i j = 2 ∨
      P.pairingIn Int i j = 3 ∨ P.pairingIn Int i j = -4 ∨ P.pairingIn Int i j = 4 := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₁ : P.pairingIn Int j i = -1 ∨ P.pairingIn Int j i = 1 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₂ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases aux₁ with hji | hji <;> rcases hij' with hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hji]; rw [hij'] at aux₂ <;> lia

variable {i j} in
/--
lemma `pairingIn_pairingIn_mem_set_of_length_eq` / 引理 `pairingIn_pairingIn_mem_set_of_length_eq`

English:
lemma pairingIn_pairingIn_mem_set_of_length_eq
  statement: {B : P.InvariantForm}
  proof: by
  replace len_eq : P.pairingIn Int i j = P.pairingIn Int j i := by
    simp only [← (FaithfulSMul.algebraMap_injective Int R).eq_iff, algebraMap_pairingIn]
    exact mul_right_cancel₀ (B.ne_zero j) (len_eq ▸ B.pairing_mul_eq_pairing_mul_swap j i)
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

中文:
引理 pairingIn_pairingIn_mem_set_of_length_eq
  结论: {B : P.不变形式}
  证明: by
  replace len_eq : P.pairingIn Int i j = P.pairingIn Int j i := by
    simp only [← (FaithfulSMul.algebraMap_injective Int R).eq_iff, algebraMap_pairingIn]
    exact mul_right_cancel₀ (B.ne_zero j) (len_eq ▸ B.pairing_mul_eq_pairing_mul_swap j i)
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

Depends on / 依赖: B.ne_zero, B.pairing_mul_eq_pairing_mul_swap, FaithfulSMul, FaithfulSMul.algebraMap_injective, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystallographic, algebraMap_injective, algebraMap_pairingIn, community, eq_iff, faster, github, github.com, issues, leanprover, len_eq, mathlib4, ne_zero, pairingIn, pairingIn_pairingIn_mem_set_of_isCrystallographic
-/
lemma pairingIn_pairingIn_mem_set_of_length_eq {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j)) :
    (P.pairingIn Int i j, P.pairingIn Int j i) in
      ({(0, 0), (1, 1), (-1, -1), (2, 2), (-2, -2)} : Set (Int × Int)) := by
  replace len_eq : P.pairingIn Int i j = P.pairingIn Int j i := by
    simp only [← (FaithfulSMul.algebraMap_injective Int R).eq_iff, algebraMap_pairingIn]
    exact mul_right_cancel₀ (B.ne_zero j) (len_eq ▸ B.pairing_mul_eq_pairing_mul_swap j i)
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

variable {i j} in
/--
lemma `pairingIn_pairingIn_mem_set_of_length_eq_of_ne` / 引理 `pairingIn_pairingIn_mem_set_of_length_eq_of_ne`

English:
lemma pairingIn_pairingIn_mem_set_of_length_eq_of_ne
  statement: {B : P.InvariantForm}
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_length_eq len_eq
  simp_all

omit [Finite ι] in

中文:
引理 pairingIn_pairingIn_mem_set_of_length_eq_of_ne
  结论: {B : P.不变形式}
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_length_eq len_eq
  simp_all

omit [Finite ι] in

Depends on / 依赖: IsReflexive, Module, Module.IsReflexive, P.pairingIn_pairingIn_mem_set_of_length_eq, P.toLinearMap, len_eq, of_isPerfPair, pairingIn_pairingIn_mem_set_of_length_eq, toLinearMap
-/
lemma pairingIn_pairingIn_mem_set_of_length_eq_of_ne {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j))
    (ne : i != j) (ne' : α i != -α j) :
    (P.pairingIn Int i j, P.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1)} : Set (Int × Int)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_length_eq len_eq
  simp_all

omit [Finite ι] in
/--
lemma `coxeterWeightIn_eq_zero_iff` / 引理 `coxeterWeightIn_eq_zero_iff`

English:
lemma coxeterWeightIn_eq_zero_iff
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [coxeterWeightIn, h, zero_mul]⟩
  rwa [← (algebraMap_injective Int R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    RootPairing.coxeterWeight_zero_iff_isOrthogonal, IsOrthogonal,
    P.pairing_eq_zero_iff' (i := j) (j := i), and_self, ← P.algebraMap_pairingIn Int,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

中文:
引理 coxeterWeightIn_eq_zero_iff
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [coxeterWeightIn, h, zero_mul]⟩
  rwa [← (algebraMap_injective Int R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    RootPairing.coxeterWeight_zero_iff_isOrthogonal, IsOrthogonal,
    P.pairing_eq_zero_iff' (i := j) (j := i), and_self, ← P.algebraMap_pairingIn Int,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, IsOrthogonal, P.algebraMap_pairingIn, P.pairing_eq_zero_iff, RootPairing, RootPairing.coxeterWeight_zero_iff_isOrthogonal, algebraMap_coxeterWeightIn, algebraMap_eq_zero_iff, algebraMap_injective, algebraMap_pairingIn, and_self, coxeterWeightIn, coxeterWeight_zero_iff_isOrthogonal, eq_iff, map_zero, pairing_eq_zero_iff, zero_mul
-/
lemma coxeterWeightIn_eq_zero_iff :
    P.coxeterWeightIn Int i j = 0 ↔ P.pairingIn Int i j = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [coxeterWeightIn, h, zero_mul]⟩
  rwa [← (algebraMap_injective Int R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    RootPairing.coxeterWeight_zero_iff_isOrthogonal, IsOrthogonal,
    P.pairing_eq_zero_iff' (i := j) (j := i), and_self, ← P.algebraMap_pairingIn Int,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

variable {i j}

/--
lemma `root_sub_root_mem_of_pairingIn_pos` / 引理 `root_sub_root_mem_of_pairingIn_pos`

English:
lemma root_sub_root_mem_of_pairingIn_pos
  given: (h : 0 < P.pairingIn Int i j) (h' : i != j)
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn Int i j = 1 ∨ P.pairingIn Int j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn Int]
        exact ⟨P.reflectionPerm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn Int]
        rw [← neg_mem_range_root_iff]; rw [neg_sub]
        exact ⟨P.reflectionPerm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
    have : P.coxeterWeightIn Int i j in ({1, 2, 3} : Set _) := by
      have aux₁ := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
      have aux₂ := (linearIndependent_iff_coxeterWeightIn_ne_four P Int).mp hli
      have aux₃ : P.coxeterWeightIn Int i j != 0 := by
        simpa only [ne_eq, P.coxeterWeightIn_eq_zero_iff] using h.ne'
      simp_all
    simp_rw [coxeterWeightIn, Int.mul_mem_one_two_three_iff, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq] at this
    lia
  · -- The case where the two roots are linearly dependent
    have : (P.pairingIn Int i j, P.pairingIn Int j i) in ({(1, 4), (2, 2), (4, 1)} : Set _) := by
      have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
      replace hli : P.pairingIn Int i j * P.pairingIn Int j i = 4 :=
        (P.coxeterWeightIn_eq_four_iff_not_linearIndependent Int).mpr hli
      aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff Int i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff Int j i).mp hij, two_smul]

中文:
引理 root_sub_root_mem_of_pairingIn_pos
  条件: (h : 0 < P.pairingIn 整数 i j) (h' : i != j)
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn Int i j = 1 ∨ P.pairingIn Int j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn Int]
        exact ⟨P.reflectionPerm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn Int]
        rw [← neg_mem_range_root_iff]; rw [neg_sub]
        exact ⟨P.reflectionPerm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
    have : P.coxeterWeightIn Int i j in ({1, 2, 3} : Set _) := by
      have aux₁ := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
      have aux₂ := (linearIndependent_iff_coxeterWeightIn_ne_four P Int).mp hli
      have aux₃ : P.coxeterWeightIn Int i j != 0 := by
        simpa only [ne_eq, P.coxeterWeightIn_eq_zero_iff] using h.ne'
      simp_all
    simp_rw [coxeterWeightIn, Int.mul_mem_one_two_three_iff, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq] at this
    lia
  · -- The case where the two roots are linearly dependent
    have : (P.pairingIn Int i j, P.pairingIn Int j i) in ({(1, 4), (2, 2), (4, 1)} : Set _) := by
      have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
      replace hli : P.pairingIn Int i j * P.pairingIn Int j i = 4 :=
        (P.coxeterWeightIn_eq_four_iff_not_linearIndependent Int).mpr hli
      aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff Int i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff Int j i).mp hij, two_smul]

Depends on / 依赖: IsAddTorsionFree, IsReflexive, LinearIndependent, Module, Module.IsReflexive, P.algebraMap_pairingIn, P.flip.toLinearMap, P.pairing, P.pairingIn, P.reflectionPerm, P.toLinearMap, algebraMap_pairingIn, independent, linearly, of_isPerfPair, of_isTorsionFree, pairing, pairingIn, reflectionPerm, replace
-/
lemma root_sub_root_mem_of_pairingIn_pos (h : 0 < P.pairingIn Int i j) (h' : i != j) :
    α i - α j in Φ := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn Int i j = 1 ∨ P.pairingIn Int j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn Int]
        exact ⟨P.reflectionPerm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn Int]
        rw [← neg_mem_range_root_iff]; rw [neg_sub]
        exact ⟨P.reflectionPerm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
    have : P.coxeterWeightIn Int i j in ({1, 2, 3} : Set _) := by
      have aux₁ := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
      have aux₂ := (linearIndependent_iff_coxeterWeightIn_ne_four P Int).mp hli
      have aux₃ : P.coxeterWeightIn Int i j != 0 := by
        simpa only [ne_eq, P.coxeterWeightIn_eq_zero_iff] using h.ne'
      simp_all
    simp_rw [coxeterWeightIn, Int.mul_mem_one_two_three_iff, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq] at this
    lia
  · -- The case where the two roots are linearly dependent
    have : (P.pairingIn Int i j, P.pairingIn Int j i) in ({(1, 4), (2, 2), (4, 1)} : Set _) := by
      have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
      replace hli : P.pairingIn Int i j * P.pairingIn Int j i = 4 :=
        (P.coxeterWeightIn_eq_four_iff_not_linearIndependent Int).mpr hli
      aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff Int i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff Int j i).mp hij, two_smul]

/--
lemma `root_add_root_mem_of_pairingIn_neg` / 引理 `root_add_root_mem_of_pairingIn_neg`

English:
lemma root_add_root_mem_of_pairingIn_neg
  given: (h : P.pairingIn Int i j < 0) (h' : α i != -α j)
  proof: by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn Int i (-j) := by simpa
  replace h' : i != -j := by contrapose h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'

中文:
引理 root_add_root_mem_of_pairingIn_neg
  条件: (h : P.pairingIn 整数 i j < 0) (h' : α i != -α j)
  证明: by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn Int i (-j) := by simpa
  replace h' : i != -j := by contrapose h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'

Depends on / 依赖: P.indexNeg, P.pairingIn, P.root_sub_root_mem_of_pairingIn_pos, contrapose, indexNeg, pairingIn, replace, root_sub_root_mem_of_pairingIn_pos
-/
lemma root_add_root_mem_of_pairingIn_neg (h : P.pairingIn Int i j < 0) (h' : α i != -α j) :
    α i + α j in Φ := by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn Int i (-j) := by simpa
  replace h' : i != -j := by contrapose h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'

/--
lemma `pairingIn_eq_zero_of_add_notMem_of_sub_notMem` / 引理 `pairingIn_eq_zero_of_add_notMem_of_sub_notMem`

English:
lemma pairingIn_eq_zero_of_add_notMem_of_sub_notMem
  statement: (hp : i != j) (hn : α i != -α j)
  proof: by
  apply le_antisymm
  · contrapose! h_sub
    exact root_sub_root_mem_of_pairingIn_pos P h_sub hp
  · contrapose! h_add
    exact root_add_root_mem_of_pairingIn_neg P h_add hn

中文:
引理 pairingIn_eq_zero_of_add_notMem_of_sub_notMem
  结论: (hp : i != j) (hn : α i != -α j)
  证明: by
  apply le_antisymm
  · contrapose! h_sub
    exact root_sub_root_mem_of_pairingIn_pos P h_sub hp
  · contrapose! h_add
    exact root_add_root_mem_of_pairingIn_neg P h_add hn

Depends on / 依赖: contrapose, h_add, h_sub, le_antisymm, root_add_root_mem_of_pairingIn_neg, root_sub_root_mem_of_pairingIn_pos
-/
lemma pairingIn_eq_zero_of_add_notMem_of_sub_notMem (hp : i != j) (hn : α i != -α j)
    (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) :
    P.pairingIn Int i j = 0 := by
  apply le_antisymm
  · contrapose! h_sub
    exact root_sub_root_mem_of_pairingIn_pos P h_sub hp
  · contrapose! h_add
    exact root_add_root_mem_of_pairingIn_neg P h_add hn

/--
lemma `pairing_eq_zero_of_add_notMem_of_sub_notMem` / 引理 `pairing_eq_zero_of_add_notMem_of_sub_notMem`

English:
lemma pairing_eq_zero_of_add_notMem_of_sub_notMem
  statement: (hp : i != j) (hn : α i != -α j)
  proof: by
  rw [← P.algebraMap_pairingIn Int]; rw [P.pairingIn_eq_zero_of_add_notMem_of_sub_notMem hp hn h_add h_sub]; rw [map_zero]

omit [Finite ι] in

中文:
引理 pairing_eq_zero_of_add_notMem_of_sub_notMem
  结论: (hp : i != j) (hn : α i != -α j)
  证明: by
  rw [← P.algebraMap_pairingIn Int]; rw [P.pairingIn_eq_zero_of_add_notMem_of_sub_notMem hp hn h_add h_sub]; rw [map_zero]

omit [Finite ι] in

Depends on / 依赖: P.algebraMap_pairingIn, P.pairingIn_eq_zero_of_add_notMem_of_sub_notMem, algebraMap_pairingIn, h_add, h_sub, map_zero, pairingIn_eq_zero_of_add_notMem_of_sub_notMem
-/
lemma pairing_eq_zero_of_add_notMem_of_sub_notMem (hp : i != j) (hn : α i != -α j)
    (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) :
    P.pairing i j = 0 := by
  rw [← P.algebraMap_pairingIn Int]; rw [P.pairingIn_eq_zero_of_add_notMem_of_sub_notMem hp hn h_add h_sub]; rw [map_zero]

omit [Finite ι] in
/--
lemma `root_mem_submodule_iff_of_add_mem_invtSubmodule` / 引理 `root_mem_submodule_iff_of_add_mem_invtSubmodule`

English:
lemma root_mem_submodule_iff_of_add_mem_invtSubmodule
  proof: by
  obtain ⟨q, hq⟩ := q
  rw [mem_invtRootSubmodule_iff] at hq
  suffices forall i j, P.root i + P.root j in range P.root -> P.root i in q -> P.root j in q by
    have aux := this j i (by rwa [add_comm]); tauto
  rintro i j ⟨k, hk⟩ hi
  rcases eq_or_ne (P.pairing i j) 0 with hij₀ | hij₀
  · have hik : P.pairing i k != 0 := by
      rw [ne_eq]; rw [P.pairing_eq_zero_iff]; rw [← root_coroot_eq_pairing]; rw [hk]
      simpa [P.pairing_eq_zero_iff.mp hij₀] using two_ne_zero
suffices P.root k in q from (q.add_mem_iff_right hi).mp hk ▸ this
    replace hq : P.root i - P.pairing i k • P.root k in q := by
      simpa [reflection_apply_root] using hq k hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hik] at hq
  · replace hq : P.root i - P.pairing i j • P.root j in q := by
      simpa [reflection_apply_root] using hq j hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hij₀] at hq

中文:
引理 root_mem_submodule_iff_of_add_mem_invtSubmodule
  证明: by
  obtain ⟨q, hq⟩ := q
  rw [mem_invtRootSubmodule_iff] at hq
  suffices forall i j, P.root i + P.root j in range P.root -> P.root i in q -> P.root j in q by
    have aux := this j i (by rwa [add_comm]); tauto
  rintro i j ⟨k, hk⟩ hi
  rcases eq_or_ne (P.pairing i j) 0 with hij₀ | hij₀
  · have hik : P.pairing i k != 0 := by
      rw [ne_eq]; rw [P.pairing_eq_zero_iff]; rw [← root_coroot_eq_pairing]; rw [hk]
      simpa [P.pairing_eq_zero_iff.mp hij₀] using two_ne_zero
suffices P.root k in q from (q.add_mem_iff_right hi).mp hk ▸ this
    replace hq : P.root i - P.pairing i k • P.root k in q := by
      simpa [reflection_apply_root] using hq k hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hik] at hq
  · replace hq : P.root i - P.pairing i j • P.root j in q := by
      simpa [reflection_apply_root] using hq j hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hij₀] at hq

Depends on / 依赖: P.pairing, P.pairing_eq_zero_iff, P.pairing_eq_zero_iff.mp, P.root, add_comm, add_mem_iff_right, eq_or_ne, mem_invtRootSubmodule_iff, ne_eq, pairing, pairing_eq_zero_iff, q.add_mem_iff_right, root_coroot_eq_pairing, two_ne_zero
-/
lemma root_mem_submodule_iff_of_add_mem_invtSubmodule
    {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N] {P : RootPairing ι K M N}
    (q : P.invtRootSubmodule)
    (hij : P.root i + P.root j in range P.root) :
    P.root i in (q : Submodule K M) ↔ P.root j in (q : Submodule K M) := by
  obtain ⟨q, hq⟩ := q
  rw [mem_invtRootSubmodule_iff] at hq
  suffices forall i j, P.root i + P.root j in range P.root -> P.root i in q -> P.root j in q by
    have aux := this j i (by rwa [add_comm]); tauto
  rintro i j ⟨k, hk⟩ hi
  rcases eq_or_ne (P.pairing i j) 0 with hij₀ | hij₀
  · have hik : P.pairing i k != 0 := by
      rw [ne_eq]; rw [P.pairing_eq_zero_iff]; rw [← root_coroot_eq_pairing]; rw [hk]
      simpa [P.pairing_eq_zero_iff.mp hij₀] using two_ne_zero
suffices P.root k in q from (q.add_mem_iff_right hi).mp hk ▸ this
    replace hq : P.root i - P.pairing i k • P.root k in q := by
      simpa [reflection_apply_root] using hq k hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hik] at hq
  · replace hq : P.root i - P.pairing i j • P.root j in q := by
      simpa [reflection_apply_root] using hq j hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hij₀] at hq

namespace InvariantForm

variable [P.IsReduced] (B : P.InvariantForm)
variable {P}

/--
lemma `apply_eq_or_aux` / 引理 `apply_eq_or_aux`

English:
lemma apply_eq_or_aux
  given: (i j : ι) (h : P.pairingIn Int i j != 0)
  proof: by
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have h₂ : algebraMap Int R (P.pairingIn Int j i) * B.form (α i) (α i) =
            algebraMap Int R (P.pairingIn Int i j) * B.form (α j) (α j) := by
    simpa only [algebraMap_pairingIn] using B.pairing_mul_eq_pairing_mul_swap i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

中文:
引理 apply_eq_or_aux
  条件: (i j : ι) (h : P.pairingIn 整数 i j != 0)
  证明: by
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have h₂ : algebraMap Int R (P.pairingIn Int j i) * B.form (α i) (α i) =
            algebraMap Int R (P.pairingIn Int i j) * B.form (α j) (α j) := by
    simpa only [algebraMap_pairingIn] using B.pairing_mul_eq_pairing_mul_swap i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

Depends on / 依赖: B.form, B.pairing_mul_eq_pairing_mul_swap, P.pairingIn, P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, algebraMap, algebraMap_pairingIn, community, faster, github, github.com, issues, leanprover, mathlib4, pairingIn, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, pairing_mul_eq_pairing_mul_swap, should
-/
lemma apply_eq_or_aux (i j : ι) (h : P.pairingIn Int i j != 0) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have h₂ : algebraMap Int R (P.pairingIn Int j i) * B.form (α i) (α i) =
            algebraMap Int R (P.pairingIn Int i j) * B.form (α j) (α j) := by
    simpa only [algebraMap_pairingIn] using B.pairing_mul_eq_pairing_mul_swap i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

variable [P.IsIrreducible]

/--
lemma `apply_eq_or` / 引理 `apply_eq_or`

English:
lemma apply_eq_or
  given: (i j : ι)
  proof: by
  obtain ⟨j', h₁, h₂⟩ := P.exists_form_eq_form_and_form_ne_zero B i j
  suffices P.pairingIn Int i j' != 0 by simp only [← h₁, B.apply_eq_or_aux i j' this]
  contrapose h₂
  replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn Int, h₂, map_zero]
  exact (B.apply_root_root_zero_iff i j').mpr h₂

中文:
引理 apply_eq_or
  条件: (i j : ι)
  证明: by
  obtain ⟨j', h₁, h₂⟩ := P.exists_form_eq_form_and_form_ne_zero B i j
  suffices P.pairingIn Int i j' != 0 by simp only [← h₁, B.apply_eq_or_aux i j' this]
  contrapose h₂
  replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn Int, h₂, map_zero]
  exact (B.apply_root_root_zero_iff i j').mpr h₂

Depends on / 依赖: B.apply_eq_or_aux, B.apply_root_root_zero_iff, IsEmpty, IsFiniteMeasure, P.algebraMap_pairingIn, P.exists_form_eq_form_and_form_ne_zero, P.pairing, P.pairingIn, algebraMap_pairingIn, apply_eq_or_aux, apply_root_root_zero_iff, contrapose, eq_zero_of_isEmpty, exists_form_eq_form_and_form_ne_zero, infer_instance, isFiniteMeasureOfIsEmpty, map_zero, pairing, pairingIn, replace
-/
lemma apply_eq_or (i j : ι) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  obtain ⟨j', h₁, h₂⟩ := P.exists_form_eq_form_and_form_ne_zero B i j
  suffices P.pairingIn Int i j' != 0 by simp only [← h₁, B.apply_eq_or_aux i j' this]
  contrapose h₂
  replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn Int, h₂, map_zero]
  exact (B.apply_root_root_zero_iff i j').mpr h₂

/--
lemma `exists_apply_eq_or` / 引理 `exists_apply_eq_or`

English:
lemma exists_apply_eq_or
  given: [Nonempty ι]
  statement: exists i j, forall k,
  proof: by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  by_cases! h : (forall j, B.form (α j) (α j) = B.form (α i) (α i))
  · refine ⟨i, i, fun j => by simp [h j]⟩
  · obtain ⟨j, hji_ne⟩ := h
    refine ⟨i, j, fun k => ?_⟩
    by_contra! ⟨hki_ne, hkj_ne⟩
    have hij := (B.apply_eq_or i j).resolve_left hji_ne.symm
    have hik := (B.apply_eq_or i k).resolve_left hki_ne.symm
    have hjk := (B.apply_eq_or j k).resolve_left hkj_ne.symm
    grind

中文:
引理 存在_apply_eq_or
  条件: [非空 ι]
  结论: 存在 i j, 对任意 k,
  证明: by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  by_cases! h : (forall j, B.form (α j) (α j) = B.form (α i) (α i))
  · refine ⟨i, i, fun j => by simp [h j]⟩
  · obtain ⟨j, hji_ne⟩ := h
    refine ⟨i, j, fun k => ?_⟩
    by_contra! ⟨hki_ne, hkj_ne⟩
    have hij := (B.apply_eq_or i j).resolve_left hji_ne.symm
    have hik := (B.apply_eq_or i k).resolve_left hki_ne.symm
    have hjk := (B.apply_eq_or j k).resolve_left hkj_ne.symm
    grind

Depends on / 依赖: B.apply_eq_or, B.form, Nonempty, apply_eq_or, hji_ne, hji_ne.symm, hki_ne, hki_ne.symm, hkj_ne, hkj_ne.symm, resolve_left
-/
lemma exists_apply_eq_or [Nonempty ι] : exists i j, forall k,
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  by_cases! h : (forall j, B.form (α j) (α j) = B.form (α i) (α i))
  · refine ⟨i, i, fun j => by simp [h j]⟩
  · obtain ⟨j, hji_ne⟩ := h
    refine ⟨i, j, fun k => ?_⟩
    by_contra! ⟨hki_ne, hkj_ne⟩
    have hij := (B.apply_eq_or i j).resolve_left hji_ne.symm
    have hik := (B.apply_eq_or i k).resolve_left hki_ne.symm
    have hjk := (B.apply_eq_or j k).resolve_left hkj_ne.symm
    grind

/--
lemma `apply_eq_or_of_apply_ne` / 引理 `apply_eq_or_of_apply_ne`

English:
lemma apply_eq_or_of_apply_ne
  proof: by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i', j', h'⟩ := B.exists_apply_eq_or
  rcases h' i with hi | hi <;>
  rcases h' j with hj | hj <;>
  specialize h' k <;>
  aesop

中文:
引理 apply_eq_or_of_apply_ne
  证明: by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i', j', h'⟩ := B.exists_apply_eq_or
  rcases h' i with hi | hi <;>
  rcases h' j with hj | hj <;>
  specialize h' k <;>
  aesop

Depends on / 依赖: B.exists_apply_eq_or, Nonempty, exists_apply_eq_or, specialize
-/
lemma apply_eq_or_of_apply_ne
    (h : B.form (α i) (α i) != B.form (α j) (α j)) (k : ι) :
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i', j', h'⟩ := B.exists_apply_eq_or
  rcases h' i with hi | hi <;>
  rcases h' j with hj | hj <;>
  specialize h' k <;>
  aesop

end InvariantForm

/--
lemma `forall_pairing_eq_swap_or` / 引理 `forall_pairing_eq_swap_or`

English:
lemma forall_pairing_eq_swap_or
  given: [P.IsReduced] [P.IsIrreducible]
  proof: by
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  by_cases! h : forall i j, B.form (α i) (α i) = B.form (α j) (α j)
  · refine Or.inl fun i j => Or.inl ?_
    have := B.pairing_mul_eq_pairing_mul_swap j i
    rwa [h i j, mul_left_inj' (B.ne_zero j)] at this
  obtain ⟨i, j, hij⟩ := h
  have key := B.apply_eq_or_of_apply_ne hij
  set li := B.form (α i) (α i)
  set lj := B.form (α j) (α j)
  have : (li = 2 * lj ∨ lj = 2 * li) ∨ (li = 3 * lj ∨ lj = 3 * li) := by
    have := B.apply_eq_or i j; tauto
  rcases this with this | this
  · refine Or.inl fun k₁ k₂ => ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  · refine Or.inr fun k₁ k₂ => ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

中文:
引理 对任意_pairing_eq_swap_or
  条件: [P.是既约] [P.是不可约]
  证明: by
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  by_cases! h : forall i j, B.form (α i) (α i) = B.form (α j) (α j)
  · refine Or.inl fun i j => Or.inl ?_
    have := B.pairing_mul_eq_pairing_mul_swap j i
    rwa [h i j, mul_left_inj' (B.ne_zero j)] at this
  obtain ⟨i, j, hij⟩ := h
  have key := B.apply_eq_or_of_apply_ne hij
  set li := B.form (α i) (α i)
  set lj := B.form (α j) (α j)
  have : (li = 2 * lj ∨ lj = 2 * li) ∨ (li = 3 * lj ∨ lj = 3 * li) := by
    have := B.apply_eq_or i j; tauto
  rcases this with this | this
  · refine Or.inl fun k₁ k₂ => ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  · refine Or.inr fun k₁ k₂ => ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

Depends on / 依赖: B.apply_eq_, B.apply_eq_or_of_apply_ne, B.form, B.ne_zero, B.pairing_mul_eq_pairing_mul_swap, Fintype, Fintype.ofFinite, Or.inl, P.posRootForm, apply_eq_, apply_eq_or_of_apply_ne, mul_left_inj, ne_zero, ofFinite, pairing_mul_eq_pairing_mul_swap, posRootForm, toInvariantForm
-/
lemma forall_pairing_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (forall i j, P.pairing i j = P.pairing j i ∨
            P.pairing i j = 2 * P.pairing j i ∨
            P.pairing j i = 2 * P.pairing i j) ∨
    (forall i j, P.pairing i j = P.pairing j i ∨
            P.pairing i j = 3 * P.pairing j i ∨
            P.pairing j i = 3 * P.pairing i j) := by
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm Int).toInvariantForm
  by_cases! h : forall i j, B.form (α i) (α i) = B.form (α j) (α j)
  · refine Or.inl fun i j => Or.inl ?_
    have := B.pairing_mul_eq_pairing_mul_swap j i
    rwa [h i j, mul_left_inj' (B.ne_zero j)] at this
  obtain ⟨i, j, hij⟩ := h
  have key := B.apply_eq_or_of_apply_ne hij
  set li := B.form (α i) (α i)
  set lj := B.form (α j) (α j)
  have : (li = 2 * lj ∨ lj = 2 * li) ∨ (li = 3 * lj ∨ lj = 3 * li) := by
    have := B.apply_eq_or i j; tauto
  rcases this with this | this
  · refine Or.inl fun k₁ k₂ => ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  · refine Or.inr fun k₁ k₂ => ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

/--
lemma `forall_pairingIn_eq_swap_or` / 引理 `forall_pairingIn_eq_swap_or`

English:
lemma forall_pairingIn_eq_swap_or
  given: [P.IsReduced] [P.IsIrreducible]
  proof: by
  simpa only [← P.algebraMap_pairingIn Int, eq_intCast, ← Int.cast_mul, Int.cast_inj,
    ← map_ofNat (algebraMap Int R)] using P.forall_pairing_eq_swap_or

中文:
引理 对任意_pairingIn_eq_swap_or
  条件: [P.是既约] [P.是不可约]
  证明: by
  simpa only [← P.algebraMap_pairingIn Int, eq_intCast, ← Int.cast_mul, Int.cast_inj,
    ← map_ofNat (algebraMap Int R)] using P.forall_pairing_eq_swap_or

Depends on / 依赖: Int.cast_inj, Int.cast_mul, P.algebraMap_pairingIn, P.forall_pairing_eq_swap_or, algebraMap, algebraMap_pairingIn, cast_inj, cast_mul, eq_intCast, forall_pairing_eq_swap_or, map_ofNat
-/
lemma forall_pairingIn_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (forall i j, P.pairingIn Int i j = P.pairingIn Int j i ∨
            P.pairingIn Int i j = 2 * P.pairingIn Int j i ∨
            P.pairingIn Int j i = 2 * P.pairingIn Int i j) ∨
    (forall i j, P.pairingIn Int i j = P.pairingIn Int j i ∨
            P.pairingIn Int i j = 3 * P.pairingIn Int j i ∨
            P.pairingIn Int j i = 3 * P.pairingIn Int i j) := by
  simpa only [← P.algebraMap_pairingIn Int, eq_intCast, ← Int.cast_mul, Int.cast_inj,
    ← map_ofNat (algebraMap Int R)] using P.forall_pairing_eq_swap_or

end RootPairing
