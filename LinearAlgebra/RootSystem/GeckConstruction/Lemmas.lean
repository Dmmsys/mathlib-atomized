/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.G2

/-!
# Supporting lemmas for Geck's construction of a Lie algebra associated to a root system
-/

public section

open Set
open FaithfulSMul (algebraMap_injective)

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic]

local notation "Φ" => range P.root
local notation "α" => P.root

namespace Base

variable {b : P.Base} (i j k : ι) (hij : i != j) (hi : i in b.support) (hj : j in b.support)
include hij hi hj

/--
lemma `root_sub_root_mem_of_mem_of_mem` / 引理 `root_sub_root_mem_of_mem_of_mem`

English:
lemma root_sub_root_mem_of_mem_of_mem
  statement: (hk : α k + α i - α j in Φ)
  proof: by
  rcases lt_or_ge 0 (P.pairingIn Int j k) with hm | hm
  · rw [← neg_mem_range_root_iff, neg_sub]
    exact P.root_sub_root_mem_of_pairingIn_pos hm hkj.symm
  obtain ⟨l, hl⟩ := hk
  have hli : l != i := by
    rintro rfl
    rw [add_comm]; rw [add_sub_assoc]; rw [left_eq_add]; rw [sub_eq_zero]; r

中文:
引理 root_sub_root_mem_of_mem_of_mem
  结论: (hk : α k + α i - α j in Φ)
  证明: by
  rcases lt_or_ge 0 (P.pairingIn Int j k) with hm | hm
  · rw [← neg_mem_range_root_iff, neg_sub]
    exact P.root_sub_root_mem_of_pairingIn_pos hm hkj.symm
  obtain ⟨l, hl⟩ := hk
  have hli : l != i := by
    rintro rfl
    rw [add_comm]; rw [add_sub_assoc]; rw [left_eq_add]; rw [sub_eq_zero]; r

Depends on / 依赖: P.pairingIn, P.root.injective.eq_iff, P.root_sub_root_mem_of_pairingIn_pos, add_comm, add_sub_assoc, convert, eq_iff, hkj.symm, injective, left_eq_add, lt_or_ge, module, neg_mem_range_root_iff, neg_sub, pairingIn, root_sub_root_mem_of_pairingIn_pos, sub_eq_zero
-/
lemma root_sub_root_mem_of_mem_of_mem (hk : α k + α i - α j in Φ)
    (hkj : k != j) (hk' : α k + α i in Φ) :
    α k - α j in Φ := by
  rcases lt_or_ge 0 (P.pairingIn Int j k) with hm | hm
  · rw [← neg_mem_range_root_iff, neg_sub]
    exact P.root_sub_root_mem_of_pairingIn_pos hm hkj.symm
  obtain ⟨l, hl⟩ := hk
  have hli : l != i := by
    rintro rfl
    rw [add_comm]; rw [add_sub_assoc]; rw [left_eq_add]; rw [sub_eq_zero]; rw [P.root.injective.eq_iff] at hl
    exact hkj hl
  suffices 0 < P.pairingIn Int l i by
    convert! P.root_sub_root_mem_of_pairingIn_pos this hli using 1
    rw [hl]
    module
have hkl : l != k := by rintro rfl; exact hij by simpa [add_sub_assoc, sub_eq_zero] using hl
  replace hkl : P.pairingIn Int l k <= 0 := by
    suffices α l - α k ∉ Φ by contrapose! this; exact P.root_sub_root_mem_of_pairingIn_pos this hkl
    replace hl : α l - α k = α i - α j := by rw [hl]; module
    rw [hl]
    exact b.sub_notMem_range_root hi hj
  have hki : P.pairingIn Int i k <= -2 := by
    suffices P.pairingIn Int l k = 2 + P.pairingIn Int i k - P.pairingIn Int j k by linarith
    apply algebraMap_injective Int R
    simp only [algebraMap_pairingIn, map_sub, map_add]
    simpa using (P.coroot' k : M ->ₗ[R] R).congr_arg hl
  replace hki : P.pairingIn Int k i = -1 := by
    replace hk' : α i != - α k := by
      rw [← sub_ne_zero]; rw [sub_neg_eq_add]; rw [add_comm]
      intro contra
      rw [contra] at hk'
      exact P.ne_zero _ hk'.choose_spec
    have aux (h : P.pairingIn Int i k = -2) : ¬P.pairingIn Int k i = -2 := by
      have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
      contrapose hk'; exact (P.pairingIn_neg_two_neg_two_iff Int i k).mp ⟨h, hk'⟩
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i k
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  replace hki : P.pairing k i = -1 := by rw [← P.algebraMap_pairingIn Int, hki]; simp
  have : P.pairingIn Int l i = 1 - P.pairingIn Int j i := by
    apply algebraMap_injective Int R
    simp only [algebraMap_pairingIn, map_sub, map_one, algebraMap_pairingIn]
    convert! (P.coroot' i : M ->ₗ[R] R).congr_arg hl using 1
    simp only [map_sub, map_add, LinearMap.flip_apply, root_coroot_eq_pairing, hki, pairing_same,
      sub_left_inj]
    ring
  replace hij := pairingIn_le_zero_of_ne b hij.symm hj hi
  omega

/--
lemma `root_add_root_mem_of_mem_of_mem` / 引理 `root_add_root_mem_of_mem_of_mem`

English:
lemma root_add_root_mem_of_mem_of_mem
  statement: (hk : α k + α i - α j in Φ)
  proof: by
  let _i := P.indexNeg
  replace hk : α (-k) + α j - α i in Φ := by
    rw [← neg_mem_range_root_iff]
    convert! hk using 1
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
    module
  rw [← neg_mem_range_root_iff]
  convert!
    b.root_sub_root_mem_of_mem_of_mem j i (-

中文:
引理 root_add_root_mem_of_mem_of_mem
  结论: (hk : α k + α i - α j in Φ)
  证明: by
  let _i := P.indexNeg
  replace hk : α (-k) + α j - α i in Φ := by
    rw [← neg_mem_range_root_iff]
    convert! hk using 1
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
    module
  rw [← neg_mem_range_root_iff]
  convert!
    b.root_sub_root_mem_of_mem_of_mem j i (-

Depends on / 依赖: P.indexNeg, P.neg_mem_range_root_iff.mpr, b.root_sub_root_mem_of_mem_of_mem, contrapose, convert, hij.symm, indexNeg, indexNeg_neg, module, neg_add_eq_sub, neg_mem_range_root_iff, reflection_apply_self, replace, root_reflectionPerm, root_sub_root_mem_of_mem_of_mem
-/
lemma root_add_root_mem_of_mem_of_mem (hk : α k + α i - α j in Φ)
    (hkj : α k != -α i) (hk' : α k - α j in Φ) :
    α k + α i in Φ := by
  let _i := P.indexNeg
  replace hk : α (-k) + α j - α i in Φ := by
    rw [← neg_mem_range_root_iff]
    convert! hk using 1
    simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
    module
  rw [← neg_mem_range_root_iff]
  convert!
    b.root_sub_root_mem_of_mem_of_mem j i (-k) hij.symm hj hi hk (by contrapose hkj; aesop)
      (by convert! P.neg_mem_range_root_iff.mpr hk' using 1; simp [neg_add_eq_sub]) using 1
  simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self]
  module

/--
lemma `root_sub_mem_iff_root_add_mem` / 引理 `root_sub_mem_iff_root_add_mem`

English:
lemma root_sub_mem_iff_root_add_mem
  given: (hkj : k != j) (hkj' : α k != -α i) (hk : α k + α i - α j in Φ)
  proof: ⟨b.root_add_root_mem_of_mem_of_mem i j k hij hi hj hk hkj',
   b.root_sub_root_mem_of_mem_of_mem i j k hij hi hj hk hkj⟩

中文:
引理 root_sub_mem_iff_root_add_mem
  条件: (hkj : k != j) (hkj' : α k != -α i) (hk : α k + α i - α j in Φ)
  证明: ⟨b.root_add_root_mem_of_mem_of_mem i j k hij hi hj hk hkj',
   b.root_sub_root_mem_of_mem_of_mem i j k hij hi hj hk hkj⟩

Depends on / 依赖: b.root_add_root_mem_of_mem_of_mem, b.root_sub_root_mem_of_mem_of_mem, root_add_root_mem_of_mem_of_mem, root_sub_root_mem_of_mem_of_mem
-/
lemma root_sub_mem_iff_root_add_mem (hkj : k != j) (hkj' : α k != -α i) (hk : α k + α i - α j in Φ) :
    α k - α j in Φ ↔ α k + α i in Φ :=
  ⟨b.root_add_root_mem_of_mem_of_mem i j k hij hi hj hk hkj',
   b.root_sub_root_mem_of_mem_of_mem i j k hij hi hj hk hkj⟩

end Base

section chainBotCoeff_mul_chainTopCoeff

/-! The proof of Lemma 2.6 from [Geck](Geck2017). -/

variable {b : P.Base} {i j k l m : ι}

set_option linter.overlappingInstances false in
/--
lemma `chainBotCoeff_mul_chainTopCoeff.aux_0` / 引理 `chainBotCoeff_mul_chainTopCoeff.aux_0`

English:
lemma chainBotCoeff_mul_chainTopCoeff.aux_0
  statement: [P.IsNotG2]
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := pairingIn_le_zero_of_root_add_mem hik_mem
  rw [add_comm] at hik_mem
  rw [P.chainBotCoeff_if_one_zero hik_mem]; rw [ite_eq_right_iff]; rw [P.pairingIn_eq_zero_iff (i := i)]
  lia

中文:
引理 chainBotCoeff_mul_chainTopCoeff.aux_0
  结论: [P.是NotG2]
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := pairingIn_le_zero_of_root_add_mem hik_mem
  rw [add_comm] at hik_mem
  rw [P.chainBotCoeff_if_one_zero hik_mem]; rw [ite_eq_right_iff]; rw [P.pairingIn_eq_zero_iff (i := i)]
  lia
-/
private lemma chainBotCoeff_mul_chainTopCoeff.aux_0 [P.IsNotG2]
    (hik_mem : P.root k + P.root i in range P.root) :
    P.pairingIn Int k i = 0 ∨ (P.pairingIn Int k i < 0 ∧ P.chainBotCoeff i k = 0) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := pairingIn_le_zero_of_root_add_mem hik_mem
  rw [add_comm] at hik_mem
  rw [P.chainBotCoeff_if_one_zero hik_mem]; rw [ite_eq_right_iff]; rw [P.pairingIn_eq_zero_iff (i := i)]
  lia

variable [P.IsReduced] [P.IsIrreducible]
  (hi : i in b.support) (hj : j in b.support) (hij : i != j)
  (h₁ : P.root k + P.root i = P.root l)
  (h₂ : P.root k - P.root j = P.root m)
  (h₃ : P.root k + P.root i - P.root j in range P.root)

include hi hj hij h₁ h₂ h₃

/--
lemma `chainBotCoeff_mul_chainTopCoeff.isNotG2` / 引理 `chainBotCoeff_mul_chainTopCoeff.isNotG2`

English:
lemma chainBotCoeff_mul_chainTopCoeff.isNotG2
  statement: P.IsNotG2
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  rw [← P.not_isG2_iff_isNotG2]
  intro contra
  obtain ⟨n, h₃⟩ := h₃
  obtain ⟨x, y, h₀⟩ : exists x y : Int, x • P.root i + y • P.root j = P.root k := by
    rw [← Submodule.mem_s

中文:
引理 chainBotCoeff_mul_chainTopCoeff.isNotG2
  结论: P.是NotG2
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  rw [← P.not_isG2_iff_isNotG2]
  intro contra
  obtain ⟨n, h₃⟩ := h₃
  obtain ⟨x, y, h₀⟩ : exists x y : Int, x • P.root i + y • P.root j = P.root k := by
    rw [← Submodule.mem_s

Depends on / 依赖: IsAddTorsionFree, IsG2.span_eq_rootSpan_int, IsReflexive, Module, Module.IsReflexive, P.not_isG2_iff_isNotG2, P.pairingIn, P.root, P.toLinearMap, Submodule, Submodule.mem_span_pair, Submodule.subset_span, contra, mem_range_self, mem_span_pair, not_isG2_iff_isNotG2, of_isPerfPair, of_isTorsionFree, pairingIn, span_eq_rootSpan_int
-/
lemma chainBotCoeff_mul_chainTopCoeff.isNotG2 : P.IsNotG2 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  rw [← P.not_isG2_iff_isNotG2]
  intro contra
  obtain ⟨n, h₃⟩ := h₃
  obtain ⟨x, y, h₀⟩ : exists x y : Int, x • P.root i + y • P.root j = P.root k := by
    rw [← Submodule.mem_span_pair]; rw [IsG2.span_eq_rootSpan_int hi hj hij]
    exact Submodule.subset_span (mem_range_self k)
  let s : Set Int := {-3, -1, 0, 1, 3}
  let A : Int := P.pairingIn Int j i
  have hki : P.root k != P.root i := fun contra => by
    replace h₁ : 2 • P.root i = P.root l := by rwa [contra, ← two_nsmul] at h₁
    exact P.nsmul_notMem_range_root ⟨_, h₁.symm⟩
  have hki' : P.root k != -P.root i := fun contra => by
    replace h₁ : P.root l = 0 := by rwa [contra, neg_add_cancel, eq_comm] at h₁
    exact P.ne_zero _ h₁
  have hli : P.root l != P.root i := fun contra => by
    replace h₁ : P.root k = 0 := by rwa [contra, add_eq_right] at h₁
    exact P.ne_zero _ h₁
  have hli' : P.root l != -P.root i := fun contra => by
    replace h₁ : P.root k = 2 • P.root l := by
      rwa [← neg_eq_iff_eq_neg.mpr contra, ← sub_eq_add_neg, sub_eq_iff_eq_add, ← two_nsmul] at h₁
    exact P.nsmul_notMem_range_root ⟨_, h₁⟩
  have hmi : P.root m != P.root i := fun contra => by
    replace h₂ : P.root k = P.root i + P.root j := by rwa [contra, sub_eq_iff_eq_add] at h₂
    replace h₃ : P.root n = 2 • P.root i := by rw [h₃, h₂]; abel
    exact P.nsmul_notMem_range_root ⟨_, h₃⟩
  have hmi' : P.root m != -P.root i := fun contra => by
    replace h₂ : P.root k = -P.root i + P.root j := by rwa [contra, sub_eq_iff_eq_add] at h₂
    replace h₃ : P.root n = 0 := by rw [h₃, h₂]; abel
    exact P.ne_zero _ h₃
  have hni : P.root n != P.root i := fun contra => by
    replace h₃ : P.root k = P.root j := by
      rwa [contra, add_comm, add_sub_assoc, left_eq_add, sub_eq_zero] at h₃
    replace h₂ : P.root m = 0 := by rw [← h₂, h₃, sub_self]
    exact P.ne_zero _ h₂
  have hni' : P.root n != -P.root i := fun contra => by
    replace h₃ : 2 • P.root n = P.root m := by
      rwa [← neg_eq_iff_eq_neg.mpr contra, add_comm, add_sub_assoc, eq_neg_add_iff_add_eq,
        ← two_nsmul, h₂] at h₃
    exact P.nsmul_notMem_range_root ⟨_, h₃.symm⟩
  replace h₁ : 2 * (x + 1) + A * y in s := by
    convert! IsG2.pairingIn_mem_zero_one_three P l i hli hli'
    replace h₁ : P.root l = (x + 1) • P.root i + y • P.root j := by rw [← h₁, ← h₀]; module
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (S := Int) (j := i) h₁]; rw [pairingIn_same]; rw [Int.zsmul_eq_mul]; rw [Int.zsmul_eq_mul]
    ring
  replace h₂ : 2 * x + A * (y - 1) in s := by
    convert! IsG2.pairingIn_mem_zero_one_three P m i hmi hmi'
    replace h₂ : P.root m = x • P.root i + (y - 1) • P.root j := by rw [← h₂, ← h₀]; module
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (S := Int) (j := i) h₂]; rw [pairingIn_same]; rw [Int.zsmul_eq_mul]; rw [Int.zsmul_eq_mul]
    ring
  replace h₃ : 2 * (x + 1) + A * (y - 1) in s := by
    convert! IsG2.pairingIn_mem_zero_one_three P n i hni hni'
    replace h₃ : P.root n = (x + 1) • P.root i + (y - 1) • P.root j := by rw [h₃, ← h₀]; module
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (S := Int) (j := i) h₃]; rw [pairingIn_same]; rw [Int.zsmul_eq_mul]; rw [Int.zsmul_eq_mul]
    ring
  replace h₀ : 2 * x + A * y in s := by
    convert! IsG2.pairingIn_mem_zero_one_three P k i hki hki'
    rw [pairingIn_eq_add_of_root_eq_smul_add_smul (j := i) h₀.symm]; rw [pairingIn_same]; rw [Int.zsmul_eq_mul]; rw [Int.zsmul_eq_mul]
    ring
  have hA : A in s := IsG2.pairingIn_mem_zero_one_three P j i (P.root.injective.ne_iff.mpr hij.symm)
    (b.root_ne_neg_of_ne hj hi hij.symm)
  subst s
  simp only [mem_insert_iff, mem_singleton_iff] at h₀ h₁ h₂ h₃ hA
  rcases hA with hA | hA | hA | hA | hA <;> rw [hA] at h₀ h₁ h₂ h₃ <;> lia

/--
lemma `chainBotCoeff_mul_chainTopCoeff.aux_1` / 引理 `chainBotCoeff_mul_chainTopCoeff.aux_1`

English:
lemma chainBotCoeff_mul_chainTopCoeff.aux_1
  proof: .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m in range P.root -> P.root j + P.root (-l) in range P.root ->
      P.root j + P.root (-k) in range P.root ->
      (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
        (P.chainBotCoeff j (-l) + 1) * (P.chainBot

中文:
引理 chainBotCoeff_mul_chainTopCoeff.aux_1
  证明: .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m in range P.root -> P.root j + P.root (-l) in range P.root ->
      P.root j + P.root (-k) in range P.root ->
      (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
        (P.chainBotCoeff j (-l) + 1) * (P.chainBot
-/
private lemma chainBotCoeff_mul_chainTopCoeff.aux_1
    (hki : P.pairingIn Int k i = 0) :
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m in range P.root -> P.root j + P.root (-l) in range P.root ->
      P.root j + P.root (-k) in range P.root ->
      (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
        (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) := by
  intro _ him_mem hjl_mem hjk_mem
  /- Setup some typeclasses and name the 6th root `n`. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  let := P.indexNeg
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  obtain ⟨n, hn⟩ := h₃
  /- Establish basic relationships about roots and their sums / differences. -/
  have hnk_ne : n != k := by rintro rfl; simp [sub_eq_zero, hij, add_sub_assoc] at hn
have hkj_ne : k != j ∧ P.root k != -P.root j := (IsReduced.linearIndependent_iff _).mp
P.linearIndependent_of_sub_mem_range_root h₂ ▸ mem_range_self m
  have hnk_notMem : P.root n - P.root k ∉ range P.root := by
    convert! b.sub_notMem_range_root hi hj using 2; rw [hn]; module
  /- Calculate some auxiliary relationships between root pairings. -/
  have aux₀ : P.pairingIn Int j i = - P.pairingIn Int m i := by
    suffices P.pairing j i = - P.pairing m i from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_neg]
    replace hki : P.pairing k i = 0 := by rw [← P.algebraMap_pairingIn Int, hki, map_zero]
    simp only [← root_coroot_eq_pairing, ← h₂]
    simp [hki]
  have aux₁ : P.pairingIn Int j i = 0 := by
    refine le_antisymm (b.pairingIn_le_zero_of_ne hij.symm hj hi) ?_
    rw [aux₀]; rw [neg_nonneg]
    refine P.pairingIn_le_zero_of_root_add_mem ⟨n, ?_⟩
    rw [hn]; rw [← h₂]
    abel
  /- Calculate the pairings between four key root pairs. -/
  have key₁ : P.pairingIn Int i k = 0 := by rwa [pairingIn_eq_zero_iff]
have key₂ : P.pairingIn Int i m = 0 := P.pairingIn_eq_zero_iff.mp by simpa [aux₁] using aux₀
  have key₃ : P.pairingIn Int j k = 2 := by
    suffices 2 <= P.pairingIn Int j k by have := IsNotG2.pairingIn_mem_zero_one_two (P := P) j k; grind
    have hn₁ : P.pairingIn Int n k = 2 + P.pairingIn Int i k - P.pairingIn Int j k := by
      apply algebraMap_injective Int R
      simp only [map_add, map_sub, algebraMap_pairingIn, ← root_coroot_eq_pairing, hn]
      simp
    have hn₂ : P.pairingIn Int n k <= 0 := by
by_contra! contra; exact hnk_notMem P.root_sub_root_mem_of_pairingIn_pos contra hnk_ne
    lia
  have key₄ : P.pairingIn Int l j = 1 := by
    have hij : P.pairing i j = 0 := by
      rw [pairing_eq_zero_iff]; rw [← P.algebraMap_pairingIn Int]; rw [aux₁]; rw [map_zero]
    have hkj : P.pairing k j = 1 := by
      rw [← P.algebraMap_pairingIn Int]
      have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' j k (by grind) (by grind)
      aesop
    apply algebraMap_injective Int R
    rw [algebraMap_pairingIn]; rw [← root_coroot_eq_pairing]; rw [← h₁]
    simp [hkj, hij]
  replace key₄ : P.pairingIn Int j l != 0 := by rw [ne_eq, P.pairingIn_eq_zero_iff]; lia
  /- Calculate the value of each of the four terms in the goal. -/
  have hik_mem : P.root i + P.root k in range P.root := ⟨l, by rw [← h₁, add_comm]⟩
  simp only [P.chainBotCoeff_if_one_zero, hik_mem, him_mem, hjl_mem, hjk_mem]
  simp [key₁, key₂, key₃, key₄]

set_option backward.isDefEq.respectTransparency.types false in
/- An auxiliary result en route to `RootPairing.chainBotCoeff_mul_chainTopCoeff`. -/
open RootPositiveForm in
/--
lemma `chainBotCoeff_mul_chainTopCoeff.aux_2` / 引理 `chainBotCoeff_mul_chainTopCoeff.aux_2`

English:
lemma chainBotCoeff_mul_chainTopCoeff.aux_2
  proof: .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m in range P.root -> P.root j + P.root (-l) in range P.root ->
      P.root j + P.root (-k) in range P.root ->
      ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) := by
  intro _ him_mem hjl_mem hjk_mem
  let := P.i

中文:
引理 chainBotCoeff_mul_chainTopCoeff.aux_2
  证明: .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m in range P.root -> P.root j + P.root (-l) in range P.root ->
      P.root j + P.root (-k) in range P.root ->
      ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) := by
  intro _ him_mem hjl_mem hjk_mem
  let := P.i
-/
private lemma chainBotCoeff_mul_chainTopCoeff.aux_2
    (hki' : P.pairingIn Int k i < 0) (hkj' : 0 < P.pairingIn Int k j) :
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    letI := P.indexNeg
    P.root i + P.root m in range P.root -> P.root j + P.root (-l) in range P.root ->
      P.root j + P.root (-k) in range P.root ->
      ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) := by
  intro _ him_mem hjl_mem hjk_mem
  let := P.indexNeg
  /- Setup some typeclasses. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  /- Establish basic relationships about roots and their sums / differences. -/
have hkj_ne : k != j ∧ P.root k != -P.root j := (IsReduced.linearIndependent_iff _).mp
P.linearIndependent_of_sub_mem_range_root h₂ ▸ mem_range_self m
  have hlj_mem : P.root l - P.root j in range P.root := by rwa [← h₁]
  /- It is sufficient to prove that two key pairings vanish. -/
  suffices ¬ (P.pairingIn Int m i = 0 ∧ P.pairingIn Int l j != 0) by
    contrapose this
    rcases ne_or_eq (P.pairingIn Int m i) 0 with hmi | hmi
    · simpa [hmi, this.1, P.pairingIn_eq_zero_iff (i := i)] using chainBotCoeff_if_one_zero him_mem
    refine ⟨hmi, fun hlj => ?_⟩
    rw [chainBotCoeff_if_one_zero hjl_mem] at this
    simp [P.pairingIn_eq_zero_iff (i := j), hlj] at this
  /- Assume for contradiction that the two pairings do not vanish. -/
  rintro ⟨hmi, hlj⟩
  /- Use the assumptions to calculate various relationships between root pairings. -/
  have aux₀ : P.pairingIn Int j i = P.pairingIn Int k i := by
    suffices P.pairing j i = P.pairing k i from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn]
    replace h₂ : P.root k = P.root j + P.root m := (add_eq_of_eq_sub' h₂.symm).symm
    simpa [← P.root_coroot_eq_pairing k, h₂, ← P.algebraMap_pairingIn Int]
  obtain ⟨aux₁, aux₂⟩ : P.pairingIn Int i j = -1 ∧ P.pairingIn Int k j = 2 := by
    suffices 0 < - P.pairingIn Int i j ∧ - P.pairingIn Int i j < P.pairingIn Int k j ∧
      P.pairingIn Int k j <= 2 by lia
    refine ⟨?_, ?_, ?_⟩
    · rwa [neg_pos, P.pairingIn_lt_zero_iff, aux₀]
    · suffices P.pairingIn Int l j = P.pairingIn Int i j + P.pairingIn Int k j by
        have := zero_le_pairingIn_of_root_sub_mem hlj_mem; lia
      suffices P.pairing l j = P.pairing i j + P.pairing k j from
algebraMap_injective Int R by simpa only [algebraMap_pairingIn, map_add]
      simp [← P.root_coroot_eq_pairing l, ← h₁, add_comm]
    · have := IsNotG2.pairingIn_mem_zero_one_two (P := P) k j
      grind
  /- Choose a positive invariant form. -/
  obtain B : RootPositiveForm Int P := have : Fintype ι := Fintype.ofFinite ι; P.posRootForm Int
  /- Calculate root length relationships implied by the pairings calculated above. -/
  have ⟨aux₃, aux₄⟩ : B.rootLength i = B.rootLength j ∧ B.rootLength j < B.rootLength k := by
have hij_le : B.rootLength i <= B.rootLength j := B.rootLength_le_of_pairingIn_eq Or.inl aux₁
    have hjk_lt : B.rootLength j < B.rootLength k :=
B.rootLength_lt_of_pairingIn_notMem (by grind) hkj_ne.2 by grind
    refine ⟨?_, hjk_lt⟩
    simpa [posForm, rootLength] using (B.toInvariantForm.apply_eq_or_of_apply_ne (i := j) (j := k)
      (by simpa [posForm, rootLength] using hjk_lt.ne) i).resolve_right
      (by simpa [posForm, rootLength] using (lt_of_le_of_lt hij_le hjk_lt).ne)
  /- Use the root length results to calculate a final root pairing. -/
  have aux₅ : P.pairingIn Int k i = -1 := by
    suffices P.pairingIn Int j i = -1 by lia
    have aux : B.toInvariantForm.form (P.root i) (P.root i) =
        B.toInvariantForm.form (P.root j) (P.root j) := by simpa [posForm, rootLength] using aux₃
    have := P.pairingIn_pairingIn_mem_set_of_length_eq_of_ne aux hij (b.root_ne_neg_of_ne hi hj hij)
    grind
  /- Use the newly calculated pairing result to obtain further information about root lengths. -/
have aux₆ : B.rootLength k <= B.rootLength i := B.rootLength_le_of_pairingIn_eq Or.inl aux₅
  /- We now have contradictory information about root lengths. -/
  lia

open chainBotCoeff_mul_chainTopCoeff in
/--
lemma `chainBotCoeff_mul_chainTopCoeff` / 引理 `chainBotCoeff_mul_chainTopCoeff`

English:
lemma chainBotCoeff_mul_chainTopCoeff
  proof: by
  /- Setup some typeclasses. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  let := P.indexNeg
  suffices (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
      (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) by simpa
  /- Establish basic relationships

中文:
引理 chainBotCoeff_mul_chainTopCoeff
  证明: by
  /- Setup some typeclasses. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  let := P.indexNeg
  suffices (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
      (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) by simpa
  /- Establish basic relationships
-/
lemma chainBotCoeff_mul_chainTopCoeff :
    (P.chainBotCoeff i m + 1) * (P.chainTopCoeff j k + 1) =
      (P.chainTopCoeff j l + 1) * (P.chainBotCoeff i k + 1) := by
  /- Setup some typeclasses. -/
  have := chainBotCoeff_mul_chainTopCoeff.isNotG2 hi hj hij h₁ h₂ h₃
  let := P.indexNeg
  suffices (P.chainBotCoeff i m + 1) * (P.chainBotCoeff j (-k) + 1) =
      (P.chainBotCoeff j (-l) + 1) * (P.chainBotCoeff i k + 1) by simpa
  /- Establish basic relationships about roots and their sums / differences. -/
  have him_mem : P.root i + P.root m in range P.root := by rw [← h₂]; convert! h₃ using 1; abel
  have hik_mem : P.root k + P.root i in range P.root := h₁ ▸ mem_range_self l
  have hjk_mem : P.root j + P.root (-k) in range P.root := by
    convert! mem_range_self (-m) using 1; simpa [sub_eq_add_neg] using congr(-$h₂)
  have hjl_mem : P.root j + P.root (-l) in range P.root := by
    rw [h₁]; rw [← neg_mem_range_root_iff] at h₃; convert! h₃ using 1; simp [sub_eq_add_neg]
  have h₁' : P.root (-k) - P.root i = P.root (-l) := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]; rw [← h₁]; abel
  have h₂' : P.root (-k) + P.root j = P.root (-m) := by
    simp only [root_reflectionPerm, reflection_apply_self, indexNeg_neg]; rw [← h₂]; abel
  have h₃' : P.root (-k) + P.root j - P.root i in range P.root := by grind
  /- Proceed to the main argument, following Geck's case splits. It's all just bookkeeping. -/
  rcases aux_0 hik_mem with hki | ⟨hki, hik⟩
  · /- Geck "Case 1" -/
    exact aux_1 hi hj hij h₁ h₂ h₃ hki him_mem hjl_mem hjk_mem
  rw [add_comm] at hik_mem hjk_mem
  rcases aux_0 hjk_mem with hkj | ⟨hkj, hjk⟩
  · /- Geck "Case 2" -/
    simpa only [neg_neg] using (aux_1 hj hi hij.symm h₂' h₁' h₃' hkj hjl_mem
      (by simpa only [neg_neg]) (by simpa only [neg_neg])).symm
  /- Geck "Case 3" -/
  suffices P.chainBotCoeff i m = P.chainBotCoeff j (-l) by rw [hik, hjk, this]
  have aux₁ : ¬ (P.chainBotCoeff i m = 1 ∧ P.chainBotCoeff j (-l) = 0) :=
aux_2 hi hj hij h₁ h₂ h₃ hki (by simpa using hkj) him_mem hjl_mem by rwa [add_comm]
  have aux₂ : ¬(P.chainBotCoeff j (-l) = 1 ∧ P.chainBotCoeff i m = 0) := by
    simpa using aux_2 hj hi hij.symm h₂' h₁' h₃' hkj (by simpa)
      hjl_mem (by simpa only [neg_neg]) (by simpa only [neg_neg])
  have aux₃ : P.chainBotCoeff i m = 0 ∨ P.chainBotCoeff i m = 1 := by
    have := P.chainBotCoeff_if_one_zero him_mem
    split at this <;> simp [this]
  have aux₄ : P.chainBotCoeff j (-l) = 0 ∨ P.chainBotCoeff j (-l) = 1 := by
    have := P.chainBotCoeff_if_one_zero hjl_mem
    split at this <;> simp only [this, true_or, or_true]
  lia

end chainBotCoeff_mul_chainTopCoeff

end RootPairing
