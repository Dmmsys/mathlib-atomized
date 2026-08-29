/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.Order.Interval.Set.OrdConnectedLinear

/-!
# Chains of roots

Given roots `α` and `β`, the `α`-chain through `β` is the set of roots of the form `α + z • β`
for an integer `z`. This is known as a "root chain" and also a "root string". For linearly
independent roots in finite crystallographic root pairings, these chains are always unbroken, i.e.,
of the form: `β - q • α, ..., β - α, β, β + α, ..., β + p • α` for natural numbers `p`, `q`, and the
length, `p + q` is at most 3.

## Main definitions / results:
* `RootPairing.chainTopCoeff`: the natural number `p` in the chain
  `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.chainTopCoeff`: the natural number `q` in the chain
  `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.root_add_zsmul_mem_range_iff`: every chain is an interval (aka unbroken).
* `RootPairing.chainBotCoeff_add_chainTopCoeff_le`: every chain has length at most three.

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {i j : ι}

/--
lemma `setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent` / 引理 `setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`

English:
lemma setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
  proof: by
replace h := LinearIndependent.pair_iff.mp h.restrict_scalars' Int
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  have hS₀ : 0 in S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S => z.property.choose) from Finite.of_injective _ this

中文:
引理 setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
  证明: by
replace h := LinearIndependent.pair_iff.mp h.restrict_scalars' Int
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  have hS₀ : 0 in S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S => z.property.choose) from Finite.of_injective _ this

Depends on / 依赖: Finite, Finite.of_injective, Injective, IsAddTorsionFree, IsReflexive, LinearIndependent, LinearIndependent.pair_iff.mp, Module, Module.IsReflexive, P.ro, P.root, P.toLinearMap, S.Finite, S_def, add_right_inj, h.restrict_scalars, h_fin, of_injective, of_isPerfPair, of_isTorsionFree
-/
lemma setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
    (h : LinearIndependent R ![P.root i, P.root j]) :
    existsᵉ (q <= 0) (p >= 0), {z : Int | P.root j + z • P.root i in range P.root} = Icc q p := by
replace h := LinearIndependent.pair_iff.mp h.restrict_scalars' Int
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  have hS₀ : 0 in S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S => z.property.choose) from Finite.of_injective _ this
    intro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have : IsAddTorsionFree M := .of_isTorsionFree R M
    have : z • P.root i = z' • P.root i := by
      rwa [← add_right_inj (P.root j), ← hz.choose_spec, ← hz'.choose_spec, P.root.injective.eq_iff]
exact Subtype.ext smul_left_injective Int (P.ne_zero i) this
  have h_ne : S.Nonempty := ⟨0, by simp [S_def]⟩
  refine ⟨sInf S, csInf_le h_fin.bddBelow hS₀, sSup S, le_csSup h_fin.bddAbove hS₀,
    (h_ne.eq_Icc_iff_int h_fin.bddBelow h_fin.bddAbove).mpr fun r ⟨k, hk⟩ s ⟨l, hl⟩ hrs => ?_⟩
  by_contra! contra
  have hki_notMem : P.root k + P.root i ∉ range P.root := by
    replace hk : P.root k + P.root i = P.root j + (r + 1) • P.root i := by rw [hk]; module
replace contra : r + 1 ∉ S := hrs.notMem_of_mem_left by simp [contra]
    simpa only [hk, S_def, mem_ofPred_eq, S] using contra
  have hki_ne : P.root k != -P.root i := by
    rw [hk]
    contrapose! h
    replace h : r • P.root i = - P.root j - P.root i := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨r + 1, 1, by simp [add_smul, h], by lia⟩
  have hli_notMem : P.root l - P.root i ∉ range P.root := by
    replace hl : P.root l - P.root i = P.root j + (s - 1) • P.root i := by rw [hl]; module
replace contra : s - 1 ∉ S := hrs.notMem_of_mem_left by simp [lt_sub_right_of_add_lt contra]
    simpa only [hl, S_def, mem_ofPred_eq, S] using contra
  have hli_ne : P.root l != P.root i := by
    rw [hl]
    contrapose! h
    replace h : s • P.root i = P.root i - P.root j := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨s - 1, 1, by simp [sub_smul, h], by lia⟩
  have h₁ : 0 <= P.pairingIn Int k i := by
    have := P.root_add_root_mem_of_pairingIn_neg (i := k) (j := i)
    contrapose! this
    exact ⟨this, hki_ne, hki_notMem⟩
  have h₂ : P.pairingIn Int k i = P.pairingIn Int j i + r * 2 := by
    apply algebraMap_injective Int R
    rw [algebraMap_pairingIn]; rw [map_add]; rw [map_mul]; rw [algebraMap_pairingIn]; rw [← root_coroot'_eq_pairing]; rw [hk]
    simp
  have h₃ : P.pairingIn Int l i <= 0 := by
    have := P.root_sub_root_mem_of_pairingIn_pos (i := l) (j := i)
    contrapose! this
    exact ⟨this, fun x => hli_ne (congrArg P.root x), hli_notMem⟩
  have h₄ : P.pairingIn Int l i = P.pairingIn Int j i + s * 2 := by
    apply algebraMap_injective Int R
    rw [algebraMap_pairingIn]; rw [map_add]; rw [map_mul]; rw [algebraMap_pairingIn]; rw [← root_coroot'_eq_pairing]; rw [hl]
    simp
  lia

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_eq_Icc_of_linearIndependent :=
  setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent

variable (i j)

open scoped Classical in
/--
Definition of `chainTopCoeff` / `chainTopCoeff` 的定义

English:
definition chainTopCoeff
  signature: : Nat
  body: if h : LinearIndependent R ![P.root i, P.root j]
    then (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat
    else 0

中文:
定义 chainTopCoeff
  签名: : 自然数
  定义体: if h : LinearIndependent R ![P.root i, P.root j]
    then (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat
    else 0

Depends on / 依赖: LinearIndependent, P.root, P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent, choose.toNat, choose_spec, setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
-/
def chainTopCoeff : Nat :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat
    else 0

open scoped Classical in
/--
Definition of `chainBotCoeff` / `chainBotCoeff` 的定义

English:
definition chainBotCoeff
  signature: : Nat
  body: if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat
    else 0

中文:
定义 chainBotCoeff
  签名: : 自然数
  定义体: if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat
    else 0

Depends on / 依赖: LinearIndependent, P.root, P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent, setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
-/
def chainBotCoeff : Nat :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat
    else 0

variable {i j}

/--
lemma `chainTopCoeff_of_not_linearIndependent` / 引理 `chainTopCoeff_of_not_linearIndependent`

English:
lemma chainTopCoeff_of_not_linearIndependent
  given: (h : ¬ LinearIndependent R ![P.root i, P.root j])
  proof: by
  simp only [chainTopCoeff, h, reduceDIte]

中文:
引理 chainTopCoeff_of_not_linearIndependent
  条件: (h : ¬ LinearIndependent R ![P.root i, P.root j])
  证明: by
  simp only [chainTopCoeff, h, reduceDIte]

Depends on / 依赖: chainTopCoeff, reduceDIte
-/
lemma chainTopCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainTopCoeff i j = 0 := by
  simp only [chainTopCoeff, h, reduceDIte]

/--
lemma `chainBotCoeff_of_not_linearIndependent` / 引理 `chainBotCoeff_of_not_linearIndependent`

English:
lemma chainBotCoeff_of_not_linearIndependent
  given: (h : ¬ LinearIndependent R ![P.root i, P.root j])
  proof: by
  simp only [chainBotCoeff, h, reduceDIte]

中文:
引理 chainBotCoeff_of_not_linearIndependent
  条件: (h : ¬ LinearIndependent R ![P.root i, P.root j])
  证明: by
  simp only [chainBotCoeff, h, reduceDIte]

Depends on / 依赖: chainBotCoeff, reduceDIte
-/
lemma chainBotCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainBotCoeff i j = 0 := by
  simp only [chainBotCoeff, h, reduceDIte]

variable (h : LinearIndependent R ![P.root i, P.root j])
include h

/--
lemma `root_add_nsmul_mem_range_iff_le_chainTopCoeff` / 引理 `root_add_nsmul_mem_range_iff_le_chainTopCoeff`

English:
lemma root_add_nsmul_mem_range_iff_le_chainTopCoeff
  given: {n : Nat}
  proof: by
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  suffices (n : Int) in S ↔ n <= P.chainTopCoeff i j by
    simpa only [S_def, mem_ofPred_eq, natCast_zsmul] using this
  have aux : P.chainTopCoeff i j =
      (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h)

中文:
引理 root_add_nsmul_mem_range_iff_le_chainTopCoeff
  条件: {n : 自然数}
  证明: by
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  suffices (n : Int) in S ↔ n <= P.chainTopCoeff i j by
    simpa only [S_def, mem_ofPred_eq, natCast_zsmul] using this
  have aux : P.chainTopCoeff i j =
      (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h)

Depends on / 依赖: P.chainTopCoeff, P.root, P.set, P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent, S_def, chainTopCoeff, choose.toNat, choose_spec, mem_Icc, mem_ofPred_eq, natCast_zsmul, setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
-/
lemma root_add_nsmul_mem_range_iff_le_chainTopCoeff {n : Nat} :
    P.root j + n • P.root i in range P.root ↔ n <= P.chainTopCoeff i j := by
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  suffices (n : Int) in S ↔ n <= P.chainTopCoeff i j by
    simpa only [S_def, mem_ofPred_eq, natCast_zsmul] using this
  have aux : P.chainTopCoeff i j =
      (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat := by
    simp [chainTopCoeff, h]
  obtain ⟨hp, h₂ : S = _⟩ :=
    (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose_spec
  rw [aux]; rw [h₂]; rw [mem_Icc]
  have := (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.1
  lia

/--
lemma `root_sub_nsmul_mem_range_iff_le_chainBotCoeff` / 引理 `root_sub_nsmul_mem_range_iff_le_chainBotCoeff`

English:
lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff
  given: {n : Nat}
  proof: by
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  suffices -(n : Int) in S ↔ n <= P.chainBotCoeff i j by
    simpa only [S_def, mem_ofPred_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOfPred_root_add_zsmul

中文:
引理 root_sub_nsmul_mem_range_iff_le_chainBotCoeff
  条件: {n : 自然数}
  证明: by
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  suffices -(n : Int) in S ↔ n <= P.chainBotCoeff i j by
    simpa only [S_def, mem_ofPred_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOfPred_root_add_zsmul

Depends on / 依赖: P.chainBotCoeff, P.root, P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent, S_def, chainBotCoeff, choose_spec, mem_Icc, mem_ofPred_eq, natCast_zsmul, neg_smul, setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent, sub_eq_add_neg
-/
lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : Nat} :
    P.root j - n • P.root i in range P.root ↔ n <= P.chainBotCoeff i j := by
  set S : Set Int := {z | P.root j + z • P.root i in range P.root} with S_def
  suffices -(n : Int) in S ↔ n <= P.chainBotCoeff i j by
    simpa only [S_def, mem_ofPred_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat := by
    simp [chainBotCoeff, h]
  obtain ⟨hq, p, hp, h₂ : S = _⟩ :=
    (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec
  rw [aux]; rw [h₂]; rw [mem_Icc]
  lia

/--
lemma `Iic_chainTopCoeff_eq` / 引理 `Iic_chainTopCoeff_eq`

English:
lemma Iic_chainTopCoeff_eq
  proof: by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]

中文:
引理 Iic_chainTopCoeff_eq
  证明: by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]

Depends on / 依赖: P.root_add_nsmul_mem_range_iff_le_chainTopCoeff, root_add_nsmul_mem_range_iff_le_chainTopCoeff
-/
lemma Iic_chainTopCoeff_eq :
    Iic (P.chainTopCoeff i j) = {k | P.root j + k • P.root i in range P.root} := by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]

/--
lemma `Iic_chainBotCoeff_eq` / 引理 `Iic_chainBotCoeff_eq`

English:
lemma Iic_chainBotCoeff_eq
  proof: by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

omit h in

中文:
引理 Iic_chainBotCoeff_eq
  证明: by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

omit h in

Depends on / 依赖: P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff, root_sub_nsmul_mem_range_iff_le_chainBotCoeff
-/
lemma Iic_chainBotCoeff_eq :
    Iic (P.chainBotCoeff i j) = {k | P.root j - k • P.root i in range P.root} := by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

omit h in
/--
lemma `one_le_chainTopCoeff_of_root_add_mem` / 引理 `one_le_chainTopCoeff_of_root_add_mem`

English:
lemma one_le_chainTopCoeff_of_root_add_mem
  given: [P.IsReduced] (h : P.root i + P.root j in range P.root)
  proof: by
  have h' := P.linearIndependent_of_add_mem_range_root' h
  rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff h', one_smul, add_comm]

omit h in

中文:
引理 one_le_chainTopCoeff_of_root_add_mem
  条件: [P.是既约] (h : P.root i + P.root j in range P.root)
  证明: by
  have h' := P.linearIndependent_of_add_mem_range_root' h
  rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff h', one_smul, add_comm]

omit h in

Depends on / 依赖: P.linearIndependent_of_add_mem_range_root, add_comm, linearIndependent_of_add_mem_range_root, one_smul, root_add_nsmul_mem_range_iff_le_chainTopCoeff
-/
lemma one_le_chainTopCoeff_of_root_add_mem [P.IsReduced] (h : P.root i + P.root j in range P.root) :
    1 <= P.chainTopCoeff i j := by
  have h' := P.linearIndependent_of_add_mem_range_root' h
  rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff h', one_smul, add_comm]

omit h in
/--
lemma `one_le_chainBotCoeff_of_root_add_mem` / 引理 `one_le_chainBotCoeff_of_root_add_mem`

English:
lemma one_le_chainBotCoeff_of_root_add_mem
  given: [P.IsReduced] (h : P.root i - P.root j in range P.root)
  proof: by
  have h' := P.linearIndependent_of_sub_mem_range_root' h
  rwa [← root_sub_nsmul_mem_range_iff_le_chainBotCoeff h', one_smul, ← neg_mem_range_root_iff,
    neg_sub]

中文:
引理 one_le_chainBotCoeff_of_root_add_mem
  条件: [P.是既约] (h : P.root i - P.root j in range P.root)
  证明: by
  have h' := P.linearIndependent_of_sub_mem_range_root' h
  rwa [← root_sub_nsmul_mem_range_iff_le_chainBotCoeff h', one_smul, ← neg_mem_range_root_iff,
    neg_sub]

Depends on / 依赖: P.linearIndependent_of_sub_mem_range_root, linearIndependent_of_sub_mem_range_root, neg_mem_range_root_iff, neg_sub, one_smul, root_sub_nsmul_mem_range_iff_le_chainBotCoeff
-/
lemma one_le_chainBotCoeff_of_root_add_mem [P.IsReduced] (h : P.root i - P.root j in range P.root) :
    1 <= P.chainBotCoeff i j := by
  have h' := P.linearIndependent_of_sub_mem_range_root' h
  rwa [← root_sub_nsmul_mem_range_iff_le_chainBotCoeff h', one_smul, ← neg_mem_range_root_iff,
    neg_sub]

/--
lemma `root_add_zsmul_mem_range_iff` / 引理 `root_add_zsmul_mem_range_iff`

English:
lemma root_add_zsmul_mem_range_iff
  given: {z : Int}
  proof: by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]

中文:
引理 root_add_zsmul_mem_range_iff
  条件: {z : 整数}
  证明: by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]

Depends on / 依赖: P.root_add_nsmul_mem_range_iff_le_chainTopCoeff, P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff, eq_nat_or_neg, root_add_nsmul_mem_range_iff_le_chainTopCoeff, root_sub_nsmul_mem_range_iff_le_chainBotCoeff, sub_eq_add_neg, z.eq_nat_or_neg
-/
lemma root_add_zsmul_mem_range_iff {z : Int} :
    P.root j + z • P.root i in range P.root ↔
      z in Icc (-P.chainBotCoeff i j : Int) (P.chainTopCoeff i j) := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]

/--
lemma `root_sub_zsmul_mem_range_iff` / 引理 `root_sub_zsmul_mem_range_iff`

English:
lemma root_sub_zsmul_mem_range_iff
  given: {z : Int}
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [P.root_add_zsmul_mem_range_iff h]; rw [mem_Icc]; rw [mem_Icc]
  grind

中文:
引理 root_sub_zsmul_mem_range_iff
  条件: {z : 整数}
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [P.root_add_zsmul_mem_range_iff h]; rw [mem_Icc]; rw [mem_Icc]
  grind

Depends on / 依赖: P.root_add_zsmul_mem_range_iff, mem_Icc, neg_smul, root_add_zsmul_mem_range_iff, sub_eq_add_neg
-/
lemma root_sub_zsmul_mem_range_iff {z : Int} :
    P.root j - z • P.root i in range P.root ↔
      z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) := by
  rw [sub_eq_add_neg]; rw [← neg_smul]; rw [P.root_add_zsmul_mem_range_iff h]; rw [mem_Icc]; rw [mem_Icc]
  grind

/--
lemma `setOfPred_root_add_zsmul_mem_eq_Icc` / 引理 `setOfPred_root_add_zsmul_mem_eq_Icc`

English:
lemma setOfPred_root_add_zsmul_mem_eq_Icc
  proof: by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_mem_eq_Icc := setOfPred_root_add_zsmul_mem_eq_Icc

中文:
引理 setOfPred_root_add_zsmul_mem_eq_Icc
  证明: by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_mem_eq_Icc := setOfPred_root_add_zsmul_mem_eq_Icc

Depends on / 依赖: P.root_add_zsmul_mem_range_iff, root_add_zsmul_mem_range_iff
-/
lemma setOfPred_root_add_zsmul_mem_eq_Icc :
    {k : Int | P.root j + k • P.root i in range P.root} =
      Icc (-P.chainBotCoeff i j : Int) (P.chainTopCoeff i j) := by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_mem_eq_Icc := setOfPred_root_add_zsmul_mem_eq_Icc

/--
lemma `setOfPred_root_sub_zsmul_mem_eq_Icc` / 引理 `setOfPred_root_sub_zsmul_mem_eq_Icc`

English:
lemma setOfPred_root_sub_zsmul_mem_eq_Icc
  proof: by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_root_sub_zsmul_mem_eq_Icc := setOfPred_root_sub_zsmul_mem_eq_Icc

中文:
引理 setOfPred_root_sub_zsmul_mem_eq_Icc
  证明: by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_root_sub_zsmul_mem_eq_Icc := setOfPred_root_sub_zsmul_mem_eq_Icc

Depends on / 依赖: mem_ofPred_eq, root_sub_zsmul_mem_range_iff
-/
lemma setOfPred_root_sub_zsmul_mem_eq_Icc :
    {k : Int | P.root j - k • P.root i in range P.root} =
      Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) := by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_root_sub_zsmul_mem_eq_Icc := setOfPred_root_sub_zsmul_mem_eq_Icc

/--
lemma `chainTopCoeff_eq_sSup` / 引理 `chainTopCoeff_eq_sSup`

English:
lemma chainTopCoeff_eq_sSup
  proof: by
  rw [← Iic_chainTopCoeff_eq h]; rw [csSup_Iic]

中文:
引理 chainTopCoeff_eq_sSup
  证明: by
  rw [← Iic_chainTopCoeff_eq h]; rw [csSup_Iic]

Depends on / 依赖: Iic_chainTopCoeff_eq, csSup_Iic
-/
lemma chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k | P.root j + k • P.root i in range P.root} := by
  rw [← Iic_chainTopCoeff_eq h]; rw [csSup_Iic]

/--
lemma `chainBotCoeff_eq_sSup` / 引理 `chainBotCoeff_eq_sSup`

English:
lemma chainBotCoeff_eq_sSup
  proof: by
  rw [← Iic_chainBotCoeff_eq h]; rw [csSup_Iic]

中文:
引理 chainBotCoeff_eq_sSup
  证明: by
  rw [← Iic_chainBotCoeff_eq h]; rw [csSup_Iic]

Depends on / 依赖: Iic_chainBotCoeff_eq, csSup_Iic
-/
lemma chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k | P.root j - k • P.root i in range P.root} := by
  rw [← Iic_chainBotCoeff_eq h]; rw [csSup_Iic]

/--
lemma `coe_chainTopCoeff_eq_sSup` / 引理 `coe_chainTopCoeff_eq_sSup`

English:
lemma coe_chainTopCoeff_eq_sSup
  proof: by
  rw [setOfPred_root_add_zsmul_mem_eq_Icc h]
  simp

中文:
引理 coe_chainTopCoeff_eq_sSup
  证明: by
  rw [setOfPred_root_add_zsmul_mem_eq_Icc h]
  simp

Depends on / 依赖: setOfPred_root_add_zsmul_mem_eq_Icc
-/
lemma coe_chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k : Int | P.root j + k • P.root i in range P.root} := by
  rw [setOfPred_root_add_zsmul_mem_eq_Icc h]
  simp

/--
lemma `coe_chainBotCoeff_eq_sSup` / 引理 `coe_chainBotCoeff_eq_sSup`

English:
lemma coe_chainBotCoeff_eq_sSup
  proof: by
  rw [setOfPred_root_sub_zsmul_mem_eq_Icc h]
  simp

omit h

中文:
引理 coe_chainBotCoeff_eq_sSup
  证明: by
  rw [setOfPred_root_sub_zsmul_mem_eq_Icc h]
  simp

omit h

Depends on / 依赖: setOfPred_root_sub_zsmul_mem_eq_Icc
-/
lemma coe_chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k : Int | P.root j - k • P.root i in range P.root} := by
  rw [setOfPred_root_sub_zsmul_mem_eq_Icc h]
  simp

omit h

/--
lemma `chainCoeff_reflectionPerm_left_aux` / 引理 `chainCoeff_reflectionPerm_left_aux`

English:
lemma chainCoeff_reflectionPerm_left_aux
  proof: P.indexNeg
    Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext

中文:
引理 chainCoeff_reflectionPerm_left_aux
  证明: P.indexNeg
    Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext
-/
private lemma chainCoeff_reflectionPerm_left_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h']; rw [indexNeg_neg]; rw [root_reflectionPerm]; rw [mem_Icc]; rw [reflection_apply_self]; rw [smul_neg]; rw [← neg_smul]; rw [P.root_add_zsmul_mem_range_iff h]; rw [mem_Icc]
    grind
  · have h' : ¬ LinearIndependent R ![P.root (-i), P.root j] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

/--
lemma `chainCoeff_reflectionPerm_right_aux` / 引理 `chainCoeff_reflectionPerm_right_aux`

English:
lemma chainCoeff_reflectionPerm_right_aux
  proof: P.indexNeg
    Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext

中文:
引理 chainCoeff_reflectionPerm_right_aux
  证明: P.indexNeg
    Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext
-/
private lemma chainCoeff_reflectionPerm_right_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h']; rw [indexNeg_neg]; rw [root_reflectionPerm]; rw [mem_Icc]; rw [reflection_apply_self]; rw [← sub_neg_eq_add]; rw [← neg_sub']; rw [neg_mem_range_root_iff]; rw [P.root_sub_zsmul_mem_range_iff h]; rw [mem_Icc]
  · have h' : ¬ LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

@[simp]
/--
lemma `chainTopCoeff_reflectionPerm_left` / 引理 `chainTopCoeff_reflectionPerm_left`

English:
lemma chainTopCoeff_reflectionPerm_left
  proof: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)

中文:
引理 chainTopCoeff_reflectionPerm_left
  证明: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)

Depends on / 依赖: P.chainBotCoeff, P.chainCoeff_reflectionPerm_left_aux, P.chainTopCoeff, P.indexNeg, chainBotCoeff, chainCoeff_reflectionPerm_left_aux, chainTopCoeff, indexNeg, le_antisymm
-/
lemma chainTopCoeff_reflectionPerm_left :
    P.chainTopCoeff (P.reflectionPerm i i) j = P.chainBotCoeff i j := by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)
  · simpa using this (P.chainBotCoeff i j)

@[simp]
/--
lemma `chainBotCoeff_reflectionPerm_left` / 引理 `chainBotCoeff_reflectionPerm_left`

English:
lemma chainBotCoeff_reflectionPerm_left
  proof: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j

中文:
引理 chainBotCoeff_reflectionPerm_left
  证明: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j

Depends on / 依赖: P.chainBotCoeff, P.chainCoeff_reflectionPerm_left_aux, P.chainTopCoeff, P.indexNeg, chainBotCoeff, chainCoeff_reflectionPerm_left_aux, chainTopCoeff, indexNeg, le_antisymm
-/
lemma chainBotCoeff_reflectionPerm_left :
    P.chainBotCoeff (P.reflectionPerm i i) j = P.chainTopCoeff i j := by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff (-i) j : Int) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j)
  · simpa using this (-P.chainTopCoeff i j)

@[simp]
/--
lemma `chainTopCoeff_reflectionPerm_right` / 引理 `chainTopCoeff_reflectionPerm_right`

English:
lemma chainTopCoeff_reflectionPerm_right
  proof: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff i (-j)

中文:
引理 chainTopCoeff_reflectionPerm_right
  证明: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff i (-j)

Depends on / 依赖: P.chainBotCoeff, P.chainCoeff_reflectionPerm_right_aux, P.chainTopCoeff, P.indexNeg, chainBotCoeff, chainCoeff_reflectionPerm_right_aux, chainTopCoeff, indexNeg, le_antisymm
-/
lemma chainTopCoeff_reflectionPerm_right :
    P.chainTopCoeff i (P.reflectionPerm j j) = P.chainBotCoeff i j := by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff i (-j))
  · simpa using this (P.chainBotCoeff i j)

@[simp]
/--
lemma `chainBotCoeff_reflectionPerm_right` / 引理 `chainBotCoeff_reflectionPerm_right`

English:
lemma chainBotCoeff_reflectionPerm_right
  proof: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff i (-j

中文:
引理 chainBotCoeff_reflectionPerm_right
  证明: by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff i (-j

Depends on / 依赖: P.chainBotCoeff, P.chainCoeff_reflectionPerm_right_aux, P.chainTopCoeff, P.indexNeg, chainBotCoeff, chainCoeff_reflectionPerm_right_aux, chainTopCoeff, indexNeg, le_antisymm
-/
lemma chainBotCoeff_reflectionPerm_right :
    P.chainBotCoeff i (P.reflectionPerm j j) = P.chainTopCoeff i j := by
  let := P.indexNeg
  have (z : Int) : z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j) ↔
      z in Icc (-P.chainBotCoeff i (-j) : Int) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff i (-j))
  · simpa using this (-P.chainTopCoeff i j)

/--
lemma `chainBotCoeff_eq_zero_iff` / 引理 `chainBotCoeff_eq_zero_iff`

English:
lemma chainBotCoeff_eq_zero_iff
  proof: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainBotCoeff_of_not_linearIndependent h, h]
  have : P.chainBotCoeff i j = 0 ↔ Iic (P.chainBotCoeff i j) = {0} := by
    simpa [Set.ext_iff, mem_Iic, mem_singleton_iff] using ⟨fun h => by simp [h], fun h => by rw [← h]⟩
  s

中文:
引理 chainBotCoeff_eq_zero_iff
  证明: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainBotCoeff_of_not_linearIndependent h, h]
  have : P.chainBotCoeff i j = 0 ↔ Iic (P.chainBotCoeff i j) = {0} := by
    simpa [Set.ext_iff, mem_Iic, mem_singleton_iff] using ⟨fun h => by simp [h], fun h => by rw [← h]⟩
  s

Depends on / 依赖: Iic_chainBotCoeff_eq, LinearIndependent, P.chainBotCoeff, P.root, Set.ext_iff, chainBotCoeff, chainBotCoeff_of_not_linearIndependent, ext_iff, false_or, mem_Iic, mem_ofPred_eq, mem_singleton_iff, not_true_eq_false
-/
lemma chainBotCoeff_eq_zero_iff :
    P.chainBotCoeff i j = 0 ↔
      ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j - P.root i ∉ range P.root := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainBotCoeff_of_not_linearIndependent h, h]
  have : P.chainBotCoeff i j = 0 ↔ Iic (P.chainBotCoeff i j) = {0} := by
    simpa [Set.ext_iff, mem_Iic, mem_singleton_iff] using ⟨fun h => by simp [h], fun h => by rw [← h]⟩
  simp only [h, not_true_eq_false, false_or, this, Iic_chainBotCoeff_eq h, Set.ext_iff,
    mem_ofPred_eq, mem_singleton_iff]
  refine ⟨fun h' => by simpa using h' 1, fun h' n => ⟨fun h'' => ?_, fun h'' => by simp [h'']⟩⟩
  replace h' : 1 ∉ {k | P.root j - k • P.root i in range P.root} := by simpa using h'
  rw [← Iic_chainBotCoeff_eq h]; rw [mem_Iic]; rw [not_le]; rw [Nat.lt_one_iff] at h'
  rw [root_sub_nsmul_mem_range_iff_le_chainBotCoeff h] at h''
  lia

/--
lemma `chainTopCoeff_eq_zero_iff` / 引理 `chainTopCoeff_eq_zero_iff`

English:
lemma chainTopCoeff_eq_zero_iff
  proof: by
  rw [← chainBotCoeff_reflectionPerm_left]
  simp [-chainBotCoeff_reflectionPerm_left, chainBotCoeff_eq_zero_iff]

include h

中文:
引理 chainTopCoeff_eq_zero_iff
  证明: by
  rw [← chainBotCoeff_reflectionPerm_left]
  simp [-chainBotCoeff_reflectionPerm_left, chainBotCoeff_eq_zero_iff]

include h

Depends on / 依赖: chainBotCoeff_eq_zero_iff, chainBotCoeff_reflectionPerm_left
-/
lemma chainTopCoeff_eq_zero_iff :
    P.chainTopCoeff i j = 0 ↔
      ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j + P.root i ∉ range P.root := by
  rw [← chainBotCoeff_reflectionPerm_left]
  simp [-chainBotCoeff_reflectionPerm_left, chainBotCoeff_eq_zero_iff]

include h

/--
lemma `chainBotCoeff_of_add` / 引理 `chainBotCoeff_of_add`

English:
lemma chainBotCoeff_of_add
  given: {k : ι} (hk : P.root k = P.root j + P.root i)
  proof: by
  have h' : LinearIndependent R ![P.root i, P.root k] := by simpa [hk, add_comm]
  apply Nat.cast_injective (R := Int)
  rw [Nat.cast_add]; rw [Nat.cast_one]; rw [coe_chainBotCoeff_eq_sSup h']; rw [coe_chainBotCoeff_eq_sSup h]
  have (z : Int) : P.root k - z • P.root i = P.root j - (z - 1) • P.ro

中文:
引理 chainBotCoeff_of_add
  条件: {k : ι} (hk : P.root k = P.root j + P.root i)
  证明: by
  have h' : LinearIndependent R ![P.root i, P.root k] := by simpa [hk, add_comm]
  apply Nat.cast_injective (R := Int)
  rw [Nat.cast_add]; rw [Nat.cast_one]; rw [coe_chainBotCoeff_eq_sSup h']; rw [coe_chainBotCoeff_eq_sSup h]
  have (z : Int) : P.root k - z • P.root i = P.root j - (z - 1) • P.ro

Depends on / 依赖: LinearIndependent, Nat.cast_add, Nat.cast_injective, Nat.cast_one, OrderIso, OrderIso.addRight, P.root, addRight, add_comm, cast_add, cast_injective, cast_one, coe_chainBotCoeff_eq_sSup, module, replace, sub_eq_add_neg
-/
lemma chainBotCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainBotCoeff i k = P.chainBotCoeff i j + 1 := by
  have h' : LinearIndependent R ![P.root i, P.root k] := by simpa [hk, add_comm]
  apply Nat.cast_injective (R := Int)
  rw [Nat.cast_add]; rw [Nat.cast_one]; rw [coe_chainBotCoeff_eq_sSup h']; rw [coe_chainBotCoeff_eq_sSup h]
  have (z : Int) : P.root k - z • P.root i = P.root j - (z - 1) • P.root i := by rw [hk]; module
  replace this : {z : Int | P.root k - z • P.root i in range P.root} =
      OrderIso.addRight 1 '' {n | P.root j - n • P.root i in range P.root} := by
    simp [this, sub_eq_add_neg]
  have bdd : BddAbove {z : Int | P.root j - z • P.root i in range P.root} := by
    rw [setOfPred_root_sub_zsmul_mem_eq_Icc h]
    exact bddAbove_Icc
  rw [this]; rw [← OrderIso.map_csSup' _ ⟨0]; rw [by simp⟩ bdd]; rw [OrderIso.addRight_apply]

/--
lemma `chainTopCoeff_of_sub` / 引理 `chainTopCoeff_of_sub`

English:
lemma chainTopCoeff_of_sub
  given: {k : ι} (hk : P.root k = P.root j - P.root i)
  proof: by
  let := P.indexNeg
  replace hk : P.root k = P.root j + P.root (-i) := by simpa [sub_eq_add_neg] using hk
  simpa using chainBotCoeff_of_add (by simpa) hk

中文:
引理 chainTopCoeff_of_sub
  条件: {k : ι} (hk : P.root k = P.root j - P.root i)
  证明: by
  let := P.indexNeg
  replace hk : P.root k = P.root j + P.root (-i) := by simpa [sub_eq_add_neg] using hk
  simpa using chainBotCoeff_of_add (by simpa) hk

Depends on / 依赖: P.indexNeg, P.root, chainBotCoeff_of_add, indexNeg, replace, sub_eq_add_neg
-/
lemma chainTopCoeff_of_sub {k : ι} (hk : P.root k = P.root j - P.root i) :
    P.chainTopCoeff i k = P.chainTopCoeff i j + 1 := by
  let := P.indexNeg
  replace hk : P.root k = P.root j + P.root (-i) := by simpa [sub_eq_add_neg] using hk
  simpa using chainBotCoeff_of_add (by simpa) hk

/--
lemma `chainTopCoeff_of_add` / 引理 `chainTopCoeff_of_add`

English:
lemma chainTopCoeff_of_add
  given: {k : ι} (hk : P.root k = P.root j + P.root i)
  proof: by
  replace h : LinearIndependent R ![P.root i, P.root k] := by rw [hk, add_comm]; simpa
  replace hk : P.root j = P.root k - P.root i := by rw [hk]; abel
  exact chainTopCoeff_of_sub h hk

omit h

中文:
引理 chainTopCoeff_of_add
  条件: {k : ι} (hk : P.root k = P.root j + P.root i)
  证明: by
  replace h : LinearIndependent R ![P.root i, P.root k] := by rw [hk, add_comm]; simpa
  replace hk : P.root j = P.root k - P.root i := by rw [hk]; abel
  exact chainTopCoeff_of_sub h hk

omit h

Depends on / 依赖: LinearIndependent, P.root, add_comm, chainTopCoeff_of_sub, replace
-/
lemma chainTopCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainTopCoeff i j = P.chainTopCoeff i k + 1 := by
  replace h : LinearIndependent R ![P.root i, P.root k] := by rw [hk, add_comm]; simpa
  replace hk : P.root j = P.root k - P.root i := by rw [hk]; abel
  exact chainTopCoeff_of_sub h hk

omit h
variable (i j)

open scoped Classical in
/--
Definition of `chainTopIdx` / `chainTopIdx` 的定义

English:
definition chainTopIdx
  signature: : ι
  body: if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
.choose (le_refl <| P.chainTopCoeff i j)
    else j

中文:
定义 chainTopIdx
  签名: : ι
  定义体: if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
.choose (le_refl <| P.chainTopCoeff i j)
    else j

Depends on / 依赖: LinearIndependent, P.chainTopCoeff, P.root, P.root_add_nsmul_mem_range_iff_le_chainTopCoeff, chainTopCoeff, le_refl, root_add_nsmul_mem_range_iff_le_chainTopCoeff
-/
def chainTopIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
.choose (le_refl <| P.chainTopCoeff i j)
    else j

open scoped Classical in
/--
Definition of `chainBotIdx` / `chainBotIdx` 的定义

English:
definition chainBotIdx
  signature: : ι
  body: if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
.choose (le_refl <| P.chainBotCoeff i j)
    else j

中文:
定义 chainBotIdx
  签名: : ι
  定义体: if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
.choose (le_refl <| P.chainBotCoeff i j)
    else j

Depends on / 依赖: LinearIndependent, P.chainBotCoeff, P.root, P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff, chainBotCoeff, le_refl, root_sub_nsmul_mem_range_iff_le_chainBotCoeff
-/
def chainBotIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
.choose (le_refl <| P.chainBotCoeff i j)
    else j

variable {i j}

@[simp]
/--
lemma `root_chainTopIdx` / 引理 `root_chainTopIdx`

English:
lemma root_chainTopIdx
  proof: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainTopIdx, reduceDIte, h]
    exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
.choose_spec (le_refl <| P.chainTopCoeff i j)
  · simp only [chainTopIdx, chainTopCoeff, h, reduceDIte, zero_smul, add_zero]

@[sim

中文:
引理 root_chainTopIdx
  证明: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainTopIdx, reduceDIte, h]
    exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
.choose_spec (le_refl <| P.chainTopCoeff i j)
  · simp only [chainTopIdx, chainTopCoeff, h, reduceDIte, zero_smul, add_zero]

@[sim

Depends on / 依赖: LinearIndependent, P.chainTopCoeff, P.root, P.root_add_nsmul_mem_range_iff_le_chainTopCoeff, add_zero, chainTopCoeff, chainTopIdx, choose_spec, le_refl, reduceDIte, root_add_nsmul_mem_range_iff_le_chainTopCoeff, zero_smul
-/
lemma root_chainTopIdx :
    P.root (P.chainTopIdx i j) = P.root j + P.chainTopCoeff i j • P.root i := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainTopIdx, reduceDIte, h]
    exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
.choose_spec (le_refl <| P.chainTopCoeff i j)
  · simp only [chainTopIdx, chainTopCoeff, h, reduceDIte, zero_smul, add_zero]

@[simp]
/--
lemma `root_chainBotIdx` / 引理 `root_chainBotIdx`

English:
lemma root_chainBotIdx
  proof: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainBotIdx, reduceDIte, h]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
.choose_spec (le_refl <| P.chainBotCoeff i j)
  · simp only [chainBotIdx, chainBotCoeff, h, reduceDIte, zero_smul, sub_zero]

inclu

中文:
引理 root_chainBotIdx
  证明: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainBotIdx, reduceDIte, h]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
.choose_spec (le_refl <| P.chainBotCoeff i j)
  · simp only [chainBotIdx, chainBotCoeff, h, reduceDIte, zero_smul, sub_zero]

inclu

Depends on / 依赖: LinearIndependent, P.chainBotCoeff, P.root, P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff, chainBotCoeff, chainBotIdx, choose_spec, le_refl, reduceDIte, root_sub_nsmul_mem_range_iff_le_chainBotCoeff, sub_zero, zero_smul
-/
lemma root_chainBotIdx :
    P.root (P.chainBotIdx i j) = P.root j - P.chainBotCoeff i j • P.root i := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainBotIdx, reduceDIte, h]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
.choose_spec (le_refl <| P.chainBotCoeff i j)
  · simp only [chainBotIdx, chainBotCoeff, h, reduceDIte, zero_smul, sub_zero]

include h

/--
lemma `chainBotCoeff_sub_chainTopCoeff` / 引理 `chainBotCoeff_sub_chainTopCoeff`

English:
lemma chainBotCoeff_sub_chainTopCoeff
  proof: by
  suffices forall i j, LinearIndependent R ![P.root i, P.root j] ->
      P.chainBotCoeff i j - P.chainTopCoeff i j <= P.pairingIn Int j i by
    refine le_antisymm (this i j h) ?_
    specialize this (P.reflectionPerm i i) j (by simpa)
    simp only [chainBotCoeff_reflectionPerm_left, chainTopCo

中文:
引理 chainBotCoeff_sub_chainTopCoeff
  证明: by
  suffices forall i j, LinearIndependent R ![P.root i, P.root j] ->
      P.chainBotCoeff i j - P.chainTopCoeff i j <= P.pairingIn Int j i by
    refine le_antisymm (this i j h) ?_
    specialize this (P.reflectionPerm i i) j (by simpa)
    simp only [chainBotCoeff_reflectionPerm_left, chainTopCo

Depends on / 依赖: LinearIndependent, P.chainBotCoeff, P.chainBotIdx, P.chainTopCoeff, P.pairingIn, P.reflection, P.reflectionPerm, P.root, chainBotCoeff, chainBotCoeff_reflectionPerm_left, chainBotIdx, chainTopCoeff, chainTopCoeff_reflectionPerm_left, le_antisymm, pairingIn, pairingIn_reflectionPerm_self_right, reflection, reflectionPerm, specialize
-/
lemma chainBotCoeff_sub_chainTopCoeff :
    P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn Int j i := by
  suffices forall i j, LinearIndependent R ![P.root i, P.root j] ->
      P.chainBotCoeff i j - P.chainTopCoeff i j <= P.pairingIn Int j i by
    refine le_antisymm (this i j h) ?_
    specialize this (P.reflectionPerm i i) j (by simpa)
    simp only [chainBotCoeff_reflectionPerm_left, chainTopCoeff_reflectionPerm_left,
      pairingIn_reflectionPerm_self_right] at this
    lia
  intro i j h
  have h₁ : P.reflection i (P.root <| P.chainBotIdx i j) =
      P.root j + (P.chainBotCoeff i j - P.pairingIn Int j i) • P.root i := by
    simp [reflection_apply_root, ← P.algebraMap_pairingIn Int]
    module
  have h₂ : P.reflection i (P.root <| P.chainBotIdx i j) in range P.root := by
    rw [← root_reflectionPerm]
    exact mem_range_self _
  rw [h₁]; rw [root_add_zsmul_mem_range_iff h]; rw [mem_Icc] at h₂
  grind

/--
lemma `chainTopCoeff_sub_chainBotCoeff` / 引理 `chainTopCoeff_sub_chainBotCoeff`

English:
lemma chainTopCoeff_sub_chainBotCoeff
  proof: by
  rw [← chainBotCoeff_sub_chainTopCoeff h]; rw [neg_sub]

omit h

中文:
引理 chainTopCoeff_sub_chainBotCoeff
  证明: by
  rw [← chainBotCoeff_sub_chainTopCoeff h]; rw [neg_sub]

omit h

Depends on / 依赖: chainBotCoeff_sub_chainTopCoeff, neg_sub
-/
lemma chainTopCoeff_sub_chainBotCoeff :
    P.chainTopCoeff i j - P.chainBotCoeff i j = -P.pairingIn Int j i := by
  rw [← chainBotCoeff_sub_chainTopCoeff h]; rw [neg_sub]

omit h

/--
lemma `chainCoeff_chainTopIdx_aux` / 引理 `chainCoeff_chainTopIdx_aux`

English:
lemma chainCoeff_chainTopIdx_aux
  proof: by
  have aux : LinearIndependent R ![P.root i, P.root j] ↔
      LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rw [P.root_chainTopIdx]; rw [add_comm (P.root j)]; rw [← natCast_zsmul]; rw [LinearIndependent.pair_add_smul_right_iff]
  by_cases h : LinearIndependent R ![P.root 

中文:
引理 chainCoeff_chainTopIdx_aux
  证明: by
  have aux : LinearIndependent R ![P.root i, P.root j] ↔
      LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rw [P.root_chainTopIdx]; rw [add_comm (P.root j)]; rw [← natCast_zsmul]; rw [LinearIndependent.pair_add_smul_right_iff]
  by_cases h : LinearIndependent R ![P.root 

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_add_smul_right_iff, P.chainTopIdx, P.root, P.root_chainTopIdx, add_comm, chainBotCoeff_of_not_linearIndependent, chainTopCoeff_of_not_linearIndependent, chainTopIdx, natCast_zsmul, pair_add_smul_right_iff, root_chainTopIdx
-/
lemma chainCoeff_chainTopIdx_aux :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j ∧
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 := by
  have aux : LinearIndependent R ![P.root i, P.root j] ↔
      LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rw [P.root_chainTopIdx]; rw [add_comm (P.root j)]; rw [← natCast_zsmul]; rw [LinearIndependent.pair_add_smul_right_iff]
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  have h' : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by rwa [← aux]
  set S₁ : Set Int := {z | P.root j + z • P.root i in range P.root} with S₁_def
  set S₂ : Set Int := {z | P.root (P.chainTopIdx i j) + z • P.root i in range P.root} with S₂_def
  have hS₁₂ : S₂ = (fun z => (-P.chainTopCoeff i j : Int) + z) '' S₁ := by
    ext; simp [S₁_def, S₂_def, root_chainTopIdx, add_smul, add_assoc, natCast_zsmul]
  have hS₁ : S₁ = Icc (-P.chainBotCoeff i j : Int) (P.chainTopCoeff i j) := by
    ext; rw [S₁_def, mem_ofPred_eq, root_add_zsmul_mem_range_iff h]
  have hS₂ : S₂ = Icc (-P.chainBotCoeff i (P.chainTopIdx i j) : Int)
      (P.chainTopCoeff i (P.chainTopIdx i j)) := by
    ext; rw [S₂_def, mem_ofPred_eq, root_add_zsmul_mem_range_iff h']
  rw [hS₁]; rw [hS₂]; rw [image_const_add_Icc]; rw [neg_add_cancel]; rw [Icc_eq_Icc_iff (by simp)]; rw [neg_eq_iff_eq_neg]; rw [neg_add_rev]; rw [neg_neg]; rw [neg_neg] at hS₁₂
  norm_cast at hS₁₂

@[simp]
/--
lemma `chainBotCoeff_chainTopIdx` / 引理 `chainBotCoeff_chainTopIdx`

English:
lemma chainBotCoeff_chainTopIdx
  proof: chainCoeff_chainTopIdx_aux.1

@[simp]

中文:
引理 chainBotCoeff_chainTopIdx
  证明: chainCoeff_chainTopIdx_aux.1

@[simp]

Depends on / 依赖: Basis.addHaar_def, FiniteDimensional, addHaar_def, b.finiteDimensional_of_finite, chainCoeff_chainTopIdx_aux, finiteDimensional_of_finite, sigmaFinite_addHaarMeasure
-/
lemma chainBotCoeff_chainTopIdx :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j :=
  chainCoeff_chainTopIdx_aux.1

@[simp]
/--
lemma `chainTopCoeff_chainTopIdx` / 引理 `chainTopCoeff_chainTopIdx`

English:
lemma chainTopCoeff_chainTopIdx
  proof: chainCoeff_chainTopIdx_aux.2

include h in

中文:
引理 chainTopCoeff_chainTopIdx
  证明: chainCoeff_chainTopIdx_aux.2

include h in

Depends on / 依赖: chainCoeff_chainTopIdx_aux
-/
lemma chainTopCoeff_chainTopIdx :
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 :=
  chainCoeff_chainTopIdx_aux.2

include h in
/--
lemma `chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx` / 引理 `chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx`

English:
lemma chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx
  proof: by
  replace h : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  calc (P.chainBotCoeff i j + P.chainTopCoeff i j : Int)
    _ = P.chainBotCoeff i (P.chainTopIdx i j

中文:
引理 chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx
  证明: by
  replace h : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  calc (P.chainBotCoeff i j + P.chainTopCoeff i j : Int)
    _ = P.chainBotCoeff i (P.chainTopIdx i j

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_add_smul_right_iff, P.chainBotCoeff, P.chainBotCoeff_sub_chainTopCoeff, P.chainTopCoeff, P.chainTopIdx, P.pairingIn, P.root, P.root_chainTopIdx, add_comm, chainBotCoeff, chainBotCoeff_sub_chainTopCoeff, chainTopCoeff, chainTopIdx, natCast_zsmul, pair_add_smul_right_iff, pairingIn, replace, root_chainTopIdx
-/
lemma chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx :
    P.chainBotCoeff i j + P.chainTopCoeff i j = P.pairingIn Int (P.chainTopIdx i j) i := by
  replace h : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  calc (P.chainBotCoeff i j + P.chainTopCoeff i j : Int)
    _ = P.chainBotCoeff i (P.chainTopIdx i j) := by simp
    _ = P.chainBotCoeff i (P.chainTopIdx i j) - P.chainTopCoeff i (P.chainTopIdx i j) := by simp
    _ = P.pairingIn Int (P.chainTopIdx i j) i := by rw [P.chainBotCoeff_sub_chainTopCoeff h]

/--
lemma `chainBotCoeff_add_chainTopCoeff_le_three` / 引理 `chainBotCoeff_add_chainTopCoeff_le_three`

English:
lemma chainBotCoeff_add_chainTopCoeff_le_three
  given: [P.IsReduced]
  proof: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le]; rw [Nat.cast_add]; rw [Nat.cast_ofNat]; rw [chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := P.pa

中文:
引理 chainBotCoeff_add_chainTopCoeff_le_three
  条件: [P.是既约]
  证明: by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le]; rw [Nat.cast_add]; rw [Nat.cast_ofNat]; rw [chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := P.pa

Depends on / 依赖: Int.ofNat_le, LinearIndependent, Nat.cast_add, Nat.cast_ofNat, P.chainTopIdx, P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed, P.root, cast_add, cast_ofNat, chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx, chainBotCoeff_of_not_linearIndependent, chainTopCoeff_of_not_linearIndependent, chainTopIdx, ofNat_le, pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed
-/
lemma chainBotCoeff_add_chainTopCoeff_le_three [P.IsReduced] :
    P.chainBotCoeff i j + P.chainTopCoeff i j <= 3 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le]; rw [Nat.cast_add]; rw [Nat.cast_ofNat]; rw [chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i (P.chainTopIdx i j)
  aesop

end RootPairing
