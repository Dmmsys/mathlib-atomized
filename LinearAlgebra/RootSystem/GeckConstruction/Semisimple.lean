/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import Mathlib.Algebra.Lie.Weights.Linear
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
public import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# Geck's construction of a Lie algebra associated to a root system yields semisimple algebras

This file contains a proof that `RootPairing.GeckConstruction.lieAlgebra` yields semisimple Lie
algebras.

## Main definitions:

* `RootPairing.GeckConstruction.trace_toEnd_eq_zero`: the Geck construction yields trace-free
  matrices.
* `RootPairing.GeckConstruction.instIsIrreducible`: the defining representation of the Geck
  construction is irreducible.
* `RootPairing.GeckConstruction.instHasTrivialRadical`: the Geck construction yields semisimple
  Lie algebras.

-/

@[expose] public section

noncomputable section

namespace RootPairing.GeckConstruction

open Function Submodule
open Set hiding diagonal
open scoped Matrix

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

section IsDomain

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
  [Fintype ι] [DecidableEq ι] (i : b.support)

/--
lemma `isNilpotent_e_aux` / 引理 `isNilpotent_e_aux`

English:
lemma isNilpotent_e_aux
  given: {j : ι} (n : Nat) (h : letI _i := P.indexNeg; j != -i)
  proof: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  have aux (n : Nat) : (e i ^ (n + 1)).col (.inr j) = (e i).mulVec ((e i ^ n).col (.inr j)) := by
    rw [pow_succ']; rw [← Matrix.mulVec_single_one]; rw [← Mat

中文:
引理 isNilpotent_e_aux
  条件: {j : ι} (n : 自然数) (h : letI _i := P.indexNeg; j != -i)
  证明: by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  have aux (n : Nat) : (e i ^ (n + 1)).col (.inr j) = (e i).mulVec ((e i ^ n).col (.inr j)) := by
    rw [pow_succ']; rw [← Matrix.mulVec_single_one]; rw [← Mat
-/
private lemma isNilpotent_e_aux {j : ι} (n : Nat) (h : letI _i := P.indexNeg; j != -i) :
    (e i ^ n).col (.inr j) = 0 ∨
      exists (k : ι) (x : Nat), P.root k = P.root j + n • P.root i ∧
        (e i ^ n).col (.inr j) = x • Pi.single (.inr k) 1 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  have aux (n : Nat) : (e i ^ (n + 1)).col (.inr j) = (e i).mulVec ((e i ^ n).col (.inr j)) := by
    rw [pow_succ']; rw [← Matrix.mulVec_single_one]; rw [← Matrix.mulVec_mulVec]; simp
  induction n with
  | zero => exact Or.inr ⟨j, 1, by simp, by ext; simp [Pi.single_apply]⟩
  | succ n ih =>
    rcases ih with hn | ⟨k, x, hk₁, hk₂⟩
    · left; simp [aux, hn]
    rw [aux]; rw [hk₂]; rw [Matrix.mulVec_smul]
    have hki : k != -i := by
      rintro rfl
      replace hk₁ : P.root (-j) = (n + 1) • P.root i := by
        simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self, neg_eq_iff_add_eq_zero,
          add_smul, one_smul] at hk₁ ⊢
        rw [← hk₁]
        module
      rcases n.eq_zero_or_pos with rfl | hn
      · apply h
        rw [zero_add]; rw [one_smul]; rw [EmbeddingLike.apply_eq_iff_eq] at hk₁
        simp [← hk₁, -indexNeg_neg]
      · have _i : (n + 1).AtLeastTwo := ⟨by lia⟩
        exact P.nsmul_notMem_range_root (n := n + 1) (i := i) ⟨-j, hk₁⟩
    by_cases hij : P.root j + (n + 1) • P.root i in range P.root
    · obtain ⟨l, hl⟩ := hij
      right
      refine ⟨l, x * (P.chainBotCoeff i k + 1), hl, ?_⟩
      ext (m | m)
      · simp [e, -indexNeg_neg, hki]
      · rcases eq_or_ne m l with rfl | hml
        · replace hl : P.root m = P.root i + P.root k := by rw [hl, hk₁]; module
          simp [e, -indexNeg_neg, hl, mul_add]
        · replace hl : P.root m != P.root i + P.root k :=
            fun contra => hml (P.root.injective <| by rw [hl, contra, hk₁]; module)
          simp [e, -indexNeg_neg, hml, hl]
    · left
      ext (l | l)
      · simp [e, -indexNeg_neg, hki]
      · replace hij : P.root l != P.root i + P.root k :=
          fun contra => hij ⟨l, by rw [contra, hk₁]; module⟩
        simp [e, -indexNeg_neg, hij]

/--
lemma `isNilpotent_e` / 引理 `isNilpotent_e`

English:
lemma isNilpotent_e
  proof: by
  classical
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  rw [Matrix.isNilpotent_iff_forall_col]
  have case_inl (j : b.support) : (e i ^ 2).col (Sum.inl j) = 0 := by
    ext (k | k)
    · simp [e, sq, ne

中文:
引理 isNilpotent_e
  证明: by
  classical
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  rw [Matrix.isNilpotent_iff_forall_col]
  have case_inl (j : b.support) : (e i ^ 2).col (Sum.inl j) = 0 := by
    ext (k | k)
    · simp [e, sq, ne

Depends on / 依赖: Finset, Finset.univ, IsAddTorsionFree, IsReflexive, Matrix, Matrix.isNilpotent_iff_forall_col, Module, Module.IsReflexive, P.indexNeg, P.nsmul_notMem_ra, P.root, P.toLinearMap, Sum.inl, b.support, case_inl, classical, contra, indexNeg, indexNeg_neg, isNilpotent_iff_forall_col
-/
lemma isNilpotent_e :
    IsNilpotent (e i) := by
  classical
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  rw [Matrix.isNilpotent_iff_forall_col]
  have case_inl (j : b.support) : (e i ^ 2).col (Sum.inl j) = 0 := by
    ext (k | k)
    · simp [e, sq, ne_neg P i, -indexNeg_neg]
    · have aux : forall x : ι, x in Finset.univ -> ¬ (x = i ∧ P.root k = P.root i + P.root x) := by
        suffices P.root k != (2 : Nat) • P.root i by simpa [two_smul]
        exact fun contra => P.nsmul_notMem_range_root (n := 2) (i := i) ⟨k, contra⟩
      simp [e, sq, -indexNeg_neg, ← ite_and, Finset.sum_ite_of_false aux]
  rintro (j | j)
  · exact ⟨2, case_inl j⟩
  · by_cases hij : j = -i
    · use 2 + 1
      replace hij : (e i).col (Sum.inr j) = u i := by
        ext (k | k)
        · simp [e, -indexNeg_neg, Pi.single_apply, hij]
        · have hk : P.root k != P.root i + P.root j := by simp [hij, P.ne_zero k]
          simp [e, -indexNeg_neg, hk]
      rw [pow_succ]; rw [← Matrix.mulVec_single_one]; rw [← Matrix.mulVec_mulVec]
      simp [hij, case_inl i]
    use P.chainTopCoeff i j + 1
    rcases isNilpotent_e_aux i (P.chainTopCoeff i j + 1) hij with this | ⟨k, x, hk₁, -⟩
    · assumption
    exfalso
    replace hk₁ : P.root j + (P.chainTopCoeff i j + 1) • P.root i in range P.root := ⟨k, hk₁⟩
    have hij' : LinearIndependent R ![P.root i, P.root j] := by
      apply IsReduced.linearIndependent P ?_ ?_
      · rintro rfl
        apply P.nsmul_notMem_range_root (n := P.chainTopCoeff i i + 2) (i := i)
        convert! hk₁ using 1
        module
      · contrapose hij
        rw [root_eq_neg_iff] at hij
        rw [hij]; rw [← indexNeg_neg]; rw [neg_neg]
    rw [root_add_nsmul_mem_range_iff_le_chainTopCoeff hij'] at hk₁
    lia

/--
lemma `isNilpotent_f` / 引理 `isNilpotent_f`

English:
lemma isNilpotent_f
  proof: by
  obtain ⟨n, hn⟩ := isNilpotent_e i
  suffices (ω b) * (f i ^ n) = 0 from ⟨n, by simpa [← mul_assoc] using congr_arg (ω b * ·) this⟩
  suffices (ω b) * (f i ^ n) = (e i ^ n) * (ω b) by simp [this, hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_as

中文:
引理 isNilpotent_f
  证明: by
  obtain ⟨n, hn⟩ := isNilpotent_e i
  suffices (ω b) * (f i ^ n) = 0 from ⟨n, by simpa [← mul_assoc] using congr_arg (ω b * ·) this⟩
  suffices (ω b) * (f i ^ n) = (e i ^ n) * (ω b) by simp [this, hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_as

Depends on / 依赖: congr_arg, isNilpotent_e, mul_assoc, pow_succ
-/
lemma isNilpotent_f :
    IsNilpotent (f i) := by
  obtain ⟨n, hn⟩ := isNilpotent_e i
  suffices (ω b) * (f i ^ n) = 0 from ⟨n, by simpa [← mul_assoc] using congr_arg (ω b * ·) this⟩
  suffices (ω b) * (f i ^ n) = (e i ^ n) * (ω b) by simp [this, hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, ω_mul_f, ← mul_assoc]

omit [P.IsReduced] [IsDomain R] [DecidableEq ι] in
/--
lemma `trace_h_eq_zero` / 引理 `trace_h_eq_zero`

English:
lemma trace_h_eq_zero
  proof: by
  classical
  let _i := P.indexNeg
  suffices ∑ j, P.pairingIn Int j i = 0 by
    simp only [h_eq_diagonal, Matrix.trace_diagonal, Fintype.sum_sum_type, Finset.univ_eq_attach,
      Sum.elim_inl, Pi.zero_apply, Finset.sum_const_zero, Sum.elim_inr, zero_add]
    norm_cast
  suffices ∑ j, P.pairing

中文:
引理 trace_h_eq_zero
  证明: by
  classical
  let _i := P.indexNeg
  suffices ∑ j, P.pairingIn Int j i = 0 by
    simp only [h_eq_diagonal, Matrix.trace_diagonal, Fintype.sum_sum_type, Finset.univ_eq_attach,
      Sum.elim_inl, Pi.zero_apply, Finset.sum_const_zero, Sum.elim_inr, zero_add]
    norm_cast
  suffices ∑ j, P.pairing
-/
@[simp] lemma trace_h_eq_zero :
    (h i).trace = 0 := by
  classical
  let _i := P.indexNeg
  suffices ∑ j, P.pairingIn Int j i = 0 by
    simp only [h_eq_diagonal, Matrix.trace_diagonal, Fintype.sum_sum_type, Finset.univ_eq_attach,
      Sum.elim_inl, Pi.zero_apply, Finset.sum_const_zero, Sum.elim_inr, zero_add]
    norm_cast
  suffices ∑ j, P.pairingIn Int (-j) i = ∑ j, P.pairingIn Int j i from
eq_zero_of_neg_eq by simpa using this
  let σ : ι ≃ ι := Function.Involutive.toPerm _ neg_involutive
  exact σ.sum_comp (P.pairingIn Int · i)

attribute [local instance 100] LieRing.ofAssociativeRing

open LinearMap LieModule in
/--
lemma `trace_toEnd_eq_zero` / 引理 `trace_toEnd_eq_zero`

English:
lemma trace_toEnd_eq_zero
  given: (x : lieAlgebra b)
  proof: by
  obtain ⟨x, hx⟩ := x
  suffices trace R _ x.toLin' = 0 by simpa
  refine LieAlgebra.trace_toEnd_eq_zero ?_ hx
  rintro - ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · simp
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_e i)
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (

中文:
引理 trace_toEnd_eq_zero
  条件: (x : lieAlgebra b)
  证明: by
  obtain ⟨x, hx⟩ := x
  suffices trace R _ x.toLin' = 0 by simpa
  refine LieAlgebra.trace_toEnd_eq_zero ?_ hx
  rintro - ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · simp
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_e i)
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (

Depends on / 依赖: LieAlgebra, LieAlgebra.trace_toEnd_eq_zero, Matrix, Matrix.isNilpotent_trace_of_isNilpotent, isNilpotent_e, isNilpotent_f, isNilpotent_trace_of_isNilpotent, trace_toEnd_eq_zero, x.toLin
-/
lemma trace_toEnd_eq_zero (x : lieAlgebra b) :
    trace R _ (toEnd R _ (b.support oplus ι -> R) x) = 0 := by
  obtain ⟨x, hx⟩ := x
  suffices trace R _ x.toLin' = 0 by simpa
  refine LieAlgebra.trace_toEnd_eq_zero ?_ hx
  rintro - ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · simp
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_e i)
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_f i)

end IsDomain

section Field

variable {ι K M N : Type*} [Field K] [CharZero K] [DecidableEq ι] [Fintype ι]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsCrystallographic] {b : P.Base}

open LieModule Matrix

local notation "H" => cartanSubalgebra' b

/--
lemma `instIsIrreducible_aux₀` / 引理 `instIsIrreducible_aux₀`

English:
lemma instIsIrreducible_aux₀
  statement: {U : LieSubmodule K H (b.support oplus ι -> K)}
  proof: by
  suffices forall {w : b.support oplus ι -> K} (hw₀ : w != 0) (hw : w in genWeightSpace (b.support oplus ι -> K) χ),
      exists (i : ι) (t : K), t • w = v b i by
    obtain ⟨w, hw, hw₀⟩ : exists w in genWeightSpace U χ, w != 0 := by
      simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, 

中文:
引理 instIsIrreducible_aux₀
  结论: {U : LieSubmodule K H (b.support oplus ι -> K)}
  证明: by
  suffices forall {w : b.support oplus ι -> K} (hw₀ : w != 0) (hw : w in genWeightSpace (b.support oplus ι -> K) χ),
      exists (i : ι) (t : K), t • w = v b i by
    obtain ⟨w, hw, hw₀⟩ : exists w in genWeightSpace U χ, w != 0 := by
      simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, 

Depends on / 依赖: ENNReal, ENNReal.coe_add, coe_add
-/
private lemma instIsIrreducible_aux₀ {U : LieSubmodule K H (b.support oplus ι -> K)}
    (χ : H -> K) (hχ : χ != 0) (hχ' : genWeightSpace U χ != ⊥) :
    exists i, v b i in (genWeightSpace U χ).map U.incl := by
  suffices forall {w : b.support oplus ι -> K} (hw₀ : w != 0) (hw : w in genWeightSpace (b.support oplus ι -> K) χ),
      exists (i : ι) (t : K), t • w = v b i by
    obtain ⟨w, hw, hw₀⟩ : exists w in genWeightSpace U χ, w != 0 := by
      simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using! hχ'
    replace hw : U.incl w in genWeightSpace (b.support oplus ι -> K) χ :=
map_genWeightSpace_le (f := U.incl) by simpa
    obtain ⟨i, t, hi : t • w = v b i⟩ := this (by simpa) hw
    use i
    rw [map_genWeightSpace_eq_of_injective U.injective_incl]; rw [LieSubmodule.range_incl]; rw [← hi]; rw [LieSubmodule.mem_inf]
    exact ⟨SMulMemClass.smul_mem _ hw, SMulMemClass.smul_mem _ w.property⟩
  clear! U
  intro w hw₀ hw
  have aux (d : b.support oplus ι -> K) (x : H) (hdx : x = diagonal d) :
      w in genWeightSpaceOf (b.support oplus ι -> K) (χ x) x ↔
        exists k, diagonal ((d - χ x • 1) ^ k) *ᵥ w = 0 := by
    set μ := χ x
    obtain ⟨⟨x, hx⟩, hx'⟩ := x
    replace hdx : x = diagonal d := by simpa using! hdx
    have this (d : b.support oplus ι -> K) (μ : K) :
        (diagonal d).toLin' - μ • 1 = (diagonal (d - μ • 1)).toLin' := by
      ext i j
      simp [Pi.single_apply, ite_sub_ite]
    simp [mem_genWeightSpaceOf, hdx, this, ← toLin'_pow, diagonal_pow]
  obtain ⟨i, hi⟩ : exists i, w (Sum.inr i) != 0 := by
    obtain ⟨l, hl⟩ : exists l, χ (h' l) != 0 := by
      replace hw₀ : genWeightSpace (b.support oplus ι -> K) χ != ⊥ := by
        contrapose hw₀; rw [LieSubmodule.eq_bot_iff] at hw₀; exact hw₀ _ hw
      let χ' : H ->ₗ[K] K := (Weight.mk χ hw₀).toLinear
      replace hχ : χ' != 0 := by contrapose hχ; ext x; simpa using! LinearMap.congr_fun hχ x
      contrapose! hχ
      apply LinearMap.ext_on (span_range_h'_eq_top b)
      rintro - ⟨l, rfl⟩
      simp [χ', hχ l]
    contrapose! hw₀
    suffices forall i : b.support, w (Sum.inl i) = 0 by ext (k | k) <;> simp [hw₀, this]
    intro i
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support oplus ι -> K) (h' l) χ hw
    rw [aux (Sum.elim 0 (P.pairingIn Int · l)) (h' l) (h_eq_diagonal l)] at hw
    obtain ⟨k, hk⟩ := hw
    simpa [mulVec_eq_sum, diagonal_apply, hl] using! congr_fun hk (Sum.inl i)
  refine ⟨i, (w (Sum.inr i))⁻¹, ?_⟩
  suffices exists d : ι -> K, (forall i, d i != 0) ∧ Pairwise ((· != ·) on d) ∧
      diagonal (Sum.elim 0 d) in cartanSubalgebra b by
    obtain ⟨d, hd₀, hd₁, hd₂⟩ := this
    let x : H := ⟨⟨diagonal (Sum.elim 0 d), cartanSubalgebra_le_lieAlgebra hd₂⟩, hd₂⟩
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support oplus ι -> K) x χ hw
    rw [aux (Sum.elim 0 d) x rfl] at hw
    obtain ⟨k, hk⟩ := hw
    obtain ⟨hχx, hk₀⟩ : d i = χ x ∧ k != 0 := by
      simpa [hi, mulVec_eq_sum, diagonal_apply, sub_eq_zero] using! congr_fun hk (Sum.inr i)
    ext (j | j)
    · have : χ x != 0 := hχx ▸ hd₀ i
      simpa [hi, mulVec_eq_sum, diagonal_apply, hk₀, this] using! congr_fun hk (Sum.inl j)
    · rcases eq_or_ne i j with rfl | hij
      · simp [hi]
      · suffices d j != χ x by
          simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero, this, hij, hi] using!
            congr_fun hk (Sum.inr j)
        rw [← hχx]
exact hd₁ by simp [hij.symm]
  simp_rw [cartanSubalgebra, LieSubalgebra.mem_mk_iff', diagonal_elim_mem_span_h_iff]
  exact (exists_congr fun d => by tauto).mp b.exists_mem_span_pairingIn_ne_zero_and_pairwise_ne

/--
lemma `instIsIrreducible_aux₁` / 引理 `instIsIrreducible_aux₁`

English:
lemma instIsIrreducible_aux₁
  statement: (U : LieSubmodule K H (b.support oplus ι -> K))
  proof: by
  suffices exists χ : H -> K, χ != 0 ∧ genWeightSpace U χ != ⊥ by
    obtain ⟨χ, hχ₀, hχ⟩ := this
    obtain ⟨i, hi⟩ := instIsIrreducible_aux₀ χ hχ₀ hχ
    exact ⟨i, LieSubmodule.map_incl_le hi⟩
  contrapose! hU
  refine le_trans ?_ (map_genWeightSpace_le (f := U.incl))
  suffices genWeightSpace 

中文:
引理 instIsIrreducible_aux₁
  结论: (U : LieSubmodule K H (b.support oplus ι -> K))
  证明: by
  suffices exists χ : H -> K, χ != 0 ∧ genWeightSpace U χ != ⊥ by
    obtain ⟨χ, hχ₀, hχ⟩ := this
    obtain ⟨i, hi⟩ := instIsIrreducible_aux₀ χ hχ₀ hχ
    exact ⟨i, LieSubmodule.map_incl_le hi⟩
  contrapose! hU
  refine le_trans ?_ (map_genWeightSpace_le (f := U.incl))
  suffices genWeightSpace 
-/
private lemma instIsIrreducible_aux₁ (U : LieSubmodule K H (b.support oplus ι -> K))
    (hU : ¬ U <= genWeightSpace (b.support oplus ι -> K) 0) :
    exists i, v b i in U := by
  suffices exists χ : H -> K, χ != 0 ∧ genWeightSpace U χ != ⊥ by
    obtain ⟨χ, hχ₀, hχ⟩ := this
    obtain ⟨i, hi⟩ := instIsIrreducible_aux₀ χ hχ₀ hχ
    exact ⟨i, LieSubmodule.map_incl_le hi⟩
  contrapose! hU
  refine le_trans ?_ (map_genWeightSpace_le (f := U.incl))
  suffices genWeightSpace U (0 : H -> K) = ⊤ by simp [this]
  have : ⨆ (χ : H -> K), ⨆ (_ : χ != 0), (⊥ : LieSubmodule K H U) = ⊥ := biSup_const ⟨1, one_ne_zero⟩
  rw [← iSup_genWeightSpace_eq_top K H U]; rw [iSup_split_single _ 0]; rw [biSup_congr hU]; rw [this]; rw [sup_bot_eq]

omit [P.IsRootSystem] in
/--
lemma `instIsIrreducible_aux₂` / 引理 `instIsIrreducible_aux₂`

English:
lemma instIsIrreducible_aux₂
  statement: [P.IsReduced] [P.IsIrreducible]
  proof: by
  let _i := P.indexNeg
  have hωu (i : b.support) : ω b *ᵥ (u i) = u i := by
    ext (j | j) <;> simp [ω, u, Pi.single_apply, one_apply]
  have hωv (i : ι) : ω b *ᵥ (v b i) = v b (-i) := by ext (j | j) <;> simp [ω, v, Pi.single_apply]
  obtain ⟨j, hj⟩ : exists j : b.support, u j in U := by
    re

中文:
引理 instIsIrreducible_aux₂
  结论: [P.IsReduced] [P.IsIrreducible]
  证明: by
  let _i := P.indexNeg
  have hωu (i : b.support) : ω b *ᵥ (u i) = u i := by
    ext (j | j) <;> simp [ω, u, Pi.single_apply, one_apply]
  have hωv (i : ι) : ω b *ᵥ (v b i) = v b (-i) := by ext (j | j) <;> simp [ω, v, Pi.single_apply]
  obtain ⟨j, hj⟩ : exists j : b.support, u j in U := by
    re
-/
private lemma instIsIrreducible_aux₂ [P.IsReduced] [P.IsIrreducible]
    {U : LieSubmodule K (lieAlgebra b) (b.support oplus ι -> K)} {i : ι} (hi : v b i in U) :
    U = ⊤ := by
  let _i := P.indexNeg
  have hωu (i : b.support) : ω b *ᵥ (u i) = u i := by
    ext (j | j) <;> simp [ω, u, Pi.single_apply, one_apply]
  have hωv (i : ι) : ω b *ᵥ (v b i) = v b (-i) := by ext (j | j) <;> simp [ω, v, Pi.single_apply]
  obtain ⟨j, hj⟩ : exists j : b.support, u j in U := by
    revert U
    apply b.induction_add i
    · intro i h U hi
      replace hi : v b i in ωConjLieSubmodule U := by simpa [hωv]
      obtain ⟨j, hj⟩ := h hi
      exact ⟨j, by simpa [hωu] using! hj⟩
    · intro j hj U hj'
      let f' : lieAlgebra b := ⟨f ⟨j, hj⟩, f_mem_lieAlgebra _⟩
      have : ⁅f', v b j⁆ = u ⟨j, hj⟩ := f_lie_v_same ⟨j, hj⟩
      replace this : u ⟨j, hj⟩ in U := by
        rw [← this]
        exact U.lie_mem (x := f') hj'
      exact ⟨⟨j, hj⟩, this⟩
    · intro j k l h₁ h₂ hk U hl
      have : ⁅f ⟨k, hk⟩, v b l⁆ = (P.chainTopCoeff k l + 1 : K) • v b j := f_lie_v_ne h₁
      replace this : (P.chainTopCoeff k l + 1 : K) • v b j in U := by
        rw [← this]
        let f' : lieAlgebra b := ⟨f ⟨k, hk⟩, f_mem_lieAlgebra _⟩
        change ⁅f', v b l⁆ in U
        exact U.lie_mem hl
exact h₂ (U.smul_mem_iff (by norm_cast)).mp this
  have aux (k : b.support) : u k in U := by
    refine b.induction_on_cartanMatrix (fun k : b.support => u k in U) hj (fun l l' hl₁ hl₂ => ?_)
    suffices (↑|b.cartanMatrix l' l| : K) • u l' in U from (U.smul_mem_iff (by simpa)).mp this
    rw [Int.cast_smul_eq_zsmul]; rw [← lie_e_lie_f_apply l' l]
    let e' : lieAlgebra b := ⟨e l', e_mem_lieAlgebra l'⟩
    let f' : lieAlgebra b := ⟨f l', f_mem_lieAlgebra l'⟩
    change ⁅e', ⁅f', u l⁆⁆ in U
exact U.lie_mem U.lie_mem hl₁
  clear! j i
  suffices forall j, v b j in U by
    simp_rw [← LieSubmodule.toSubmodule_eq_top, eq_top_iff,
      ← (Pi.basisFun K (b.support oplus ι)).span_eq, Submodule.span_le, range_subset_iff,
      Pi.basisFun_apply]
    aesop
  intro j
  revert U
  apply b.induction_add j
  · intro j h U hU
    suffices v b j in ωConjLieSubmodule U by simpa [hωv] using! this
    exact h fun k => by simp [hωu, hU]
  · intro k hk U aux
    have : ⁅e ⟨k, hk⟩, u ⟨k, hk⟩⁆ = (2 : K) • v b k := by
      simpa [-lie_apply] using! e_lie_u ⟨k, hk⟩ ⟨k, hk⟩
    let e' : lieAlgebra b := ⟨e ⟨k, hk⟩, e_mem_lieAlgebra ⟨k, hk⟩⟩
    change ⁅e', u ⟨k, hk⟩⁆ = _ at this
replace aux := U.lie_mem (x := e') aux ⟨k, hk⟩
    rw [this] at aux
    exact (U.smul_mem_iff two_ne_zero).mp aux
  · intro k l m hm hk hl U aux
    rw [add_comm] at hm
    let e' : lieAlgebra b := ⟨e ⟨l, hl⟩, e_mem_lieAlgebra _⟩
    have : ⁅e', v b k⁆ = (P.chainBotCoeff l k + 1 : K) • v b m := e_lie_v_ne hm
    replace this : (P.chainBotCoeff l k + 1 : K) • v b m in U := by
      rw [← this]
      exact U.lie_mem (hk aux)
    exact (U.smul_mem_iff (by norm_cast)).mp this

omit [P.IsRootSystem] in
/--
lemma `coe_genWeightSpace_zero_eq_span_range_u` / 引理 `coe_genWeightSpace_zero_eq_span_range_u`

English:
lemma coe_genWeightSpace_zero_eq_span_range_u
  proof: by
  refine le_antisymm (fun w hw => Pi.mem_span_range_single_inl_iff.mpr fun i => ?_) ?_
  · replace hw : forall (x) (hx : x in lieAlgebra b), ⟨x, hx⟩ in H ->
        exists k, (x.toLin' ^ k) w = 0 := by simpa [mem_genWeightSpace] using hw
    obtain ⟨j, hj⟩ : exists j : b.support, P.pairingIn Int 

中文:
引理 coe_genWeightSpace_zero_eq_span_range_u
  证明: by
  refine le_antisymm (fun w hw => Pi.mem_span_range_single_inl_iff.mpr fun i => ?_) ?_
  · replace hw : forall (x) (hx : x in lieAlgebra b), ⟨x, hx⟩ in H ->
        exists k, (x.toLin' ^ k) w = 0 := by simpa [mem_genWeightSpace] using hw
    obtain ⟨j, hj⟩ : exists j : b.support, P.pairingIn Int 

Depends on / 依赖: P.pairingIn, P.pairingIn_eq_zero_iff, Pi.mem_span_range_single_inl_iff.mpr, b.exists_mem_support_pos_pairingIn_ne_zero, b.support, exists_mem_support_pos_pairingIn_ne_zero, h_mem_ca, h_mem_lieAlgebra, le_antisymm, lieAlgebra, mem_genWeightSpace, mem_span_range_single_inl_iff, ne_eq, pairingIn, pairingIn_eq_zero_iff, replace, support, x.toLin
-/
lemma coe_genWeightSpace_zero_eq_span_range_u :
    genWeightSpace (b.support oplus ι -> K) (0 : H -> K) = span K (range <| u (b := b)) := by
  refine le_antisymm (fun w hw => Pi.mem_span_range_single_inl_iff.mpr fun i => ?_) ?_
  · replace hw : forall (x) (hx : x in lieAlgebra b), ⟨x, hx⟩ in H ->
        exists k, (x.toLin' ^ k) w = 0 := by simpa [mem_genWeightSpace] using hw
    obtain ⟨j, hj⟩ : exists j : b.support, P.pairingIn Int i j != 0 := by
      obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
      rw [ne_eq]; rw [P.pairingIn_eq_zero_iff] at hj₀
      exact ⟨⟨j, hj⟩, hj₀⟩
    obtain ⟨k, hk⟩ := hw (h j) (h_mem_lieAlgebra j) (h_mem_cartanSubalgebra' j _)
    simpa [h_eq_diagonal, ← toLin'_pow, fromBlocks_diagonal_pow, diagonal_pow,
      mulVec_eq_sum, diagonal_apply, hj] using congr_fun hk (Sum.inr i)
  · rw [span_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule, mem_genWeightSpace]
    rintro ⟨⟨x, -⟩, hx⟩
    exact ⟨1, funext fun j => by simpa using apply_sum_inl_eq_zero_of_mem_span_h i j hx⟩

variable [P.IsReduced] [P.IsIrreducible]

/--
Instance `instIsIrreducible` / 实例 `instIsIrreducible`

English:
instance instIsIrreducible
  signature: [Nonempty ι]
  body: by
  refine LieModule.IsIrreducible.mk fun U hU => ?_
  suffices exists i, v b i in U by obtain ⟨i, hi⟩ := this; exact instIsIrreducible_aux₂ hi
  let U' : LieSubmodule K H (b.support oplus ι -> K) := { U with lie_mem := U.lie_mem }
  apply instIsIrreducible_aux₁ U'
  contrapose hU
  replace hU : U 

中文:
实例 instIsIrreducible
  签名: [Nonempty ι]
  定义体: by
  refine LieModule.IsIrreducible.mk fun U hU => ?_
  suffices exists i, v b i in U by obtain ⟨i, hi⟩ := this; exact instIsIrreducible_aux₂ hi
  let U' : LieSubmodule K H (b.support oplus ι -> K) := { U with lie_mem := U.lie_mem }
  apply instIsIrreducible_aux₁ U'
  contrapose hU
  replace hU : U 

Depends on / 依赖: IsIrreducible, LieModule, LieModule.IsIrreducible.mk, LieSubmodule, LieSubmodule.eq_bot_iff, U.lie_mem, b.support, coe_genWeightSpace_zero_eq_span_range_u, contrapose, eq_bot_iff, lie_mem, mem_sp, replace, support
-/
instance instIsIrreducible [Nonempty ι] :
    LieModule.IsIrreducible K (lieAlgebra b) (b.support oplus ι -> K) := by
  refine LieModule.IsIrreducible.mk fun U hU => ?_
  suffices exists i, v b i in U by obtain ⟨i, hi⟩ := this; exact instIsIrreducible_aux₂ hi
  let U' : LieSubmodule K H (b.support oplus ι -> K) := { U with lie_mem := U.lie_mem }
  apply instIsIrreducible_aux₁ U'
  contrapose hU
  replace hU : U <= span K (range (u (b := b))) := by rwa [← coe_genWeightSpace_zero_eq_span_range_u]
  refine (LieSubmodule.eq_bot_iff _).mpr fun x hx => ?_
  obtain ⟨c, hc⟩ : exists c : b.support -> K, ∑ i, c i • u i = x :=
(mem_span_range_iff_exists_fun K).mp hU hx
  suffices c = 0 by simp [this, ← hc]
  have hCM : (4 - b.cartanMatrix).det != 0 :=
    RootPairing.Base.det_four_sub_cartanMatrix_ne_zero b
  contrapose! hCM
  suffices ((Int.castRingHom K).mapMatrix (4 - b.cartanMatrix)).det = 0 by
    simpa only [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] using this
  rw [← exists_mulVec_eq_zero_iff]
  suffices (b.cartanMatrix.map abs).map (↑) *ᵥ c = 0 from ⟨c, hCM, by simpa using this⟩
  ext j
  suffices ∑ k, c k * |b.cartanMatrix j k| = 0 by
    simpa [mulVec_eq_sum, -Base.cartanMatrix_map_abs]
  by_contra contra
  have key : v b j in U := by
    have : ⁅e j, x⁆ in U := U.lie_mem (x := ⟨e j, e_mem_lieAlgebra j⟩) hx
    have aux (k : b.support) : ⁅e j, u k⁆ = |b.cartanMatrix j k| • v b j := e_lie_u j k
    simp_rw [← hc, lie_sum, lie_smul, aux, smul_comm (M := K), ← smul_assoc, ← Finset.sum_smul,
      zsmul_eq_mul, mul_comm, ← LieSubmodule.mem_toSubmodule, U.smul_mem_iff contra] at this
    assumption
  have : v b j ∉ U := fun hj => by simpa [v] using apply_inr_eq_zero_of_mem_span_range_u b j (hU hj)
  contradiction

/--
Instance `instHasTrivialRadical` / 实例 `instHasTrivialRadical`

English:
instance instHasTrivialRadical
  signature: [IsAlgClosed K]
  body: by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · exact LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful K _ _ trace_toEnd_eq_zero

中文:
实例 instHasTrivialRadical
  签名: [IsAlgClosed K]
  定义体: by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · exact LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful K _ _ trace_toEnd_eq_zero

Depends on / 依赖: LieAlgebra, LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful, hasTrivialRadical_of_isIrreducible_of_isFaithful, infer_instance, isEmpty_or_nonempty, trace_toEnd_eq_zero
-/
instance instHasTrivialRadical [IsAlgClosed K] : LieAlgebra.HasTrivialRadical K (lieAlgebra b) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · exact LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful K _ _ trace_toEnd_eq_zero

end Field

end RootPairing.GeckConstruction
