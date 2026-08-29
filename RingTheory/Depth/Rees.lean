/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# The Rees theorem

In this file we prove the Rees theorem for depth, which relates the vanishing of
certain `Ext` groups and the length of a maximal regular sequence in a certain ideal.

## Main results

* `ModuleCat.exists_isRegular_tfae` (Rees theorem) : For any `n : ℕ`, Noetherian ring `R`,
  `I : Ideal R`, and finitely generated and nontrivial `R`-module `M` satisfying `IM < M`,
  the following are equivalent:
  · for any `N : ModuleCat R` finitely generated such that `Supp N ⊆ V(I)`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (R ⧸ I) M i = 0`
  · there exists a `N : ModuleCat R` finitely generated and nontrivial with `Supp N = V(I)`
    such that `∀ i < n, Ext N M i = 0`
  · there exists a `M`-regular sequence of length `n` with every element in `I`

## References

* [Commutative Algebra, Theorem 28][matsumuraCommAlg]

-/

public section

universe v u

open LinearMap RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise IsSMulRegular

variable {R : Type u} [CommRing R]

/--
lemma `smul_top_quotSMulTop_ne_top_of_smul_top_ne_top` / 引理 `smul_top_quotSMulTop_ne_top_of_smul_top_ne_top`

English:
lemma smul_top_quotSMulTop_ne_top_of_smul_top_ne_top
  statement: {M : Type*} [AddCommGroup M]
  proof: by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI

中文:
引理 smul_top_quotSMulTop_ne_top_of_smul_top_ne_top
  结论: {M : 类型} [AddCommGroup M]
  证明: by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI
-/
private lemma smul_top_quotSMulTop_ne_top_of_smul_top_ne_top {M : Type*} [AddCommGroup M]
    [Module R M] {I : Ideal R} {r : R} (hr : r in I)
    (hI : I • (⊤ : Submodule R M) != ⊤) :
    I • (⊤ : Submodule R (QuotSMulTop r M)) != ⊤ := by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI

namespace ModuleCat

/--
lemma `exists_isRegular_of_exists_subsingleton_ext` / 引理 `exists_isRegular_of_exists_subsingleton_ext`

English:
lemma exists_isRegular_of_exists_subsingleton_ext
  statement: [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
  proof: by
  induction n generalizing M with
  | zero =>
    have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rw [Module.support_eq_zeroLocus]; rw [PrimeSpectrum.zeroLocus_eq_iff] at h_supp
    -- use `Ext N M 0` v

中文:
引理 exists_isRegular_of_exists_subsingleton_ext
  结论: [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
  证明: by
  induction n generalizing M with
  | zero =>
    have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rw [Module.support_eq_zeroLocus]; rw [PrimeSpectrum.zeroLocus_eq_iff] at h_supp
    -- use `Ext N M 0` v

Depends on / 依赖: Module, Module.support_eq_zeroLocus, Nontrivial, PrimeSpectrum, PrimeSpectrum.zeroLocus_eq_iff, Submodule, Submodule.nontrivial_iff, generalizing, h_supp, isRegular_iff, nontrivial_iff, nontrivial_of_lt, smul_lt, support_eq_zeroLocus, zeroLocus_eq_iff
-/
lemma exists_isRegular_of_exists_subsingleton_ext [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    (n : Nat) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (N : ModuleCat.{v} R) [Module.Finite R N]
    (h_supp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (h_ext : forall i < n, Subsingleton (Ext N M i)) :
    exists rs : List R, rs.length = n ∧ (forall r in rs, r in I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rw [Module.support_eq_zeroLocus]; rw [PrimeSpectrum.zeroLocus_eq_iff] at h_supp
    -- use `Ext N M 0` vanish to obtain an `M`-regular element `x` in `Ann(N)`
    have : Subsingleton (N ⟶ M) := Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
    have : Subsingleton (N ->ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    obtain ⟨x, mem_ann, hx⟩ := subsingleton_linearMap_iff.mp this
    -- take a power of it to make `xᵏ` fall into `I`
    obtain ⟨k, hk⟩ := le_of_le_of_eq Ideal.le_radical h_supp mem_ann
    -- verify that `N` indeed make `M ⧸ xᵏM` satisfy the induction hypothesis
    have h_ext' : forall i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i) := by
      intro i hi
      -- the vanishing of `Ext` is obtained from the (covariant) long exact sequence given by
      -- `M.smulShortComplex (x ^ k)`
      have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext i (by omega))
      have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext (i + 1) (by omega))
exact AddCommGrpCat.subsingleton_of_isZero ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    obtain ⟨rs, len, mem, reg⟩ := ih (ModuleCat.of R (QuotSMulTop (x ^ k) M))
      (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top hk smul_lt.ne).lt_top h_ext'
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

/--
lemma `subsingleton_ext_of_exists_isRegular` / 引理 `subsingleton_ext_of_exists_isRegular`

English:
lemma subsingleton_ext_of_exists_isRegular
  statement: [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
  proof: by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus]; rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] => simp at len
    | a :: r

中文:
引理 subsingleton_ext_of_exists_isRegular
  结论: [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
  证明: by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus]; rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] => simp at len
    | a :: r

Depends on / 依赖: Module, Module.support_eq_zeroLocus, PrimeSpectrum, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff, generalize, generalizing, le_rad, length, rs.length, support_eq_zeroLocus, zeroLocus_subset_zeroLocus_iff
-/
lemma subsingleton_ext_of_exists_isRegular [Small.{v} R] [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N subseteq PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : forall r in rs, r in I) (reg : IsRegular M rs) :
    forall i < rs.length, Subsingleton (Ext N M i) := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus]; rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] => simp at len
    | a :: rs' =>
      -- find a positive power of `a` lying in `Ann(N)`
      obtain ⟨k, hk⟩ := le_rad (mem a List.mem_cons_self)
      simp only [isRegular_cons_iff] at reg
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [List.length_cons, Nat.add_left_inj] at len
      -- prepare to apply induction hypothesis to `M/aM`
      match i with
      | 0 => -- vanishing of `Ext N M 0` follows from `aᵏ ∈ Ann(N)`
        have : Subsingleton (N ->ₗ[R] M) := subsingleton_linearMap_iff.mpr ⟨a ^ k, hk, reg.1.pow k⟩
        exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
      | i + 1 =>
        let g := (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N
          (add_zero (i + 1))))
        -- from the (covariant) long exact sequence given by `M.smulShortComplex a`
        -- we obtain scalar multiple by `a` on `Ext N M i` is injective
        have mono_g : Mono g := by
          apply (Ext.covariant_sequence_exact₁' N reg.1.smulShortComplex_shortExact i (i + 1)
            rfl).mono_g ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr ?_).eq_zero_of_src _)
          apply ih (ModuleCat.of R (QuotSMulTop a M)) _ rs' mem.2 reg.2 len i (by omega)
          exact (smul_top_quotSMulTop_ne_top_of_smul_top_ne_top mem.1 smul_lt.ne).lt_top
        let gk := AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N
          (add_zero (i + 1)))
        have mono_gk : Mono gk := by
          simp only [smulShortComplex_f_eq_smul_id, g, gk] at mono_g ⊢
exact (Ext.postcomp_smul_id_mono_iff (a ^ k) (i + 1)).mpr
            ((Ext.postcomp_smul_id_mono_iff a (i + 1)).mp mono_g).pow k
        -- scalar multiple by `aᵏ` on `Ext N M i` is zero since `aᵏ ∈ Ann(N)`, so `Ext N M i` vanish
        have zero_gk : gk = 0 := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator hk (i + 1)
        exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

/--
lemma `exists_isRegular_tfae` / 引理 `exists_isRegular_tfae`

English:
lemma exists_isRegular_tfae
  statement: [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n : Nat)
  proof: by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I 

中文:
引理 exists_isRegular_tfae
  结论: [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n : 自然数)
  证明: by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I 
-/
lemma exists_isRegular_tfae [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n : Nat)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    [forall N : ModuleCat.{v} R, Nontrivial N -> Module.Finite R N ->
      Module.support R N subseteq PrimeSpectrum.zeroLocus I -> forall i < n, Subsingleton (Ext N M i),
      forall i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      exists N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ forall i < n, Subsingleton (Ext N M i),
      exists rs : List R, rs.length = n ∧ (forall r in rs, r in I) ∧ RingTheory.Sequence.IsRegular M rs
      ].TFAE := by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq]; rw [Module.support_eq_zeroLocus]; rw [annihilator_quotient]
  tfae_have 1 -> 2 := fun h1 i hi => h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    inferInstance inferInstance suppQ.subset i hi
  tfae_have 2 -> 3 := fun h2 => ⟨(ModuleCat.of R (Shrink.{v} (R ⧸ I))),
    inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ, h2⟩
  tfae_have 3 -> 4 := fun ⟨N, _, _, h_supp, h_ext⟩ =>
    exists_isRegular_of_exists_subsingleton_ext I n M smul_lt N h_supp h_ext
  tfae_have 4 -> 1 := fun ⟨rs, len, mem, reg⟩ N Nntr Nfin Nsupp i hi =>
    subsingleton_ext_of_exists_isRegular I N Nsupp M smul_lt rs mem reg i (hi.trans_eq len.symm)
  tfae_finish

end ModuleCat
