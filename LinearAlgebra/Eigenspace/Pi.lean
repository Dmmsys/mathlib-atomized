/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Simultaneous eigenvectors and eigenvalues for families of endomorphisms

In finite dimensions, the theory of simultaneous eigenvalues for a family of linear endomorphisms
`i ↦ f i` enjoys similar properties to that of a single endomorphism, provided the family obeys a
compatibility condition. This condition is that the maximum generalised eigenspaces of each
endomorphism are invariant under the action of all members of the family. It is trivially satisfied
for commuting endomorphisms but there are important more general situations where it also holds
(e.g., representations of nilpotent Lie algebras).

## Main definitions / results
* `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`: the simultaneous generalised
  eigenspaces of a compatible family of endomorphisms are independent.
* `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`: in finite dimensions, the
  simultaneous generalised eigenspaces of a compatible family of endomorphisms span if the same
  is true of each map individually.

-/

public section

open Function Set

namespace Module.End

variable {ι R K M : Type*} [CommRing R] [Field K] [AddCommGroup M] [Module R M] [Module K M]
  (f : ι -> End R M)

/--
theorem `mem_iInf_maxGenEigenspace_iff` / 定理 `mem_iInf_maxGenEigenspace_iff`

English:
theorem mem_iInf_maxGenEigenspace_iff
  given: (χ : ι -> R) (m : M)
  proof: by
  simp

中文:
定理 mem_iInf_maxGenEigenspace_iff
  条件: (χ : ι -> R) (m : M)
  证明: by
  simp
-/
theorem mem_iInf_maxGenEigenspace_iff (χ : ι -> R) (m : M) :
    m in ⨅ i, (f i).maxGenEigenspace (χ i) ↔ forall j, exists k : Nat, ((f j - χ j • ↑1) ^ k) m = 0 := by
  simp

/--
lemma `_root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo` / 引理 `_root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`

English:
lemma _root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo
  statement: {μ : ι -> R}
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [inf_iInf, p.inf_genEigenspace _ (hfp _), Submodule.map_iInf _ p.injective_subtype]

中文:
引理 _root_.子模.inf_iInf_maxGenEigenspace_of_对任意_mapsTo
  结论: {μ : ι -> R}
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [inf_iInf, p.inf_genEigenspace _ (hfp _), Submodule.map_iInf _ p.injective_subtype]

Depends on / 依赖: Submodule, Submodule.map_iInf, iInf_of_isEmpty, inf_genEigenspace, inf_iInf, injective_subtype, isEmpty_or_nonempty, map_iInf, p.inf_genEigenspace, p.injective_subtype, simp_rw
-/
lemma _root_.Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo {μ : ι -> R}
    (p : Submodule R M) (hfp : forall i, MapsTo (f i) p p) :
    p ⊓ ⨅ i, (f i).maxGenEigenspace (μ i) =
      (⨅ i, maxGenEigenspace ((f i).restrict (hfp i)) (μ i)).map p.subtype := by
  cases isEmpty_or_nonempty ι
  · simp [iInf_of_isEmpty]
  · simp_rw [inf_iInf, p.inf_genEigenspace _ (hfp _), Submodule.map_iInf _ p.injective_subtype]

/--
lemma `iInf_maxGenEigenspace_restrict_map_subtype_eq` / 引理 `iInf_maxGenEigenspace_restrict_map_subtype_eq`

English:
lemma iInf_maxGenEigenspace_restrict_map_subtype_eq
  proof: (f i).maxGenEigenspace (μ i)
    letI q (j : ι) := maxGenEigenspace ((f j).restrict (h j)) (μ j)
    (⨅ j, q j).map p.subtype = ⨅ j, (f j).maxGenEigenspace (μ j) := by
  have : Nonempty ι := ⟨i⟩
  set p := (f i).maxGenEigenspace (μ i)
  have : ⨅ j, (f j).maxGenEigenspace (μ j) = p ⊓ ⨅ j, (f j).maxGe

中文:
引理 iInf_maxGenEigenspace_restrict_map_subtype_eq
  证明: (f i).maxGenEigenspace (μ i)
    letI q (j : ι) := maxGenEigenspace ((f j).restrict (h j)) (μ j)
    (⨅ j, q j).map p.subtype = ⨅ j, (f j).maxGenEigenspace (μ j) := by
  have : Nonempty ι := ⟨i⟩
  set p := (f i).maxGenEigenspace (μ i)
  have : ⨅ j, (f j).maxGenEigenspace (μ j) = p ⊓ ⨅ j, (f j).maxGe

Depends on / 依赖: maxGenEigenspace
-/
lemma iInf_maxGenEigenspace_restrict_map_subtype_eq
    {μ : ι -> R} (i : ι)
    (h : forall j, MapsTo (f j) ((f i).maxGenEigenspace (μ i)) ((f i).maxGenEigenspace (μ i))) :
    letI p := (f i).maxGenEigenspace (μ i)
    letI q (j : ι) := maxGenEigenspace ((f j).restrict (h j)) (μ j)
    (⨅ j, q j).map p.subtype = ⨅ j, (f j).maxGenEigenspace (μ j) := by
  have : Nonempty ι := ⟨i⟩
  set p := (f i).maxGenEigenspace (μ i)
  have : ⨅ j, (f j).maxGenEigenspace (μ j) = p ⊓ ⨅ j, (f j).maxGenEigenspace (μ j) := by
    refine le_antisymm ?_ inf_le_right
    simpa only [le_inf_iff, le_refl, and_true] using iInf_le _ _
  rw [Submodule.map_iInf _ p.injective_subtype]; rw [this]; rw [Submodule.inf_iInf]
  conv_rhs =>
    enter [1]
    ext
    rw [p.inf_genEigenspace (f _) (h _)]

variable [IsDomain R] [IsTorsionFree R M]

/--
lemma `disjoint_iInf_maxGenEigenspace` / 引理 `disjoint_iInf_maxGenEigenspace`

English:
lemma disjoint_iInf_maxGenEigenspace
  given: {χ₁ χ₂ : ι -> R} (h : χ₁ != χ₂)
  proof: by
  obtain ⟨j, hj⟩ : exists j, χ₁ j != χ₂ j := Function.ne_iff.mp h
  exact (End.disjoint_genEigenspace (f j) hj ⊤ ⊤).mono (iInf_le _ j) (iInf_le _ j)

中文:
引理 disjoint_iInf_maxGenEigenspace
  条件: {χ₁ χ₂ : ι -> R} (h : χ₁ != χ₂)
  证明: by
  obtain ⟨j, hj⟩ : exists j, χ₁ j != χ₂ j := Function.ne_iff.mp h
  exact (End.disjoint_genEigenspace (f j) hj ⊤ ⊤).mono (iInf_le _ j) (iInf_le _ j)

Depends on / 依赖: End.disjoint_genEigenspace, Function, Function.ne_iff.mp, disjoint_genEigenspace, iInf_le, ne_iff
-/
lemma disjoint_iInf_maxGenEigenspace {χ₁ χ₂ : ι -> R} (h : χ₁ != χ₂) :
    Disjoint (⨅ i, (f i).maxGenEigenspace (χ₁ i)) (⨅ i, (f i).maxGenEigenspace (χ₂ i)) := by
  obtain ⟨j, hj⟩ : exists j, χ₁ j != χ₂ j := Function.ne_iff.mp h
  exact (End.disjoint_genEigenspace (f j) hj ⊤ ⊤).mono (iInf_le _ j) (iInf_le _ j)

/--
lemma `injOn_iInf_maxGenEigenspace` / 引理 `injOn_iInf_maxGenEigenspace`

English:
lemma injOn_iInf_maxGenEigenspace
  proof: by
  rintro χ₁ _ χ₂
    hχ₂ (hχ₁₂ : ⨅ i, (f i).maxGenEigenspace (χ₁ i) = ⨅ i, (f i).maxGenEigenspace (χ₂ i))
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_iInf_maxGenEigenspace f hχ₂

中文:
引理 injOn_iInf_maxGenEigenspace
  证明: by
  rintro χ₁ _ χ₂
    hχ₂ (hχ₁₂ : ⨅ i, (f i).maxGenEigenspace (χ₁ i) = ⨅ i, (f i).maxGenEigenspace (χ₂ i))
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_iInf_maxGenEigenspace f hχ₂

Depends on / 依赖: contrapose, disjoint_iInf_maxGenEigenspace, maxGenEigenspace
-/
lemma injOn_iInf_maxGenEigenspace :
    InjOn (fun χ : ι -> R => ⨅ i, (f i).maxGenEigenspace (χ i))
      {χ | ⨅ i, (f i).maxGenEigenspace (χ i) != ⊥} := by
  rintro χ₁ _ χ₂
    hχ₂ (hχ₁₂ : ⨅ i, (f i).maxGenEigenspace (χ₁ i) = ⨅ i, (f i).maxGenEigenspace (χ₂ i))
  contrapose! hχ₂
  simpa [hχ₁₂] using disjoint_iInf_maxGenEigenspace f hχ₂

/--
lemma `independent_iInf_maxGenEigenspace_of_forall_mapsTo` / 引理 `independent_iInf_maxGenEigenspace_of_forall_mapsTo`

English:
lemma independent_iInf_maxGenEigenspace_of_forall_mapsTo
  proof: by
  replace h (l : ι) (χ : ι -> R) :
      MapsTo (f l) (⨅ i, (f i).maxGenEigenspace (χ i)) (⨅ i, (f i).maxGenEigenspace (χ i)) := by
    intro x hx
    simp only [iInf_eq_iInter, mem_iInter, SetLike.mem_coe] at hx ⊢
    exact fun i => h l i (χ i) (hx i)
  classical
  suffices forall χ (s : Finset 

中文:
引理 independent_iInf_maxGenEigenspace_of_对任意_mapsTo
  证明: by
  replace h (l : ι) (χ : ι -> R) :
      MapsTo (f l) (⨅ i, (f i).maxGenEigenspace (χ i)) (⨅ i, (f i).maxGenEigenspace (χ i)) := by
    intro x hx
    simp only [iInf_eq_iInter, mem_iInter, SetLike.mem_coe] at hx ⊢
    exact fun i => h l i (χ i) (hx i)
  classical
  suffices forall χ (s : Finset 

Depends on / 依赖: Disjoint, Finset, Finset.supIndep_iff_disjoint_erase, MapsTo, SetLike, SetLike.mem_coe, classical, iInf_eq_iInter, iSupIndep_iff_supIndep, maxGenEigenspace, mem_coe, mem_iInter, replace, s.sup, supIndep_iff_disjoint_erase
-/
lemma independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (h : forall i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ)) :
    iSupIndep fun χ : ι -> R => ⨅ i, (f i).maxGenEigenspace (χ i) := by
  replace h (l : ι) (χ : ι -> R) :
      MapsTo (f l) (⨅ i, (f i).maxGenEigenspace (χ i)) (⨅ i, (f i).maxGenEigenspace (χ i)) := by
    intro x hx
    simp only [iInf_eq_iInter, mem_iInter, SetLike.mem_coe] at hx ⊢
    exact fun i => h l i (χ i) (hx i)
  classical
  suffices forall χ (s : Finset (ι -> R)) (_ : χ ∉ s),
      Disjoint (⨅ i, (f i).maxGenEigenspace (χ i))
        (s.sup fun (χ : ι -> R) => ⨅ i, (f i).maxGenEigenspace (χ i)) by
    simpa only [iSupIndep_iff_supIndep,
      Finset.supIndep_iff_disjoint_erase] using! fun s χ _ => this _ _ (s.notMem_erase χ)
  intro χ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert χ₂ s _n ih =>
  intro hχ₁₂
  obtain ⟨hχ₁₂ : χ₁ != χ₂, hχ₁ : χ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hχ₁₂
  specialize ih hχ₁
  rw [Finset.sup_insert]; rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x in ⨅ i, (f i).maxGenEigenspace (χ₂ i) by
    rw [← Submodule.mem_bot (R := R)]; rw [← (disjoint_iInf_maxGenEigenspace f hχ₁₂).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  suffices forall l, exists (k : Nat),
      ((f l - algebraMap R (Module.End R M) (χ₂ l)) ^ k) (y + z) in
      (⨅ i, (f i).maxGenEigenspace (χ₁ i)) ⊓
        Finset.sup s fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) by
    simpa [ih.eq_bot, Submodule.mem_bot] using! this
  intro l
  let g : Module.End R M := f l - algebraMap R (Module.End R M) (χ₂ l)
  obtain ⟨k, hk : (g ^ k) y = 0⟩ := (mem_iInf_maxGenEigenspace_iff _ _ _).mp hy l
  have aux (f : End R M) (φ : R) (k : Nat) (p : Submodule R M) (hp : MapsTo f p p) :
      MapsTo ((f - algebraMap R (Module.End R M) φ) ^ k) p p := by
    rw [Module.End.coe_pow]
    exact MapsTo.iterate (fun m hm => p.sub_mem (hp hm) (p.smul_mem _ hm)) k
  refine ⟨k, Submodule.mem_inf.mp ⟨?_, ?_⟩⟩
  · refine aux (f l) (χ₂ l) k (⨅ i, (f i).maxGenEigenspace (χ₁ i)) ?_ hx
    simp only [Submodule.coe_iInf]
    exact h l χ₁
  · rw [map_add, hk, zero_add]
    suffices (s.sup fun χ => (⨅ i, (f i).maxGenEigenspace (χ i))).map (g ^ k) <=
        s.sup fun χ => (⨅ i, (f i).maxGenEigenspace (χ i)) from
      this (Submodule.mem_map_of_mem hz)
    simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := ι -> R), Submodule.map_iSup (ι := _ in s)]
    refine iSup₂_mono fun χ _ => ?_
    rintro - ⟨u, hu, rfl⟩
    refine aux (f l) (χ₂ l) k (⨅ i, (f i).maxGenEigenspace (χ i)) ?_ hu
    simp only [Submodule.coe_iInf]
    exact h l χ

/--
lemma `iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo` / 引理 `iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`

English:
lemma iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo
  statement: [FiniteDimensional K M]
  proof: by
  generalize h_dim : finrank K M = n
  induction n using Nat.strongRecOn generalizing M with | ind n ih => ?_
  obtain this | ⟨i : ι, hy : ¬ exists φ, (f i).maxGenEigenspace φ = ⊤⟩ :=
    forall_or_exists_not (fun j : ι => exists φ : K, (f j).maxGenEigenspace φ = ⊤)
  · choose χ hχ using this
   

中文:
引理 iSup_iInf_maxGenEigenspace_eq_top_of_对任意_mapsTo
  结论: [有限维 K M]
  证明: by
  generalize h_dim : finrank K M = n
  induction n using Nat.strongRecOn generalizing M with | ind n ih => ?_
  obtain this | ⟨i : ι, hy : ¬ exists φ, (f i).maxGenEigenspace φ = ⊤⟩ :=
    forall_or_exists_not (fun j : ι => exists φ : K, (f j).maxGenEigenspace φ = ⊤)
  · choose χ hχ using this
   

Depends on / 依赖: Nat.strongRecOn, eq_top_iff, finrank, forall_or_exists_not, generalize, generalizing, h_dim, le_iSup, le_trans, maxGenEigenspace, replace, simp_rw, strongRecOn
-/
lemma iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo [FiniteDimensional K M]
    (f : ι -> End K M)
    (h : forall i j φ, MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ))
    (h' : forall i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι -> K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  generalize h_dim : finrank K M = n
  induction n using Nat.strongRecOn generalizing M with | ind n ih => ?_
  obtain this | ⟨i : ι, hy : ¬ exists φ, (f i).maxGenEigenspace φ = ⊤⟩ :=
    forall_or_exists_not (fun j : ι => exists φ : K, (f j).maxGenEigenspace φ = ⊤)
  · choose χ hχ using this
    replace hχ : ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by simpa
    simp_rw [eq_top_iff] at hχ ⊢
exact le_trans hχ le_iSup (fun χ : ι -> K => ⨅ i, (f i).maxGenEigenspace (χ i)) χ
  · replace hy : forall φ, finrank K ((f i).maxGenEigenspace φ) < n := fun φ => by
      simp_rw [not_exists, ← lt_top_iff_ne_top] at hy; exact h_dim ▸ Submodule.finrank_lt (hy φ).ne
    have hi (j : ι) (φ : K) :
        MapsTo (f j) ((f i).maxGenEigenspace φ) ((f i).maxGenEigenspace φ) := by
      exact h j i φ
    replace ih (φ : K) :
        ⨆ χ : ι -> K, ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      apply ih _ (hy φ)
      · intro j k μ
        exact mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo (f j) (f k) _ _ (h j k μ)
      · exact fun j => Module.End.genEigenspace_restrict_eq_top _ (h' j)
      · rfl
    replace ih (φ : K) :
        ⨆ (χ : ι -> K) (_ : χ i = φ), ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊤ := by
      suffices forall χ : ι -> K, χ i != φ -> ⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j) = ⊥ by
        specialize ih φ; rw [iSup_split, biSup_congr this] at ih; simpa using ih
      intro χ hχ
      rw [eq_bot_iff]; rw [← ((f i).maxGenEigenspace φ).ker_subtype]; rw [LinearMap.ker]; rw [← Submodule.map_le_iff_le_comap]; rw [← Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo]; rw [← disjoint_iff_inf_le]
      exact ((f i).disjoint_genEigenspace hχ.symm _ _).mono_right (iInf_le _ i)
    replace ih (φ : K) :
        ⨆ (χ : ι -> K) (_ : χ i = φ), ⨅ j, maxGenEigenspace (f j) (χ j) =
        maxGenEigenspace (f i) φ := by
      have (χ : ι -> K) (hχ : χ i = φ) : ⨅ j, maxGenEigenspace (f j) (χ j) =
          (⨅ j, maxGenEigenspace ((f j).restrict (hi j φ)) (χ j)).map
            ((f i).maxGenEigenspace φ).subtype := by
        rw [← hχ]; rw [iInf_maxGenEigenspace_restrict_map_subtype_eq]
      simp_rw [biSup_congr this, ← Submodule.map_iSup, ih, Submodule.map_top,
        Submodule.range_subtype]
    simpa only [← ih, iSup_comm (ι := K), iSup_iSup_eq_right] using h' i

/--
theorem `iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute` / 定理 `iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`

English:
theorem iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  proof: by
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
    (fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm ?_) h'
  rcases eq_or_ne j i with rfl | hij <;> tauto

中文:
定理 iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  证明: by
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
    (fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm ?_) h'
  rcases eq_or_ne j i with rfl | hij <;> tauto

Depends on / 依赖: Module, Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo, Module.End.mapsTo_maxGenEigenspace_of_comm, eq_or_ne, iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo, mapsTo_maxGenEigenspace_of_comm
-/
theorem iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    [FiniteDimensional K M] (f : ι -> Module.End K M) (h : Pairwise fun i j => Commute (f i) (f j))
    (h' : forall i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤) :
    ⨆ χ : ι -> K, ⨅ i, (f i).maxGenEigenspace (χ i) = ⊤ := by
  refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo _
    (fun i j => Module.End.mapsTo_maxGenEigenspace_of_comm ?_) h'
  rcases eq_or_ne j i with rfl | hij <;> tauto

end Module.End
