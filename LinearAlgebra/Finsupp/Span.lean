/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finitely supported functions and spans

## Tags

function with finite support, module, linear algebra
-/

public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

@[simp]
/--
theorem `ker_lsingle` / 定理 `ker_lsingle`

English:
theorem ker_lsingle
  given: (a : α)
  statement: ker (lsingle a : M ->ₗ[R] α ->₀ M) = ⊥
  proof: ker_eq_bot_of_injective (single_injective a)

中文:
定理 ker_lsingle
  条件: (a : α)
  结论: ker (lsingle a : M ->ₗ[R] α ->₀ M) = ⊥
  证明: ker_eq_bot_of_injective (single_injective a)

Depends on / 依赖: ker_eq_bot_of_injective, single_injective
-/
theorem ker_lsingle (a : α) : ker (lsingle a : M ->ₗ[R] α ->₀ M) = ⊥ :=
  ker_eq_bot_of_injective (single_injective a)

/--
theorem `lsingle_range_le_ker_lapply` / 定理 `lsingle_range_le_ker_lapply`

English:
theorem lsingle_range_le_ker_lapply
  given: (s t : Set α) (h : Disjoint s t)
  proof: by
  refine iSup_le fun a₁ => iSup_le fun h₁ => range_le_iff_comap.2 ?_
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  intro b _ a₂ h₂
  have : a₂ != a₁ := fun eq => h.le_bot ⟨h₁, eq.symm ▸ h₂⟩
  exact single_eq_of_ne this

中文:
定理 lsingle_range_le_ker_lapply
  条件: (s t : 集合 α) (h : Disjoint s t)
  证明: by
  refine iSup_le fun a₁ => iSup_le fun h₁ => range_le_iff_comap.2 ?_
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  intro b _ a₂ h₂
  have : a₂ != a₁ := fun eq => h.le_bot ⟨h₁, eq.symm ▸ h₂⟩
  exact single_eq_of_ne this

Depends on / 依赖: SetLike, SetLike.le_def, comap_iInf, eq.symm, eq_top_iff, h.le_bot, iSup_le, ker_comp, le_bot, le_def, mem_iInf, mem_ker, range_le_iff_comap, single_eq_of_ne
-/
theorem lsingle_range_le_ker_lapply (s t : Set α) (h : Disjoint s t) :
    ⨆ a in s, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M) <=
      ⨅ a in t, ker (lapply a : (α ->₀ M) ->ₗ[R] M) := by
  refine iSup_le fun a₁ => iSup_le fun h₁ => range_le_iff_comap.2 ?_
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  intro b _ a₂ h₂
  have : a₂ != a₁ := fun eq => h.le_bot ⟨h₁, eq.symm ▸ h₂⟩
  exact single_eq_of_ne this

/--
theorem `iInf_ker_lapply_le_bot` / 定理 `iInf_ker_lapply_le_bot`

English:
theorem iInf_ker_lapply_le_bot
  statement: ⨅ a, ker (lapply a : (α ->₀ M) ->ₗ[R] M) <= ⊥
  proof: by
  simp only [SetLike.le_def, mem_iInf, mem_ker, mem_bot, lapply_apply]
  exact fun a h => Finsupp.ext h

中文:
定理 iInf_ker_lapply_le_bot
  结论: ⨅ a, ker (lapply a : (α ->₀ M) ->ₗ[R] M) <= ⊥
  证明: by
  simp only [SetLike.le_def, mem_iInf, mem_ker, mem_bot, lapply_apply]
  exact fun a h => Finsupp.ext h

Depends on / 依赖: Finsupp, Finsupp.ext, SetLike, SetLike.le_def, lapply_apply, le_def, mem_bot, mem_iInf, mem_ker
-/
theorem iInf_ker_lapply_le_bot : ⨅ a, ker (lapply a : (α ->₀ M) ->ₗ[R] M) <= ⊥ := by
  simp only [SetLike.le_def, mem_iInf, mem_ker, mem_bot, lapply_apply]
  exact fun a h => Finsupp.ext h

/--
theorem `iSup_lsingle_range` / 定理 `iSup_lsingle_range`

English:
theorem iSup_lsingle_range
  statement: ⨆ a, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M) = ⊤
  proof: by
refine eq_top_iff.2 SetLike.le_def.2 fun f _ => ?_
  rw [← sum_single f]
  exact sum_mem fun a _ => Submodule.mem_iSup_of_mem a ⟨_, rfl⟩

中文:
定理 iSup_lsingle_range
  结论: ⨆ a, 线性映射.range (lsingle a : M ->ₗ[R] α ->₀ M) = ⊤
  证明: by
refine eq_top_iff.2 SetLike.le_def.2 fun f _ => ?_
  rw [← sum_single f]
  exact sum_mem fun a _ => Submodule.mem_iSup_of_mem a ⟨_, rfl⟩

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.mem_iSup_of_mem, eq_top_iff, le_def, mem_iSup_of_mem, sum_mem, sum_single
-/
theorem iSup_lsingle_range : ⨆ a, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M) = ⊤ := by
refine eq_top_iff.2 SetLike.le_def.2 fun f _ => ?_
  rw [← sum_single f]
  exact sum_mem fun a _ => Submodule.mem_iSup_of_mem a ⟨_, rfl⟩

/--
theorem `disjoint_lsingle_lsingle` / 定理 `disjoint_lsingle_lsingle`

English:
theorem disjoint_lsingle_lsingle
  given: (s t : Set α) (hs : Disjoint s t)
  proof: by
  refine
    (Disjoint.mono
      (lsingle_range_le_ker_lapply s sᶜ disjoint_compl_right)
      (lsingle_range_le_ker_lapply t tᶜ disjoint_compl_right))
      ?_
  rw [disjoint_iff_inf_le]
  refine le_trans (le_iInf fun i => ?_) iInf_ker_lapply_le_bot
  classical
    by_cases his : i in s
    · b

中文:
定理 disjoint_lsingle_lsingle
  条件: (s t : 集合 α) (hs : Disjoint s t)
  证明: by
  refine
    (Disjoint.mono
      (lsingle_range_le_ker_lapply s sᶜ disjoint_compl_right)
      (lsingle_range_le_ker_lapply t tᶜ disjoint_compl_right))
      ?_
  rw [disjoint_iff_inf_le]
  refine le_trans (le_iInf fun i => ?_) iInf_ker_lapply_le_bot
  classical
    by_cases his : i in s
    · b

Depends on / 依赖: Disjoint, Disjoint.mono, classical, disjoint_compl_right, disjoint_iff_inf_le, hs.le_bot, iInf_ker_lapply_le_bot, iInf_le, iInf_le_of_le, inf_le_of_left_le, inf_le_of_right_le, le_bot, le_iInf, le_trans, lsingle_range_le_ker_lapply
-/
theorem disjoint_lsingle_lsingle (s t : Set α) (hs : Disjoint s t) :
    Disjoint (⨆ a in s, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M))
      (⨆ a in t, LinearMap.range (lsingle a : M ->ₗ[R] α ->₀ M)) := by
  refine
    (Disjoint.mono
      (lsingle_range_le_ker_lapply s sᶜ disjoint_compl_right)
      (lsingle_range_le_ker_lapply t tᶜ disjoint_compl_right))
      ?_
  rw [disjoint_iff_inf_le]
  refine le_trans (le_iInf fun i => ?_) iInf_ker_lapply_le_bot
  classical
    by_cases his : i in s
    · by_cases hit : i in t
      · exact (hs.le_bot ⟨his, hit⟩).elim
      exact inf_le_of_right_le (iInf_le_of_le i <| iInf_le _ hit)
    exact inf_le_of_left_le (iInf_le_of_le i <| iInf_le _ his)

/--
theorem `span_single_image` / 定理 `span_single_image`

English:
theorem span_single_image
  given: (s : Set M) (a : α)
  proof: by
  rw [← span_image]; rfl

中文:
定理 span_single_image
  条件: (s : 集合 M) (a : α)
  证明: by
  rw [← span_image]; rfl

Depends on / 依赖: span_image
-/
theorem span_single_image (s : Set M) (a : α) :
    Submodule.span R (single a '' s) = (Submodule.span R s).map (lsingle a : M ->ₗ[R] α ->₀ M) := by
  rw [← span_image]; rfl

/--
lemma `range_lmapDomain` / 引理 `range_lmapDomain`

English:
lemma range_lmapDomain
  given: {β : Type*} (u : α -> β)
  proof: by
  refine le_antisymm ?_ ?_
  · rintro x ⟨x, rfl⟩
    induction x using induction_linear with
    | single i s =>
        rw [lmapDomain_apply]; rw [mapDomain_single]; rw [← Finsupp.smul_single_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add 

中文:
引理 range_lmapDomain
  条件: {β : 类型} (u : α -> β)
  证明: by
  refine le_antisymm ?_ ?_
  · rintro x ⟨x, rfl⟩
    induction x using induction_linear with
    | single i s =>
        rw [lmapDomain_apply]; rw [mapDomain_single]; rw [← Finsupp.smul_single_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add 

Depends on / 依赖: Finsupp, Finsupp.single, Finsupp.smul_single_one, Set.range_subset_iff, Submodule, Submodule.add_mem, Submodule.smul_mem, Submodule.span_le, Submodule.subset_span, add_mem, induction_linear, le_antisymm, lmapDomain_apply, mapDomain_single, map_add, range_subset_iff, single, smul_mem, smul_single_one, span_le
-/
lemma range_lmapDomain {β : Type*} (u : α -> β) :
    LinearMap.range (lmapDomain R R u) = .span R (.range fun x => single (u x) 1) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨x, rfl⟩
    induction x using induction_linear with
    | single i s =>
        rw [lmapDomain_apply]; rw [mapDomain_single]; rw [← Finsupp.smul_single_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add f g hf hg =>
        rw [map_add]
        exact Submodule.add_mem _ hf hg
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact ⟨Finsupp.single i 1, by simp⟩

/--
lemma `span_single_eq_top` / 引理 `span_single_eq_top`

English:
lemma span_single_eq_top
  statement: span R {single i x | (i : α) (x : M)} = ⊤
  proof: by
  refine eq_top_iff'.mpr fun x => ?_
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem ..
  | add f g f_in g_in => exact add_mem f_in g_in
  | single a b => exact mem_span_of_mem ⟨a, b, rfl⟩

中文:
引理 span_single_eq_top
  结论: span R {single i x | (i : α) (x : M)} = ⊤
  证明: by
  refine eq_top_iff'.mpr fun x => ?_
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem ..
  | add f g f_in g_in => exact add_mem f_in g_in
  | single a b => exact mem_span_of_mem ⟨a, b, rfl⟩

Depends on / 依赖: Finsupp, Finsupp.induction_linear, Submodule, Submodule.zero_mem, add_mem, eq_top_iff, f_in, g_in, induction_linear, mem_span_of_mem, single, zero_mem
-/
lemma span_single_eq_top : span R {single i x | (i : α) (x : M)} = ⊤ := by
  refine eq_top_iff'.mpr fun x => ?_
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem ..
  | add f g f_in g_in => exact add_mem f_in g_in
  | single a b => exact mem_span_of_mem ⟨a, b, rfl⟩

end Finsupp

open Finsupp

namespace Submodule

section Semiring

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/--
theorem `exists_finset_of_mem_iSup` / 定理 `exists_finset_of_mem_iSup`

English:
theorem exists_finset_of_mem_iSup
  statement: {ι : Sort _} (p : ι -> Submodule R M) {m : M}
  proof: by
  have :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)
      (Submodule.singleton_span_isCompactElement m) p
  simp only [Submodule.span_singleton_le_iff_mem] at this
  exact this hm

中文:
定理 存在_finset_of_mem_iSup
  结论: {ι : 类型层 _} (p : ι -> 子模 R M) {m : M}
  证明: by
  have :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)
      (Submodule.singleton_span_isCompactElement m) p
  simp only [Submodule.span_singleton_le_iff_mem] at this
  exact this hm

Depends on / 依赖: CompleteLattice, CompleteLattice.IsCompactElement.exists_finset_of_le_iSup, IsCompactElement, Submodule, Submodule.singleton_span_isCompactElement, Submodule.span_singleton_le_iff_mem, exists_finset_of_le_iSup, singleton_span_isCompactElement, span_singleton_le_iff_mem
-/
theorem exists_finset_of_mem_iSup {ι : Sort _} (p : ι -> Submodule R M) {m : M}
    (hm : m in ⨆ i, p i) : exists s : Finset ι, m in ⨆ i in s, p i := by
  have :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)
      (Submodule.singleton_span_isCompactElement m) p
  simp only [Submodule.span_singleton_le_iff_mem] at this
  exact this hm

/--
theorem `mem_iSup_iff_exists_finset` / 定理 `mem_iSup_iff_exists_finset`

English:
theorem mem_iSup_iff_exists_finset
  given: {ι : Sort _} {p : ι -> Submodule R M} {m : M}
  proof: ⟨Submodule.exists_finset_of_mem_iSup p, fun ⟨_, hs⟩ =>
    iSup_mono (fun i => (iSup_const_le : _ <= p i)) hs⟩

中文:
定理 mem_iSup_iff_存在_finset
  条件: {ι : 类型层 _} {p : ι -> 子模 R M} {m : M}
  证明: ⟨Submodule.exists_finset_of_mem_iSup p, fun ⟨_, hs⟩ =>
    iSup_mono (fun i => (iSup_const_le : _ <= p i)) hs⟩

Depends on / 依赖: Submodule, Submodule.exists_finset_of_mem_iSup, exists_finset_of_mem_iSup, iSup_const_le, iSup_mono
-/
theorem mem_iSup_iff_exists_finset {ι : Sort _} {p : ι -> Submodule R M} {m : M} :
    (m in ⨆ i, p i) ↔ exists s : Finset ι, m in ⨆ i in s, p i :=
  ⟨Submodule.exists_finset_of_mem_iSup p, fun ⟨_, hs⟩ =>
    iSup_mono (fun i => (iSup_const_le : _ <= p i)) hs⟩

/--
theorem `mem_sSup_iff_exists_finset` / 定理 `mem_sSup_iff_exists_finset`

English:
theorem mem_sSup_iff_exists_finset
  given: {S : Set (Submodule R M)} {m : M}
  proof: by
  rw [sSup_eq_iSup]; rw [iSup_subtype']; rw [Submodule.mem_iSup_iff_exists_finset]
  refine ⟨fun ⟨s, hs⟩ => ⟨s.map (Function.Embedding.subtype (· in S)), ?_, ?_⟩,
          fun ⟨s, hsS, hs⟩ => ⟨s.preimage (↑) Subtype.coe_injective.injOn, ?_⟩⟩
  · simp
  · suffices m in ⨆ (i) (hi : i in S) (_ : ⟨i

中文:
定理 mem_sSup_iff_存在_finset
  条件: {S : 集合 (子模 R M)} {m : M}
  证明: by
  rw [sSup_eq_iSup]; rw [iSup_subtype']; rw [Submodule.mem_iSup_iff_exists_finset]
  refine ⟨fun ⟨s, hs⟩ => ⟨s.map (Function.Embedding.subtype (· in S)), ?_, ?_⟩,
          fun ⟨s, hsS, hs⟩ => ⟨s.preimage (↑) Subtype.coe_injective.injOn, ?_⟩⟩
  · simp
  · suffices m in ⨆ (i) (hi : i in S) (_ : ⟨i

Depends on / 依赖: Embedding, Finset, Finset.mem_preimage, Function, Function.Embedding.subtype, Submodule, Submodule.mem_iSup_iff_exists_finset, Subtype, Subtype.coe_injective.injOn, coe_injective, convert, iSup_and, iSup_subtype, mem_iSup_iff_exists_finset, mem_preimage, preimage, s.map, s.preimage, sSup_eq_iSup, subtype
-/
theorem mem_sSup_iff_exists_finset {S : Set (Submodule R M)} {m : M} :
    m in sSup S ↔ exists s : Finset (Submodule R M), ↑s subseteq S ∧ m in ⨆ i in s, i := by
  rw [sSup_eq_iSup]; rw [iSup_subtype']; rw [Submodule.mem_iSup_iff_exists_finset]
  refine ⟨fun ⟨s, hs⟩ => ⟨s.map (Function.Embedding.subtype (· in S)), ?_, ?_⟩,
          fun ⟨s, hsS, hs⟩ => ⟨s.preimage (↑) Subtype.coe_injective.injOn, ?_⟩⟩
  · simp
  · suffices m in ⨆ (i) (hi : i in S) (_ : ⟨i, hi⟩ in s), i by simpa
    rwa [iSup_subtype']
  · have : ⨆ (i) (_ : i in S ∧ i in s), i = ⨆ (i) (_ : i in s), i := by convert! rfl; grind
    simpa only [Finset.mem_preimage, iSup_subtype, iSup_and', this]

end Semiring

section CommSemiring

variable {R M N σ : Type*} [CommSemiring R] [AddCommMonoid M]
variable [AddCommMonoid N] [Module R M] [Module R N]

open scoped Pointwise in
/--
lemma `range_lsum_smul` / 引理 `range_lsum_smul`

English:
lemma range_lsum_smul
  given: (φ : M ->ₗ[R] N) (f : σ -> R)
  proof: by
  simp_rw [range_eq_map, ← span_single_eq_top, ← span_univ, map_span, set_smul_span]
  congr 1
  aesop (add simp Set.mem_smul)

中文:
引理 range_lsum_smul
  条件: (φ : M ->ₗ[R] N) (f : σ -> R)
  证明: by
  simp_rw [range_eq_map, ← span_single_eq_top, ← span_univ, map_span, set_smul_span]
  congr 1
  aesop (add simp Set.mem_smul)

Depends on / 依赖: Set.mem_smul, Set.range, map_span, mem_smul, range_eq_map, set_smul_span, simp_rw, span_single_eq_top, span_univ
-/
lemma range_lsum_smul (φ : M ->ₗ[R] N) (f : σ -> R) :
    (lsum (S := R) (f · • φ)).range = Set.range f • φ.range := by
  simp_rw [range_eq_map, ← span_single_eq_top, ← span_univ, map_span, set_smul_span]
  congr 1
  aesop (add simp Set.mem_smul)

open scoped Pointwise in
/--
theorem `image_smul_top_eq_range_lsum` / 定理 `image_smul_top_eq_range_lsum`

English:
theorem image_smul_top_eq_range_lsum
  given: (s : Set σ) (f : σ -> R)
  proof: by
  simpa [Set.range_comp] using (range_lsum_smul (.id (R := R) (M := M)) (f ∘ (↑) : s -> R)).symm

中文:
定理 image_smul_top_eq_range_lsum
  条件: (s : 集合 σ) (f : σ -> R)
  证明: by
  simpa [Set.range_comp] using (range_lsum_smul (.id (R := R) (M := M)) (f ∘ (↑) : s -> R)).symm

Depends on / 依赖: Set.range_comp, range_comp, range_lsum_smul
-/
theorem image_smul_top_eq_range_lsum (s : Set σ) (f : σ -> R) :
    (f '' s • ⊤ : Submodule R M) = (lsum (S := R) fun i : s => f i • .id).range := by
  simpa [Set.range_comp] using (range_lsum_smul (.id (R := R) (M := M)) (f ∘ (↑) : s -> R)).symm

open scoped Pointwise in
/--
theorem `smul_top_eq_range_lsum` / 定理 `smul_top_eq_range_lsum`

English:
theorem smul_top_eq_range_lsum
  given: (s : Set R)
  proof: by
  simpa using image_smul_top_eq_range_lsum (M := M) s id

中文:
定理 smul_top_eq_range_lsum
  条件: (s : 集合 R)
  证明: by
  simpa using image_smul_top_eq_range_lsum (M := M) s id

Depends on / 依赖: i.val, image_smul_top_eq_range_lsum
-/
theorem smul_top_eq_range_lsum (s : Set R) :
    (s • ⊤ : Submodule R M) = (lsum (S := R) fun i : s => i.val • .id).range := by
  simpa using image_smul_top_eq_range_lsum (M := M) s id

end CommSemiring

end Submodule
