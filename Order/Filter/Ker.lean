/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Filter.Map

/-!
# Kernel of a filter

In this file we define the *kernel* `Filter.ker f` of a filter `f`
to be the intersection of all its sets.

We also prove that `Filter.principal` and `Filter.ker` form a Galois coinsertion
and prove other basic theorems about `Filter.ker`.
-/

@[expose] public section

open Function Set

namespace Filter

variable {ι : Sort*} {α β : Type*} {f g : Filter α} {s : Set α} {a : α}

/--
lemma `ker_def` / 引理 `ker_def`

English:
lemma ker_def
  given: (f : Filter α)
  statement: f.ker = ⋂ s in f, s
  proof: sInter_eq_biInter

中文:
引理 ker_def
  条件: (f : Filter α)
  结论: f.ker = ⋂ s in f, s
  证明: sInter_eq_biInter

Depends on / 依赖: sInter_eq_biInter
-/
lemma ker_def (f : Filter α) : f.ker = ⋂ s in f, s := sInter_eq_biInter

/--
lemma `mem_ker` / 引理 `mem_ker`

English:
lemma mem_ker
  statement: a in f.ker ↔ forall s in f, a in s
  proof: mem_sInter

中文:
引理 mem_ker
  结论: a in f.ker ↔ 对任意 s in f, a in s
  证明: mem_sInter
-/
@[simp] lemma mem_ker : a in f.ker ↔ forall s in f, a in s := mem_sInter
/--
lemma `subset_ker` / 引理 `subset_ker`

English:
lemma subset_ker
  statement: s subseteq f.ker ↔ forall t in f, s subseteq t
  proof: subset_sInter_iff

中文:
引理 subset_ker
  结论: s subseteq f.ker ↔ 对任意 t in f, s subseteq t
  证明: subset_sInter_iff
-/
@[simp] lemma subset_ker : s subseteq f.ker ↔ forall t in f, s subseteq t := subset_sInter_iff

/--
Definition of `giPrincipalKer` / `giPrincipalKer` 的定义

English:
definition giPrincipalKer
  signature: : GaloisCoinsertion (𝓟 : Set α -> Filter α) ker
  body: GaloisConnection.toGaloisCoinsertion (fun s f => by simp [principal_le_iff]) by
    simp only [subset_def, mem_ker, mem_principal]; aesop

@[deprecated (since := "2026-07-18")]
alias gi_principal_ker := giPrincipalKer

中文:
定义 giPrincipalKer
  签名: : GaloisCoinsertion (𝓟 : Set α -> Filter α) ker
  定义体: GaloisConnection.toGaloisCoinsertion (fun s f => by simp [principal_le_iff]) by
    simp only [subset_def, mem_ker, mem_principal]; aesop

@[deprecated (since := "2026-07-18")]
alias gi_principal_ker := giPrincipalKer

Depends on / 依赖: GaloisConnection, GaloisConnection.toGaloisCoinsertion, mem_ker, mem_principal, principal_le_iff, subset_def, toGaloisCoinsertion
-/
def giPrincipalKer : GaloisCoinsertion (𝓟 : Set α -> Filter α) ker :=
GaloisConnection.toGaloisCoinsertion (fun s f => by simp [principal_le_iff]) by
    simp only [subset_def, mem_ker, mem_principal]; aesop

@[deprecated (since := "2026-07-18")]
alias gi_principal_ker := giPrincipalKer

/--
lemma `ker_mono` / 引理 `ker_mono`

English:
lemma ker_mono
  statement: Monotone (ker : Filter α -> Set α)
  proof: giPrincipalKer.gc.monotone_u

中文:
引理 ker_mono
  结论: Monotone (ker : Filter α -> Set α)
  证明: giPrincipalKer.gc.monotone_u

Depends on / 依赖: giPrincipalKer, giPrincipalKer.gc.monotone_u, monotone_u
-/
lemma ker_mono : Monotone (ker : Filter α -> Set α) := giPrincipalKer.gc.monotone_u
/--
lemma `ker_surjective` / 引理 `ker_surjective`

English:
lemma ker_surjective
  statement: Surjective (ker : Filter α -> Set α)
  proof: giPrincipalKer.u_surjective

中文:
引理 ker_surjective
  结论: Surjective (ker : Filter α -> Set α)
  证明: giPrincipalKer.u_surjective

Depends on / 依赖: giPrincipalKer, giPrincipalKer.u_surjective, u_surjective
-/
lemma ker_surjective : Surjective (ker : Filter α -> Set α) := giPrincipalKer.u_surjective

/--
lemma `ker_bot` / 引理 `ker_bot`

English:
lemma ker_bot
  statement: ker (⊥ : Filter α) = ∅
  proof: sInter_eq_empty_iff.2 fun _ => ⟨∅, trivial, id⟩

中文:
引理 ker_bot
  结论: ker (⊥ : Filter α) = ∅
  证明: sInter_eq_empty_iff.2 fun _ => ⟨∅, trivial, id⟩
-/
@[simp] lemma ker_bot : ker (⊥ : Filter α) = ∅ := sInter_eq_empty_iff.2 fun _ => ⟨∅, trivial, id⟩
/--
lemma `ker_top` / 引理 `ker_top`

English:
lemma ker_top
  statement: ker (⊤ : Filter α) = univ
  proof: giPrincipalKer.gc.u_top

中文:
引理 ker_top
  结论: ker (⊤ : Filter α) = univ
  证明: giPrincipalKer.gc.u_top
-/
@[simp] lemma ker_top : ker (⊤ : Filter α) = univ := giPrincipalKer.gc.u_top
/--
lemma `ker_eq_univ` / 引理 `ker_eq_univ`

English:
lemma ker_eq_univ
  statement: ker f = univ ↔ f = ⊤
  proof: giPrincipalKer.gc.u_eq_top.trans by simp

中文:
引理 ker_eq_univ
  结论: ker f = univ ↔ f = ⊤
  证明: giPrincipalKer.gc.u_eq_top.trans by simp
-/
@[simp] lemma ker_eq_univ : ker f = univ ↔ f = ⊤ := giPrincipalKer.gc.u_eq_top.trans by simp
/--
lemma `ker_inf` / 引理 `ker_inf`

English:
lemma ker_inf
  given: (f g : Filter α)
  statement: ker (f ⊓ g) = ker f inter ker g
  proof: giPrincipalKer.gc.u_inf

中文:
引理 ker_inf
  条件: (f g : Filter α)
  结论: ker (f ⊓ g) = ker f inter ker g
  证明: giPrincipalKer.gc.u_inf
-/
@[simp] lemma ker_inf (f g : Filter α) : ker (f ⊓ g) = ker f inter ker g := giPrincipalKer.gc.u_inf
/--
lemma `ker_iInf` / 引理 `ker_iInf`

English:
lemma ker_iInf
  given: (f : ι -> Filter α)
  statement: ker (⨅ i, f i) = ⋂ i, ker (f i)
  proof: giPrincipalKer.gc.u_iInf

中文:
引理 ker_iInf
  条件: (f : ι -> Filter α)
  结论: ker (⨅ i, f i) = ⋂ i, ker (f i)
  证明: giPrincipalKer.gc.u_iInf
-/
@[simp] lemma ker_iInf (f : ι -> Filter α) : ker (⨅ i, f i) = ⋂ i, ker (f i) :=
  giPrincipalKer.gc.u_iInf
/--
lemma `ker_sInf` / 引理 `ker_sInf`

English:
lemma ker_sInf
  given: (S : Set (Filter α))
  statement: ker (sInf S) = ⋂ f in S, ker f
  proof: giPrincipalKer.gc.u_sInf

中文:
引理 ker_sInf
  条件: (S : Set (Filter α))
  结论: ker (sInf S) = ⋂ f in S, ker f
  证明: giPrincipalKer.gc.u_sInf
-/
@[simp] lemma ker_sInf (S : Set (Filter α)) : ker (sInf S) = ⋂ f in S, ker f :=
  giPrincipalKer.gc.u_sInf
/--
lemma `ker_principal` / 引理 `ker_principal`

English:
lemma ker_principal
  given: (s : Set α)
  statement: ker (𝓟 s) = s
  proof: giPrincipalKer.u_l_eq _

中文:
引理 ker_principal
  条件: (s : Set α)
  结论: ker (𝓟 s) = s
  证明: giPrincipalKer.u_l_eq _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraicIndependent_empty_type_iff, algebraicIndependent_empty_type_iff.mpr
-/
@[simp] lemma ker_principal (s : Set α) : ker (𝓟 s) = s := giPrincipalKer.u_l_eq _

/--
lemma `ker_pure` / 引理 `ker_pure`

English:
lemma ker_pure
  given: (a : α)
  statement: ker (pure a) = {a}
  proof: by rw [← principal_singleton, ker_principal]

中文:
引理 ker_pure
  条件: (a : α)
  结论: ker (pure a) = {a}
  证明: by rw [← principal_singleton, ker_principal]
-/
@[simp] lemma ker_pure (a : α) : ker (pure a) = {a} := by rw [← principal_singleton, ker_principal]

/--
lemma `ker_comap` / 引理 `ker_comap`

English:
lemma ker_comap
  given: (m : α -> β) (f : Filter β)
  statement: ker (comap m f) = m ⁻¹' ker f
  proof: by
  ext a
  simp only [mem_ker, mem_comap, forall_exists_index, and_imp, @forall_comm (Set α), mem_preimage]
  exact forall₂_congr fun s _ => ⟨fun h => h _ Subset.rfl, fun ha t ht => ht ha⟩

@[simp]

中文:
引理 ker_comap
  条件: (m : α -> β) (f : Filter β)
  结论: ker (comap m f) = m ⁻¹' ker f
  证明: by
  ext a
  simp only [mem_ker, mem_comap, forall_exists_index, and_imp, @forall_comm (Set α), mem_preimage]
  exact forall₂_congr fun s _ => ⟨fun h => h _ Subset.rfl, fun ha t ht => ht ha⟩

@[simp]
-/
@[simp] lemma ker_comap (m : α -> β) (f : Filter β) : ker (comap m f) = m ⁻¹' ker f := by
  ext a
  simp only [mem_ker, mem_comap, forall_exists_index, and_imp, @forall_comm (Set α), mem_preimage]
  exact forall₂_congr fun s _ => ⟨fun h => h _ Subset.rfl, fun ha t ht => ht ha⟩

@[simp]
/--
theorem `ker_iSup` / 定理 `ker_iSup`

English:
theorem ker_iSup
  given: (f : ι -> Filter α)
  statement: ker (⨆ i, f i) = ⋃ i, ker (f i)
  proof: by
  refine subset_antisymm (fun x hx => ?_) ker_mono.le_map_iSup
  simp only [mem_iUnion, mem_ker] at hx ⊢
  contrapose! hx
  choose s hsf hxs using hx
  refine ⟨⋃ i, s i, ?_, by simpa⟩
  exact mem_iSup.2 fun i => mem_of_superset (hsf i) (subset_iUnion s i)

@[simp]

中文:
定理 ker_iSup
  条件: (f : ι -> Filter α)
  结论: ker (⨆ i, f i) = ⋃ i, ker (f i)
  证明: by
  refine subset_antisymm (fun x hx => ?_) ker_mono.le_map_iSup
  simp only [mem_iUnion, mem_ker] at hx ⊢
  contrapose! hx
  choose s hsf hxs using hx
  refine ⟨⋃ i, s i, ?_, by simpa⟩
  exact mem_iSup.2 fun i => mem_of_superset (hsf i) (subset_iUnion s i)

@[simp]

Depends on / 依赖: contrapose, ker_mono, ker_mono.le_map_iSup, le_map_iSup, mem_iSup, mem_iUnion, mem_ker, mem_of_superset, subset_antisymm, subset_iUnion
-/
theorem ker_iSup (f : ι -> Filter α) : ker (⨆ i, f i) = ⋃ i, ker (f i) := by
  refine subset_antisymm (fun x hx => ?_) ker_mono.le_map_iSup
  simp only [mem_iUnion, mem_ker] at hx ⊢
  contrapose! hx
  choose s hsf hxs using hx
  refine ⟨⋃ i, s i, ?_, by simpa⟩
  exact mem_iSup.2 fun i => mem_of_superset (hsf i) (subset_iUnion s i)

@[simp]
/--
theorem `ker_sSup` / 定理 `ker_sSup`

English:
theorem ker_sSup
  given: (S : Set (Filter α))
  statement: ker (sSup S) = ⋃ f in S, ker f
  proof: by
  simp [sSup_eq_iSup]

@[simp]

中文:
定理 ker_sSup
  条件: (S : Set (Filter α))
  结论: ker (sSup S) = ⋃ f in S, ker f
  证明: by
  simp [sSup_eq_iSup]

@[simp]

Depends on / 依赖: sSup_eq_iSup
-/
theorem ker_sSup (S : Set (Filter α)) : ker (sSup S) = ⋃ f in S, ker f := by
  simp [sSup_eq_iSup]

@[simp]
/--
theorem `ker_sup` / 定理 `ker_sup`

English:
theorem ker_sup
  given: (f g : Filter α)
  statement: ker (f ⊔ g) = ker f union ker g
  proof: by
  rw [← sSup_pair]; rw [ker_sSup]; rw [biUnion_pair]

@[simp]

中文:
定理 ker_sup
  条件: (f g : Filter α)
  结论: ker (f ⊔ g) = ker f union ker g
  证明: by
  rw [← sSup_pair]; rw [ker_sSup]; rw [biUnion_pair]

@[simp]

Depends on / 依赖: biUnion_pair, ker_sSup, sSup_pair
-/
theorem ker_sup (f g : Filter α) : ker (f ⊔ g) = ker f union ker g := by
  rw [← sSup_pair]; rw [ker_sSup]; rw [biUnion_pair]

@[simp]
/--
lemma `ker_prod` / 引理 `ker_prod`

English:
lemma ker_prod
  given: (f : Filter α) (g : Filter β)
  statement: ker (f ×ˢ g) = ker f ×ˢ ker g
  proof: by
  simp [Set.prod_eq, Filter.prod_eq_inf]

@[simp]

中文:
引理 ker_prod
  条件: (f : Filter α) (g : Filter β)
  结论: ker (f ×ˢ g) = ker f ×ˢ ker g
  证明: by
  simp [Set.prod_eq, Filter.prod_eq_inf]

@[simp]

Depends on / 依赖: Filter, Filter.prod_eq_inf, Set.prod_eq, prod_eq, prod_eq_inf
-/
lemma ker_prod (f : Filter α) (g : Filter β) : ker (f ×ˢ g) = ker f ×ˢ ker g := by
  simp [Set.prod_eq, Filter.prod_eq_inf]

@[simp]
/--
lemma `ker_pi` / 引理 `ker_pi`

English:
lemma ker_pi
  given: {ι : Type*} {α : ι -> Type*} (f : (i : ι) -> Filter (α i))
  proof: by
  simp [Set.pi_def, Filter.pi]

中文:
引理 ker_pi
  条件: {ι : 类型} {α : ι -> 类型} (f : (i : ι) -> Filter (α i))
  证明: by
  simp [Set.pi_def, Filter.pi]

Depends on / 依赖: Filter, Filter.pi, Set.pi_def, pi_def
-/
lemma ker_pi {ι : Type*} {α : ι -> Type*} (f : (i : ι) -> Filter (α i)) :
    ker (Filter.pi f) = univ.pi (fun i => ker (f i)) := by
  simp [Set.pi_def, Filter.pi]

end Filter
