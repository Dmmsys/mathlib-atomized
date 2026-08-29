/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Sets.Compacts

/-!
# Base changes among different families of neighbourhoods

This file builds base changes for `.compactsInside`, `openNhds`.

It also contains the evidences that `openRcNhds_to_openNhds`and
 `openRcNhds_to_compactNhds` are initials functors.

-/

@[expose] public section

namespace TopologicalSpace

open Set CategoryTheory Limits

variable {α : Type*} [TopologicalSpace α]

namespace Opens

/--
Definition of `baseChangeCompactsInside` / `baseChangeCompactsInside` 的定义

English:
definition baseChangeCompactsInside
  signature: {U V : Opens α} (h : U ⟶ V)
  body: fun ⟨K, hK⟩ => ⟨K, fun _ hx => Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

中文:
定义 baseChangeCompactsInside
  签名: {U V : Opens α} (h : U ⟶ V)
  定义体: fun ⟨K, hK⟩ => ⟨K, fun _ hx => Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

Depends on / 依赖: Set.mem_of_subset_of_mem, leOfHom, mem_of_subset_of_mem
-/
def baseChangeCompactsInside {U V : Opens α} (h : U ⟶ V) : U.compactsInside -> V.compactsInside :=
  fun ⟨K, hK⟩ => ⟨K, fun _ hx => Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

/--
lemma `baseChangeCompactsInside_mono` / 引理 `baseChangeCompactsInside_mono`

English:
lemma baseChangeCompactsInside_mono
  given: {U V : Opens α} (h : U ⟶ V)
  proof: fun _ _ hKL _ hx => SetLike.mem_coe.mpr (hKL hx)

@[simp]

中文:
引理 baseChangeCompactsInside_mono
  条件: {U V : Opens α} (h : U ⟶ V)
  证明: fun _ _ hKL _ hx => SetLike.mem_coe.mpr (hKL hx)

@[simp]

Depends on / 依赖: SetLike, SetLike.mem_coe.mpr, mem_coe
-/
lemma baseChangeCompactsInside_mono {U V : Opens α} (h : U ⟶ V) :
Monotone baseChangeCompactsInside h :=
  fun _ _ hKL _ hx => SetLike.mem_coe.mpr (hKL hx)

@[simp]
/--
lemma `baseChangeCompactsInside_comp` / 引理 `baseChangeCompactsInside_comp`

English:
lemma baseChangeCompactsInside_comp
  statement: {U V W : Opens α} (h : U ⟶ V) (k : V ⟶ W)
  proof: by rfl

@[simp]

中文:
引理 baseChangeCompactsInside_comp
  结论: {U V W : Opens α} (h : U ⟶ V) (k : V ⟶ W)
  证明: by rfl

@[simp]
-/
lemma baseChangeCompactsInside_comp {U V W : Opens α} (h : U ⟶ V) (k : V ⟶ W)
    (K : U.compactsInside) :
    baseChangeCompactsInside (h ≫ k) K = baseChangeCompactsInside k (baseChangeCompactsInside h K)
  := by rfl

@[simp]
/--
lemma `baseChangeOpenNhds_id` / 引理 `baseChangeOpenNhds_id`

English:
lemma baseChangeOpenNhds_id
  given: {U : Opens α} (K : U.compactsInside)
  proof: by rfl

中文:
引理 baseChangeOpenNhds_id
  条件: {U : Opens α} (K : U.compactsInside)
  证明: by rfl
-/
lemma baseChangeOpenNhds_id {U : Opens α} (K : U.compactsInside) :
  baseChangeCompactsInside (𝟙 U) K = K := by rfl

end Opens

namespace Compacts

/--
Definition of `baseChangeOpenNhds` / `baseChangeOpenNhds` 的定义

English:
definition baseChangeOpenNhds
  signature: {K L : Compacts α} (h : K ⟶ L)
  body: fun ⟨U, hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

中文:
定义 baseChangeOpenNhds
  签名: {K L : 余mpacts α} (h : K ⟶ L)
  定义体: fun ⟨U, hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

Depends on / 依赖: Set.mem_of_subset_of_mem, leOfHom, mem_of_subset_of_mem
-/
def baseChangeOpenNhds {K L : Compacts α} (h : K ⟶ L) : L.openNhds -> K.openNhds :=
  fun ⟨U, hU⟩ => ⟨U, fun _ hx => Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

/--
lemma `baseChangeOpenNhds_mono` / 引理 `baseChangeOpenNhds_mono`

English:
lemma baseChangeOpenNhds_mono
  given: {K L : Compacts α} (h : K ⟶ L)
  statement: Monotone baseChangeOpenNhds h
  proof: fun _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

@[simp]

中文:
引理 baseChangeOpenNhds_mono
  条件: {K L : 余mpacts α} (h : K ⟶ L)
  结论: 递增 baseChangeOpenNhds h
  证明: fun _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

@[simp]

Depends on / 依赖: SetLike, SetLike.mem_coe.mpr, mem_coe
-/
lemma baseChangeOpenNhds_mono {K L : Compacts α} (h : K ⟶ L) : Monotone baseChangeOpenNhds h :=
  fun _ _ hUV _ hx => SetLike.mem_coe.mpr (hUV hx)

@[simp]
/--
lemma `baseChangeOpenNhds_comp` / 引理 `baseChangeOpenNhds_comp`

English:
lemma baseChangeOpenNhds_comp
  given: {K L M : Compacts α} (h : K ⟶ L) (k : L ⟶ M) (U : M.openNhds)
  proof: by rfl

@[simp]

中文:
引理 baseChangeOpenNhds_comp
  条件: {K L M : 余mpacts α} (h : K ⟶ L) (k : L ⟶ M) (U : M.openNhds)
  证明: by rfl

@[simp]
-/
lemma baseChangeOpenNhds_comp {K L M : Compacts α} (h : K ⟶ L) (k : L ⟶ M) (U : M.openNhds) :
  baseChangeOpenNhds (h ≫ k) U = baseChangeOpenNhds h (baseChangeOpenNhds k U) := by rfl

@[simp]
/--
lemma `baseChangeOpenNhds_id` / 引理 `baseChangeOpenNhds_id`

English:
lemma baseChangeOpenNhds_id
  given: {K : Compacts α} (U : K.openNhds)
  proof: by rfl

中文:
引理 baseChangeOpenNhds_id
  条件: {K : 余mpacts α} (U : K.openNhds)
  证明: by rfl
-/
lemma baseChangeOpenNhds_id {K : Compacts α} (U : K.openNhds) :
  baseChangeOpenNhds (𝟙 K) U = U := by rfl

/--
Definition of `isInitialBotOpensOpenNhdsBot` / `isInitialBotOpensOpenNhdsBot` 的定义

English:
definition isInitialBotOpensOpenNhdsBot
  signature: : IsInitial (⊥ : (⊥ : Compacts α).openNhds)
  body: .ofUniqueHom
  (fun _ => homOfLE <| by tauto)
  (fun _ _ => eq_of_comp_right_eq <| by tauto)

中文:
定义 isInitialBotOpensOpenNhdsBot
  签名: : IsInitial (⊥ : (⊥ : 余mpacts α).openNhds)
  定义体: .ofUniqueHom
  (fun _ => homOfLE <| by tauto)
  (fun _ _ => eq_of_comp_right_eq <| by tauto)

Depends on / 依赖: ofUniqueHom
-/
def isInitialBotOpensOpenNhdsBot : IsInitial (⊥ : (⊥ : Compacts α).openNhds) := .ofUniqueHom
  (fun _ => homOfLE <| by tauto)
  (fun _ _ => eq_of_comp_right_eq <| by tauto)

instance {K : Compacts α} [T2Space α] [LocallyCompactSpace α] :
    K.openRcNhdsToOpenNhds_mono.functor.Initial := by
  rw [Monotone.initial_functor_iff]
  intro U
  obtain ⟨L, h1, h2, h3⟩ := exists_compact_between K.isCompact U.val.isOpen U.property
  use ⟨⟨interior L, isOpen_interior⟩,
    ⟨IsCompact.of_isClosed_subset h1 isClosed_closure
      (closure_minimal interior_subset (IsCompact.isClosed h1)),
    h2⟩⟩
  exact Subset.trans interior_subset h3

instance {K : Compacts α} [T2Space α] : K.openRcNhdsToCompactNhds_mono.functor.Initial := by
  rw [Monotone.initial_functor_iff]
  intro L
  obtain ⟨U, h1, h2⟩ := exists_open_set_nhds_of_compactsNhds L
  have h3 : closure (U : Set α) subseteq L := (IsClosed.closure_subset_iff
    (IsCompact.isClosed L.1.isCompact') ).2 h2
  exact ⟨⟨U, ⟨ IsCompact.of_isClosed_subset L.1.isCompact' isClosed_closure h3, h1⟩⟩, h3⟩

end Compacts

end TopologicalSpace
