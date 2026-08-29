/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.CompleteSublattice

/-!
# `SetLike` instance for elements of `CompleteSublattice (Set X)`

This file provides lemmas for the `SetLike` instance for elements of `CompleteSublattice (Set X)`
-/

public section

attribute [local instance] SetLike.instSubtypeSet

namespace Sublattice

variable {X : Type*} {L : Sublattice (Set X)}

variable {S T : L} {x : X}

/--
lemma `ext_mem` / 引理 `ext_mem`

English:
lemma ext_mem
  given: (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
引理 ext_mem
  条件: (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h
-/
@[ext] lemma ext_mem (h : forall x, x in S ↔ x in T) : S = T := SetLike.ext h

/--
lemma `mem_subtype` / 引理 `mem_subtype`

English:
lemma mem_subtype
  statement: x in L.subtype T ↔ x in T
  proof: Iff.rfl

中文:
引理 mem_subtype
  结论: x in L.subtype T ↔ x in T
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_subtype : x in L.subtype T ↔ x in T := Iff.rfl

/--
lemma `setLike_mem_inf` / 引理 `setLike_mem_inf`

English:
lemma setLike_mem_inf
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: by simp [← mem_subtype]

中文:
引理 setLike_mem_inf
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: by simp [← mem_subtype]
-/
@[simp] lemma setLike_mem_inf : x in S ⊓ T ↔ x in S ∧ x in T := by simp [← mem_subtype]
/--
lemma `setLike_mem_sup` / 引理 `setLike_mem_sup`

English:
lemma setLike_mem_sup
  statement: x in S ⊔ T ↔ x in S ∨ x in T
  proof: by simp [← mem_subtype]

中文:
引理 setLike_mem_sup
  结论: x in S ⊔ T ↔ x in S ∨ x in T
  证明: by simp [← mem_subtype]
-/
@[simp] lemma setLike_mem_sup : x in S ⊔ T ↔ x in S ∨ x in T := by simp [← mem_subtype]

/--
lemma `setLike_mem_coe` / 引理 `setLike_mem_coe`

English:
lemma setLike_mem_coe
  statement: x in T.val ↔ x in T
  proof: Iff.rfl

中文:
引理 setLike_mem_coe
  结论: x in T.val ↔ x in T
  证明: Iff.rfl
-/
@[simp] lemma setLike_mem_coe : x in T.val ↔ x in T := Iff.rfl

end Sublattice

namespace CompleteSublattice

variable {X : Type*} {L : CompleteSublattice (Set X)}

variable {S T : L} {𝒮 : Set L} {I : Sort*} {f : I -> L} {x : X}

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
引理 ext
  条件: (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h
-/
@[ext] lemma ext (h : forall x, x in S ↔ x in T) : S = T := SetLike.ext h

/--
lemma `mem_subtype` / 引理 `mem_subtype`

English:
lemma mem_subtype
  statement: x in L.subtype T ↔ x in T
  proof: Iff.rfl

中文:
引理 mem_subtype
  结论: x in L.subtype T ↔ x in T
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_subtype : x in L.subtype T ↔ x in T := Iff.rfl

/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: by simp [← mem_subtype]

中文:
引理 mem_inf
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_inf : x in S ⊓ T ↔ x in S ∧ x in T := by simp [← mem_subtype]
/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  statement: x in sInf 𝒮 ↔ forall T in 𝒮, x in T
  proof: by simp [← mem_subtype]

中文:
引理 mem_sInf
  结论: x in sInf 𝒮 ↔ 对任意 T in 𝒮, x in T
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_sInf : x in sInf 𝒮 ↔ forall T in 𝒮, x in T := by simp [← mem_subtype]
/--
lemma `mem_iInf` / 引理 `mem_iInf`

English:
lemma mem_iInf
  statement: x in ⨅ i : I, f i ↔ forall i : I, x in f i
  proof: by simp [← mem_subtype]

中文:
引理 mem_iInf
  结论: x in ⨅ i : I, f i ↔ 对任意 i : I, x in f i
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_iInf : x in ⨅ i : I, f i ↔ forall i : I, x in f i := by simp [← mem_subtype]

/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  statement: x in (⊤ : L)
  proof: by simp [← mem_subtype]

中文:
引理 mem_top
  结论: x in (⊤ : L)
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_top : x in (⊤ : L) := by simp [← mem_subtype]

/--
lemma `mem_sup` / 引理 `mem_sup`

English:
lemma mem_sup
  statement: x in S ⊔ T ↔ x in S ∨ x in T
  proof: by simp [← mem_subtype]

中文:
引理 mem_sup
  结论: x in S ⊔ T ↔ x in S ∨ x in T
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_sup : x in S ⊔ T ↔ x in S ∨ x in T := by simp [← mem_subtype]
/--
lemma `mem_sSup` / 引理 `mem_sSup`

English:
lemma mem_sSup
  statement: x in sSup 𝒮 ↔ exists T in 𝒮, x in T
  proof: by simp [← mem_subtype]

中文:
引理 mem_sSup
  结论: x in sSup 𝒮 ↔ 存在 T in 𝒮, x in T
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_sSup : x in sSup 𝒮 ↔ exists T in 𝒮, x in T := by simp [← mem_subtype]
/--
lemma `mem_iSup` / 引理 `mem_iSup`

English:
lemma mem_iSup
  statement: x in ⨆ i : I, f i ↔ exists i : I, x in f i
  proof: by simp [← mem_subtype]

中文:
引理 mem_iSup
  结论: x in ⨆ i : I, f i ↔ 存在 i : I, x in f i
  证明: by simp [← mem_subtype]
-/
@[simp] lemma mem_iSup : x in ⨆ i : I, f i ↔ exists i : I, x in f i := by simp [← mem_subtype]

/--
lemma `notMem_bot` / 引理 `notMem_bot`

English:
lemma notMem_bot
  statement: x ∉ (⊥ : L)
  proof: by simp [← mem_subtype]

中文:
引理 notMem_bot
  结论: x ∉ (⊥ : L)
  证明: by simp [← mem_subtype]
-/
@[simp] lemma notMem_bot : x ∉ (⊥ : L) := by simp [← mem_subtype]

end CompleteSublattice
