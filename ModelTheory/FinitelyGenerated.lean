/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.ModelTheory.Substructures

/-!
# Finitely Generated First-Order Structures

This file defines what it means for a first-order (sub)structure to be finitely or countably
generated, similarly to other finitely-generated objects in the algebra library.

## Main Definitions

- `FirstOrder.Language.Substructure.FG` indicates that a substructure is finitely generated.
- `FirstOrder.Language.Structure.FG` indicates that a structure is finitely generated.
- `FirstOrder.Language.Substructure.CG` indicates that a substructure is countably generated.
- `FirstOrder.Language.Structure.CG` indicates that a structure is countably generated.


## TODO

Develop a more unified definition of finite generation using the theory of closure operators, or use
this definition of finite generation to define the others.

-/

@[expose] public section

open FirstOrder Set

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

namespace Substructure

/--
Definition of `FG` / `FG` 的定义

English:
definition FG
  signature: (N : L.Substructure M)
  body: exists S : Finset M, closure L S = N

中文:
定义 FG
  签名: (N : L.子结构 M)
  定义体: exists S : Finset M, closure L S = N

Depends on / 依赖: Finset, closure
-/
def FG (N : L.Substructure M) : Prop :=
  exists S : Finset M, closure L S = N

/--
theorem `fg_def` / 定理 `fg_def`

English:
theorem fg_def
  given: {N : L.Substructure M}
  statement: N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
  proof: ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

中文:
定理 fg_def
  条件: {N : L.子结构 M}
  结论: N.FG ↔ 存在 S : 集合 M, S.有限 ∧ closure L S = N
  证明: ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

Depends on / 依赖: Finite, Finite.exists_finset_coe, Finset, Finset.finite_toSet, exists_finset_coe, finite_toSet
-/
theorem fg_def {N : L.Substructure M} : N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

/--
theorem `fg_iff_exists_fin_generating_family` / 定理 `fg_iff_exists_fin_generating_family`

English:
theorem fg_iff_exists_fin_generating_family
  given: {N : L.Substructure M}
  proof: by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

中文:
定理 fg_iff_存在_fin_generating_family
  条件: {N : L.子结构 M}
  证明: by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

Depends on / 依赖: Sfin.fin_embedding, fg_def, fin_embedding, finite_range
-/
theorem fg_iff_exists_fin_generating_family {N : L.Substructure M} :
    N.FG ↔ exists (n : Nat) (s : Fin n -> M), closure L (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

/--
theorem `fg_bot` / 定理 `fg_bot`

English:
theorem fg_bot
  statement: (⊥ : L.Substructure M).FG
  proof: ⟨∅, by rw [Finset.coe_empty, closure_empty]⟩

中文:
定理 fg_bot
  结论: (⊥ : L.子结构 M).FG
  证明: ⟨∅, by rw [Finset.coe_empty, closure_empty]⟩

Depends on / 依赖: Finset, Finset.coe_empty, closure_empty, coe_empty
-/
theorem fg_bot : (⊥ : L.Substructure M).FG :=
  ⟨∅, by rw [Finset.coe_empty, closure_empty]⟩

/--
Instance `instInhabited_fg` / 实例 `instInhabited_fg`

English:
instance instInhabited_fg
  signature: : Inhabited { S : L.Substructure M // S.FG }
  body: ⟨⊥, fg_bot⟩

中文:
实例 instInhabited_fg
  签名: : 可居 { S : L.子结构 M // S.FG }
  定义体: ⟨⊥, fg_bot⟩

Depends on / 依赖: fg_bot
-/
instance instInhabited_fg : Inhabited { S : L.Substructure M // S.FG } := ⟨⊥, fg_bot⟩

/--
theorem `fg_closure` / 定理 `fg_closure`

English:
theorem fg_closure
  given: {s : Set M} (hs : s.Finite)
  statement: FG (closure L s)
  proof: ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

中文:
定理 fg_closure
  条件: {s : 集合 M} (hs : s.有限)
  结论: FG (closure L s)
  证明: ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

Depends on / 依赖: coe_toFinset, hs.coe_toFinset, hs.toFinset, toFinset
-/
theorem fg_closure {s : Set M} (hs : s.Finite) : FG (closure L s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

/--
theorem `fg_closure_singleton` / 定理 `fg_closure_singleton`

English:
theorem fg_closure_singleton
  given: (x : M)
  statement: FG (closure L ({x} : Set M))
  proof: fg_closure (finite_singleton x)

中文:
定理 fg_closure_singleton
  条件: (x : M)
  结论: FG (closure L ({x} : 集合 M))
  证明: fg_closure (finite_singleton x)

Depends on / 依赖: fg_closure, finite_singleton
-/
theorem fg_closure_singleton (x : M) : FG (closure L ({x} : Set M)) :=
  fg_closure (finite_singleton x)

/--
theorem `FG.sup` / 定理 `FG.sup`

English:
theorem FG.sup
  given: {N₁ N₂ : L.Substructure M} (hN₁ : N₁.FG) (hN₂ : N₂.FG)
  statement: (N₁ ⊔ N₂).FG
  proof: let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ union t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

中文:
定理 FG.上确界
  条件: {N₁ N₂ : L.子结构 M} (hN₁ : N₁.FG) (hN₂ : N₂.FG)
  结论: (N₁ ⊔ N₂).FG
  证明: let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ union t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

Depends on / 依赖: closure_union, fg_def
-/
theorem FG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ union t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

/--
theorem `FG.map` / 定理 `FG.map`

English:
theorem FG.map
  given: {N : Type*} [L.Structure N] (f : M ->[L] N) {s : L.Substructure M} (hs : s.FG)
  proof: let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

中文:
定理 FG.map
  条件: {N : 类型} [L.结构 N] (f : M ->[L] N) {s : L.子结构 M} (hs : s.FG)
  证明: let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

Depends on / 依赖: closure_image, fg_def
-/
theorem FG.map {N : Type*} [L.Structure N] (f : M ->[L] N) {s : L.Substructure M} (hs : s.FG) :
    (s.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

/--
theorem `FG.of_map_embedding` / 定理 `FG.of_map_embedding`

English:
theorem FG.of_map_embedding
  statement: {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
  proof: by
  rcases hs with ⟨t, h⟩
  rw [fg_def]
  refine ⟨f ⁻¹' t, t.finite_toSet.preimage f.injective.injOn, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h]; rw [map_closure]; rw [Embedding.coe_toHom]; rw [image_preimage_eq_of_subset]
  intro 

中文:
定理 FG.of_map_embedding
  结论: {N : 类型} [L.结构 N] (f : M ↪[L] N) {s : L.子结构 M}
  证明: by
  rcases hs with ⟨t, h⟩
  rw [fg_def]
  refine ⟨f ⁻¹' t, t.finite_toSet.preimage f.injective.injOn, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h]; rw [map_closure]; rw [Embedding.coe_toHom]; rw [image_preimage_eq_of_subset]
  intro 

Depends on / 依赖: Embedding, Embedding.coe_toHom, Function, Function.Injective, Hom.map_le_range, Injective, coe_toHom, f.injective, f.injective.injOn, f.toHom, fg_def, finite_toSet, image_preimage_eq_of_subset, injective, map_closure, map_injective_of_injective, map_le_range, preimage, subset_closure, t.finite_toSet.preimage
-/
theorem FG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).FG) : s.FG := by
  rcases hs with ⟨t, h⟩
  rw [fg_def]
  refine ⟨f ⁻¹' t, t.finite_toSet.preimage f.injective.injOn, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h]; rw [map_closure]; rw [Embedding.coe_toHom]; rw [image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure (L := L) hx
  rw [h] at h'
  exact Hom.map_le_range h'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FG.of_finite` / 定理 `FG.of_finite`

English:
theorem FG.of_finite
  given: {s : L.Substructure M} [h : Finite s]
  statement: s.FG
  proof: ⟨Set.Finite.toFinset h, by simp only [Finite.coe_toFinset, closure_eq]⟩

中文:
定理 FG.of_finite
  条件: {s : L.子结构 M} [h : 有限 s]
  结论: s.FG
  证明: ⟨Set.Finite.toFinset h, by simp only [Finite.coe_toFinset, closure_eq]⟩

Depends on / 依赖: Finite, Finite.coe_toFinset, Set.Finite.toFinset, closure_eq, coe_toFinset, toFinset
-/
theorem FG.of_finite {s : L.Substructure M} [h : Finite s] : s.FG :=
  ⟨Set.Finite.toFinset h, by simp only [Finite.coe_toFinset, closure_eq]⟩

/--
theorem `FG.finite` / 定理 `FG.finite`

English:
theorem FG.finite
  given: [L.IsRelational] {S : L.Substructure M} (h : S.FG)
  statement: Finite S
  proof: by
  obtain ⟨s, rfl⟩ := h
  have hs := s.finite_toSet
  rw [← closure_eq_of_isRelational L (s : Set M)] at hs
  exact hs

中文:
定理 FG.finite
  条件: [L.IsRelational] {S : L.子结构 M} (h : S.FG)
  结论: 有限 S
  证明: by
  obtain ⟨s, rfl⟩ := h
  have hs := s.finite_toSet
  rw [← closure_eq_of_isRelational L (s : Set M)] at hs
  exact hs

Depends on / 依赖: closure_eq_of_isRelational, finite_toSet, s.finite_toSet
-/
theorem FG.finite [L.IsRelational] {S : L.Substructure M} (h : S.FG) : Finite S := by
  obtain ⟨s, rfl⟩ := h
  have hs := s.finite_toSet
  rw [← closure_eq_of_isRelational L (s : Set M)] at hs
  exact hs

/--
theorem `fg_iff_finite` / 定理 `fg_iff_finite`

English:
theorem fg_iff_finite
  given: [L.IsRelational] {S : L.Substructure M}
  statement: S.FG ↔ Finite S
  proof: ⟨FG.finite, fun _ => FG.of_finite⟩

中文:
定理 fg_iff_finite
  条件: [L.IsRelational] {S : L.子结构 M}
  结论: S.FG ↔ 有限 S
  证明: ⟨FG.finite, fun _ => FG.of_finite⟩

Depends on / 依赖: FG.finite, FG.of_finite, finite, of_finite
-/
theorem fg_iff_finite [L.IsRelational] {S : L.Substructure M} : S.FG ↔ Finite S :=
  ⟨FG.finite, fun _ => FG.of_finite⟩

/--
Definition of `CG` / `CG` 的定义

English:
definition CG
  signature: (N : L.Substructure M)
  body: exists S : Set M, S.Countable ∧ closure L S = N

中文:
定义 CG
  签名: (N : L.子结构 M)
  定义体: exists S : Set M, S.Countable ∧ closure L S = N

Depends on / 依赖: Countable, S.Countable, closure
-/
def CG (N : L.Substructure M) : Prop :=
  exists S : Set M, S.Countable ∧ closure L S = N

/--
theorem `cg_def` / 定理 `cg_def`

English:
theorem cg_def
  given: {N : L.Substructure M}
  statement: N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N
  proof: Iff.refl _

中文:
定理 cg_def
  条件: {N : L.子结构 M}
  结论: N.CG ↔ 存在 S : 集合 M, S.可数 ∧ closure L S = N
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
theorem cg_def {N : L.Substructure M} : N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N :=
  Iff.refl _

/--
theorem `FG.cg` / 定理 `FG.cg`

English:
theorem FG.cg
  given: {N : L.Substructure M} (h : N.FG)
  statement: N.CG
  proof: by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  exact ⟨s, hf.countable, rfl⟩

中文:
定理 FG.cg
  条件: {N : L.子结构 M} (h : N.FG)
  结论: N.CG
  证明: by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  exact ⟨s, hf.countable, rfl⟩

Depends on / 依赖: countable, fg_def, hf.countable
-/
theorem FG.cg {N : L.Substructure M} (h : N.FG) : N.CG := by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  exact ⟨s, hf.countable, rfl⟩

/--
theorem `cg_iff_empty_or_exists_nat_generating_family` / 定理 `cg_iff_empty_or_exists_nat_generating_family`

English:
theorem cg_iff_empty_or_exists_nat_generating_family
  given: {N : L.Substructure M}
  proof: by
  rw [cg_def]
  constructor
  · rintro ⟨S, Scount, hS⟩
    rcases eq_empty_or_nonempty (N : Set M) with h | h
    · exact Or.intro_left _ h
    obtain ⟨f, h'⟩ :=
      (Scount.union (Set.countable_singleton h.some)).exists_eq_range
        (singleton_nonempty h.some).inr
    refine Or.intro_right

中文:
定理 cg_iff_empty_or_存在_nat_generating_family
  条件: {N : L.子结构 M}
  证明: by
  rw [cg_def]
  constructor
  · rintro ⟨S, Scount, hS⟩
    rcases eq_empty_or_nonempty (N : Set M) with h | h
    · exact Or.intro_left _ h
    obtain ⟨f, h'⟩ :=
      (Scount.union (Set.countable_singleton h.some)).exists_eq_range
        (singleton_nonempty h.some).inr
    refine Or.intro_right

Depends on / 依赖: Or.intro_left, Or.intro_right, Scount, Scount.union, Set.countable_singleton, SetLike, cg_def, closure_eq_of_le, closure_le, closure_union, countable_empty, countable_singleton, empty_subset, eq_empty_or_nonempty, exists_eq_range, h.some, h.some_mem, intro_left, intro_right, singleton_nonempty
-/
theorem cg_iff_empty_or_exists_nat_generating_family {N : L.Substructure M} :
    N.CG ↔ N = (∅ : Set M) ∨ exists s : Nat -> M, closure L (range s) = N := by
  rw [cg_def]
  constructor
  · rintro ⟨S, Scount, hS⟩
    rcases eq_empty_or_nonempty (N : Set M) with h | h
    · exact Or.intro_left _ h
    obtain ⟨f, h'⟩ :=
      (Scount.union (Set.countable_singleton h.some)).exists_eq_range
        (singleton_nonempty h.some).inr
    refine Or.intro_right _ ⟨f, ?_⟩
    rw [← h']; rw [closure_union]; rw [hS]; rw [sup_eq_left]; rw [closure_le]
    exact singleton_subset_iff.2 h.some_mem
  · intro h
    rcases h with h | h
    · refine ⟨∅, countable_empty, closure_eq_of_le (empty_subset _) ?_⟩
      rw [← SetLike.coe_subset_coe]; rw [h]
      exact empty_subset _
    · obtain ⟨f, rfl⟩ := h
      exact ⟨range f, countable_range _, rfl⟩

/--
theorem `cg_bot` / 定理 `cg_bot`

English:
theorem cg_bot
  statement: (⊥ : L.Substructure M).CG
  proof: fg_bot.cg

中文:
定理 cg_bot
  结论: (⊥ : L.子结构 M).CG
  证明: fg_bot.cg

Depends on / 依赖: fg_bot, fg_bot.cg
-/
theorem cg_bot : (⊥ : L.Substructure M).CG :=
  fg_bot.cg

/--
theorem `cg_closure` / 定理 `cg_closure`

English:
theorem cg_closure
  given: {s : Set M} (hs : s.Countable)
  statement: CG (closure L s)
  proof: ⟨s, hs, rfl⟩

中文:
定理 cg_closure
  条件: {s : 集合 M} (hs : s.可数)
  结论: CG (closure L s)
  证明: ⟨s, hs, rfl⟩
-/
theorem cg_closure {s : Set M} (hs : s.Countable) : CG (closure L s) :=
  ⟨s, hs, rfl⟩

/--
theorem `cg_closure_singleton` / 定理 `cg_closure_singleton`

English:
theorem cg_closure_singleton
  given: (x : M)
  statement: CG (closure L ({x} : Set M))
  proof: (fg_closure_singleton x).cg

中文:
定理 cg_closure_singleton
  条件: (x : M)
  结论: CG (closure L ({x} : 集合 M))
  证明: (fg_closure_singleton x).cg

Depends on / 依赖: fg_closure_singleton
-/
theorem cg_closure_singleton (x : M) : CG (closure L ({x} : Set M)) :=
  (fg_closure_singleton x).cg

/--
theorem `CG.sup` / 定理 `CG.sup`

English:
theorem CG.sup
  given: {N₁ N₂ : L.Substructure M} (hN₁ : N₁.CG) (hN₂ : N₂.CG)
  statement: (N₁ ⊔ N₂).CG
  proof: let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2 ⟨t₁ union t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

中文:
定理 CG.上确界
  条件: {N₁ N₂ : L.子结构 M} (hN₁ : N₁.CG) (hN₂ : N₂.CG)
  结论: (N₁ ⊔ N₂).CG
  证明: let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2 ⟨t₁ union t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

Depends on / 依赖: cg_def, closure_union
-/
theorem CG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.CG) (hN₂ : N₂.CG) : (N₁ ⊔ N₂).CG :=
  let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2 ⟨t₁ union t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

/--
theorem `CG.map` / 定理 `CG.map`

English:
theorem CG.map
  given: {N : Type*} [L.Structure N] (f : M ->[L] N) {s : L.Substructure M} (hs : s.CG)
  proof: let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

中文:
定理 CG.map
  条件: {N : 类型} [L.结构 N] (f : M ->[L] N) {s : L.子结构 M} (hs : s.CG)
  证明: let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

Depends on / 依赖: cg_def, closure_image
-/
theorem CG.map {N : Type*} [L.Structure N] (f : M ->[L] N) {s : L.Substructure M} (hs : s.CG) :
    (s.map f).CG :=
  let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

/--
theorem `CG.of_map_embedding` / 定理 `CG.of_map_embedding`

English:
theorem CG.of_map_embedding
  statement: {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
  proof: by
  rcases hs with ⟨t, h1, h2⟩
  rw [cg_def]
  refine ⟨f ⁻¹' t, h1.preimage f.injective, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h2]; rw [map_closure]; rw [Embedding.coe_toHom]; rw [image_preimage_eq_of_subset]
  intro x hx
  have 

中文:
定理 CG.of_map_embedding
  结论: {N : 类型} [L.结构 N] (f : M ↪[L] N) {s : L.子结构 M}
  证明: by
  rcases hs with ⟨t, h1, h2⟩
  rw [cg_def]
  refine ⟨f ⁻¹' t, h1.preimage f.injective, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h2]; rw [map_closure]; rw [Embedding.coe_toHom]; rw [image_preimage_eq_of_subset]
  intro x hx
  have 

Depends on / 依赖: Embedding, Embedding.coe_toHom, Function, Function.Injective, Hom.map_le_range, Injective, cg_def, coe_toHom, f.injective, f.toHom, h1.preimage, image_preimage_eq_of_subset, injective, map_closure, map_injective_of_injective, map_le_range, preimage, subset_closure
-/
theorem CG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).CG) : s.CG := by
  rcases hs with ⟨t, h1, h2⟩
  rw [cg_def]
  refine ⟨f ⁻¹' t, h1.preimage f.injective, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h2]; rw [map_closure]; rw [Embedding.coe_toHom]; rw [image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure (L := L) hx
  rw [h2] at h'
  exact Hom.map_le_range h'

/--
theorem `cg_iff_countable` / 定理 `cg_iff_countable`

English:
theorem cg_iff_countable
  given: [Countable (Σ l, L.Functions l)] {s : L.Substructure M}
  proof: by
  refine ⟨?_, fun h => ⟨s, h.to_set, s.closure_eq⟩⟩
  rintro ⟨s, h, rfl⟩
  exact h.substructure_closure L

中文:
定理 cg_iff_countable
  条件: [可数 (Σ l, L.函数 l)] {s : L.子结构 M}
  证明: by
  refine ⟨?_, fun h => ⟨s, h.to_set, s.closure_eq⟩⟩
  rintro ⟨s, h, rfl⟩
  exact h.substructure_closure L

Depends on / 依赖: closure_eq, h.substructure_closure, h.to_set, s.closure_eq, substructure_closure, to_set
-/
theorem cg_iff_countable [Countable (Σ l, L.Functions l)] {s : L.Substructure M} :
    s.CG ↔ Countable s := by
  refine ⟨?_, fun h => ⟨s, h.to_set, s.closure_eq⟩⟩
  rintro ⟨s, h, rfl⟩
  exact h.substructure_closure L

/--
theorem `cg_of_countable` / 定理 `cg_of_countable`

English:
theorem cg_of_countable
  given: {s : L.Substructure M} [h : Countable s]
  statement: s.CG
  proof: ⟨s, h.to_set, s.closure_eq⟩

中文:
定理 cg_of_countable
  条件: {s : L.子结构 M} [h : 可数 s]
  结论: s.CG
  证明: ⟨s, h.to_set, s.closure_eq⟩

Depends on / 依赖: closure_eq, h.to_set, s.closure_eq, to_set
-/
theorem cg_of_countable {s : L.Substructure M} [h : Countable s] : s.CG :=
  ⟨s, h.to_set, s.closure_eq⟩

end Substructure

open Substructure

namespace Structure

variable (L) (M)

/--
Definition of `FG` / `FG` 的定义

English:
class FG
  parameters: : Prop where
  axioms and operations (1):
    - out : (⊤ : L.Substructure M).FG

中文:
类 FG
  参数: : 命题 where
  公理与运算 (1 个):
    - out : (⊤ : L.子结构 M).FG
-/
class FG : Prop where
  out : (⊤ : L.Substructure M).FG

/--
Definition of `CG` / `CG` 的定义

English:
class CG
  parameters: : Prop where
  axioms and operations (1):
    - out : (⊤ : L.Substructure M).CG

中文:
类 CG
  参数: : 命题 where
  公理与运算 (1 个):
    - out : (⊤ : L.子结构 M).CG
-/
class CG : Prop where
  out : (⊤ : L.Substructure M).CG

variable {L M}

/--
theorem `fg_def` / 定理 `fg_def`

English:
theorem fg_def
  statement: FG L M ↔ (⊤ : L.Substructure M).FG
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 fg_def
  结论: FG L M ↔ (⊤ : L.子结构 M).FG
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem fg_def : FG L M ↔ (⊤ : L.Substructure M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `fg_iff` / 定理 `fg_iff`

English:
theorem fg_iff
  statement: FG L M ↔ exists S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substructure M)
  proof: by
  rw [fg_def]; rw [Substructure.fg_def]

中文:
定理 fg_iff
  结论: FG L M ↔ 存在 S : 集合 M, S.有限 ∧ closure L S = (⊤ : L.子结构 M)
  证明: by
  rw [fg_def]; rw [Substructure.fg_def]

Depends on / 依赖: Substructure, Substructure.fg_def, fg_def
-/
theorem fg_iff : FG L M ↔ exists S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [fg_def]; rw [Substructure.fg_def]

/--
theorem `FG.range` / 定理 `FG.range`

English:
theorem FG.range
  given: {N : Type*} [L.Structure N] (h : FG L M) (f : M ->[L] N)
  statement: f.range.FG
  proof: by
  rw [Hom.range_eq_map]
  exact (fg_def.1 h).map f

中文:
定理 FG.range
  条件: {N : 类型} [L.结构 N] (h : FG L M) (f : M ->[L] N)
  结论: f.range.FG
  证明: by
  rw [Hom.range_eq_map]
  exact (fg_def.1 h).map f

Depends on / 依赖: Hom.range_eq_map, fg_def, range_eq_map
-/
theorem FG.range {N : Type*} [L.Structure N] (h : FG L M) (f : M ->[L] N) : f.range.FG := by
  rw [Hom.range_eq_map]
  exact (fg_def.1 h).map f

/--
theorem `FG.map_of_surjective` / 定理 `FG.map_of_surjective`

English:
theorem FG.map_of_surjective
  statement: {N : Type*} [L.Structure N] (h : FG L M) (f : M ->[L] N)
  proof: by
  rw [← Hom.range_eq_top] at hs
  rw [fg_def]; rw [← hs]
  exact h.range f

中文:
定理 FG.map_of_surjective
  结论: {N : 类型} [L.结构 N] (h : FG L M) (f : M ->[L] N)
  证明: by
  rw [← Hom.range_eq_top] at hs
  rw [fg_def]; rw [← hs]
  exact h.range f

Depends on / 依赖: Hom.range_eq_top, fg_def, h.range, range_eq_top
-/
theorem FG.map_of_surjective {N : Type*} [L.Structure N] (h : FG L M) (f : M ->[L] N)
    (hs : Function.Surjective f) : FG L N := by
  rw [← Hom.range_eq_top] at hs
  rw [fg_def]; rw [← hs]
  exact h.range f

/--
theorem `FG.countable_hom` / 定理 `FG.countable_hom`

English:
theorem FG.countable_hom
  given: (N : Type*) [L.Structure N] [Countable N] (h : FG L M)
  proof: by
  let ⟨S, finite_S, closure_S⟩ := fg_iff.1 h
  let g : (M ->[L] N) -> (S -> N) :=
    fun f => f ∘ (↑)
  have g_inj : Function.Injective g := by
    intro f f' h
    apply Hom.eq_of_eqOn_dense closure_S
    intro x x_in_S
    exact congr_fun h ⟨x, x_in_S⟩
  have : Finite ↑S := (S.finite_coe_iff).

中文:
定理 FG.countable_hom
  条件: (N : 类型) [L.结构 N] [可数 N] (h : FG L M)
  证明: by
  let ⟨S, finite_S, closure_S⟩ := fg_iff.1 h
  let g : (M ->[L] N) -> (S -> N) :=
    fun f => f ∘ (↑)
  have g_inj : Function.Injective g := by
    intro f f' h
    apply Hom.eq_of_eqOn_dense closure_S
    intro x x_in_S
    exact congr_fun h ⟨x, x_in_S⟩
  have : Finite ↑S := (S.finite_coe_iff).

Depends on / 依赖: Embedding, Finite, Function, Function.Embedding.countable, Function.Injective, Hom.eq_of_eqOn_dense, Injective, S.finite_coe_iff, closure_S, congr_fun, countable, eq_of_eqOn_dense, fg_iff, finite_S, finite_coe_iff, g_inj, x_in_S
-/
theorem FG.countable_hom (N : Type*) [L.Structure N] [Countable N] (h : FG L M) :
    Countable (M ->[L] N) := by
  let ⟨S, finite_S, closure_S⟩ := fg_iff.1 h
  let g : (M ->[L] N) -> (S -> N) :=
    fun f => f ∘ (↑)
  have g_inj : Function.Injective g := by
    intro f f' h
    apply Hom.eq_of_eqOn_dense closure_S
    intro x x_in_S
    exact congr_fun h ⟨x, x_in_S⟩
  have : Finite ↑S := (S.finite_coe_iff).2 finite_S
  exact Function.Embedding.countable ⟨g, g_inj⟩

/--
Instance `FG.instCountable_hom` / 实例 `FG.instCountable_hom`

English:
instance FG.instCountable_hom
  signature: (N : Type*) [L.Structure N] [Countable N] [h : FG L M]
  body: FG.countable_hom N h

中文:
实例 FG.instCountable_hom
  签名: (N : 类型) [L.结构 N] [可数 N] [h : FG L M]
  定义体: FG.countable_hom N h

Depends on / 依赖: FG.countable_hom, countable_hom
-/
instance FG.instCountable_hom (N : Type*) [L.Structure N] [Countable N] [h : FG L M] :
    Countable (M ->[L] N) :=
  FG.countable_hom N h

/--
theorem `FG.countable_embedding` / 定理 `FG.countable_embedding`

English:
theorem FG.countable_embedding
  given: (N : Type*) [L.Structure N] [Countable N] (_ : FG L M)
  proof: Function.Embedding.countable ⟨Embedding.toHom, Embedding.toHom_injective⟩

中文:
定理 FG.countable_embedding
  条件: (N : 类型) [L.结构 N] [可数 N] (_ : FG L M)
  证明: Function.Embedding.countable ⟨Embedding.toHom, Embedding.toHom_injective⟩

Depends on / 依赖: Embedding, Embedding.toHom, Embedding.toHom_injective, Function, Function.Embedding.countable, countable, toHom_injective
-/
theorem FG.countable_embedding (N : Type*) [L.Structure N] [Countable N] (_ : FG L M) :
    Countable (M ↪[L] N) :=
  Function.Embedding.countable ⟨Embedding.toHom, Embedding.toHom_injective⟩

/--
Instance `Fg.instCountable_embedding` / 实例 `Fg.instCountable_embedding`

English:
instance Fg.instCountable_embedding
  signature: (N : Type*) [L.Structure N]
  body: FG.countable_embedding N h

中文:
实例 Fg.instCountable_embedding
  签名: (N : 类型) [L.结构 N]
  定义体: FG.countable_embedding N h

Depends on / 依赖: FG.countable_embedding, countable_embedding
-/
instance Fg.instCountable_embedding (N : Type*) [L.Structure N]
    [Countable N] [h : FG L M] : Countable (M ↪[L] N) :=
  FG.countable_embedding N h

/--
theorem `FG.of_finite` / 定理 `FG.of_finite`

English:
theorem FG.of_finite
  given: [Finite M]
  statement: FG L M
  proof: by
  simp only [fg_def, Substructure.FG.of_finite]

中文:
定理 FG.of_finite
  条件: [有限 M]
  结论: FG L M
  证明: by
  simp only [fg_def, Substructure.FG.of_finite]
-/
theorem FG.of_finite [Finite M] : FG L M := by
  simp only [fg_def, Substructure.FG.of_finite]

/--
theorem `FG.finite` / 定理 `FG.finite`

English:
theorem FG.finite
  given: [L.IsRelational] (h : FG L M)
  statement: Finite M
  proof: Finite.of_finite_univ (Substructure.FG.finite (fg_def.1 h))

中文:
定理 FG.finite
  条件: [L.IsRelational] (h : FG L M)
  结论: 有限 M
  证明: Finite.of_finite_univ (Substructure.FG.finite (fg_def.1 h))
-/
theorem FG.finite [L.IsRelational] (h : FG L M) : Finite M :=
  Finite.of_finite_univ (Substructure.FG.finite (fg_def.1 h))

/--
theorem `fg_iff_finite` / 定理 `fg_iff_finite`

English:
theorem fg_iff_finite
  given: [L.IsRelational]
  statement: FG L M ↔ Finite M
  proof: ⟨FG.finite, fun _ => FG.of_finite⟩

中文:
定理 fg_iff_finite
  条件: [L.IsRelational]
  结论: FG L M ↔ 有限 M
  证明: ⟨FG.finite, fun _ => FG.of_finite⟩

Depends on / 依赖: FG.finite, FG.of_finite, finite, of_finite
-/
theorem fg_iff_finite [L.IsRelational] : FG L M ↔ Finite M :=
  ⟨FG.finite, fun _ => FG.of_finite⟩

/--
theorem `cg_def` / 定理 `cg_def`

English:
theorem cg_def
  statement: CG L M ↔ (⊤ : L.Substructure M).CG
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 cg_def
  结论: CG L M ↔ (⊤ : L.子结构 M).CG
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem cg_def : CG L M ↔ (⊤ : L.Substructure M).CG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `cg_iff` / 定理 `cg_iff`

English:
theorem cg_iff
  statement: CG L M ↔ exists S : Set M, S.Countable ∧ closure L S = (⊤ : L.Substructure M)
  proof: by
  rw [cg_def]; rw [Substructure.cg_def]

中文:
定理 cg_iff
  结论: CG L M ↔ 存在 S : 集合 M, S.可数 ∧ closure L S = (⊤ : L.子结构 M)
  证明: by
  rw [cg_def]; rw [Substructure.cg_def]

Depends on / 依赖: Substructure, Substructure.cg_def, cg_def
-/
theorem cg_iff : CG L M ↔ exists S : Set M, S.Countable ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [cg_def]; rw [Substructure.cg_def]

/--
theorem `CG.range` / 定理 `CG.range`

English:
theorem CG.range
  given: {N : Type*} [L.Structure N] (h : CG L M) (f : M ->[L] N)
  statement: f.range.CG
  proof: by
  rw [Hom.range_eq_map]
  exact (cg_def.1 h).map f

中文:
定理 CG.range
  条件: {N : 类型} [L.结构 N] (h : CG L M) (f : M ->[L] N)
  结论: f.range.CG
  证明: by
  rw [Hom.range_eq_map]
  exact (cg_def.1 h).map f

Depends on / 依赖: Hom.range_eq_map, cg_def, range_eq_map
-/
theorem CG.range {N : Type*} [L.Structure N] (h : CG L M) (f : M ->[L] N) : f.range.CG := by
  rw [Hom.range_eq_map]
  exact (cg_def.1 h).map f

/--
theorem `CG.map_of_surjective` / 定理 `CG.map_of_surjective`

English:
theorem CG.map_of_surjective
  statement: {N : Type*} [L.Structure N] (h : CG L M) (f : M ->[L] N)
  proof: by
  rw [← Hom.range_eq_top] at hs
  rw [cg_def]; rw [← hs]
  exact h.range f

中文:
定理 CG.map_of_surjective
  结论: {N : 类型} [L.结构 N] (h : CG L M) (f : M ->[L] N)
  证明: by
  rw [← Hom.range_eq_top] at hs
  rw [cg_def]; rw [← hs]
  exact h.range f

Depends on / 依赖: Hom.range_eq_top, cg_def, h.range, range_eq_top
-/
theorem CG.map_of_surjective {N : Type*} [L.Structure N] (h : CG L M) (f : M ->[L] N)
    (hs : Function.Surjective f) : CG L N := by
  rw [← Hom.range_eq_top] at hs
  rw [cg_def]; rw [← hs]
  exact h.range f

/--
theorem `cg_iff_countable` / 定理 `cg_iff_countable`

English:
theorem cg_iff_countable
  given: [Countable (Σ l, L.Functions l)]
  statement: CG L M ↔ Countable M
  proof: by
  rw [cg_def]; rw [Substructure.cg_iff_countable]; rw [topEquiv.toEquiv.countable_iff]

中文:
定理 cg_iff_countable
  条件: [可数 (Σ l, L.函数 l)]
  结论: CG L M ↔ 可数 M
  证明: by
  rw [cg_def]; rw [Substructure.cg_iff_countable]; rw [topEquiv.toEquiv.countable_iff]

Depends on / 依赖: Substructure, Substructure.cg_iff_countable, cg_def, cg_iff_countable, countable_iff, toEquiv, topEquiv, topEquiv.toEquiv.countable_iff
-/
theorem cg_iff_countable [Countable (Σ l, L.Functions l)] : CG L M ↔ Countable M := by
  rw [cg_def]; rw [Substructure.cg_iff_countable]; rw [topEquiv.toEquiv.countable_iff]

/--
theorem `cg_of_countable` / 定理 `cg_of_countable`

English:
theorem cg_of_countable
  given: [Countable M]
  statement: CG L M
  proof: by
  simp only [cg_def, Substructure.cg_of_countable]

中文:
定理 cg_of_countable
  条件: [可数 M]
  结论: CG L M
  证明: by
  simp only [cg_def, Substructure.cg_of_countable]

Depends on / 依赖: Substructure, Substructure.cg_of_countable, cg_def, cg_of_countable
-/
theorem cg_of_countable [Countable M] : CG L M := by
  simp only [cg_def, Substructure.cg_of_countable]

/--
theorem `FG.cg` / 定理 `FG.cg`

English:
theorem FG.cg
  given: (h : FG L M)
  statement: CG L M
  proof: cg_def.2 (fg_def.1 h).cg

中文:
定理 FG.cg
  条件: (h : FG L M)
  结论: CG L M
  证明: cg_def.2 (fg_def.1 h).cg
-/
theorem FG.cg (h : FG L M) : CG L M :=
  cg_def.2 (fg_def.1 h).cg

instance (priority := 100) cg_of_fg [h : FG L M] : CG L M :=
  h.cg

end Structure

/--
theorem `Equiv.fg_iff` / 定理 `Equiv.fg_iff`

English:
theorem Equiv.fg_iff
  given: {N : Type*} [L.Structure N] (f : M ≃[L] N)
  proof: ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

中文:
定理 等价.fg_iff
  条件: {N : 类型} [L.结构 N] (f : M ≃[L] N)
  证明: ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

Depends on / 依赖: f.symm.toHom, f.toEquiv.surjective, f.toEquiv.symm.surjective, f.toHom, h.map_of_surjective, map_of_surjective, surjective, toEquiv
-/
theorem Equiv.fg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.FG L M ↔ Structure.FG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

/--
theorem `Substructure.fg_iff_structure_fg` / 定理 `Substructure.fg_iff_structure_fg`

English:
theorem Substructure.fg_iff_structure_fg
  given: (S : L.Substructure M)
  statement: S.FG ↔ Structure.FG L S
  proof: by
  rw [Structure.fg_def]
  refine ⟨fun h => FG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map]; rw [range_subtype] at h
    exact h

中文:
定理 子结构.fg_iff_structure_fg
  条件: (S : L.子结构 M)
  结论: S.FG ↔ 结构.FG L S
  证明: by
  rw [Structure.fg_def]
  refine ⟨fun h => FG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map]; rw [range_subtype] at h
    exact h

Depends on / 依赖: FG.of_map_embedding, Hom.range_eq_map, S.subtype, S.subtype.toHom, Structure, Structure.fg_def, fg_def, h.map, of_map_embedding, range_eq_map, range_subtype, subtype
-/
theorem Substructure.fg_iff_structure_fg (S : L.Substructure M) : S.FG ↔ Structure.FG L S := by
  rw [Structure.fg_def]
  refine ⟨fun h => FG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map]; rw [range_subtype] at h
    exact h

/--
theorem `Equiv.cg_iff` / 定理 `Equiv.cg_iff`

English:
theorem Equiv.cg_iff
  given: {N : Type*} [L.Structure N] (f : M ≃[L] N)
  proof: ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

中文:
定理 等价.cg_iff
  条件: {N : 类型} [L.结构 N] (f : M ≃[L] N)
  证明: ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

Depends on / 依赖: f.symm.toHom, f.toEquiv.surjective, f.toEquiv.symm.surjective, f.toHom, h.map_of_surjective, map_of_surjective, surjective, toEquiv
-/
theorem Equiv.cg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.CG L M ↔ Structure.CG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

/--
theorem `Substructure.cg_iff_structure_cg` / 定理 `Substructure.cg_iff_structure_cg`

English:
theorem Substructure.cg_iff_structure_cg
  given: (S : L.Substructure M)
  statement: S.CG ↔ Structure.CG L S
  proof: by
  rw [Structure.cg_def]
  refine ⟨fun h => CG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map]; rw [range_subtype] at h
    exact h

中文:
定理 子结构.cg_iff_structure_cg
  条件: (S : L.子结构 M)
  结论: S.CG ↔ 结构.CG L S
  证明: by
  rw [Structure.cg_def]
  refine ⟨fun h => CG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map]; rw [range_subtype] at h
    exact h

Depends on / 依赖: CG.of_map_embedding, Hom.range_eq_map, S.subtype, S.subtype.toHom, Structure, Structure.cg_def, cg_def, h.map, of_map_embedding, range_eq_map, range_subtype, subtype
-/
theorem Substructure.cg_iff_structure_cg (S : L.Substructure M) : S.CG ↔ Structure.CG L S := by
  rw [Structure.cg_def]
  refine ⟨fun h => CG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map]; rw [range_subtype] at h
    exact h

/--
theorem `Substructure.countable_fg_substructures_of_countable` / 定理 `Substructure.countable_fg_substructures_of_countable`

English:
theorem Substructure.countable_fg_substructures_of_countable
  given: [Countable M]
  proof: by
  let g : { S : L.Substructure M // S.FG } -> Finset M :=
    fun S => Exists.choose S.prop
  have g_inj : Function.Injective g := by
    intro S S' h
    apply Subtype.ext
    rw [(Exists.choose_spec S.prop).symm]; rw [(Exists.choose_spec S'.prop).symm]
    exact congr_arg (closure L ∘ SetLike.c

中文:
定理 子结构.countable_fg_substructures_of_countable
  条件: [可数 M]
  证明: by
  let g : { S : L.Substructure M // S.FG } -> Finset M :=
    fun S => Exists.choose S.prop
  have g_inj : Function.Injective g := by
    intro S S' h
    apply Subtype.ext
    rw [(Exists.choose_spec S.prop).symm]; rw [(Exists.choose_spec S'.prop).symm]
    exact congr_arg (closure L ∘ SetLike.c

Depends on / 依赖: Embedding, Exists, Exists.choose, Exists.choose_spec, Finset, Function, Function.Embedding.countable, Function.Injective, Injective, L.Substructure, S.FG, S.prop, SetLike, SetLike.coe, Substructure, Subtype, Subtype.ext, choose_spec, closure, congr_arg
-/
theorem Substructure.countable_fg_substructures_of_countable [Countable M] :
    Countable { S : L.Substructure M // S.FG } := by
  let g : { S : L.Substructure M // S.FG } -> Finset M :=
    fun S => Exists.choose S.prop
  have g_inj : Function.Injective g := by
    intro S S' h
    apply Subtype.ext
    rw [(Exists.choose_spec S.prop).symm]; rw [(Exists.choose_spec S'.prop).symm]
    exact congr_arg (closure L ∘ SetLike.coe) h
  exact Function.Embedding.countable ⟨g, g_inj⟩

/--
Instance `Substructure.instCountable_fg_substructures_of_countable` / 实例 `Substructure.instCountable_fg_substructures_of_countable`

English:
instance Substructure.instCountable_fg_substructures_of_countable
  signature: [Countable M]
  body: countable_fg_substructures_of_countable

中文:
实例 子结构.instCountable_fg_substructures_of_countable
  签名: [可数 M]
  定义体: countable_fg_substructures_of_countable

Depends on / 依赖: countable_fg_substructures_of_countable
-/
instance Substructure.instCountable_fg_substructures_of_countable [Countable M] :
    Countable { S : L.Substructure M // S.FG } :=
  countable_fg_substructures_of_countable

end Language

end FirstOrder
