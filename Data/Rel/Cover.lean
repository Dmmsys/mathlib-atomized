/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Separated

/-!
# Covers in a uniform space

This file defines covers, aka nets, which are a quantitative notion of compactness given an
entourage.

A `U`-cover of a set `s` is a set `N` such that every element of `s` is `U`-close to some element of
`N`.

The concept of uniform covers is used to define two further notions of covering:
* Metric covers: `Metric.IsCover`, defined using the distance entourage.
* Dynamical covers: `Dynamics.IsDynCoverOf`, defined using the dynamical entourage.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

@[expose] public section

open Set

namespace SetRel
variable {X : Type*} {U V : SetRel X X} {s t N N₁ N₂ : Set X} {x : X}

/--
Definition of `IsCover` / `IsCover` 的定义

English:
definition IsCover
  signature: (U : SetRel X X) (s N : Set X)
  body: forall ⦃x⦄, x in s -> exists y in N, x ~[U] y

中文:
定义 IsCover
  签名: (U : SetRel X X) (s N : 集合 X)
  定义体: forall ⦃x⦄, x in s -> exists y in N, x ~[U] y
-/
def IsCover (U : SetRel X X) (s N : Set X) : Prop := forall ⦃x⦄, x in s -> exists y in N, x ~[U] y

/--
lemma `IsCover.empty` / 引理 `IsCover.empty`

English:
lemma IsCover.empty
  statement: IsCover U ∅ N
  proof: by simp [IsCover]

中文:
引理 IsCover.empty
  结论: IsCover U ∅ N
  证明: by simp [IsCover]
-/
@[simp] lemma IsCover.empty : IsCover U ∅ N := by simp [IsCover]

/--
lemma `isCover_empty_right` / 引理 `isCover_empty_right`

English:
lemma isCover_empty_right
  statement: IsCover U s ∅ ↔ s = ∅
  proof: by
  simp [IsCover, eq_empty_iff_forall_notMem]

protected nonrec lemma IsCover.nonempty (hsN : IsCover U s N) (hs : s.Nonempty) : N.Nonempty :=
  let ⟨_x, hx⟩ := hs; let ⟨y, hy, _⟩ := hsN hx; ⟨y, hy⟩

中文:
引理 isCover_empty_right
  结论: IsCover U s ∅ ↔ s = ∅
  证明: by
  simp [IsCover, eq_empty_iff_forall_notMem]

protected nonrec lemma IsCover.nonempty (hsN : IsCover U s N) (hs : s.Nonempty) : N.Nonempty :=
  let ⟨_x, hx⟩ := hs; let ⟨y, hy, _⟩ := hsN hx; ⟨y, hy⟩
-/
@[simp] lemma isCover_empty_right : IsCover U s ∅ ↔ s = ∅ := by
  simp [IsCover, eq_empty_iff_forall_notMem]

protected nonrec lemma IsCover.nonempty (hsN : IsCover U s N) (hs : s.Nonempty) : N.Nonempty :=
  let ⟨_x, hx⟩ := hs; let ⟨y, hy, _⟩ := hsN hx; ⟨y, hy⟩

/--
lemma `IsCover.refl` / 引理 `IsCover.refl`

English:
lemma IsCover.refl
  given: (U : SetRel X X) [U.IsRefl] (s : Set X)
  statement: IsCover U s s
  proof: fun a ha => ⟨a, ha, U.rfl⟩

中文:
引理 IsCover.refl
  条件: (U : SetRel X X) [U.IsRefl] (s : 集合 X)
  结论: IsCover U s s
  证明: fun a ha => ⟨a, ha, U.rfl⟩
-/
@[simp] lemma IsCover.refl (U : SetRel X X) [U.IsRefl] (s : Set X) : IsCover U s s :=
  fun a ha => ⟨a, ha, U.rfl⟩

/--
lemma `IsCover.rfl` / 引理 `IsCover.rfl`

English:
lemma IsCover.rfl
  given: {U : SetRel X X} [U.IsRefl] {s : Set X}
  statement: IsCover U s s
  proof: refl U s

中文:
引理 IsCover.rfl
  条件: {U : SetRel X X} [U.IsRefl] {s : 集合 X}
  结论: IsCover U s s
  证明: refl U s

Depends on / 依赖: EuclideanSpace, MeasureTheory, MeasureTheory.isAddHaarMeasure_hausdorffMeasure, isAddHaarMeasure_hausdorffMeasure
-/
lemma IsCover.rfl {U : SetRel X X} [U.IsRefl] {s : Set X} : IsCover U s s := refl U s

/--
lemma `isCover_univ` / 引理 `isCover_univ`

English:
lemma isCover_univ
  statement: IsCover univ s N ↔ (s.Nonempty -> N.Nonempty)
  proof: by
  simp [IsCover, Set.Nonempty]

中文:
引理 isCover_univ
  结论: IsCover univ s N ↔ (s.非空 -> N.非空)
  证明: by
  simp [IsCover, Set.Nonempty]
-/
@[simp] protected lemma isCover_univ : IsCover univ s N ↔ (s.Nonempty -> N.Nonempty) := by
  simp [IsCover, Set.Nonempty]

/--
lemma `IsCover.mono` / 引理 `IsCover.mono`

English:
lemma IsCover.mono
  given: (hN : N₁ subseteq N₂) (h₁ : IsCover U s N₁)
  statement: IsCover U s N₂
  proof: fun _x hx => let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩

中文:
引理 IsCover.mono
  条件: (hN : N₁ subseteq N₂) (h₁ : IsCover U s N₁)
  结论: IsCover U s N₂
  证明: fun _x hx => let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩
-/
lemma IsCover.mono (hN : N₁ subseteq N₂) (h₁ : IsCover U s N₁) : IsCover U s N₂ :=
  fun _x hx => let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩

/--
lemma `IsCover.anti` / 引理 `IsCover.anti`

English:
lemma IsCover.anti
  given: (hst : s subseteq t) (ht : IsCover U t N)
  statement: IsCover U s N
  proof: fun _x hx => ht hst hx

中文:
引理 IsCover.anti
  条件: (hst : s subseteq t) (ht : IsCover U t N)
  结论: IsCover U s N
  证明: fun _x hx => ht hst hx
-/
lemma IsCover.anti (hst : s subseteq t) (ht : IsCover U t N) : IsCover U s N := fun _x hx => ht hst hx

/--
lemma `IsCover.mono_entourage` / 引理 `IsCover.mono_entourage`

English:
lemma IsCover.mono_entourage
  given: (hUV : U subseteq V) (hU : IsCover U s N)
  statement: IsCover V s N
  proof: fun _x hx => let ⟨y, hy, hxy⟩ := hU hx; ⟨y, hy, hUV hxy⟩

中文:
引理 IsCover.mono_entourage
  条件: (hUV : U subseteq V) (hU : IsCover U s N)
  结论: IsCover V s N
  证明: fun _x hx => let ⟨y, hy, hxy⟩ := hU hx; ⟨y, hy, hUV hxy⟩
-/
lemma IsCover.mono_entourage (hUV : U subseteq V) (hU : IsCover U s N) : IsCover V s N :=
  fun _x hx => let ⟨y, hy, hxy⟩ := hU hx; ⟨y, hy, hUV hxy⟩

/--
lemma `IsCover.union` / 引理 `IsCover.union`

English:
lemma IsCover.union
  given: (hs : IsCover U s N₁) (ht : IsCover U t N₂)
  statement: IsCover U (s union t) (N₁ union N₂)
  proof: fun
  | _x, .inl hx => let ⟨y, hy, hxy⟩ := hs hx; ⟨y, .inl hy, hxy⟩
  | _x, .inr hx => let ⟨y, hy, hxy⟩ := ht hx; ⟨y, .inr hy, hxy⟩

中文:
引理 IsCover.union
  条件: (hs : IsCover U s N₁) (ht : IsCover U t N₂)
  结论: IsCover U (s union t) (N₁ union N₂)
  证明: fun
  | _x, .inl hx => let ⟨y, hy, hxy⟩ := hs hx; ⟨y, .inl hy, hxy⟩
  | _x, .inr hx => let ⟨y, hy, hxy⟩ := ht hx; ⟨y, .inr hy, hxy⟩
-/
lemma IsCover.union (hs : IsCover U s N₁) (ht : IsCover U t N₂) : IsCover U (s union t) (N₁ union N₂) := fun
  | _x, .inl hx => let ⟨y, hy, hxy⟩ := hs hx; ⟨y, .inl hy, hxy⟩
  | _x, .inr hx => let ⟨y, hy, hxy⟩ := ht hx; ⟨y, .inr hy, hxy⟩

/--
lemma `IsCover.of_maximal_isSeparated` / 引理 `IsCover.of_maximal_isSeparated`

English:
lemma IsCover.of_maximal_isSeparated
  statement: [U.IsRefl] [U.IsSymm]
  proof: by
  rintro x hx
  by_contra! h
simpa [U.rfl] using h _ hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert fun y hy hxy => (h y hy hxy).elim⟩ (subset_insert _ _) (mem_insert _ _)

中文:
引理 IsCover.of_maximal_isSeparated
  结论: [U.IsRefl] [U.是Symm]
  证明: by
  rintro x hx
  by_contra! h
simpa [U.rfl] using h _ hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert fun y hy hxy => (h y hy hxy).elim⟩ (subset_insert _ _) (mem_insert _ _)

Depends on / 依赖: U.rfl, insert, insert_subset_iff, mem_insert, subset_insert
-/
lemma IsCover.of_maximal_isSeparated [U.IsRefl] [U.IsSymm]
    (hN : Maximal (fun N => N subseteq s ∧ IsSeparated U N) N) : IsCover U s N := by
  rintro x hx
  by_contra! h
simpa [U.rfl] using h _ hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert fun y hy hxy => (h y hy hxy).elim⟩ (subset_insert _ _) (mem_insert _ _)

/--
lemma `isCover_id` / 引理 `isCover_id`

English:
lemma isCover_id
  statement: IsCover .id s N ↔ s subseteq N
  proof: by simp [IsCover, subset_def]

中文:
引理 isCover_id
  结论: IsCover .id s N ↔ s subseteq N
  证明: by simp [IsCover, subset_def]
-/
@[simp] lemma isCover_id : IsCover .id s N ↔ s subseteq N := by simp [IsCover, subset_def]

end SetRel
