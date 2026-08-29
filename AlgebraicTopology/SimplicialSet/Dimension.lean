/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Dimension of a simplicial set

For a simplicial set `X` and `d : ℕ`, we introduce a typeclass
`X.HasDimensionLT d` saying that the dimension of `X` is `< d`,
i.e. all nondegenerate simplices of `X` are of dimension `< d`.

-/

public section

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-- A simplicial set `X` has dimension `< d` iff for any `n : ℕ`
such that `d ≤ n`, all `n`-simplices are degenerate. -/
@[mk_iff]
/--
Definition of `HasDimensionLT` / `HasDimensionLT` 的定义

English:
class HasDimensionLT
  parameters: (X : SSet.{u}) (d : Nat)
  axioms and operations (1):
    - degenerate_eq_top((n : Nat) (hn : d <= n)) : X.degenerate n = ⊤

中文:
类 有DimensionLT
  参数: (X : SSet.{u}) (d : 自然数)
  公理与运算 (1 个):
    - degenerate_eq_top((n : 自然数) (hn : d <= n)) : X.degenerate n = ⊤
-/
class HasDimensionLT (X : SSet.{u}) (d : Nat) : Prop where
  degenerate_eq_top (n : Nat) (hn : d <= n) : X.degenerate n = ⊤

/--
Definition of `HasDimensionLE` / `HasDimensionLE` 的定义

English:
abbreviation HasDimensionLE
  signature: (X : SSet.{u}) (d : Nat)
  body: X.HasDimensionLT (d + 1)

中文:
缩写 HasDimensionLE
  签名: (X : SSet.{u}) (d : 自然数)
  定义体: X.HasDimensionLT (d + 1)

Depends on / 依赖: HasDimensionLT, X.HasDimensionLT
-/
abbrev HasDimensionLE (X : SSet.{u}) (d : Nat) := X.HasDimensionLT (d + 1)

section

variable (X : SSet.{u}) (d : Nat) [X.HasDimensionLT d] (n : Nat)

/--
lemma `degenerate_eq_univ_of_hasDimensionLT` / 引理 `degenerate_eq_univ_of_hasDimensionLT`

English:
lemma degenerate_eq_univ_of_hasDimensionLT
  given: (hn : d <= n := by lia)
  statement: X.degenerate n = Set.univ
  proof: HasDimensionLT.degenerate_eq_top n hn

中文:
引理 degenerate_eq_univ_of_hasDimensionLT
  条件: (hn : d <= n := by lia)
  结论: X.degenerate n = 集合.univ
  证明: HasDimensionLT.degenerate_eq_top n hn

Depends on / 依赖: HasDimensionLT, HasDimensionLT.degenerate_eq_top, Set.univ, X.degenerate, degenerate, degenerate_eq_top
-/
lemma degenerate_eq_univ_of_hasDimensionLT (hn : d <= n := by lia) : X.degenerate n = Set.univ :=
  HasDimensionLT.degenerate_eq_top n hn

/--
lemma `nonDegenerate_eq_empty_of_hasDimensionLT` / 引理 `nonDegenerate_eq_empty_of_hasDimensionLT`

English:
lemma nonDegenerate_eq_empty_of_hasDimensionLT
  given: (hn : d <= n := by lia)
  statement: X.nonDegenerate n = ∅
  proof: by
  simp [nonDegenerate, X.degenerate_eq_univ_of_hasDimensionLT d n hn]

@[deprecated (since := "2026-04-06")]
alias degenerate_eq_top_of_hasDimensionLT := degenerate_eq_univ_of_hasDimensionLT
@[deprecated (since := "2026-04-06")]
alias nonDegenerate_eq_bot_of_hasDimensionLT := nonDegenerate_eq_emp

中文:
引理 nonDegenerate_eq_empty_of_hasDimensionLT
  条件: (hn : d <= n := by lia)
  结论: X.nonDegenerate n = ∅
  证明: by
  simp [nonDegenerate, X.degenerate_eq_univ_of_hasDimensionLT d n hn]

@[deprecated (since := "2026-04-06")]
alias degenerate_eq_top_of_hasDimensionLT := degenerate_eq_univ_of_hasDimensionLT
@[deprecated (since := "2026-04-06")]
alias nonDegenerate_eq_bot_of_hasDimensionLT := nonDegenerate_eq_emp

Depends on / 依赖: X.degenerate_eq_univ_of_hasDimensionLT, X.nonDegenerate, degenerate_eq_univ_of_hasDimensionLT, nonDegenerate
-/
lemma nonDegenerate_eq_empty_of_hasDimensionLT (hn : d <= n := by lia) : X.nonDegenerate n = ∅ := by
  simp [nonDegenerate, X.degenerate_eq_univ_of_hasDimensionLT d n hn]

@[deprecated (since := "2026-04-06")]
alias degenerate_eq_top_of_hasDimensionLT := degenerate_eq_univ_of_hasDimensionLT
@[deprecated (since := "2026-04-06")]
alias nonDegenerate_eq_bot_of_hasDimensionLT := nonDegenerate_eq_empty_of_hasDimensionLT

/--
lemma `dim_lt_of_nonDegenerate` / 引理 `dim_lt_of_nonDegenerate`

English:
lemma dim_lt_of_nonDegenerate
  statement: {n : Nat} (x : X.nonDegenerate n) (d : Nat)
  proof: by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nonDegenerate_eq_empty_of_hasDimensionLT d n this] at hx

中文:
引理 dim_lt_of_nonDegenerate
  结论: {n : 自然数} (x : X.nonDegenerate n) (d : 自然数)
  证明: by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nonDegenerate_eq_empty_of_hasDimensionLT d n this] at hx

Depends on / 依赖: X.nonDegenerate_eq_empty_of_hasDimensionLT, nonDegenerate_eq_empty_of_hasDimensionLT
-/
lemma dim_lt_of_nonDegenerate {n : Nat} (x : X.nonDegenerate n) (d : Nat)
    [X.HasDimensionLT d] : n < d := by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nonDegenerate_eq_empty_of_hasDimensionLT d n this] at hx

/--
lemma `dim_le_of_nonDegenerate` / 引理 `dim_le_of_nonDegenerate`

English:
lemma dim_le_of_nonDegenerate
  statement: {n : Nat} (x : X.nonDegenerate n) (d : Nat)
  proof: Nat.le_of_lt_succ (X.dim_lt_of_nonDegenerate x (d + 1))

中文:
引理 dim_le_of_nonDegenerate
  结论: {n : 自然数} (x : X.nonDegenerate n) (d : 自然数)
  证明: Nat.le_of_lt_succ (X.dim_lt_of_nonDegenerate x (d + 1))

Depends on / 依赖: Nat.le_of_lt_succ, X.dim_lt_of_nonDegenerate, dim_lt_of_nonDegenerate, le_of_lt_succ
-/
lemma dim_le_of_nonDegenerate {n : Nat} (x : X.nonDegenerate n) (d : Nat)
    [X.HasDimensionLE d] : n <= d :=
  Nat.le_of_lt_succ (X.dim_lt_of_nonDegenerate x (d + 1))

/--
lemma `hasDimensionLT_of_le` / 引理 `hasDimensionLT_of_le`

English:
lemma hasDimensionLT_of_le
  given: (hn : d <= n := by lia)
  statement: HasDimensionLT X n where
  proof: X.degenerate_eq_univ_of_hasDimensionLT d i (hn.trans hi)

中文:
引理 hasDimensionLT_of_le
  条件: (hn : d <= n := by lia)
  结论: 有DimensionLT X n where
  证明: X.degenerate_eq_univ_of_hasDimensionLT d i (hn.trans hi)

Depends on / 依赖: HasDimensionLT, X.degenerate_eq_univ_of_hasDimensionLT, degenerate_eq_top, degenerate_eq_univ_of_hasDimensionLT, hn.trans
-/
lemma hasDimensionLT_of_le (hn : d <= n := by lia) : HasDimensionLT X n where
  degenerate_eq_top i hi :=
    X.degenerate_eq_univ_of_hasDimensionLT d i (hn.trans hi)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasDimensionLT
  signature: X n] (k
  body: X.hasDimensionLT_of_le n _

中文:
实例 [有DimensionLT
  签名: X n] (k
  定义体: X.hasDimensionLT_of_le n _

Depends on / 依赖: X.hasDimensionLT_of_le, hasDimensionLT_of_le
-/
instance [HasDimensionLT X n] (k : Nat) : HasDimensionLT X (n + k) :=
  X.hasDimensionLT_of_le n _

end

namespace Subcomplex

variable {X : SSet.{u}}

set_option backward.isDefEq.respectTransparency false in
instance (d : Nat) [X.HasDimensionLT d] (A : X.Subcomplex) : HasDimensionLT A d where
  degenerate_eq_top (n : Nat) (hd : d <= n) := by
    ext x
    simp [A.mem_degenerate_iff, X.degenerate_eq_univ_of_hasDimensionLT d n hd]

/--
lemma `le_iff_of_hasDimensionLT` / 引理 `le_iff_of_hasDimensionLT`

English:
lemma le_iff_of_hasDimensionLT
  given: (A B : X.Subcomplex) (d : Nat) [X.HasDimensionLT d]
  proof: by
  refine ⟨fun h i hi a ⟨ha, _⟩ => h _ ha, fun h => ?_⟩
  rw [le_iff_contains_nonDegenerate]
  rintro n x hx
  exact h _ (X.dim_lt_of_nonDegenerate x d) ⟨hx, x.prop⟩

中文:
引理 le_iff_of_hasDimensionLT
  条件: (A B : X.子复形) (d : 自然数) [X.有DimensionLT d]
  证明: by
  refine ⟨fun h i hi a ⟨ha, _⟩ => h _ ha, fun h => ?_⟩
  rw [le_iff_contains_nonDegenerate]
  rintro n x hx
  exact h _ (X.dim_lt_of_nonDegenerate x d) ⟨hx, x.prop⟩

Depends on / 依赖: X.dim_lt_of_nonDegenerate, dim_lt_of_nonDegenerate, le_iff_contains_nonDegenerate, x.prop
-/
lemma le_iff_of_hasDimensionLT (A B : X.Subcomplex) (d : Nat) [X.HasDimensionLT d] :
    A <= B ↔ forall i < d, A.obj _ inter X.nonDegenerate i subseteq B.obj (op ⦋i⦌) := by
  refine ⟨fun h i hi a ⟨ha, _⟩ => h _ ha, fun h => ?_⟩
  rw [le_iff_contains_nonDegenerate]
  rintro n x hx
  exact h _ (X.dim_lt_of_nonDegenerate x d) ⟨hx, x.prop⟩

/--
lemma `eq_top_iff_of_hasDimensionLT` / 引理 `eq_top_iff_of_hasDimensionLT`

English:
lemma eq_top_iff_of_hasDimensionLT
  given: (A : X.Subcomplex) (d : Nat) [X.HasDimensionLT d]
  proof: by
  simp [← top_le_iff, le_iff_of_hasDimensionLT ⊤ A d]

中文:
引理 eq_top_iff_of_hasDimensionLT
  条件: (A : X.子复形) (d : 自然数) [X.有DimensionLT d]
  证明: by
  simp [← top_le_iff, le_iff_of_hasDimensionLT ⊤ A d]

Depends on / 依赖: le_iff_of_hasDimensionLT, top_le_iff
-/
lemma eq_top_iff_of_hasDimensionLT (A : X.Subcomplex) (d : Nat) [X.HasDimensionLT d] :
    A = ⊤ ↔ forall i < d, X.nonDegenerate i subseteq A.obj _ := by
  simp [← top_le_iff, le_iff_of_hasDimensionLT ⊤ A d]

end Subcomplex

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasDimensionLT_of_mono` / 引理 `hasDimensionLT_of_mono`

English:
lemma hasDimensionLT_of_mono
  statement: {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : Nat)
  proof: by
    ext x
    rw [← degenerate_iff_of_isIso (Subcomplex.toRange f)]; rw [Subcomplex.mem_degenerate_iff]; rw [Y.degenerate_eq_univ_of_hasDimensionLT d n hn]
    simp

中文:
引理 hasDimensionLT_of_mono
  结论: {X Y : SSet.{u}} (f : X ⟶ Y) [单态射 f] (d : 自然数)
  证明: by
    ext x
    rw [← degenerate_iff_of_isIso (Subcomplex.toRange f)]; rw [Subcomplex.mem_degenerate_iff]; rw [Y.degenerate_eq_univ_of_hasDimensionLT d n hn]
    simp

Depends on / 依赖: Subcomplex, Subcomplex.mem_degenerate_iff, Subcomplex.toRange, Y.degenerate_eq_univ_of_hasDimensionLT, degenerate_eq_univ_of_hasDimensionLT, degenerate_iff_of_isIso, mem_degenerate_iff, toRange
-/
lemma hasDimensionLT_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : Nat)
    [Y.HasDimensionLT d] : X.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    rw [← degenerate_iff_of_isIso (Subcomplex.toRange f)]; rw [Subcomplex.mem_degenerate_iff]; rw [Y.degenerate_eq_univ_of_hasDimensionLT d n hn]
    simp

/--
lemma `Subcomplex.hasDimensionLT_of_le` / 引理 `Subcomplex.hasDimensionLT_of_le`

English:
lemma Subcomplex.hasDimensionLT_of_le
  proof: hasDimensionLT_of_mono (Subcomplex.homOfLE h) d

中文:
引理 子复形.hasDimensionLT_of_le
  证明: hasDimensionLT_of_mono (Subcomplex.homOfLE h) d

Depends on / 依赖: Subcomplex, Subcomplex.homOfLE, hasDimensionLT_of_mono, homOfLE
-/
lemma Subcomplex.hasDimensionLT_of_le
    {X : SSet.{u}} {A B : X.Subcomplex} (h : A <= B) (d : Nat) [HasDimensionLT B d] :
    HasDimensionLT A d :=
  hasDimensionLT_of_mono (Subcomplex.homOfLE h) d

/--
lemma `hasDimensionLT_of_epi` / 引理 `hasDimensionLT_of_epi`

English:
lemma hasDimensionLT_of_epi
  statement: {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f] (d : Nat)
  proof: by
    ext y
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := epi_iff_surjective (f := (f.app (op ⦋n⦌))).1 inferInstance y
    apply degenerate_app_apply
    simp [X.degenerate_eq_univ_of_hasDimensionLT d n hn]

中文:
引理 hasDimensionLT_of_epi
  结论: {X Y : SSet.{u}} (f : X ⟶ Y) [满态射 f] (d : 自然数)
  证明: by
    ext y
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := epi_iff_surjective (f := (f.app (op ⦋n⦌))).1 inferInstance y
    apply degenerate_app_apply
    simp [X.degenerate_eq_univ_of_hasDimensionLT d n hn]

Depends on / 依赖: Set.mem_univ, Set.top_eq_univ, X.degenerate_eq_univ_of_hasDimensionLT, degenerate_app_apply, degenerate_eq_univ_of_hasDimensionLT, epi_iff_surjective, f.app, iff_true, mem_univ, top_eq_univ
-/
lemma hasDimensionLT_of_epi {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f] (d : Nat)
    [X.HasDimensionLT d] : Y.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext y
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := epi_iff_surjective (f := (f.app (op ⦋n⦌))).1 inferInstance y
    apply degenerate_app_apply
    simp [X.degenerate_eq_univ_of_hasDimensionLT d n hn]

/--
lemma `hasDimensionLT_iff_of_iso` / 引理 `hasDimensionLT_iff_of_iso`

English:
lemma hasDimensionLT_iff_of_iso
  given: {X Y : SSet.{u}} (e : X ≅ Y) (d : Nat)
  proof: ⟨fun _ => hasDimensionLT_of_epi e.hom d, fun _ => hasDimensionLT_of_epi e.inv d⟩

中文:
引理 hasDimensionLT_iff_of_iso
  条件: {X Y : SSet.{u}} (e : X ≅ Y) (d : 自然数)
  证明: ⟨fun _ => hasDimensionLT_of_epi e.hom d, fun _ => hasDimensionLT_of_epi e.inv d⟩

Depends on / 依赖: e.hom, e.inv, hasDimensionLT_of_epi
-/
lemma hasDimensionLT_iff_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (d : Nat) :
    X.HasDimensionLT d ↔ Y.HasDimensionLT d :=
  ⟨fun _ => hasDimensionLT_of_epi e.hom d, fun _ => hasDimensionLT_of_epi e.inv d⟩

instance {X Y : SSet.{u}} (f : X ⟶ Y) (d : Nat) [X.HasDimensionLT d] :
    HasDimensionLT (Subcomplex.range f) d :=
  hasDimensionLT_of_epi (Subcomplex.toRange f) d

/--
lemma `hasDimensionLT_iSup_iff` / 引理 `hasDimensionLT_iSup_iff`

English:
lemma hasDimensionLT_iSup_iff
  given: {X : SSet.{u}} {ι : Type*} (A : ι -> X.Subcomplex) (d : Nat)
  proof: by
  simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff]
  aesop

中文:
引理 hasDimensionLT_iSup_iff
  条件: {X : SSet.{u}} {ι : 类型} (A : ι -> X.子复形) (d : 自然数)
  证明: by
  simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff]
  aesop

Depends on / 依赖: Subcomplex, Subcomplex.degenerate_eq_top_iff, degenerate_eq_top_iff, hasDimensionLT_iff
-/
lemma hasDimensionLT_iSup_iff {X : SSet.{u}} {ι : Type*} (A : ι -> X.Subcomplex) (d : Nat) :
    HasDimensionLT (⨆ i, A i :) d ↔ forall i, HasDimensionLT (A i) d := by
  simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff]
  aesop

/--
lemma `hasDimensionLT_subcomplex_top_iff` / 引理 `hasDimensionLT_subcomplex_top_iff`

English:
lemma hasDimensionLT_subcomplex_top_iff
  given: (X : SSet.{u}) (d : Nat)
  proof: hasDimensionLT_iff_of_iso (Subcomplex.topIso X) _

中文:
引理 hasDimensionLT_subcomplex_top_iff
  条件: (X : SSet.{u}) (d : 自然数)
  证明: hasDimensionLT_iff_of_iso (Subcomplex.topIso X) _

Depends on / 依赖: Subcomplex, Subcomplex.topIso, hasDimensionLT_iff_of_iso, topIso
-/
lemma hasDimensionLT_subcomplex_top_iff (X : SSet.{u}) (d : Nat) :
    HasDimensionLT (⊤ : X.Subcomplex) d ↔ X.HasDimensionLT d :=
  hasDimensionLT_iff_of_iso (Subcomplex.topIso X) _

instance {X : SSet.{u}} (n : Nat) : HasDimensionLT (⊥ : X.Subcomplex) n where
  degenerate_eq_top k hk := by
    ext ⟨x, hx⟩
    tauto

end SSet
