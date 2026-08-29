/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.Data.Finite.Sigma

/-!
# Existence of a rank function to natural numbers

In this file, we show that if `P : A.Pairing` is
a regular pairing of subcomplex `A` of a simplicial set `X`,
then there exists a rank function for `P` with values in `ℕ`.

-/

@[expose] public section

universe u

open Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable (P : A.Pairing)

instance (y : P.II) : Finite { x // P.AncestralRel x y } := by
  let T := { x : P.II // P.AncestralRel x y }
  let U := Σ (d : Fin (P.p y).1.dim), ⦋d⦌ ⟶ ⦋(P.p y).1.1.1.1⦌
  let ψ : U -> X.S := fun ⟨d, f⟩ => S.mk (X.map f.op (P.p y).1.simplex)
  have h (t : T) : exists u, ψ u = t.1.1.toS := by
    obtain ⟨f, _, hf⟩ := N.le_iff_exists_mono.1 t.2.2.le
    refine ⟨⟨⟨t.1.1.dim, ?_⟩, f⟩, ?_⟩
    · simpa using SSet.N.dim_lt_of_lt t.2.2
    · rwa [SSet.S.ext_iff]
  choose φ hφ using h
  apply Finite.of_injective φ
  intro t₁ t₂ h
  rw [Subtype.ext_iff]; rw [Subtype.ext_iff]; rw [N.ext_iff]; rw [SSet.N.ext_iff]; rw [← hφ]; rw [← hφ]; rw [h]

section

variable {y : P.II} (hy : Acc P.AncestralRel y)

/--
Definition of `rank'` / `rank'` 的定义

English:
definition rank'
  signature: : Nat
  body: Acc.recOn hy (fun y _ r => ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)

中文:
定义 rank'
  签名: : 自然数
  定义体: Acc.recOn hy (fun y _ r => ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)

Depends on / 依赖: Acc.recOn, AncestralRel, P.AncestralRel
-/
noncomputable def rank' : Nat :=
  Acc.recOn hy (fun y _ r => ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)

/--
lemma `rank'_eq` / 引理 `rank'_eq`

English:
lemma rank'_eq
  proof: by
  change P.rank' (Acc.intro y fun _ => hy.inv) = _
  rfl

中文:
引理 rank'_eq
  证明: by
  change P.rank' (Acc.intro y fun _ => hy.inv) = _
  rfl
-/
lemma rank'_eq :
    P.rank' hy = ⨆ (x : { x // P.AncestralRel x y }), P.rank' (hy.inv x.2) + 1 := by
  change P.rank' (Acc.intro y fun _ => hy.inv) = _
  rfl

/--
lemma `rank'_lt` / 引理 `rank'_lt`

English:
lemma rank'_lt
  given: {x : P.II} (r : P.AncestralRel x y)
  proof: by
  rw [P.rank'_eq hy]; rw [← Nat.add_one_le_iff]
  exact le_csSup (Finite.bddAbove_range _) ⟨⟨x, r⟩, rfl⟩

中文:
引理 rank'_lt
  条件: {x : P.II} (r : P.AncestralRel x y)
  证明: by
  rw [P.rank'_eq hy]; rw [← Nat.add_one_le_iff]
  exact le_csSup (Finite.bddAbove_range _) ⟨⟨x, r⟩, rfl⟩
-/
lemma rank'_lt {x : P.II} (r : P.AncestralRel x y) :
    P.rank' (hy.inv r) < P.rank' hy := by
  rw [P.rank'_eq hy]; rw [← Nat.add_one_le_iff]
  exact le_csSup (Finite.bddAbove_range _) ⟨⟨x, r⟩, rfl⟩

end

section IsRegular

variable [P.IsRegular]

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: (x : P.II)
  body: P.rank' (P.wf.apply x)

中文:
定义 rank
  签名: (x : P.II)
  定义体: P.rank' (P.wf.apply x)

Depends on / 依赖: P.rank, P.wf.apply
-/
noncomputable def rank (x : P.II) : Nat :=
  P.rank' (P.wf.apply x)

variable {P} in
/--
lemma `rank_lt` / 引理 `rank_lt`

English:
lemma rank_lt
  given: {x y : P.II} (h : P.AncestralRel x y)
  proof: P.rank'_lt _ h

中文:
引理 rank_lt
  条件: {x y : P.II} (h : P.AncestralRel x y)
  证明: P.rank'_lt _ h

Depends on / 依赖: P.rank
-/
lemma rank_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank x < P.rank y :=
  P.rank'_lt _ h

/--
Definition of `rankFunction` / `rankFunction` 的定义

English:
definition rankFunction
  signature: : P.RankFunction Nat where
  body: P.rank
  lt := P.rank_lt

中文:
定义 rankFunction
  签名: : P.RankFunction 自然数 where
  定义体: P.rank
  lt := P.rank_lt

Depends on / 依赖: P.rank
-/
noncomputable def rankFunction : P.RankFunction Nat where
  rank := P.rank
  lt := P.rank_lt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (P.RankFunction Nat)
  body: ⟨P.rankFunction⟩

中文:
实例 :
  签名: 非空 (P.RankFunction 自然数)
  定义体: ⟨P.rankFunction⟩

Depends on / 依赖: P.rankFunction, rankFunction
-/
instance : Nonempty (P.RankFunction Nat) := ⟨P.rankFunction⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (P.WeakRankFunction Nat)
  body: ⟨P.rankFunction.toWeakRankFunction⟩

中文:
实例 :
  签名: 非空 (P.WeakRankFunction 自然数)
  定义体: ⟨P.rankFunction.toWeakRankFunction⟩

Depends on / 依赖: P.rankFunction.toWeakRankFunction, rankFunction, toWeakRankFunction
-/
instance : Nonempty (P.WeakRankFunction Nat) := ⟨P.rankFunction.toWeakRankFunction⟩

end IsRegular

/--
lemma `isRegular_iff_nonempty_rankFunction` / 引理 `isRegular_iff_nonempty_rankFunction`

English:
lemma isRegular_iff_nonempty_rankFunction
  given: [P.IsProper]
  proof: ⟨fun _ => inferInstance, fun ⟨h⟩ => h.isRegular⟩

中文:
引理 isRegular_iff_nonempty_rankFunction
  条件: [P.是真]
  证明: ⟨fun _ => inferInstance, fun ⟨h⟩ => h.isRegular⟩

Depends on / 依赖: h.isRegular, isRegular
-/
lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction Nat) :=
  ⟨fun _ => inferInstance, fun ⟨h⟩ => h.isRegular⟩

/--
lemma `isRegular_iff_nonempty_weakRankFunction` / 引理 `isRegular_iff_nonempty_weakRankFunction`

English:
lemma isRegular_iff_nonempty_weakRankFunction
  given: [P.IsProper]
  proof: ⟨fun _ => inferInstance, fun ⟨h⟩ => h.isRegular⟩

中文:
引理 isRegular_iff_nonempty_weakRankFunction
  条件: [P.是真]
  证明: ⟨fun _ => inferInstance, fun ⟨h⟩ => h.isRegular⟩

Depends on / 依赖: h.isRegular, isRegular
-/
lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction Nat) :=
  ⟨fun _ => inferInstance, fun ⟨h⟩ => h.isRegular⟩

end Pairing

namespace PairingCore

variable (P : A.PairingCore)

/--
lemma `isRegular_iff_nonempty_rankFunction` / 引理 `isRegular_iff_nonempty_rankFunction`

English:
lemma isRegular_iff_nonempty_rankFunction
  given: [P.IsProper]
  proof: by
  rw [← isRegular_pairing_iff]; rw [Pairing.isRegular_iff_nonempty_rankFunction]
  exact (P.rankFunctionEquiv Nat).symm.nonempty_congr

中文:
引理 isRegular_iff_nonempty_rankFunction
  条件: [P.是真]
  证明: by
  rw [← isRegular_pairing_iff]; rw [Pairing.isRegular_iff_nonempty_rankFunction]
  exact (P.rankFunctionEquiv Nat).symm.nonempty_congr

Depends on / 依赖: P.rankFunctionEquiv, Pairing, Pairing.isRegular_iff_nonempty_rankFunction, isRegular_iff_nonempty_rankFunction, isRegular_pairing_iff, nonempty_congr, rankFunctionEquiv, symm.nonempty_congr
-/
lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction Nat) := by
  rw [← isRegular_pairing_iff]; rw [Pairing.isRegular_iff_nonempty_rankFunction]
  exact (P.rankFunctionEquiv Nat).symm.nonempty_congr

/--
lemma `isRegular_iff_nonempty_weakRankFunction` / 引理 `isRegular_iff_nonempty_weakRankFunction`

English:
lemma isRegular_iff_nonempty_weakRankFunction
  given: [P.IsProper]
  proof: by
  rw [← isRegular_pairing_iff]; rw [Pairing.isRegular_iff_nonempty_weakRankFunction]
  exact (P.weakRankFunctionEquiv Nat).symm.nonempty_congr

中文:
引理 isRegular_iff_nonempty_weakRankFunction
  条件: [P.是真]
  证明: by
  rw [← isRegular_pairing_iff]; rw [Pairing.isRegular_iff_nonempty_weakRankFunction]
  exact (P.weakRankFunctionEquiv Nat).symm.nonempty_congr

Depends on / 依赖: P.weakRankFunctionEquiv, Pairing, Pairing.isRegular_iff_nonempty_weakRankFunction, isRegular_iff_nonempty_weakRankFunction, isRegular_pairing_iff, nonempty_congr, symm.nonempty_congr, weakRankFunctionEquiv
-/
lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction Nat) := by
  rw [← isRegular_pairing_iff]; rw [Pairing.isRegular_iff_nonempty_weakRankFunction]
  exact (P.weakRankFunctionEquiv Nat).symm.nonempty_congr

end PairingCore

end SSet.Subcomplex
