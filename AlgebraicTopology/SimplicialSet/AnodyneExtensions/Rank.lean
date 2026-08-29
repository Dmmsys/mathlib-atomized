/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
public import Mathlib.Order.OrderIsoNat

/-!
# Rank functions for pairings

We introduce types of (weak) rank functions for a pairing `P`
of a subcomplex `A` of a simplicial set `X`. These are
functions `f : P.II → α` such that `P.AncestralRel x y` implies `f x < f y`
(in the weak case, we require this only under the additional condition
that `x` and `y` are of the same dimension). Such rank functions
are used in order to show that the ancestrality relation on `P.II` is well founded,
i.e. that `P` is regular (when we already know `P` is proper).
Conversely, we shall show that if `P` is regular,
then `P.RankFunction ℕ` is non empty (TODO @joelriou).

(We also introduce similar definitions for the structure `PairingCore`.)


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
  (α : Type v) [PartialOrder α]

/--
Definition of `RankFunction` / `RankFunction` 的定义

English:
structure RankFunction
  parameters: where
  axioms and operations (2):
    - rank : P.II -> α
    - lt({x y : P.II}) : P.AncestralRel x y -> rank x < rank y

中文:
结构 RankFunction
  参数: where
  公理与运算 (2 个):
    - rank : P.II -> α
    - lt({x y : P.II}) : P.AncestralRel x y -> rank x < rank y
-/
structure RankFunction where
  /-- the rank function -/
  rank : P.II -> α
  lt {x y : P.II} : P.AncestralRel x y -> rank x < rank y

namespace RankFunction

variable {P α} [WellFoundedLT α] (f : P.RankFunction α)

include f

/--
lemma `wf_ancestralRel` / 引理 `wf_ancestralRel`

English:
lemma wf_ancestralRel
  statement: WellFounded P.AncestralRel
  proof: by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun ⟨g, hg⟩ => not_strictAnti_of_wellFoundedLT (f.rank ∘ g)
    (strictAnti_nat_of_succ_lt (fun n => f.lt (hg n)))⟩

中文:
引理 wf_ancestralRel
  结论: 良基 P.AncestralRel
  证明: by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun ⟨g, hg⟩ => not_strictAnti_of_wellFoundedLT (f.rank ∘ g)
    (strictAnti_nat_of_succ_lt (fun n => f.lt (hg n)))⟩

Depends on / 依赖: f.lt, f.rank, not_strictAnti_of_wellFoundedLT, strictAnti_nat_of_succ_lt, wellFounded_iff_isEmpty_descending_chain
-/
lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun ⟨g, hg⟩ => not_strictAnti_of_wellFoundedLT (f.rank ∘ g)
    (strictAnti_nat_of_succ_lt (fun n => f.lt (hg n)))⟩

/--
lemma `isRegular` / 引理 `isRegular`

English:
lemma isRegular
  given: [P.IsProper]
  statement: P.IsRegular where
  proof: f.wf_ancestralRel

中文:
引理 isRegular
  条件: [P.是真]
  结论: P.是正则 where
  证明: f.wf_ancestralRel

Depends on / 依赖: f.wf_ancestralRel, wf_ancestralRel
-/
lemma isRegular [P.IsProper] : P.IsRegular where
  wf := f.wf_ancestralRel

end RankFunction

/--
Definition of `WeakRankFunction` / `WeakRankFunction` 的定义

English:
structure WeakRankFunction
  parameters: where
  axioms and operations (2):
    - rank : P.II -> α
    - lt({x y : P.II}) : P.AncestralRel x y -> x.1.dim = y.1.dim -> rank x < rank y

中文:
结构 WeakRankFunction
  参数: where
  公理与运算 (2 个):
    - rank : P.II -> α
    - lt({x y : P.II}) : P.AncestralRel x y -> x.1.dim = y.1.dim -> rank x < rank y
-/
structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : P.II -> α
  lt {x y : P.II} : P.AncestralRel x y -> x.1.dim = y.1.dim -> rank x < rank y

namespace WeakRankFunction

variable {P α} [WellFoundedLT α] [P.IsProper] (f : P.WeakRankFunction α)

include f

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `wf_ancestralRel` / 引理 `wf_ancestralRel`

English:
lemma wf_ancestralRel
  statement: WellFounded P.AncestralRel
  proof: by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨g, hg⟩ => ?_⟩
  obtain ⟨n₀, hn₀⟩ :=
    (wellFoundedGT_iff_monotone_chain_condition (α := Natᵒᵈ)).1
      inferInstance ⟨fun n => (g n).1.dim,
        monotone_nat_of_le_succ (fun n => (hg n).dim_le)⟩
  dsimp at hn₀
  refine not_stric

中文:
引理 wf_ancestralRel
  结论: 良基 P.AncestralRel
  证明: by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨g, hg⟩ => ?_⟩
  obtain ⟨n₀, hn₀⟩ :=
    (wellFoundedGT_iff_monotone_chain_condition (α := Natᵒᵈ)).1
      inferInstance ⟨fun n => (g n).1.dim,
        monotone_nat_of_le_succ (fun n => (hg n).dim_le)⟩
  dsimp at hn₀
  refine not_stric

Depends on / 依赖: add_assoc, dim_le, f.lt, f.rank, monotone_nat_of_le_succ, not_strictAnti_of_wellFoundedLT, strictAnti_nat_of_succ_lt, wellFoundedGT_iff_monotone_chain_condition, wellFounded_iff_isEmpty_descending_chain
-/
lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨g, hg⟩ => ?_⟩
  obtain ⟨n₀, hn₀⟩ :=
    (wellFoundedGT_iff_monotone_chain_condition (α := Natᵒᵈ)).1
      inferInstance ⟨fun n => (g n).1.dim,
        monotone_nat_of_le_succ (fun n => (hg n).dim_le)⟩
  dsimp at hn₀
  refine not_strictAnti_of_wellFoundedLT (fun n => f.rank (g (n₀ + n)))
    (strictAnti_nat_of_succ_lt (fun n => ?_))
  rw [← add_assoc]
  exact f.lt (hg _) (by rw [← hn₀ (n₀ + n + 1) (by lia), ← hn₀ (n₀ + n) (by lia)])

/--
lemma `isRegular` / 引理 `isRegular`

English:
lemma isRegular
  statement: P.IsRegular where
  proof: f.wf_ancestralRel

中文:
引理 isRegular
  结论: P.是正则 where
  证明: f.wf_ancestralRel

Depends on / 依赖: f.wf_ancestralRel, wf_ancestralRel
-/
lemma isRegular : P.IsRegular where
  wf := f.wf_ancestralRel

end WeakRankFunction

/-- The weak rank function attached to a rank function. -/
@[simps]
/--
Definition of `RankFunction.toWeakRankFunction` / `RankFunction.toWeakRankFunction` 的定义

English:
definition RankFunction.toWeakRankFunction
  signature: (f : P.RankFunction α)
  body: f.rank
  lt h _ := f.lt h

中文:
定义 RankFunction.toWeakRankFunction
  签名: (f : P.RankFunction α)
  定义体: f.rank
  lt h _ := f.lt h

Depends on / 依赖: f.rank
-/
def RankFunction.toWeakRankFunction (f : P.RankFunction α) :
    P.WeakRankFunction α where
  rank := f.rank
  lt h _ := f.lt h

end Pairing

namespace PairingCore

variable {X : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore)
  (α : Type v) [PartialOrder α]

/--
Definition of `RankFunction` / `RankFunction` 的定义

English:
structure RankFunction
  parameters: where
  axioms and operations (2):
    - rank : h.ι -> α
    - lt({x y : h.ι}) : h.AncestralRel x y -> rank x < rank y

中文:
结构 RankFunction
  参数: where
  公理与运算 (2 个):
    - rank : h.ι -> α
    - lt({x y : h.ι}) : h.AncestralRel x y -> rank x < rank y
-/
structure RankFunction where
  /-- the rank function -/
  rank : h.ι -> α
  lt {x y : h.ι} : h.AncestralRel x y -> rank x < rank y

/--
Definition of `WeakRankFunction` / `WeakRankFunction` 的定义

English:
structure WeakRankFunction
  parameters: where
  axioms and operations (2):
    - rank : h.ι -> α
    - lt({x y : h.ι}) : h.AncestralRel x y -> h.dim x = h.dim y -> rank x < rank y

中文:
结构 WeakRankFunction
  参数: where
  公理与运算 (2 个):
    - rank : h.ι -> α
    - lt({x y : h.ι}) : h.AncestralRel x y -> h.dim x = h.dim y -> rank x < rank y
-/
structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : h.ι -> α
  lt {x y : h.ι} : h.AncestralRel x y -> h.dim x = h.dim y -> rank x < rank y

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `rankFunctionEquiv` / `rankFunctionEquiv` 的定义

English:
definition rankFunctionEquiv
  signature: :
  body: { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := 

中文:
定义 rankFunctionEquiv
  签名: :
  定义体: { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := 

Depends on / 依赖: ancestralRel_iff, equivII, f.lt, f.rank, g.lt, g.rank, h.equivII, h.equivII.surjective, h.equivII.symm, invFun, left_inv, right_inv, surjective
-/
noncomputable def rankFunctionEquiv :
    h.RankFunction α ≃ h.pairing.RankFunction α where
  toFun f :=
    { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := by
        rw [ancestralRel_iff] at hxy
        exact g.lt hxy }
  left_inv _ := by simp
  right_inv _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `weakRankFunctionEquiv` / `weakRankFunctionEquiv` 的定义

English:
definition weakRankFunctionEquiv
  signature: :
  body: { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := 

中文:
定义 weakRankFunctionEquiv
  签名: :
  定义体: { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := 

Depends on / 依赖: ancestralRel_iff, equivII, f.lt, f.rank, g.lt, g.rank, h.equivII, h.equivII.surjective, h.equivII.symm, invFun, left_inv, right_inv, surjective
-/
noncomputable def weakRankFunctionEquiv :
    h.WeakRankFunction α ≃ h.pairing.WeakRankFunction α where
  toFun f :=
    { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := by
        rw [ancestralRel_iff] at hxy
        exact g.lt hxy }
  left_inv _ := by simp
  right_inv _ := by simp

variable {h α} [WellFoundedLT α]

/--
lemma `RankFunction.isRegular` / 引理 `RankFunction.isRegular`

English:
lemma RankFunction.isRegular
  given: [h.IsProper] (f : h.RankFunction α)
  statement: h.IsRegular
  proof: by
  rw [← isRegular_pairing_iff]
  exact (h.rankFunctionEquiv α f).isRegular

中文:
引理 RankFunction.isRegular
  条件: [h.是真] (f : h.RankFunction α)
  结论: h.是正则
  证明: by
  rw [← isRegular_pairing_iff]
  exact (h.rankFunctionEquiv α f).isRegular

Depends on / 依赖: h.rankFunctionEquiv, isRegular, isRegular_pairing_iff, rankFunctionEquiv
-/
lemma RankFunction.isRegular [h.IsProper] (f : h.RankFunction α) : h.IsRegular := by
  rw [← isRegular_pairing_iff]
  exact (h.rankFunctionEquiv α f).isRegular

/--
lemma `WeakRankFunction.isRegular` / 引理 `WeakRankFunction.isRegular`

English:
lemma WeakRankFunction.isRegular
  given: [h.IsProper] (f : h.WeakRankFunction α)
  statement: h.IsRegular
  proof: by
  rw [← isRegular_pairing_iff]
  exact (h.weakRankFunctionEquiv α f).isRegular

中文:
引理 WeakRankFunction.isRegular
  条件: [h.是真] (f : h.WeakRankFunction α)
  结论: h.是正则
  证明: by
  rw [← isRegular_pairing_iff]
  exact (h.weakRankFunctionEquiv α f).isRegular

Depends on / 依赖: h.weakRankFunctionEquiv, isRegular, isRegular_pairing_iff, weakRankFunctionEquiv
-/
lemma WeakRankFunction.isRegular [h.IsProper] (f : h.WeakRankFunction α) : h.IsRegular := by
  rw [← isRegular_pairing_iff]
  exact (h.weakRankFunctionEquiv α f).isRegular

end PairingCore

end SSet.Subcomplex
