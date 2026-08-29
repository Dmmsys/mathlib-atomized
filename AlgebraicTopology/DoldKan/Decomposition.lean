/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.PInfty

/-!

# Decomposition of the Q endomorphisms

In this file, we obtain a lemma `decomposition_Q` which expresses
explicitly the projection `(Q q).f (n+1) : X _⦋n+1⦌ ⟶ X _⦋n+1⦌`
(`X : SimplicialObject C` with `C` a preadditive category) as
a sum of terms which are postcompositions with degeneracies.

(TODO @joelriou: when `C` is abelian, define the degenerate
subcomplex of the alternating face map complex of `X` and show
that it is a complement to the normalized Moore complex.)

Then, we introduce an ad hoc structure `MorphComponents X n Z` which
can be used in order to define morphisms `X _⦋n+1⦌ ⟶ Z` using the
decomposition provided by `decomposition_Q`. This shall play a critical
role in the proof that the functor
`N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  Opposite Simplicial

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X X' : SimplicialObject C}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `decomposition_Q` / 定理 `decomposition_Q`

English:
theorem decomposition_Q
  given: (n q : Nat)
  proof: by
  induction q with
  | zero =>
    simp only [Q_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero,
      Finset.filter_false, Finset.sum_empty]
  | succ q hq =>
    by_cases! hqn : n < q
    · rw [Q_is_eventually_constant (show n + 1 <= q by lia), hq]
      congr 1
      ext ⟨x, hx⟩
      simp_rw [Finset.mem_filter_univ]
      lia
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      rw [Q_succ]; rw [HomologicalComplex.sub_f_apply]; rw [HomologicalComplex.comp_f]; rw [hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, Nat.lt_succ_of_le hqn⟩
      rw [← @Finset.add_sum_erase _ _ _ _ _ _ q' (by simp [q'])]
      congr
      · have hnaq' : n = a + q := by lia
        simp only [(HigherFacesVanish.of_P q n).comp_Hσ_eq hnaq', q'.rev_eq hnaq', neg_neg]
        rfl
      · ext ⟨i, hi⟩
        simp_rw [Finset.mem_erase, Finset.mem_filter_univ, q', ne_eq, Fin.mk.injEq]
        lia

中文:
定理 decomposition_Q
  条件: (n q : 自然数)
  证明: by
  induction q with
  | zero =>
    simp only [Q_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero,
      Finset.filter_false, Finset.sum_empty]
  | succ q hq =>
    by_cases! hqn : n < q
    · rw [Q_is_eventually_constant (show n + 1 <= q by lia), hq]
      congr 1
      ext ⟨x, hx⟩
      simp_rw [Finset.mem_filter_univ]
      lia
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      rw [Q_succ]; rw [HomologicalComplex.sub_f_apply]; rw [HomologicalComplex.comp_f]; rw [hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, Nat.lt_succ_of_le hqn⟩
      rw [← @Finset.add_sum_erase _ _ _ _ _ _ q' (by simp [q'])]
      congr
      · have hnaq' : n = a + q := by lia
        simp only [(HigherFacesVanish.of_P q n).comp_Hσ_eq hnaq', q'.rev_eq hnaq', neg_neg]
        rfl
      · ext ⟨i, hi⟩
        simp_rw [Finset.mem_erase, Finset.mem_filter_univ, q', ne_eq, Fin.mk.injEq]
        lia

Depends on / 依赖: Finset, Finset.filter_false, Finset.mem_filter_univ, Finset.sum_empty, HomologicalComplex, HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, HomologicalComplex.zero_f_apply, Nat.le.dest, Nat.lt, Nat.not_lt_zero, Q_is_eventually_constant, Q_succ, Q_zero, add_comm, comp_f, conv_rhs, filter_false, mem_filter_univ, not_lt_zero
-/
theorem decomposition_Q (n q : Nat) :
    ((Q q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌) =
      ∑ i : Fin (n + 1) with i.val < q, (P i).f (n + 1) ≫ X.δ i.rev.succ ≫ X.σ (Fin.rev i) := by
  induction q with
  | zero =>
    simp only [Q_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero,
      Finset.filter_false, Finset.sum_empty]
  | succ q hq =>
    by_cases! hqn : n < q
    · rw [Q_is_eventually_constant (show n + 1 <= q by lia), hq]
      congr 1
      ext ⟨x, hx⟩
      simp_rw [Finset.mem_filter_univ]
      lia
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      rw [Q_succ]; rw [HomologicalComplex.sub_f_apply]; rw [HomologicalComplex.comp_f]; rw [hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, Nat.lt_succ_of_le hqn⟩
      rw [← @Finset.add_sum_erase _ _ _ _ _ _ q' (by simp [q'])]
      congr
      · have hnaq' : n = a + q := by lia
        simp only [(HigherFacesVanish.of_P q n).comp_Hσ_eq hnaq', q'.rev_eq hnaq', neg_neg]
        rfl
      · ext ⟨i, hi⟩
        simp_rw [Finset.mem_erase, Finset.mem_filter_univ, q', ne_eq, Fin.mk.injEq]
        lia

variable (X)

/-- The structure `MorphComponents` is an ad hoc structure that is used in
the proof that `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms. The fields are the data that are needed in order to
construct a morphism `X _⦋n+1⦌ ⟶ Z` (see `φ`) using the decomposition of the
identity given by `decomposition_Q n (n+1)`. -/
@[ext]
/--
Definition of `MorphComponents` / `MorphComponents` 的定义

English:
structure MorphComponents
  parameters: (n : Nat) (Z : C)
  axioms and operations (2):
    - a : X _⦋n + 1⦌ ⟶ Z
    - b : Fin (n + 1) -> (X _⦋n⦌ ⟶ Z)

中文:
结构 MorphComponents
  参数: (n : 自然数) (Z : C)
  公理与运算 (2 个):
    - a : X _⦋n + 1⦌ ⟶ Z
    - b : 有限集 (n + 1) -> (X _⦋n⦌ ⟶ Z)
-/
structure MorphComponents (n : Nat) (Z : C) where
  a : X _⦋n + 1⦌ ⟶ Z
  b : Fin (n + 1) -> (X _⦋n⦌ ⟶ Z)

namespace MorphComponents

variable {X} {n : Nat} {Z Z' : C} (f : MorphComponents X n Z) (g : X' ⟶ X) (h : Z ⟶ Z')

/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: {Z : C} (f : MorphComponents X n Z)
  body: PInfty.f (n + 1) ≫ f.a + ∑ i : Fin (n + 1), (P i).f (n + 1) ≫ X.δ i.rev.succ ≫
    f.b (Fin.rev i)

中文:
定义 φ
  签名: {Z : C} (f : MorphComponents X n Z)
  定义体: PInfty.f (n + 1) ≫ f.a + ∑ i : Fin (n + 1), (P i).f (n + 1) ≫ X.δ i.rev.succ ≫
    f.b (Fin.rev i)

Depends on / 依赖: Fin.rev, PInfty, PInfty.f, i.rev.succ
-/
def φ {Z : C} (f : MorphComponents X n Z) : X _⦋n + 1⦌ ⟶ Z :=
  PInfty.f (n + 1) ≫ f.a + ∑ i : Fin (n + 1), (P i).f (n + 1) ≫ X.δ i.rev.succ ≫
    f.b (Fin.rev i)

variable (X n)

/-- the canonical `MorphComponents` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : MorphComponents X n (X _⦋n + 1⦌) where
  body: PInfty.f (n + 1)
  b i := X.σ i

中文:
定义 id
  签名: : MorphComponents X n (X _⦋n + 1⦌) where
  定义体: PInfty.f (n + 1)
  b i := X.σ i

Depends on / 依赖: PInfty, PInfty.f
-/
def id : MorphComponents X n (X _⦋n + 1⦌) where
  a := PInfty.f (n + 1)
  b i := X.σ i

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `id_φ` / 定理 `id_φ`

English:
theorem id_φ
  statement: (id X n).φ = 𝟙 _
  proof: by
  simp only [← P_add_Q_f (n + 1) (n + 1), φ]
  congr 1
  · simp only [id, PInfty_f, P_f_idem]
  · exact Eq.trans (by simp) (decomposition_Q n (n + 1)).symm

中文:
定理 id_φ
  结论: (id X n).φ = 𝟙 _
  证明: by
  simp only [← P_add_Q_f (n + 1) (n + 1), φ]
  congr 1
  · simp only [id, PInfty_f, P_f_idem]
  · exact Eq.trans (by simp) (decomposition_Q n (n + 1)).symm

Depends on / 依赖: Eq.trans, PInfty_f, P_add_Q_f, P_f_idem, decomposition_Q
-/
theorem id_φ : (id X n).φ = 𝟙 _ := by
  simp only [← P_add_Q_f (n + 1) (n + 1), φ]
  congr 1
  · simp only [id, PInfty_f, P_f_idem]
  · exact Eq.trans (by simp) (decomposition_Q n (n + 1)).symm

variable {X n}

/-- A `MorphComponents` can be postcomposed with a morphism. -/
@[simps]
/--
Definition of `postComp` / `postComp` 的定义

English:
definition postComp
  signature: : MorphComponents X n Z' where
  body: f.a ≫ h
  b i := f.b i ≫ h

中文:
定义 postComp
  签名: : MorphComponents X n Z' where
  定义体: f.a ≫ h
  b i := f.b i ≫ h
-/
def postComp : MorphComponents X n Z' where
  a := f.a ≫ h
  b i := f.b i ≫ h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `postComp_φ` / 定理 `postComp_φ`

English:
theorem postComp_φ
  statement: (f.postComp h).φ = f.φ ≫ h
  proof: by
  unfold φ postComp
  simp only [add_comp, sum_comp, assoc]

中文:
定理 postComp_φ
  结论: (f.postComp h).φ = f.φ ≫ h
  证明: by
  unfold φ postComp
  simp only [add_comp, sum_comp, assoc]

Depends on / 依赖: add_comp, postComp, sum_comp
-/
theorem postComp_φ : (f.postComp h).φ = f.φ ≫ h := by
  unfold φ postComp
  simp only [add_comp, sum_comp, assoc]

/-- A `MorphComponents` can be precomposed with a morphism of simplicial objects. -/
@[simps]
/--
Definition of `preComp` / `preComp` 的定义

English:
definition preComp
  signature: : MorphComponents X' n Z where
  body: g.app (op ⦋n + 1⦌) ≫ f.a
  b i := g.app (op ⦋n⦌) ≫ f.b i

中文:
定义 preComp
  签名: : MorphComponents X' n Z where
  定义体: g.app (op ⦋n + 1⦌) ≫ f.a
  b i := g.app (op ⦋n⦌) ≫ f.b i

Depends on / 依赖: g.app
-/
def preComp : MorphComponents X' n Z where
  a := g.app (op ⦋n + 1⦌) ≫ f.a
  b i := g.app (op ⦋n⦌) ≫ f.b i

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `preComp_φ` / 定理 `preComp_φ`

English:
theorem preComp_φ
  statement: (f.preComp g).φ = g.app (op ⦋n + 1⦌) ≫ f.φ
  proof: by
  unfold φ preComp
  simp only [PInfty_f, comp_add]
  congr 1
  · simp
  · simp only [comp_sum, P_f_naturality_assoc, SimplicialObject.δ_naturality_assoc]

中文:
定理 preComp_φ
  结论: (f.preComp g).φ = g.app (op ⦋n + 1⦌) ≫ f.φ
  证明: by
  unfold φ preComp
  simp only [PInfty_f, comp_add]
  congr 1
  · simp
  · simp only [comp_sum, P_f_naturality_assoc, SimplicialObject.δ_naturality_assoc]

Depends on / 依赖: PInfty_f, P_f_naturality_assoc, SimplicialObject, comp_add, comp_sum, preComp
-/
theorem preComp_φ : (f.preComp g).φ = g.app (op ⦋n + 1⦌) ≫ f.φ := by
  unfold φ preComp
  simp only [PInfty_f, comp_add]
  congr 1
  · simp
  · simp only [comp_sum, P_f_naturality_assoc, SimplicialObject.δ_naturality_assoc]

end MorphComponents

end DoldKan

end AlgebraicTopology
