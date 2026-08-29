/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Faces
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!

# Construction of projections for the Dold-Kan correspondence

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`HigherFacesVanish.of_P`, `HigherFacesVanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `natTransP`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `PInfty.lean`
in order to define `PInfty : K[X] ⟶ K[X]`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject Opposite CategoryTheory.Idempotents

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: : Nat -> (K[X] ⟶ K[X])

中文:
定义 P
  签名: : 自然数 -> (K[X] ⟶ K[X])
-/
noncomputable def P : Nat -> (K[X] ⟶ K[X])
  | 0 => 𝟙 _
  | q + 1 => P q ≫ (𝟙 _ + Hσ q)

/--
lemma `P_zero` / 引理 `P_zero`

English:
lemma P_zero
  statement: (P 0 : K[X] ⟶ K[X]) = 𝟙 _
  proof: rfl

中文:
引理 P_zero
  结论: (P 0 : K[X] ⟶ K[X]) = 𝟙 _
  证明: rfl
-/
lemma P_zero : (P 0 : K[X] ⟶ K[X]) = 𝟙 _ := rfl
/--
lemma `P_succ` / 引理 `P_succ`

English:
lemma P_succ
  given: (q : Nat)
  statement: (P (q + 1) : K[X] ⟶ K[X]) = P q ≫ (𝟙 _ + Hσ q)
  proof: rfl

中文:
引理 P_succ
  条件: (q : 自然数)
  结论: (P (q + 1) : K[X] ⟶ K[X]) = P q ≫ (𝟙 _ + Hσ q)
  证明: rfl
-/
lemma P_succ (q : Nat) : (P (q + 1) : K[X] ⟶ K[X]) = P q ≫ (𝟙 _ + Hσ q) := rfl

/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
@[simp]
/--
theorem `P_f_0_eq` / 定理 `P_f_0_eq`

English:
theorem P_f_0_eq
  given: (q : Nat)
  statement: ((P q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
  proof: by
  induction q with
  | zero => rfl
  | succ q hq =>
    simp only [P_succ, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, id_comp, hq, Hσ_eq_zero, add_zero]

中文:
定理 P_f_0_eq
  条件: (q : 自然数)
  结论: ((P q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
  证明: by
  induction q with
  | zero => rfl
  | succ q hq =>
    simp only [P_succ, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, id_comp, hq, Hσ_eq_zero, add_zero]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.id_f, P_succ, add_f_apply, add_zero, comp_f, id_comp, id_f
-/
theorem P_f_0_eq (q : Nat) : ((P q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _ := by
  induction q with
  | zero => rfl
  | succ q hq =>
    simp only [P_succ, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, id_comp, hq, Hσ_eq_zero, add_zero]

/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  signature: (q : Nat)
  body: 𝟙 _ - P q

中文:
定义 Q
  签名: (q : 自然数)
  定义体: 𝟙 _ - P q
-/
def Q (q : Nat) : K[X] ⟶ K[X] :=
  𝟙 _ - P q

/--
theorem `P_add_Q` / 定理 `P_add_Q`

English:
theorem P_add_Q
  given: (q : Nat)
  statement: P q + Q q = 𝟙 K[X]
  proof: by
  rw [Q]
  abel

中文:
定理 P_add_Q
  条件: (q : 自然数)
  结论: P q + Q q = 𝟙 K[X]
  证明: by
  rw [Q]
  abel
-/
theorem P_add_Q (q : Nat) : P q + Q q = 𝟙 K[X] := by
  rw [Q]
  abel

/--
theorem `P_add_Q_f` / 定理 `P_add_Q_f`

English:
theorem P_add_Q_f
  given: (q n : Nat)
  statement: (P q).f n + (Q q).f n = 𝟙 (X _⦋n⦌)
  proof: HomologicalComplex.congr_hom (P_add_Q q) n

@[simp]

中文:
定理 P_add_Q_f
  条件: (q n : 自然数)
  结论: (P q).f n + (Q q).f n = 𝟙 (X _⦋n⦌)
  证明: HomologicalComplex.congr_hom (P_add_Q q) n

@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, P_add_Q, congr_hom
-/
theorem P_add_Q_f (q n : Nat) : (P q).f n + (Q q).f n = 𝟙 (X _⦋n⦌) :=
  HomologicalComplex.congr_hom (P_add_Q q) n

@[simp]
/--
theorem `Q_zero` / 定理 `Q_zero`

English:
theorem Q_zero
  statement: (Q 0 : K[X] ⟶ _) = 0
  proof: sub_self _

中文:
定理 Q_zero
  结论: (Q 0 : K[X] ⟶ _) = 0
  证明: sub_self _

Depends on / 依赖: sub_self
-/
theorem Q_zero : (Q 0 : K[X] ⟶ _) = 0 :=
  sub_self _

/--
theorem `Q_succ` / 定理 `Q_succ`

English:
theorem Q_succ
  given: (q : Nat)
  statement: (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q
  proof: by
  simp only [Q, P_succ, comp_add, comp_id]
  abel

中文:
定理 Q_succ
  条件: (q : 自然数)
  结论: (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q
  证明: by
  simp only [Q, P_succ, comp_add, comp_id]
  abel

Depends on / 依赖: P_succ, comp_add, comp_id
-/
theorem Q_succ (q : Nat) : (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q := by
  simp only [Q, P_succ, comp_add, comp_id]
  abel

/-- All the `Q q` coincide with `0` in degree 0. -/
@[simp]
/--
theorem `Q_f_0_eq` / 定理 `Q_f_0_eq`

English:
theorem Q_f_0_eq
  given: (q : Nat)
  statement: ((Q q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0
  proof: by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]

中文:
定理 Q_f_0_eq
  条件: (q : 自然数)
  结论: ((Q q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0
  证明: by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply, P_f_0_eq, id_f, sub_f_apply, sub_self
-/
theorem Q_f_0_eq (q : Nat) : ((Q q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0 := by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]

namespace HigherFacesVanish

/--
theorem `of_P` / 定理 `of_P`

English:
theorem of_P
  statement: forall q n : Nat, HigherFacesVanish q ((P q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌)

中文:
定理 of_P
  结论: 对任意 q n : 自然数, HigherFacesVanish q ((P q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌)
-/
theorem of_P : forall q n : Nat, HigherFacesVanish q ((P q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌)
  | 0 => fun n j hj₁ => by lia
  | q + 1 => fun n => by
    simp only [P_succ]
    exact (of_P q n).induction

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `comp_P_eq_self` / 定理 `comp_P_eq_self`

English:
theorem comp_P_eq_self
  given: {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  proof: by
  induction q with
  | zero =>
    simp only [P_zero]
    apply comp_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, ← assoc, hq v.of_succ, add_eq_left]
    by_cases! hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero h

中文:
定理 comp_P_eq_self
  条件: {Y : C} {n q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  证明: by
  induction q with
  | zero =>
    simp only [P_zero]
    apply comp_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, ← assoc, hq v.of_succ, add_eq_left]
    by_cases! hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero h

Depends on / 依赖: Fin.succ_mk, HomologicalComplex, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, Nat.le.dest, P_succ, P_zero, add_assoc, add_eq_left, add_f_apply, comp_add, comp_f, comp_id, neg_eq_zero, of_succ, succ_mk, v.of_succ, v.of_succ.comp_H
-/
theorem comp_P_eq_self {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) :
    φ ≫ (P q).f (n + 1) = φ := by
  induction q with
  | zero =>
    simp only [P_zero]
    apply comp_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, ← assoc, hq v.of_succ, add_eq_left]
    by_cases! hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero hqn
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      have hnaq : n = a + q := by lia
      simp only [v.of_succ.comp_Hσ_eq hnaq, neg_eq_zero, ← assoc]
      have eq := v ⟨a, by lia⟩ (by
        simp only [hnaq, add_assoc]
        rfl)
      simp only [Fin.succ_mk] at eq
      simp only [eq, zero_comp]

end HigherFacesVanish

/--
theorem `comp_P_eq_self_iff` / 定理 `comp_P_eq_self_iff`

English:
theorem comp_P_eq_self_iff
  given: {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌}
  proof: by
  constructor
  · intro hφ
    rw [← hφ]
    apply HigherFacesVanish.of_comp
    apply HigherFacesVanish.of_P
  · exact HigherFacesVanish.comp_P_eq_self

@[reassoc (attr := simp)]

中文:
定理 comp_P_eq_self_iff
  条件: {Y : C} {n q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌}
  证明: by
  constructor
  · intro hφ
    rw [← hφ]
    apply HigherFacesVanish.of_comp
    apply HigherFacesVanish.of_P
  · exact HigherFacesVanish.comp_P_eq_self

@[reassoc (attr := simp)]

Depends on / 依赖: HigherFacesVanish, HigherFacesVanish.comp_P_eq_self, HigherFacesVanish.of_P, HigherFacesVanish.of_comp, comp_P_eq_self, of_P, of_comp
-/
theorem comp_P_eq_self_iff {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} :
    φ ≫ (P q).f (n + 1) = φ ↔ HigherFacesVanish q φ := by
  constructor
  · intro hφ
    rw [← hφ]
    apply HigherFacesVanish.of_comp
    apply HigherFacesVanish.of_P
  · exact HigherFacesVanish.comp_P_eq_self

@[reassoc (attr := simp)]
/--
theorem `P_f_idem` / 定理 `P_f_idem`

English:
theorem P_f_idem
  given: (q n : Nat)
  statement: ((P q).f n : X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n
  proof: by
  rcases n with (_ | n)
  · rw [P_f_0_eq q, comp_id]
  · exact (HigherFacesVanish.of_P q n).comp_P_eq_self

@[reassoc (attr := simp)]

中文:
定理 P_f_idem
  条件: (q n : 自然数)
  结论: ((P q).f n : X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n
  证明: by
  rcases n with (_ | n)
  · rw [P_f_0_eq q, comp_id]
  · exact (HigherFacesVanish.of_P q n).comp_P_eq_self

@[reassoc (attr := simp)]

Depends on / 依赖: HigherFacesVanish, HigherFacesVanish.of_P, P_f_0_eq, comp_P_eq_self, comp_id, of_P
-/
theorem P_f_idem (q n : Nat) : ((P q).f n : X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n := by
  rcases n with (_ | n)
  · rw [P_f_0_eq q, comp_id]
  · exact (HigherFacesVanish.of_P q n).comp_P_eq_self

@[reassoc (attr := simp)]
/--
theorem `Q_f_idem` / 定理 `Q_f_idem`

English:
theorem Q_f_idem
  given: (q n : Nat)
  statement: ((Q q).f n : X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n
  proof: idem_of_id_sub_idem _ (P_f_idem q n)

@[reassoc (attr := simp)]

中文:
定理 Q_f_idem
  条件: (q n : 自然数)
  结论: ((Q q).f n : X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n
  证明: idem_of_id_sub_idem _ (P_f_idem q n)

@[reassoc (attr := simp)]

Depends on / 依赖: P_f_idem, idem_of_id_sub_idem
-/
theorem Q_f_idem (q n : Nat) : ((Q q).f n : X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n :=
  idem_of_id_sub_idem _ (P_f_idem q n)

@[reassoc (attr := simp)]
/--
theorem `P_idem` / 定理 `P_idem`

English:
theorem P_idem
  given: (q : Nat)
  statement: (P q : K[X] ⟶ K[X]) ≫ P q = P q
  proof: by
  ext n
  exact P_f_idem q n

@[reassoc (attr := simp)]

中文:
定理 P_idem
  条件: (q : 自然数)
  结论: (P q : K[X] ⟶ K[X]) ≫ P q = P q
  证明: by
  ext n
  exact P_f_idem q n

@[reassoc (attr := simp)]

Depends on / 依赖: P_f_idem
-/
theorem P_idem (q : Nat) : (P q : K[X] ⟶ K[X]) ≫ P q = P q := by
  ext n
  exact P_f_idem q n

@[reassoc (attr := simp)]
/--
theorem `Q_idem` / 定理 `Q_idem`

English:
theorem Q_idem
  given: (q : Nat)
  statement: (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q
  proof: by
  ext n
  exact Q_f_idem q n

中文:
定理 Q_idem
  条件: (q : 自然数)
  结论: (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q
  证明: by
  ext n
  exact Q_f_idem q n

Depends on / 依赖: Q_f_idem
-/
theorem Q_idem (q : Nat) : (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q := by
  ext n
  exact Q_f_idem q n

set_option backward.isDefEq.respectTransparency false in
/-- For each `q`, `P q` is a natural transformation. -/
@[simps]
/--
Definition of `natTransP` / `natTransP` 的定义

English:
definition natTransP
  signature: (q : Nat)
  body: P q
  naturality _ _ f := by
    induction q with
    | zero =>
      dsimp [alternatingFaceMapComplex]
      simp only [P_zero, id_comp, comp_id]
    | succ q hq =>
      simp only [P_succ, add_comp, comp_add, assoc, comp_id, hq, reassoc_of% hq]
      -- `erw` is needed to see through `natTransHσ q

中文:
定义 natTransP
  签名: (q : 自然数)
  定义体: P q
  naturality _ _ f := by
    induction q with
    | zero =>
      dsimp [alternatingFaceMapComplex]
      simp only [P_zero, id_comp, comp_id]
    | succ q hq =>
      simp only [P_succ, add_comp, comp_add, assoc, comp_id, hq, reassoc_of% hq]
      -- `erw` is needed to see through `natTransHσ q
-/
def natTransP (q : Nat) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := P q
  naturality _ _ f := by
    induction q with
    | zero =>
      dsimp [alternatingFaceMapComplex]
      simp only [P_zero, id_comp, comp_id]
    | succ q hq =>
      simp only [P_succ, add_comp, comp_add, assoc, comp_id, hq, reassoc_of% hq]
      -- `erw` is needed to see through `natTransHσ q).app = Hσ q`
      erw [(natTransHσ q).naturality f]
      rfl

set_option backward.isDefEq.respectTransparency false in -- This is needed in AlgebraicTopology/DoldKan/Decomposition.lean
@[reassoc (attr := simp)]
/--
theorem `P_f_naturality` / 定理 `P_f_naturality`

English:
theorem P_f_naturality
  given: (q n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y)
  proof: HomologicalComplex.congr_hom ((natTransP q).naturality f) n

中文:
定理 P_f_naturality
  条件: (q n : 自然数) {X Y : SimplicialObject C} (f : X ⟶ Y)
  证明: HomologicalComplex.congr_hom ((natTransP q).naturality f) n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, congr_hom, natTransP, naturality
-/
theorem P_f_naturality (q n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ (P q).f n = (P q).f n ≫ f.app (op ⦋n⦌) :=
  HomologicalComplex.congr_hom ((natTransP q).naturality f) n

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `Q_f_naturality` / 定理 `Q_f_naturality`

English:
theorem Q_f_naturality
  given: (q n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y)
  proof: by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]

中文:
定理 Q_f_naturality
  条件: (q n : 自然数) {X Y : SimplicialObject C} (f : X ⟶ Y)
  证明: by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply, P_f_naturality, comp_id, comp_sub, id_comp, id_f, sub_comp, sub_f_apply, sub_left_inj
-/
theorem Q_f_naturality (q n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ (Q q).f n = (Q q).f n ≫ f.app (op ⦋n⦌) := by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- For each `q`, `Q q` is a natural transformation. -/
@[simps]
/--
Definition of `natTransQ` / `natTransQ` 的定义

English:
definition natTransQ
  signature: (q : Nat)
  body: Q q

中文:
定义 natTransQ
  签名: (q : 自然数)
  定义体: Q q
-/
def natTransQ (q : Nat) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := Q q

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_P` / 定理 `map_P`

English:
theorem map_P
  statement: {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  proof: by
  induction q with
  | zero =>
    simp only [P_zero]
    apply G.map_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, Functor.map_add, Functor.map_comp, hq, map_Hσ]

中文:
定理 map_P
  结论: {D : 类型} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  证明: by
  induction q with
  | zero =>
    simp only [P_zero]
    apply G.map_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, Functor.map_add, Functor.map_comp, hq, map_Hσ]

Depends on / 依赖: Functor, Functor.map_add, Functor.map_comp, G.map_id, HomologicalComplex, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, P_succ, P_zero, add_f_apply, comp_add, comp_f, comp_id, map_add, map_comp, map_id
-/
theorem map_P {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : Nat) :
    G.map ((P q : K[X] ⟶ _).f n) = (P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n := by
  induction q with
  | zero =>
    simp only [P_zero]
    apply G.map_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, Functor.map_add, Functor.map_comp, hq, map_Hσ]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_Q` / 定理 `map_Q`

English:
theorem map_Q
  statement: {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  proof: by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id

中文:
定理 map_Q
  结论: {D : 类型} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  证明: by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id

Depends on / 依赖: G.map, G.map_add, G.map_id, P_add_Q_f, add_right_inj, map_P, map_add, map_id
-/
theorem map_Q {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : Nat) :
    G.map ((Q q : K[X] ⟶ _).f n) = (Q q : K[((whiskering C D).obj G).obj X] ⟶ _).f n := by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id

end DoldKan

end AlgebraicTopology
