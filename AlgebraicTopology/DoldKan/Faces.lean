/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Homotopies
public import Mathlib.Tactic.Ring

/-!

# Study of face maps for the Dold-Kan correspondence

In this file, we obtain the technical lemmas that are used in the file
`Projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `Homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `HigherFacesVanish.induction`. It is based
on two technical lemmas `HigherFacesVanish.comp_Hσ_eq` and
`HigherFacesVanish.comp_Hσ_eq_zero`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Preadditive CategoryTheory.SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]
variable {X : SimplicialObject C}

/--
Definition of `HigherFacesVanish` / `HigherFacesVanish` 的定义

English:
definition HigherFacesVanish
  signature: {Y : C} {n : Nat} (q : Nat) (φ : Y ⟶ X _⦋n + 1⦌)
  body: forall j : Fin (n + 1), n + 1 <= (j : Nat) + q -> φ ≫ X.δ j.succ = 0

中文:
定义 HigherFacesVanish
  签名: {Y : C} {n : 自然数} (q : 自然数) (φ : Y ⟶ X _⦋n + 1⦌)
  定义体: forall j : Fin (n + 1), n + 1 <= (j : Nat) + q -> φ ≫ X.δ j.succ = 0

Depends on / 依赖: j.succ
-/
def HigherFacesVanish {Y : C} {n : Nat} (q : Nat) (φ : Y ⟶ X _⦋n + 1⦌) : Prop :=
  forall j : Fin (n + 1), n + 1 <= (j : Nat) + q -> φ ≫ X.δ j.succ = 0

namespace HigherFacesVanish

@[reassoc]
/--
theorem `comp_δ_eq_zero` / 定理 `comp_δ_eq_zero`

English:
theorem comp_δ_eq_zero
  statement: {Y : C} {n : Nat} {q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  proof: by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj₁
  apply v i
  simp only [Fin.val_succ] at hj₂
  lia

中文:
定理 comp_δ_eq_zero
  结论: {Y : C} {n : 自然数} {q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  证明: by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj₁
  apply v i
  simp only [Fin.val_succ] at hj₂
  lia

Depends on / 依赖: Fin.eq_succ_of_ne_zero, Fin.val_succ, eq_succ_of_ne_zero, val_succ
-/
theorem comp_δ_eq_zero {Y : C} {n : Nat} {q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
    (j : Fin (n + 2)) (hj₁ : j != 0) (hj₂ : n + 2 <= (j : Nat) + q) : φ ≫ X.δ j = 0 := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj₁
  apply v i
  simp only [Fin.val_succ] at hj₂
  lia

/--
theorem `of_succ` / 定理 `of_succ`

English:
theorem of_succ
  given: {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish (q + 1) φ)
  proof: fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)

中文:
定理 of_succ
  条件: {Y : C} {n q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish (q + 1) φ)
  证明: fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)

Depends on / 依赖: add_assoc, le_add_right
-/
theorem of_succ {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish (q + 1) φ) :
    HigherFacesVanish q φ := fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  given: {Y Z : C} {q n : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (f : Z ⟶ Y)
  proof: fun j hj => by rw [assoc, v j hj, comp_zero]

中文:
定理 of_comp
  条件: {Y Z : C} {q n : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (f : Z ⟶ Y)
  证明: fun j hj => by rw [assoc, v j hj, comp_zero]

Depends on / 依赖: comp_zero
-/
theorem of_comp {Y Z : C} {q n : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (f : Z ⟶ Y) :
    HigherFacesVanish q (f ≫ φ) := fun j hj => by rw [assoc, v j hj, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_Hσ_eq` / 定理 `comp_Hσ_eq`

English:
theorem comp_Hσ_eq
  statement: {Y : C} {n a q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  proof: by
  have hnaq_shift (d : Nat) : n + d = a + d + q := by lia
  rw [Hσ]; rw [Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]; rw [hσ'_eq hnaq (c_mk (n + 1) n rfl)]; rw [hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [AlternatingFaceMapComplex.obj_d_eq, eqT

中文:
定理 comp_Hσ_eq
  结论: {Y : C} {n a q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  证明: by
  have hnaq_shift (d : Nat) : n + d = a + d + q := by lia
  rw [Hσ]; rw [Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]; rw [hσ'_eq hnaq (c_mk (n + 1) n rfl)]; rw [hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [AlternatingFaceMapComplex.obj_d_eq, eqT

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_d_eq, Homotopy, Homotopy.nullHomotopicMap, c_mk, comp_add, comp_id, comp_sum, comp_zsmul, eqToHom_refl, hnaq_shift, mul_zsmul, nullHomotopicMap, obj_d_eq, sum_comp, zsmul_comp
-/
theorem comp_Hσ_eq {Y : C} {n a q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
    (hnaq : n = a + q) :
    φ ≫ (Hσ q).f (n + 1) = -φ ≫ X.δ ⟨a + 1, by lia⟩ ≫ X.σ ⟨a, by lia⟩ := by
  have hnaq_shift (d : Nat) : n + d = a + d + q := by lia
  rw [Hσ]; rw [Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]; rw [hσ'_eq hnaq (c_mk (n + 1) n rfl)]; rw [hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [AlternatingFaceMapComplex.obj_d_eq, eqToHom_refl, comp_id, comp_sum, sum_comp,
    comp_add]
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul]
  -- cleaning up the first sum
  rw [← Fin.sum_congr' _ (hnaq_shift 2).symm]; rw [Fin.sum_trunc]
  swap
  · rintro ⟨k, hk⟩
    suffices φ ≫ X.δ (⟨a + 2 + k, by lia⟩ : Fin (n + 2)) = 0 by
      simp only [this, Fin.natAdd_mk, Fin.cast_mk, zero_comp, smul_zero]
    convert! v ⟨a + k + 1, by lia⟩ (by rw [Fin.val_mk]; lia)
    dsimp
    lia
  -- cleaning up the second sum
  rw [← Fin.sum_congr' _ (hnaq_shift 3).symm]; rw [@Fin.sum_trunc _ _ (a + 3)]
  swap
  · rintro ⟨k, hk⟩
    rw [assoc]; rw [X.δ_comp_σ_of_gt']; rw [v.comp_δ_eq_zero_assoc]; rw [zero_comp]; rw [zsmul_zero]
    · intro h
      replace h : a + 3 + k = 1 := by simp [Fin.ext_iff] at h
      lia
    · dsimp [Fin.cast, Fin.pred]
      rw [Nat.add_right_comm]; rw [Nat.add_sub_assoc (by simp : 1 <= 3)]
      lia
    · simp only [Fin.lt_def]
      dsimp [Fin.natAdd, Fin.cast]
      lia
  simp only [assoc]
  conv_lhs =>
    congr
    · rw [Fin.sum_univ_castSucc]
    · rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  dsimp [Fin.cast, Fin.castLE, Fin.castLT]
  /- the purpose of the following `simplif` is to create three subgoals in order
      to finish the proof -/
  have simplif :
    forall a b c d e f : Y ⟶ X _⦋n + 1⦌, b = f -> d + e = 0 -> c + a = 0 -> a + b + (c + d + e) = f := by
    intro a b c d e f h1 h2 h3
    rw [add_assoc c d e]; rw [h2]; rw [add_zero]; rw [add_comm a]; rw [add_assoc]; rw [add_comm a]; rw [h3]; rw [add_zero]; rw [h1]
  apply simplif
  · -- b = f
    rw [← pow_add]; rw [Odd.neg_one_pow]; rw [neg_smul]; rw [one_zsmul]
    exact ⟨a, by lia⟩
  · -- d + e = 0
    rw [X.δ_comp_σ_self' (Fin.castSucc_mk _ _ _).symm]; rw [X.δ_comp_σ_succ' (Fin.succ_mk _ _ _).symm]
    simp only [comp_id, pow_add _ (a + 1) 1, pow_one, mul_neg, mul_one, neg_mul, neg_smul,
      add_neg_cancel]
  · -- c + a = 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    rintro ⟨i, hi⟩ _
    simp only
    have hia : (⟨i, by lia⟩ : Fin (n + 2)) <=
        Fin.castSucc (⟨a, by lia⟩ : Fin (n + 1)) := by
      rw [Fin.le_iff_val_le_val]
      dsimp
      lia
    generalize_proofs
    rw [← Fin.succ_mk (n + 1) a ‹_›]; rw [← Fin.castSucc_mk (n + 2) i ‹_›]; rw [δ_comp_σ_of_le X hia]; rw [add_eq_zero_iff_eq_neg]; rw [← neg_zsmul]
    congr 2
    ring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_Hσ_eq_zero` / 定理 `comp_Hσ_eq_zero`

English:
theorem comp_Hσ_eq_zero
  statement: {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  proof: by
  simp only [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl)]; rw [comp_zero]; rw [zero_add]
  by_cases hqn' : n + 1 < q
  · rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
  · simp only [hσ'_eq (s

中文:
定理 comp_Hσ_eq_zero
  结论: {Y : C} {n q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  证明: by
  simp only [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl)]; rw [comp_zero]; rw [zero_add]
  by_cases hqn' : n + 1 < q
  · rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
  · simp only [hσ'_eq (s

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_d_eq, Fin.mk_zero, Homotopy, Homotopy.nullHomotopicMap, _eq_zero, c_mk, comp_id, comp_sum, comp_zero, eqToHom_refl, mk_zero, nullHomotopicMap, obj_d_eq, one_zsmul, pow_zero, zero_add, zero_comp
-/
theorem comp_Hσ_eq_zero {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
    (hqn : n < q) : φ ≫ (Hσ q).f (n + 1) = 0 := by
  simp only [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl)]; rw [comp_zero]; rw [zero_add]
  by_cases hqn' : n + 1 < q
  · rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
  · simp only [hσ'_eq (show n + 1 = 0 + q by lia) (c_mk (n + 2) (n + 1) rfl), pow_zero,
      Fin.mk_zero, one_zsmul, eqToHom_refl, comp_id, comp_sum,
      AlternatingFaceMapComplex.obj_d_eq]
    -- All terms of the sum but the first two are zeros
    rw [Fin.sum_univ_succ]; rw [Fin.sum_univ_succ]; rw [Fintype.sum_eq_zero]; rw [add_zero]
    · simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, zero_add, pow_zero, one_smul,
        pow_one, neg_smul, comp_neg, ← Fin.castSucc_zero (n := n + 2), δ_comp_σ_self, δ_comp_σ_succ,
        add_neg_cancel]
    · intro j
      rw [comp_zsmul]; rw [comp_zsmul]; rw [δ_comp_σ_of_gt']; rw [v.comp_δ_eq_zero_assoc]; rw [zero_comp]; rw [zsmul_zero]
      · simp [Fin.succ_ne_zero]
      · dsimp
        lia
      · simp only [Fin.succ_lt_succ_iff, j.succ_pos]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  given: {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  proof: by
  intro j hj₁
  dsimp
  simp only [comp_add, add_comp, comp_id]
  -- when n < q, the result follows immediately from the assumption
  by_cases! hqn : n < q
  · rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by lia)]
  -- we now assume that n≥q, and write n=a+q
  obtain ⟨a, ha⟩ := Nat.le.des

中文:
定理 induction
  条件: {Y : C} {n q : 自然数} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
  证明: by
  intro j hj₁
  dsimp
  simp only [comp_add, add_comp, comp_id]
  -- when n < q, the result follows immediately from the assumption
  by_cases! hqn : n < q
  · rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by lia)]
  -- we now assume that n≥q, and write n=a+q
  obtain ⟨a, ha⟩ := Nat.le.des

Depends on / 依赖: add_comp, comp_add, comp_id
-/
theorem induction {Y : C} {n q : Nat} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) :
    HigherFacesVanish (q + 1) (φ ≫ (𝟙 _ + Hσ q).f (n + 1)) := by
  intro j hj₁
  dsimp
  simp only [comp_add, add_comp, comp_id]
  -- when n < q, the result follows immediately from the assumption
  by_cases! hqn : n < q
  · rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by lia)]
  -- we now assume that n≥q, and write n=a+q
  obtain ⟨a, ha⟩ := Nat.le.dest hqn
  rw [v.comp_Hσ_eq (show n = a + q by lia)]; rw [neg_comp]; rw [add_neg_eq_zero]; rw [assoc]; rw [assoc]
  rcases n with - | m
  -- the boundary case n=0
  · simp only [Nat.eq_zero_of_add_eq_zero_left ha, Fin.eq_zero j, Fin.mk_zero,
      δ_comp_σ_succ, comp_id]
    rfl
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂ : a = (j : Nat)
  · simp only [hj₂, Fin.eta, δ_comp_σ_succ, comp_id]
    rfl
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a < j := (Ne.le_iff_lt hj₂).mp (by lia)
  have ham : a <= m := by grind
  rw [X.δ_comp_σ_of_gt']; rw [j.pred_succ]
  swap
  · rw [Fin.lt_def]
    simpa only [Fin.val_mk, Fin.val_succ, add_lt_add_iff_right] using haj
  obtain _ | ham'' := ham.lt_or_eq
  · -- case where `a<m`
    rw [← X.δ_comp_δ''_assoc]
    swap
    · rw [Fin.le_iff_val_le_val]
      dsimp
      lia
    simp only [← assoc, v j (by lia), zero_comp]
  · -- in the last case, a=m, q=1 and j=a+1
    rw [X.δ_comp_δ_self'_assoc]
    swap
    · ext
      cases j
      dsimp
      dsimp only [Nat.succ_eq_add_one] at *
      lia
    simp only [← assoc, v j (by lia), zero_comp]

end HigherFacesVanish

end DoldKan

end AlgebraicTopology
