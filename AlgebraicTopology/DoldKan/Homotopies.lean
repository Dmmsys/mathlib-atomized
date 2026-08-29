/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicTopology.DoldKan.Notations

/-!

# Construction of homotopies for the Dold-Kan correspondence

(The general strategy of proof of the Dold-Kan correspondence is explained
in `Equivalence.lean`.)

The purpose of the files `Homotopies.lean`, `Faces.lean`, `Projections.lean`
and `PInfty.lean` is to construct an idempotent endomorphism
`PInfty : K[X] ⟶ K[X]` of the alternating face map complex
for each `X : SimplicialObject C` when `C` is a preadditive category.
In the case `C` is abelian, this `PInfty` shall be the projection on the
normalized Moore subcomplex of `K[X]` associated to the decomposition of the
complex `K[X]` as a direct sum of this normalized subcomplex and of the
degenerate subcomplex.

In `PInfty.lean`, this endomorphism `PInfty` shall be obtained by
passing to the limit idempotent endomorphisms `P q` for all `(q : ℕ)`.
These endomorphisms `P q` are defined by induction. The idea is to
start from the identity endomorphism `P 0` of `K[X]` and to ensure by
induction that the `q` higher face maps (except $d_0$) vanish on the
image of `P q`. Then, in a certain degree `n`, the image of `P q` for
a big enough `q` will be contained in the normalized subcomplex. This
construction is done in `Projections.lean`.

It would be easy to define the `P q` degreewise (similarly as it is done
in *Simplicial Homotopy Theory* by Goerss-Jardine p. 149), but then we would
have to prove that they are compatible with the differential (i.e. they
are chain complex maps), and also that they are homotopic to the identity.
These two verifications are quite technical. In order to reduce the number
of such technical lemmas, the strategy that is followed here is to define
a series of null homotopic maps `Hσ q` (attached to families of maps `hσ`)
and use these in order to construct `P q` : the endomorphisms `P q`
shall basically be obtained by altering the identity endomorphism by adding
null homotopic maps, so that we get for free that they are morphisms
of chain complexes and that they are homotopic to the identity. The most
technical verifications that are needed about the null homotopic maps `Hσ`
are obtained in `Faces.lean`.

In this file `Homotopies.lean`, we define the null homotopic maps
`Hσ q : K[X] ⟶ K[X]`, show that they are natural (see `natTransHσ`) and
compatible with the application of additive functors (see `map_Hσ`).

## References
* [Albrecht Dold, *Homology of Symmetric Products and Other Functors of Complexes*][dold1958]
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject Homotopy Opposite Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]
variable {X : SimplicialObject C}

/--
Definition of `c` / `c` 的定义

English:
abbreviation c
  body: ComplexShape.down Nat

中文:
缩写 c
  定义体: ComplexShape.down Nat

Depends on / 依赖: ComplexShape, ComplexShape.down
-/
abbrev c :=
  ComplexShape.down Nat

/--
theorem `c_mk` / 定理 `c_mk`

English:
theorem c_mk
  given: (i j : Nat) (h : j + 1 = i)
  statement: c.Rel i j
  proof: ComplexShape.down_mk i j h

中文:
定理 c_mk
  条件: (i j : 自然数) (h : j + 1 = i)
  结论: c.Rel i j
  证明: ComplexShape.down_mk i j h

Depends on / 依赖: ComplexShape, ComplexShape.down_mk, down_mk
-/
theorem c_mk (i j : Nat) (h : j + 1 = i) : c.Rel i j :=
  ComplexShape.down_mk i j h

set_option backward.defeqAttrib.useBackward true in
/--
theorem `cs_down_0_not_rel_left` / 定理 `cs_down_0_not_rel_left`

English:
theorem cs_down_0_not_rel_left
  given: (j : Nat)
  statement: ¬c.Rel 0 j
  proof: by
  intro hj
  dsimp at hj
  apply Nat.not_succ_le_zero j
  rw [Nat.succ_eq_add_one]; rw [hj]

中文:
定理 cs_down_0_not_rel_left
  条件: (j : 自然数)
  结论: ¬c.Rel 0 j
  证明: by
  intro hj
  dsimp at hj
  apply Nat.not_succ_le_zero j
  rw [Nat.succ_eq_add_one]; rw [hj]

Depends on / 依赖: Nat.not_succ_le_zero, Nat.succ_eq_add_one, not_succ_le_zero, succ_eq_add_one
-/
theorem cs_down_0_not_rel_left (j : Nat) : ¬c.Rel 0 j := by
  intro hj
  dsimp at hj
  apply Nat.not_succ_le_zero j
  rw [Nat.succ_eq_add_one]; rw [hj]

/--
Definition of `hσ` / `hσ` 的定义

English:
definition hσ
  signature: (q : Nat) (n : Nat)
  body: if n < q then 0 else (-1 : Int) ^ (n - q) • X.σ ⟨n - q, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

中文:
定义 hσ
  签名: (q : 自然数) (n : 自然数)
  定义体: if n < q then 0 else (-1 : Int) ^ (n - q) • X.σ ⟨n - q, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

Depends on / 依赖: Nat.lt_succ_of_le, Nat.sub_le, lt_succ_of_le, sub_le
-/
def hσ (q : Nat) (n : Nat) : X _⦋n⦌ ⟶ X _⦋n + 1⦌ :=
  if n < q then 0 else (-1 : Int) ^ (n - q) • X.σ ⟨n - q, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/--
Definition of `hσ'` / `hσ'` 的定义

English:
definition hσ'
  signature: (q : Nat)
  body: fun n m hnm =>
  hσ q n ≫ eqToHom (by congr)

中文:
定义 hσ'
  签名: (q : 自然数)
  定义体: fun n m hnm =>
  hσ q n ≫ eqToHom (by congr)
-/
def hσ' (q : Nat) : forall n m, c.Rel m n -> (K[X].X n ⟶ K[X].X m) := fun n m hnm =>
  hσ q n ≫ eqToHom (by congr)

/--
theorem `hσ'_eq_zero` / 定理 `hσ'_eq_zero`

English:
theorem hσ'_eq_zero
  given: {q n m : Nat} (hnq : n < q) (hnm : c.Rel m n)
  proof: by
  simp only [hσ', hσ]
  split_ifs
  exact zero_comp

中文:
定理 hσ'_eq_zero
  条件: {q n m : 自然数} (hnq : n < q) (hnm : c.Rel m n)
  证明: by
  simp only [hσ', hσ]
  split_ifs
  exact zero_comp
-/
theorem hσ'_eq_zero {q n m : Nat} (hnq : n < q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _⦋n⦌ ⟶ X _⦋m⦌) = 0 := by
  simp only [hσ', hσ]
  split_ifs
  exact zero_comp

/--
theorem `hσ'_eq` / 定理 `hσ'_eq`

English:
theorem hσ'_eq
  given: {q n a m : Nat} (ha : n = a + q) (hnm : c.Rel m n)
  proof: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization w

中文:
定理 hσ'_eq
  条件: {q n a m : 自然数} (ha : n = a + q) (hnm : c.Rel m n)
  证明: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization w
-/
theorem hσ'_eq {q n a m : Nat} (ha : n = a + q) (hnm : c.Rel m n) :
    (hσ' q n m hnm : X _⦋n⦌ ⟶ X _⦋m⦌) =
      ((-1 : Int) ^ a • X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro (Eq.symm ha))⟩) ≫
        eqToHom (by congr) := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind [hσ', hσ]` -/
  simp [hσ', hσ, ha]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hσ'_eq'` / 定理 `hσ'_eq'`

English:
theorem hσ'_eq'
  given: {q n a : Nat} (ha : n = a + q)
  proof: by
  rw [hσ'_eq ha rfl]; rw [eqToHom_refl]; rw [comp_id]

中文:
定理 hσ'_eq'
  条件: {q n a : 自然数} (ha : n = a + q)
  证明: by
  rw [hσ'_eq ha rfl]; rw [eqToHom_refl]; rw [comp_id]
-/
theorem hσ'_eq' {q n a : Nat} (ha : n = a + q) :
    (hσ' q n (n + 1) rfl : X _⦋n⦌ ⟶ X _⦋n + 1⦌) =
      (-1 : Int) ^ a • X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro (Eq.symm ha))⟩ := by
  rw [hσ'_eq ha rfl]; rw [eqToHom_refl]; rw [comp_id]

/--
Definition of `Hσ` / `Hσ` 的定义

English:
definition Hσ
  signature: (q : Nat)
  body: nullHomotopicMap' (hσ' q)

中文:
定义 Hσ
  签名: (q : 自然数)
  定义体: nullHomotopicMap' (hσ' q)

Depends on / 依赖: nullHomotopicMap
-/
def Hσ (q : Nat) : K[X] ⟶ K[X] :=
  nullHomotopicMap' (hσ' q)

/--
Definition of `homotopyHσToZero` / `homotopyHσToZero` 的定义

English:
definition homotopyHσToZero
  signature: (q : Nat)
  body: nullHomotopy' (hσ' q)

中文:
定义 homotopyHσToZero
  签名: (q : 自然数)
  定义体: nullHomotopy' (hσ' q)

Depends on / 依赖: nullHomotopy
-/
def homotopyHσToZero (q : Nat) : Homotopy (Hσ q : K[X] ⟶ K[X]) 0 :=
  nullHomotopy' (hσ' q)

/--
theorem `Hσ_eq_zero` / 定理 `Hσ_eq_zero`

English:
theorem Hσ_eq_zero
  given: (q : Nat)
  statement: (Hσ q : K[X] ⟶ K[X]).f 0 = 0
  proof: by
  unfold Hσ
  rw [nullHomotopicMap'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left]
  rcases q with (_ | q)
  · rw [hσ'_eq (show 0 = 0 + 0 by rfl) (c_mk 1 0 rfl)]
    suffices X.σ 0 ≫ X.δ 0 + -X.σ 0 ≫ X.δ 1 = 0 by simpa
    rw [← Fin.succ_zero_eq_one]; rw [δ_comp_σ_succ]; rw [δ_comp_σ_se

中文:
定理 Hσ_eq_zero
  条件: (q : 自然数)
  结论: (Hσ q : K[X] ⟶ K[X]).f 0 = 0
  证明: by
  unfold Hσ
  rw [nullHomotopicMap'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left]
  rcases q with (_ | q)
  · rw [hσ'_eq (show 0 = 0 + 0 by rfl) (c_mk 1 0 rfl)]
    suffices X.σ 0 ≫ X.δ 0 + -X.σ 0 ≫ X.δ 1 = 0 by simpa
    rw [← Fin.succ_zero_eq_one]; rw [δ_comp_σ_succ]; rw [δ_comp_σ_se

Depends on / 依赖: Fin.castSucc_zero.symm, Fin.succ_zero_eq_one, Nat.succ_pos, _eq_zero, _f_of_not_rel_left, c_mk, castSucc_zero, cs_down_0_not_rel_left, nullHomotopicMap, succ_pos, succ_zero_eq_one, zero_comp
-/
theorem Hσ_eq_zero (q : Nat) : (Hσ q : K[X] ⟶ K[X]).f 0 = 0 := by
  unfold Hσ
  rw [nullHomotopicMap'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left]
  rcases q with (_ | q)
  · rw [hσ'_eq (show 0 = 0 + 0 by rfl) (c_mk 1 0 rfl)]
    suffices X.σ 0 ≫ X.δ 0 + -X.σ 0 ≫ X.δ 1 = 0 by simpa
    rw [← Fin.succ_zero_eq_one]; rw [δ_comp_σ_succ]; rw [δ_comp_σ_self' X (Fin.castSucc_zero.symm)]
    simp
  · rw [hσ'_eq_zero (Nat.succ_pos q) (c_mk 1 0 rfl), zero_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `hσ'_naturality` / 定理 `hσ'_naturality`

English:
theorem hσ'_naturality
  given: (q : Nat) (n m : Nat) (hnm : c.Rel m n) {X Y : SimplicialObject C} (f : X ⟶ Y)
  proof: by
  obtain rfl : n + 1 = m := hnm
  -- `simp? [hσ', hσ]` says:
  simp only [AlternatingFaceMapComplex.obj_X, hσ', hσ, Int.reduceNeg, eqToHom_refl, comp_id]
  split_ifs
  · rw [zero_comp, comp_zero]
  · simp

中文:
定理 hσ'_naturality
  条件: (q : 自然数) (n m : 自然数) (hnm : c.Rel m n) {X Y : SimplicialObject C} (f : X ⟶ Y)
  证明: by
  obtain rfl : n + 1 = m := hnm
  -- `simp? [hσ', hσ]` says:
  simp only [AlternatingFaceMapComplex.obj_X, hσ', hσ, Int.reduceNeg, eqToHom_refl, comp_id]
  split_ifs
  · rw [zero_comp, comp_zero]
  · simp
-/
theorem hσ'_naturality (q : Nat) (n m : Nat) (hnm : c.Rel m n) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ hσ' q n m hnm = hσ' q n m hnm ≫ f.app (op ⦋m⦌) := by
  obtain rfl : n + 1 = m := hnm
  -- `simp? [hσ', hσ]` says:
  simp only [AlternatingFaceMapComplex.obj_X, hσ', hσ, Int.reduceNeg, eqToHom_refl, comp_id]
  split_ifs
  · rw [zero_comp, comp_zero]
  · simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `natTransHσ` / `natTransHσ` 的定义

English:
definition natTransHσ
  signature: (q : Nat)
  body: Hσ q
  naturality _ _ f := by
    unfold Hσ
    rw [nullHomotopicMap'_comp]; rw [comp_nullHomotopicMap']
    congr
    ext n m hnm
    simp only [alternatingFaceMapComplex_map_f, hσ'_naturality]

中文:
定义 natTransHσ
  签名: (q : 自然数)
  定义体: Hσ q
  naturality _ _ f := by
    unfold Hσ
    rw [nullHomotopicMap'_comp]; rw [comp_nullHomotopicMap']
    congr
    ext n m hnm
    simp only [alternatingFaceMapComplex_map_f, hσ'_naturality]
-/
def natTransHσ (q : Nat) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := Hσ q
  naturality _ _ f := by
    unfold Hσ
    rw [nullHomotopicMap'_comp]; rw [comp_nullHomotopicMap']
    congr
    ext n m hnm
    simp only [alternatingFaceMapComplex_map_f, hσ'_naturality]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_hσ'` / 定理 `map_hσ'`

English:
theorem map_hσ'
  statement: {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  proof: by
  unfold hσ' hσ
  split_ifs
  · simp only [Functor.map_zero, zero_comp]
  · simp only [eqToHom_map, Functor.map_comp, Functor.map_zsmul]
    rfl

中文:
定理 map_hσ'
  结论: {D : 类型} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  证明: by
  unfold hσ' hσ
  split_ifs
  · simp only [Functor.map_zero, zero_comp]
  · simp only [eqToHom_map, Functor.map_comp, Functor.map_zsmul]
    rfl

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_zero, Functor.map_zsmul, eqToHom_map, map_comp, map_zero, map_zsmul, split_ifs, zero_comp
-/
theorem map_hσ' {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n m : Nat) (hnm : c.Rel m n) :
    (hσ' q n m hnm : K[((whiskering _ _).obj G).obj X].X n ⟶ _) =
      G.map (hσ' q n m hnm : K[X].X n ⟶ _) := by
  unfold hσ' hσ
  split_ifs
  · simp only [Functor.map_zero, zero_comp]
  · simp only [eqToHom_map, Functor.map_comp, Functor.map_zsmul]
    rfl

/--
theorem `map_Hσ` / 定理 `map_Hσ`

English:
theorem map_Hσ
  statement: {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  proof: by
  unfold Hσ
  have eq := HomologicalComplex.congr_hom (map_nullHomotopicMap' G (@hσ' _ _ _ X q)) n
  simp only [Functor.mapHomologicalComplex_map_f, ← map_hσ'] at eq
  rw [eq]
  let h := (Functor.congr_obj (map_alternatingFaceMapComplex G) X).symm
  congr

中文:
定理 map_Hσ
  结论: {D : 类型} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  证明: by
  unfold Hσ
  have eq := HomologicalComplex.congr_hom (map_nullHomotopicMap' G (@hσ' _ _ _ X q)) n
  simp only [Functor.mapHomologicalComplex_map_f, ← map_hσ'] at eq
  rw [eq]
  let h := (Functor.congr_obj (map_alternatingFaceMapComplex G) X).symm
  congr

Depends on / 依赖: Functor, Functor.congr_obj, Functor.mapHomologicalComplex_map_f, HomologicalComplex, HomologicalComplex.congr_hom, congr_hom, congr_obj, mapHomologicalComplex_map_f, map_alternatingFaceMapComplex, map_nullHomotopicMap
-/
theorem map_Hσ {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : Nat) :
    (Hσ q : K[((whiskering C D).obj G).obj X] ⟶ _).f n = G.map ((Hσ q : K[X] ⟶ _).f n) := by
  unfold Hσ
  have eq := HomologicalComplex.congr_hom (map_nullHomotopicMap' G (@hσ' _ _ _ X q)) n
  simp only [Functor.mapHomologicalComplex_map_f, ← map_hσ'] at eq
  rw [eq]
  let h := (Functor.congr_obj (map_alternatingFaceMapComplex G) X).symm
  congr

end DoldKan

end AlgebraicTopology
