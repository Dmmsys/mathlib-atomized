/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Projections
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!

# Construction of the projection `PInfty` for the Dold-Kan correspondence

In this file, we construct the projection `PInfty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `Projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `PInfty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject CategoryTheory.Idempotents Opposite Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

/--
theorem `P_is_eventually_constant` / 定理 `P_is_eventually_constant`

English:
theorem P_is_eventually_constant
  given: {q n : Nat} (hqn : n <= q)
  proof: by
  cases n with
  | zero => simp only [P_f_0_eq]
  | succ n =>
    simp only [P_succ, comp_add, comp_id, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      add_eq_left]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)

中文:
定理 P_is_eventually_constant
  条件: {q n : 自然数} (hqn : n <= q)
  证明: by
  cases n with
  | zero => simp only [P_f_0_eq]
  | succ n =>
    simp only [P_succ, comp_add, comp_id, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      add_eq_left]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)

Depends on / 依赖: HigherFacesVanish, HigherFacesVanish.of_P, HomologicalComplex, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, Nat.succ_le_iff.mp, P_f_0_eq, P_succ, add_eq_left, add_f_apply, comp_add, comp_f, comp_id, of_P, succ_le_iff
-/
theorem P_is_eventually_constant {q n : Nat} (hqn : n <= q) :
    ((P (q + 1)).f n : X _⦋n⦌ ⟶ _) = (P q).f n := by
  cases n with
  | zero => simp only [P_f_0_eq]
  | succ n =>
    simp only [P_succ, comp_add, comp_id, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      add_eq_left]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)

/--
theorem `Q_is_eventually_constant` / 定理 `Q_is_eventually_constant`

English:
theorem Q_is_eventually_constant
  given: {q n : Nat} (hqn : n <= q)
  proof: by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

中文:
定理 Q_is_eventually_constant
  条件: {q n : 自然数} (hqn : n <= q)
  证明: by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.sub_f_apply, P_is_eventually_constant, sub_f_apply
-/
theorem Q_is_eventually_constant {q n : Nat} (hqn : n <= q) :
    ((Q (q + 1)).f n : X _⦋n⦌ ⟶ _) = (Q q).f n := by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

/--
Definition of `PInfty` / `PInfty` 的定义

English:
definition PInfty
  signature: : K[X] ⟶ K[X]
  body: ChainComplex.ofHom (fun n => ((P n).f n : X _⦋n⦌ ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n <= n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n

中文:
定义 PInfty
  签名: : K[X] ⟶ K[X]
  定义体: ChainComplex.ofHom (fun n => ((P n).f n : X _⦋n⦌ ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n <= n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_d_eq, ChainComplex, ChainComplex.ofHom, P_is_eventually_constant, obj_d_eq
-/
noncomputable def PInfty : K[X] ⟶ K[X] :=
  ChainComplex.ofHom (fun n => ((P n).f n : X _⦋n⦌ ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n <= n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n

/--
Definition of `QInfty` / `QInfty` 的定义

English:
definition QInfty
  signature: : K[X] ⟶ K[X]
  body: 𝟙 _ - PInfty

@[simp]

中文:
定义 QInfty
  签名: : K[X] ⟶ K[X]
  定义体: 𝟙 _ - PInfty

@[simp]

Depends on / 依赖: PInfty
-/
noncomputable def QInfty : K[X] ⟶ K[X] :=
  𝟙 _ - PInfty

@[simp]
/--
theorem `PInfty_f_0` / 定理 `PInfty_f_0`

English:
theorem PInfty_f_0
  statement: (PInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
  proof: rfl

中文:
定理 PInfty_f_0
  结论: (PInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _
  证明: rfl
-/
theorem PInfty_f_0 : (PInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _ := rfl

/--
theorem `PInfty_f` / 定理 `PInfty_f`

English:
theorem PInfty_f
  given: (n : Nat)
  statement: (PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n
  proof: rfl

中文:
定理 PInfty_f
  条件: (n : 自然数)
  结论: (PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n
  证明: rfl
-/
theorem PInfty_f (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `QInfty_f_0` / 定理 `QInfty_f_0`

English:
theorem QInfty_f_0
  statement: (QInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0
  proof: by
  dsimp [QInfty]
  simp only [sub_self]

中文:
定理 QInfty_f_0
  结论: (QInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0
  证明: by
  dsimp [QInfty]
  simp only [sub_self]

Depends on / 依赖: QInfty, sub_self
-/
theorem QInfty_f_0 : (QInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0 := by
  dsimp [QInfty]
  simp only [sub_self]

/--
theorem `QInfty_f` / 定理 `QInfty_f`

English:
theorem QInfty_f
  given: (n : Nat)
  statement: (QInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n
  proof: rfl

#adaptation_note

中文:
定理 QInfty_f
  条件: (n : 自然数)
  结论: (QInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n
  证明: rfl

#adaptation_note
-/
theorem QInfty_f (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `PInfty_f_naturality` / 定理 `PInfty_f_naturality`

English:
theorem PInfty_f_naturality
  given: (n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y)
  proof: P_f_naturality n n f

#adaptation_note

中文:
定理 PInfty_f_naturality
  条件: (n : 自然数) {X Y : SimplicialObject C} (f : X ⟶ Y)
  证明: P_f_naturality n n f

#adaptation_note

Depends on / 依赖: P_f_naturality
-/
theorem PInfty_f_naturality (n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ PInfty.f n = PInfty.f n ≫ f.app (op ⦋n⦌) :=
  P_f_naturality n n f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
theorem `QInfty_f_naturality` / 定理 `QInfty_f_naturality`

English:
theorem QInfty_f_naturality
  given: (n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y)
  proof: Q_f_naturality n n f

@[reassoc (attr := simp)]

中文:
定理 QInfty_f_naturality
  条件: (n : 自然数) {X Y : SimplicialObject C} (f : X ⟶ Y)
  证明: Q_f_naturality n n f

@[reassoc (attr := simp)]

Depends on / 依赖: Q_f_naturality
-/
theorem QInfty_f_naturality (n : Nat) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ QInfty.f n = QInfty.f n ≫ f.app (op ⦋n⦌) :=
  Q_f_naturality n n f

@[reassoc (attr := simp)]
/--
theorem `PInfty_f_idem` / 定理 `PInfty_f_idem`

English:
theorem PInfty_f_idem
  given: (n : Nat)
  statement: (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n
  proof: by
  simp only [PInfty_f, P_f_idem]

@[reassoc (attr := simp)]

中文:
定理 PInfty_f_idem
  条件: (n : 自然数)
  结论: (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n
  证明: by
  simp only [PInfty_f, P_f_idem]

@[reassoc (attr := simp)]

Depends on / 依赖: PInfty_f, P_f_idem
-/
theorem PInfty_f_idem (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n := by
  simp only [PInfty_f, P_f_idem]

@[reassoc (attr := simp)]
/--
theorem `PInfty_idem` / 定理 `PInfty_idem`

English:
theorem PInfty_idem
  statement: (PInfty : K[X] ⟶ _) ≫ PInfty = PInfty
  proof: by
  ext n
  exact PInfty_f_idem n

@[reassoc (attr := simp)]

中文:
定理 PInfty_idem
  结论: (PInfty : K[X] ⟶ _) ≫ PInfty = PInfty
  证明: by
  ext n
  exact PInfty_f_idem n

@[reassoc (attr := simp)]

Depends on / 依赖: PInfty_f_idem
-/
theorem PInfty_idem : (PInfty : K[X] ⟶ _) ≫ PInfty = PInfty := by
  ext n
  exact PInfty_f_idem n

@[reassoc (attr := simp)]
/--
theorem `QInfty_f_idem` / 定理 `QInfty_f_idem`

English:
theorem QInfty_f_idem
  given: (n : Nat)
  statement: (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.f n
  proof: Q_f_idem _ _

@[reassoc (attr := simp)]

中文:
定理 QInfty_f_idem
  条件: (n : 自然数)
  结论: (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.f n
  证明: Q_f_idem _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Q_f_idem
-/
theorem QInfty_f_idem (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.f n :=
  Q_f_idem _ _

@[reassoc (attr := simp)]
/--
theorem `QInfty_idem` / 定理 `QInfty_idem`

English:
theorem QInfty_idem
  statement: (QInfty : K[X] ⟶ _) ≫ QInfty = QInfty
  proof: by
  ext n
  exact QInfty_f_idem n

@[reassoc (attr := simp)]

中文:
定理 QInfty_idem
  结论: (QInfty : K[X] ⟶ _) ≫ QInfty = QInfty
  证明: by
  ext n
  exact QInfty_f_idem n

@[reassoc (attr := simp)]

Depends on / 依赖: QInfty_f_idem
-/
theorem QInfty_idem : (QInfty : K[X] ⟶ _) ≫ QInfty = QInfty := by
  ext n
  exact QInfty_f_idem n

@[reassoc (attr := simp)]
/--
theorem `PInfty_f_comp_QInfty_f` / 定理 `PInfty_f_comp_QInfty_f`

English:
theorem PInfty_f_comp_QInfty_f
  given: (n : Nat)
  statement: (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = 0
  proof: by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, comp_id,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]

中文:
定理 PInfty_f_comp_QInfty_f
  条件: (n : 自然数)
  结论: (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = 0
  证明: by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, comp_id,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply, PInfty_f_idem, QInfty, comp_id, comp_sub, id_f, sub_f_apply, sub_self
-/
theorem PInfty_f_comp_QInfty_f (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = 0 := by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, comp_id,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]
/--
theorem `PInfty_comp_QInfty` / 定理 `PInfty_comp_QInfty`

English:
theorem PInfty_comp_QInfty
  statement: (PInfty : K[X] ⟶ _) ≫ QInfty = 0
  proof: by
  ext n
  apply PInfty_f_comp_QInfty_f

@[reassoc (attr := simp)]

中文:
定理 PInfty_comp_QInfty
  结论: (PInfty : K[X] ⟶ _) ≫ QInfty = 0
  证明: by
  ext n
  apply PInfty_f_comp_QInfty_f

@[reassoc (attr := simp)]

Depends on / 依赖: PInfty_f_comp_QInfty_f
-/
theorem PInfty_comp_QInfty : (PInfty : K[X] ⟶ _) ≫ QInfty = 0 := by
  ext n
  apply PInfty_f_comp_QInfty_f

@[reassoc (attr := simp)]
/--
theorem `QInfty_f_comp_PInfty_f` / 定理 `QInfty_f_comp_PInfty_f`

English:
theorem QInfty_f_comp_PInfty_f
  given: (n : Nat)
  statement: (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = 0
  proof: by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, sub_comp, id_comp,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]

中文:
定理 QInfty_f_comp_PInfty_f
  条件: (n : 自然数)
  结论: (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = 0
  证明: by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, sub_comp, id_comp,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply, PInfty_f_idem, QInfty, id_comp, id_f, sub_comp, sub_f_apply, sub_self
-/
theorem QInfty_f_comp_PInfty_f (n : Nat) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = 0 := by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, sub_comp, id_comp,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]
/--
theorem `QInfty_comp_PInfty` / 定理 `QInfty_comp_PInfty`

English:
theorem QInfty_comp_PInfty
  statement: (QInfty : K[X] ⟶ _) ≫ PInfty = 0
  proof: by
  ext n
  apply QInfty_f_comp_PInfty_f

@[simp]

中文:
定理 QInfty_comp_PInfty
  结论: (QInfty : K[X] ⟶ _) ≫ PInfty = 0
  证明: by
  ext n
  apply QInfty_f_comp_PInfty_f

@[simp]

Depends on / 依赖: QInfty_f_comp_PInfty_f
-/
theorem QInfty_comp_PInfty : (QInfty : K[X] ⟶ _) ≫ PInfty = 0 := by
  ext n
  apply QInfty_f_comp_PInfty_f

@[simp]
/--
theorem `PInfty_add_QInfty` / 定理 `PInfty_add_QInfty`

English:
theorem PInfty_add_QInfty
  statement: (PInfty : K[X] ⟶ _) + QInfty = 𝟙 _
  proof: by
  dsimp only [QInfty]
  simp only [add_sub_cancel]

中文:
定理 PInfty_add_QInfty
  结论: (PInfty : K[X] ⟶ _) + QInfty = 𝟙 _
  证明: by
  dsimp only [QInfty]
  simp only [add_sub_cancel]

Depends on / 依赖: QInfty, add_sub_cancel
-/
theorem PInfty_add_QInfty : (PInfty : K[X] ⟶ _) + QInfty = 𝟙 _ := by
  dsimp only [QInfty]
  simp only [add_sub_cancel]

/--
theorem `PInfty_f_add_QInfty_f` / 定理 `PInfty_f_add_QInfty_f`

English:
theorem PInfty_f_add_QInfty_f
  given: (n : Nat)
  statement: (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n = 𝟙 _
  proof: HomologicalComplex.congr_hom PInfty_add_QInfty n

中文:
定理 PInfty_f_add_QInfty_f
  条件: (n : 自然数)
  结论: (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n = 𝟙 _
  证明: HomologicalComplex.congr_hom PInfty_add_QInfty n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, PInfty_add_QInfty, congr_hom
-/
theorem PInfty_f_add_QInfty_f (n : Nat) : (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n = 𝟙 _ :=
  HomologicalComplex.congr_hom PInfty_add_QInfty n

variable (C)

/-- `PInfty` induces a natural transformation, i.e. an endomorphism of
the functor `alternatingFaceMapComplex C`. -/
@[simps]
/--
Definition of `natTransPInfty` / `natTransPInfty` 的定义

English:
definition natTransPInfty
  signature: : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  body: PInfty
  naturality X Y f := by
    ext n
    exact PInfty_f_naturality n f

中文:
定义 natTransPInfty
  签名: : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  定义体: PInfty
  naturality X Y f := by
    ext n
    exact PInfty_f_naturality n f

Depends on / 依赖: PInfty
-/
noncomputable def natTransPInfty : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := PInfty
  naturality X Y f := by
    ext n
    exact PInfty_f_naturality n f

/-- The natural transformation in each degree that is induced by `natTransPInfty`. -/
@[simps!]
/--
Definition of `natTransPInfty_f` / `natTransPInfty_f` 的定义

English:
definition natTransPInfty_f
  signature: (n : Nat)
  body: natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)

中文:
定义 natTransPInfty_f
  签名: (n : 自然数)
  定义体: natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.eval, natTransPInfty
-/
noncomputable def natTransPInfty_f (n : Nat) :=
  natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)

variable {C}

@[simp]
/--
theorem `map_PInfty_f` / 定理 `map_PInfty_f`

English:
theorem map_PInfty_f
  statement: {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
  proof: by
  simp only [PInfty_f, map_P]

中文:
定理 map_PInfty_f
  结论: {D : 类型} [范畴* D] [预加性 D] (G : C ⥤ D) [G.加性]
  证明: by
  simp only [PInfty_f, map_P]

Depends on / 依赖: PInfty_f, map_P
-/
theorem map_PInfty_f {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (n : Nat) :
    (PInfty : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
      G.map ((PInfty : AlternatingFaceMapComplex.obj X ⟶ _).f n) := by
  simp only [PInfty_f, map_P]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `karoubi_PInfty_f` / 定理 `karoubi_PInfty_f`

English:
theorem karoubi_PInfty_f
  given: {Y : Karoubi (SimplicialObject C)} (n : Nat)
  proof: by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubiFunctorCategoryEmbedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (toKaroubi C)).obj Y.X
  let Y₄ := (karoubiFunctorCategoryEmbedding _ _).obj ((toKaroubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := PInfty
  let P₂ : K[Y₂] ⟶ _ := PInfty
  let P₃ : K[Y₃] ⟶ _ := PInfty
  let P₄ : K[Y₄] ⟶ _ := PInfty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op ⦋n⦌) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := Karoubi.hom_ext_iff.mp (map_PInfty_f (toKaroubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := Functor.congr_obj (toKaroubi_comp_karoubiFunctorCategoryEmbedding _ _) Y₂
    simp only [P₃, P₄, ← natTransPInfty_f_app]
    congr 1
  have h₁₄ := Idempotents.natTrans_eq
    ((𝟙 (karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C)) ◫
      (natTransPInfty_f (Karoubi C) n)) Y
  dsimp [natTransPInfty_f] at h₁₄
  rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂]; rw [← h₄₃]; rw [h₁₄]
  simp only [KaroubiFunctorCategoryEmbedding.map_app_f, Karoubi.decompId_p_f,
    Karoubi.decompId_i_f, Karoubi.comp_f]
  let π : Y₄ ⟶ Y₄ := (toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding _ _).map Y.p
  have eq := Karoubi.hom_ext_iff.mp (PInfty_f_naturality n π)
  simp only [Karoubi.comp_f] at eq
  dsimp [π] at eq
  rw [← eq]; rw [app_idem_assoc Y (op ⦋n⦌)]

中文:
定理 karoubi_PInfty_f
  条件: {Y : Karoubi (SimplicialObject C)} (n : 自然数)
  证明: by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubiFunctorCategoryEmbedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (toKaroubi C)).obj Y.X
  let Y₄ := (karoubiFunctorCategoryEmbedding _ _).obj ((toKaroubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := PInfty
  let P₂ : K[Y₂] ⟶ _ := PInfty
  let P₃ : K[Y₃] ⟶ _ := PInfty
  let P₄ : K[Y₄] ⟶ _ := PInfty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op ⦋n⦌) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := Karoubi.hom_ext_iff.mp (map_PInfty_f (toKaroubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := Functor.congr_obj (toKaroubi_comp_karoubiFunctorCategoryEmbedding _ _) Y₂
    simp only [P₃, P₄, ← natTransPInfty_f_app]
    congr 1
  have h₁₄ := Idempotents.natTrans_eq
    ((𝟙 (karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C)) ◫
      (natTransPInfty_f (Karoubi C) n)) Y
  dsimp [natTransPInfty_f] at h₁₄
  rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂]; rw [← h₄₃]; rw [h₁₄]
  simp only [KaroubiFunctorCategoryEmbedding.map_app_f, Karoubi.decompId_p_f,
    Karoubi.decompId_i_f, Karoubi.comp_f]
  let π : Y₄ ⟶ Y₄ := (toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding _ _).map Y.p
  have eq := Karoubi.hom_ext_iff.mp (PInfty_f_naturality n π)
  simp only [Karoubi.comp_f] at eq
  dsimp [π] at eq
  rw [← eq]; rw [app_idem_assoc Y (op ⦋n⦌)]
-/
theorem karoubi_PInfty_f {Y : Karoubi (SimplicialObject C)} (n : Nat) :
    ((PInfty : K[(karoubiFunctorCategoryEmbedding _ _).obj Y] ⟶ _).f n).f =
      Y.p.app (op ⦋n⦌) ≫ (PInfty : K[Y.X] ⟶ _).f n := by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubiFunctorCategoryEmbedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (toKaroubi C)).obj Y.X
  let Y₄ := (karoubiFunctorCategoryEmbedding _ _).obj ((toKaroubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := PInfty
  let P₂ : K[Y₂] ⟶ _ := PInfty
  let P₃ : K[Y₃] ⟶ _ := PInfty
  let P₄ : K[Y₄] ⟶ _ := PInfty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op ⦋n⦌) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := Karoubi.hom_ext_iff.mp (map_PInfty_f (toKaroubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := Functor.congr_obj (toKaroubi_comp_karoubiFunctorCategoryEmbedding _ _) Y₂
    simp only [P₃, P₄, ← natTransPInfty_f_app]
    congr 1
  have h₁₄ := Idempotents.natTrans_eq
    ((𝟙 (karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C)) ◫
      (natTransPInfty_f (Karoubi C) n)) Y
  dsimp [natTransPInfty_f] at h₁₄
  rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂]; rw [← h₄₃]; rw [h₁₄]
  simp only [KaroubiFunctorCategoryEmbedding.map_app_f, Karoubi.decompId_p_f,
    Karoubi.decompId_i_f, Karoubi.comp_f]
  let π : Y₄ ⟶ Y₄ := (toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding _ _).map Y.p
  have eq := Karoubi.hom_ext_iff.mp (PInfty_f_naturality n π)
  simp only [Karoubi.comp_f] at eq
  dsimp [π] at eq
  rw [← eq]; rw [app_idem_assoc Y (op ⦋n⦌)]

end DoldKan

end AlgebraicTopology
