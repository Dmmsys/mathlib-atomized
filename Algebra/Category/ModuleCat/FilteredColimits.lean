/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ ModuleCat R`. We show that the colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrpCat`
(in `AddCommGrpCat`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (ModuleCat R) AddCommGrpCat` preserves filtered colimits. In particular, this
implies that `forget (ModuleCat R)` preserves filtered colimits.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits ConcreteCategory

open CategoryTheory.IsFiltered renaming max -> max' -- avoid name collision with `_root_.max`.

namespace ModuleCat.FilteredColimits

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ ModuleCat.{max v u, u} R)

/--
Definition of `M` / `M` 的定义

English:
definition M
  signature: : AddCommGrpCat
  body: AddCommGrpCat.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})

中文:
定义 M
  签名: : 加法交换群范畴
  定义体: AddCommGrpCat.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimit, FilteredColimits, ModuleCat, colimit
-/
def M : AddCommGrpCat :=
  AddCommGrpCat.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})

/--
Definition of `M.mk` / `M.mk` 的定义

English:
definition M.mk
  signature: : (Σ j, F.obj j) -> M F
  body: fun x => (F ⋙ forget (ModuleCat R)).ιColimitType x.1 x.2

中文:
定义 M.mk
  签名: : (Σ j, F.obj j) -> M F
  定义体: fun x => (F ⋙ forget (ModuleCat R)).ιColimitType x.1 x.2

Depends on / 依赖: ModuleCat, forget
-/
def M.mk : (Σ j, F.obj j) -> M F :=
  fun x => (F ⋙ forget (ModuleCat R)).ιColimitType x.1 x.2

/--
lemma `M.mk_surjective` / 引理 `M.mk_surjective`

English:
lemma M.mk_surjective
  given: (m : M F)
  proof: (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m

中文:
引理 M.mk_surjective
  条件: (m : M F)
  证明: (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m

Depends on / 依赖: ModuleCat, forget
-/
lemma M.mk_surjective (m : M F) :
    exists (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m :=
  (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m

/--
theorem `M.mk_eq` / 定理 `M.mk_eq`

English:
theorem M.mk_eq
  statement: (x y : Σ j, F.obj j)
  proof: Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

中文:
定理 M.mk_eq
  结论: (x y : Σ j, F.obj j)
  证明: Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

Depends on / 依赖: FilteredColimit, ModuleCat, Quot.eqvGen_sound, Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel, eqvGen_colimitTypeRel_of_rel, eqvGen_sound, forget
-/
theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : exists (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

/--
lemma `M.mk_map` / 引理 `M.mk_map`

English:
lemma M.mk_map
  given: {j k : J} (f : j ⟶ k) (x : F.obj j)
  proof: M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

中文:
引理 M.mk_map
  条件: {j k : J} (f : j ⟶ k) (x : F.obj j)
  证明: M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

Depends on / 依赖: M.mk_eq, mk_eq
-/
lemma M.mk_map {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ :=
  M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

/--
Definition of `colimitSMulAux` / `colimitSMulAux` 的定义

English:
definition colimitSMulAux
  signature: (r : R) (x : Σ j, F.obj j)
  body: M.mk F ⟨x.1, r • x.2⟩

中文:
定义 colimitSMulAux
  签名: (r : R) (x : Σ j, F.obj j)
  定义体: M.mk F ⟨x.1, r • x.2⟩

Depends on / 依赖: M.mk
-/
def colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F :=
  M.mk F ⟨x.1, r • x.2⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `colimitSMulAux_eq_of_rel` / 定理 `colimitSMulAux_eq_of_rel`

English:
theorem colimitSMulAux_eq_of_rel
  statement: (r : R) (x y : Σ j, F.obj j)
  proof: by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  simp [hfg]

中文:
定理 colimitSMulAux_eq_of_rel
  结论: (r : R) (x y : Σ j, F.obj j)
  证明: by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  simp [hfg]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.comp_map, Functor.comp_obj, M.mk_eq, TypeCat, TypeCat.Fun.coe_mk, coe_mk, comp_map, comp_obj, hom_ofHom, mk_eq
-/
theorem colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    colimitSMulAux F r x = colimitSMulAux F r y := by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  simp [hfg]

/--
Instance `colimitHasSMul` / 实例 `colimitHasSMul`

English:
instance colimitHasSMul
  signature: : SMul R (M F) where
  body: by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

中文:
实例 colimitHasSMul
  签名: : 标量乘法 R (M F) where
  定义体: by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

Depends on / 依赖: FilteredColimit, Quot.lift, Types.FilteredColimit.rel_of_colimitTypeRel, colimitSMulAux, colimitSMulAux_eq_of_rel, rel_of_colimitTypeRel
-/
instance colimitHasSMul : SMul R (M F) where
  smul r x := by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

/--
lemma `colimit_zero_eq` / 引理 `colimit_zero_eq`

English:
lemma colimit_zero_eq
  given: (j : J)
  proof: by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

中文:
引理 colimit_zero_eq
  条件: (j : J)
  证明: by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

Depends on / 依赖: AddMonCat, AddMonCat.FilteredColimits.colimit_zero_eq, FilteredColimits, colimit_zero_eq
-/
lemma colimit_zero_eq (j : J) :
    0 = M.mk F ⟨j, 0⟩ := by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

/--
lemma `colimit_add_mk_eq` / 引理 `colimit_add_mk_eq`

English:
lemma colimit_add_mk_eq
  statement: (x y : Σ j, F.obj j) (k : J)
  proof: by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq

中文:
引理 colimit_add_mk_eq
  结论: (x y : Σ j, F.obj j) (k : J)
  证明: by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq

Depends on / 依赖: AddMonCat, AddMonCat.FilteredColimits.colimit_add_mk_eq, FilteredColimits, colimit_add_mk_eq
-/
lemma colimit_add_mk_eq (x y : Σ j, F.obj j) (k : J)
    (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk _ x + M.mk _ y = M.mk _ ⟨k, F.map f x.2 + F.map g y.2⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq

/--
lemma `colimit_add_mk_eq'` / 引理 `colimit_add_mk_eq'`

English:
lemma colimit_add_mk_eq'
  given: {j : J} (x y : F.obj j)
  proof: by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'

@[simp]

中文:
引理 colimit_add_mk_eq'
  条件: {j : J} (x y : F.obj j)
  证明: by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'

@[simp]

Depends on / 依赖: AddMonCat, AddMonCat.FilteredColimits.colimit_add_mk_eq, FilteredColimits, colimit_add_mk_eq
-/
lemma colimit_add_mk_eq' {j : J} (x y : F.obj j) :
    M.mk F ⟨j, x⟩ + M.mk F ⟨j, y⟩ = M.mk F ⟨j, x + y⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'

@[simp]
/--
theorem `colimit_smul_mk_eq` / 定理 `colimit_smul_mk_eq`

English:
theorem colimit_smul_mk_eq
  given: (r : R) (x : Σ j, F.obj j)
  statement: r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩
  proof: rfl

中文:
定理 colimit_smul_mk_eq
  条件: (r : R) (x : Σ j, F.obj j)
  结论: r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩
  证明: rfl
-/
theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩ :=
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): writing directly the `Module` instance makes things very slow.
/--
Instance `colimitMulAction` / 实例 `colimitMulAction`

English:
instance colimitMulAction
  signature: : MulAction R (M F) where
  body: by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp
  mul_smul r s x := by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [mul_smul]

中文:
实例 colimitMulAction
  签名: : 乘法作用 R (M F) where
  定义体: by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp
  mul_smul r s x := by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [mul_smul]

Depends on / 依赖: M.mk_surjective, UnivLE, hasColimitsOfSize, mk_surjective, mul_smul
-/
instance colimitMulAction : MulAction R (M F) where
  one_smul x := by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp
  mul_smul r s x := by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [mul_smul]

/--
Instance `colimitSMulWithZero` / 实例 `colimitSMulWithZero`

English:
instance colimitSMulWithZero
  signature: : SMulWithZero R (M F)
  body: { colimitMulAction F with
  smul_zero := fun r => by
    rw [colimit_zero_eq _ (IsFiltered.nonempty.some : J)]; rw [colimit_smul_mk_eq]; rw [smul_zero]
  zero_smul := fun x => by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [← colimit_zero_eq] }

中文:
实例 colimitSMulWithZero
  签名: : 带零标量乘法 R (M F)
  定义体: { colimitMulAction F with
  smul_zero := fun r => by
    rw [colimit_zero_eq _ (IsFiltered.nonempty.some : J)]; rw [colimit_smul_mk_eq]; rw [smul_zero]
  zero_smul := fun x => by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [← colimit_zero_eq] }

Depends on / 依赖: IsFiltered, IsFiltered.nonempty.some, M.mk_surjective, colimitMulAction, colimit_smul_mk_eq, colimit_zero_eq, mk_surjective, nonempty, smul_zero, zero_smul
-/
instance colimitSMulWithZero : SMulWithZero R (M F) :=
{ colimitMulAction F with
  smul_zero := fun r => by
    rw [colimit_zero_eq _ (IsFiltered.nonempty.some : J)]; rw [colimit_smul_mk_eq]; rw [smul_zero]
  zero_smul := fun x => by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [← colimit_zero_eq] }

/--
Instance `colimitModule` / 实例 `colimitModule`

English:
instance colimitModule
  signature: : Module R (M F)
  body: { colimitMulAction F,
  colimitSMulWithZero F with
  smul_add := fun r x y => by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    obtain ⟨j, y, rfl⟩ := M.mk_surjective F y
    rw [colimit_smul_mk_eq]; rw [colimit_smul_mk_eq]; rw [colimit_add_mk_eq _ ⟨i]; rw [_⟩ ⟨j]; rw [_⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]; rw [colimit_smul_mk_eq]; rw [smul_add]; rw [colimit_add_mk_eq _ ⟨i]; rw [_⟩ ⟨j]; rw [_⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]; rw [map_smul]; rw [map_smul]
  add_smul r s x := by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    simp [_root_.add_smul, colimit_add_mk_eq'] }

中文:
实例 colimitModule
  签名: : 模 R (M F)
  定义体: { colimitMulAction F,
  colimitSMulWithZero F with
  smul_add := fun r x y => by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    obtain ⟨j, y, rfl⟩ := M.mk_surjective F y
    rw [colimit_smul_mk_eq]; rw [colimit_smul_mk_eq]; rw [colimit_add_mk_eq _ ⟨i]; rw [_⟩ ⟨j]; rw [_⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]; rw [colimit_smul_mk_eq]; rw [smul_add]; rw [colimit_add_mk_eq _ ⟨i]; rw [_⟩ ⟨j]; rw [_⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]; rw [map_smul]; rw [map_smul]
  add_smul r s x := by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    simp [_root_.add_smul, colimit_add_mk_eq'] }

Depends on / 依赖: IsFiltered, IsFiltered.leftToMax, IsFiltered.rightToMax, M.mk_surjective, colimitMulAction, colimitSMulWithZero, colimit_add_mk_eq, colimit_smul_mk_eq, leftToMax, map_smul, mk_surjective, rightToMax, smul_add
-/
instance colimitModule : Module R (M F) :=
{ colimitMulAction F,
  colimitSMulWithZero F with
  smul_add := fun r x y => by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    obtain ⟨j, y, rfl⟩ := M.mk_surjective F y
    rw [colimit_smul_mk_eq]; rw [colimit_smul_mk_eq]; rw [colimit_add_mk_eq _ ⟨i]; rw [_⟩ ⟨j]; rw [_⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]; rw [colimit_smul_mk_eq]; rw [smul_add]; rw [colimit_add_mk_eq _ ⟨i]; rw [_⟩ ⟨j]; rw [_⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j)]; rw [map_smul]; rw [map_smul]
  add_smul r s x := by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    simp [_root_.add_smul, colimit_add_mk_eq'] }

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : ModuleCat.{max v u, u} R
  body: ModuleCat.of R (M F)

中文:
定义 colimit
  签名: : 模范畴.{最大值 v u, u} R
  定义体: ModuleCat.of R (M F)

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
def colimit : ModuleCat.{max v u, u} R :=
  ModuleCat.of R (M F)

/--
Definition of `coconeMorphism` / `coconeMorphism` 的定义

English:
definition coconeMorphism
  signature: (j : J)
  body: ofHom
    { ((AddCommGrpCat.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})).ι.app j).hom with
    map_smul' := by solve_by_elim }

中文:
定义 coconeMorphism
  签名: (j : J)
  定义体: ofHom
    { ((AddCommGrpCat.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})).ι.app j).hom with
    map_smul' := by solve_by_elim }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimitCocone, FilteredColimits, ModuleCat, colimitCocone, map_smul, solve_by_elim
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
    { ((AddCommGrpCat.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})).ι.app j).hom with
    map_smul' := by solve_by_elim }

/-- The cocone over the proposed colimit module. -/
@[implicit_reducible]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit F
  ι :=
    { app := coconeMorphism F
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget (ModuleCat R))).ι.naturality_apply f _ }

中文:
定义 colimitCocone
  签名: : 余锥 F where
  定义体: colimit F
  ι :=
    { app := coconeMorphism F
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget (ModuleCat R))).ι.naturality_apply f _ }

Depends on / 依赖: colimit
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := coconeMorphism F
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget (ModuleCat R))).ι.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitDesc` / `colimitDesc` 的定义

English:
definition colimitDesc
  signature: (t : Cocone F)
  body: let h := (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  let f : colimit F ->+ t.pt := (h.desc ((forget₂ _ _).mapCocone t)).hom
  have hf {j : J} (x : F.obj j) : f (M.mk _ ⟨j, x⟩) = t.ι.app j x :=
    congr_hom ((forget AddCommGrpCat).congr_map (h.fac ((forget₂ _ _).mapCocone t) j)) x
  ofHom
    { f with
      map_smul' := fun r x => by
        obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
        simp [hf] }

中文:
定义 colimitDesc
  签名: (t : 余锥 F)
  定义体: let h := (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  let f : colimit F ->+ t.pt := (h.desc ((forget₂ _ _).mapCocone t)).hom
  have hf {j : J} (x : F.obj j) : f (M.mk _ ⟨j, x⟩) = t.ι.app j x :=
    congr_hom ((forget AddCommGrpCat).congr_map (h.fac ((forget₂ _ _).mapCocone t) j)) x
  ofHom
    { f with
      map_smul' := fun r x => by
        obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
        simp [hf] }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit, F.obj, FilteredColimits, M.mk, M.mk_surjective, colimit, colimitCoconeIsColimit, congr_hom, congr_map, forget, h.desc, h.fac, mapCocone, map_smul, mk_surjective, t.pt
-/
def colimitDesc (t : Cocone F) : colimit F ⟶ t.pt :=
  let h := (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  let f : colimit F ->+ t.pt := (h.desc ((forget₂ _ _).mapCocone t)).hom
  have hf {j : J} (x : F.obj j) : f (M.mk _ ⟨j, x⟩) = t.ι.app j x :=
    congr_hom ((forget AddCommGrpCat).congr_map (h.fac ((forget₂ _ _).mapCocone t) j)) x
  ofHom
    { f with
      map_smul' := fun r x => by
        obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
        simp [hf] }

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_colimitDesc` / 引理 `ι_colimitDesc`

English:
lemma ι_colimitDesc
  given: (t : Cocone F) (j : J)
  proof: (forget₂ _ AddCommGrpCat).map_injective
    ((AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

中文:
引理 ι_colimitDesc
  条件: (t : 余锥 F) (j : J)
  证明: (forget₂ _ AddCommGrpCat).map_injective
    ((AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit, FilteredColimits, colimitCoconeIsColimit, map_injective
-/
lemma ι_colimitDesc (t : Cocone F) (j : J) :
    dsimp% (colimitCocone F).ι.app j ≫ colimitDesc F t = t.ι.app j :=
  (forget₂ _ AddCommGrpCat).map_injective
    ((AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit (colimitCocone F) where
  body: colimitDesc F
  fac t j := by simp
  uniq t _ h := by
    ext ⟨j, x⟩
    exact (congr_hom ((forget (ModuleCat _)).congr_map (h j)) _).trans
      (congr_hom ((forget (ModuleCat _)).congr_map (ι_colimitDesc F t j)) x).symm

中文:
定义 colimitCoconeIsColimit
  签名: : 是余极限 (colimitCocone F) where
  定义体: colimitDesc F
  fac t j := by simp
  uniq t _ h := by
    ext ⟨j, x⟩
    exact (congr_hom ((forget (ModuleCat _)).congr_map (h j)) _).trans
      (congr_hom ((forget (ModuleCat _)).congr_map (ι_colimitDesc F t j)) x).symm

Depends on / 依赖: colimitDesc
-/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac t j := by simp
  uniq t _ h := by
    ext ⟨j, x⟩
    exact (congr_hom ((forget (ModuleCat _)).congr_map (h j)) _).trans
      (congr_hom ((forget (ModuleCat _)).congr_map (ι_colimitDesc F t j)) x).symm

/--
Instance `forget₂AddCommGroup_preservesFilteredColimits` / 实例 `forget₂AddCommGroup_preservesFilteredColimits`

English:
instance forget₂AddCommGroup_preservesFilteredColimits
  signature: :
  body: { preservesColimit := fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
        (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) }

中文:
实例 forget₂AddCommGroup_preservesFilteredColimits
  签名: :
  定义体: { preservesColimit := fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
        (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit, FilteredColimits, ModuleCat, colimitCoconeIsColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance forget₂AddCommGroup_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
  { preservesColimit := fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
        (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) }

/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: : PreservesFilteredColimits (forget (ModuleCat.{u} R))
  body: Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrpCat)
    (forget AddCommGrpCat)

中文:
实例 forget_preservesFilteredColimits
  签名: : PreservesFilteredColimits (forget (模范畴.{u} R))
  定义体: Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrpCat)
    (forget AddCommGrpCat)

Depends on / 依赖: AddCommGrpCat, Limits, Limits.comp_preservesFilteredColimits, ModuleCat, comp_preservesFilteredColimits, forget
-/
instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrpCat)
    (forget AddCommGrpCat)

/--
Instance `forget_reflectsFilteredColimits` / 实例 `forget_reflectsFilteredColimits`

English:
instance forget_reflectsFilteredColimits
  signature: : ReflectsFilteredColimits (forget (ModuleCat.{u} R)) where
  body: { reflectsColimit := reflectsColimit_of_reflectsIsomorphisms _ _ }

中文:
实例 forget_reflectsFilteredColimits
  签名: : ReflectsFilteredColimits (forget (模范畴.{u} R)) where
  定义体: { reflectsColimit := reflectsColimit_of_reflectsIsomorphisms _ _ }

Depends on / 依赖: reflectsColimit, reflectsColimit_of_reflectsIsomorphisms
-/
instance forget_reflectsFilteredColimits : ReflectsFilteredColimits (forget (ModuleCat.{u} R)) where
  reflects_filtered_colimits _ := { reflectsColimit := reflectsColimit_of_reflectsIsomorphisms _ _ }

end

end ModuleCat.FilteredColimits
