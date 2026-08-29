/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ GrpCat`.
We show that the colimit of `F ⋙ forget₂ GrpCat MonCat` (in `MonCat`) carries the structure of a
group,
thereby showing that the forgetful functor `forget₂ GrpCat MonCat` preserves filtered colimits.
In particular, this implies that `forget GrpCat` preserves filtered colimits.
Similarly for `AddGrpCat`, `CommGrpCat` and `AddCommGrpCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max -> max' -- avoid name collision with `_root_.max`.

namespace GrpCat.FilteredColimits

section

-- Mathlib3 used parameters here, mainly so we could have the abbreviations `G` and `G.mk` below,
-- without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

/-- The colimit of `F ⋙ forget₂ GrpCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive
  /-- The colimit of `F ⋙ forget₂ AddGrpCat AddMonCat` in the category `AddMonCat`.
  In the following, we will show that this has the structure of an additive group. -/]
/--
Definition of `G` / `G` 的定义

English:
abbreviation G
  signature: : MonCat
  body: MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ GrpCat MonCat.{max v u})

中文:
缩写 G
  签名: : MonCat
  定义体: MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ GrpCat MonCat.{max v u})

Depends on / 依赖: FilteredColimits, GrpCat, MonCat, MonCat.FilteredColimits.colimit, colimit
-/
noncomputable abbrev G : MonCat :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ GrpCat MonCat.{max v u})

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive /-- The canonical projection into the colimit, as a quotient type. -/]
/--
Definition of `G.mk` / `G.mk` 的定义

English:
abbreviation G.mk
  signature: : (Σ j, F.obj j) -> G.{v, u} F
  body: fun x => (F ⋙ forget GrpCat).ιColimitType x.1 x.2

@[to_additive]

中文:
缩写 G.mk
  签名: : (Σ j, F.obj j) -> G.{v, u} F
  定义体: fun x => (F ⋙ forget GrpCat).ιColimitType x.1 x.2

@[to_additive]

Depends on / 依赖: GrpCat, forget
-/
abbrev G.mk : (Σ j, F.obj j) -> G.{v, u} F :=
  fun x => (F ⋙ forget GrpCat).ιColimitType x.1 x.2

@[to_additive]
/--
theorem `G.mk_eq` / 定理 `G.mk_eq`

English:
theorem G.mk_eq
  statement: (x y : Σ j, F.obj j)
  proof: Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget GrpCat) x y h)

@[to_additive]

中文:
定理 G.mk_eq
  结论: (x y : Σ j, F.obj j)
  证明: Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget GrpCat) x y h)

@[to_additive]

Depends on / 依赖: FilteredColimit, GrpCat, Quot.eqvGen_sound, Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel, eqvGen_colimitTypeRel_of_rel, eqvGen_sound, forget
-/
theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : exists (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    G.mk.{v, u} F x = G.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget GrpCat) x y h)

@[to_additive]
/--
theorem `colimit_one_eq` / 定理 `colimit_one_eq`

English:
theorem colimit_one_eq
  given: (j : J)
  statement: (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩
  proof: MonCat.FilteredColimits.colimit_one_eq _ _

@[to_additive]

中文:
定理 colimit_one_eq
  条件: (j : J)
  结论: (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩
  证明: MonCat.FilteredColimits.colimit_one_eq _ _

@[to_additive]

Depends on / 依赖: FilteredColimits, MonCat, MonCat.FilteredColimits.colimit_one_eq, colimit_one_eq
-/
theorem colimit_one_eq (j : J) : (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩ :=
  MonCat.FilteredColimits.colimit_one_eq _ _

@[to_additive]
/--
theorem `colimit_mul_mk_eq` / 定理 `colimit_mul_mk_eq`

English:
theorem colimit_mul_mk_eq
  given: (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k)
  proof: MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

@[to_additive]

中文:
定理 colimit_mul_mk_eq
  条件: (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k)
  证明: MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

@[to_additive]

Depends on / 依赖: FilteredColimits, MonCat, MonCat.FilteredColimits.colimit_mul_mk_eq, colimit_mul_mk_eq
-/
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    G.mk.{v, u} F x * G.mk F y = G.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ :=
  MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

@[to_additive]
/--
lemma `colimit_mul_mk_eq'` / 引理 `colimit_mul_mk_eq'`

English:
lemma colimit_mul_mk_eq'
  given: {j : J} (x y : F.obj j)
  proof: by
  #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  `simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  have := colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  simpa using this

中文:
引理 colimit_mul_mk_eq'
  条件: {j : J} (x y : F.obj j)
  证明: by
  #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  `simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  have := colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  simpa using this

Depends on / 依赖: adaptation_note, colimit_mul_mk_eq, leanprover
-/
lemma colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    G.mk.{v, u} F ⟨j, x⟩ * G.mk.{v, u} F ⟨j, y⟩ = G.mk.{v, u} F ⟨j, x * y⟩ := by
  #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  `simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  have := colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  simpa using this

/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive /-- The "unlifted" version of negation in the colimit. -/]
/--
Definition of `colimitInvAux` / `colimitInvAux` 的定义

English:
definition colimitInvAux
  signature: (x : Σ j, F.obj j)
  body: G.mk F ⟨x.1, x.2⁻¹⟩

@[to_additive]

中文:
定义 colimitInvAux
  签名: (x : Σ j, F.obj j)
  定义体: G.mk F ⟨x.1, x.2⁻¹⟩

@[to_additive]

Depends on / 依赖: G.mk
-/
def colimitInvAux (x : Σ j, F.obj j) : G.{v, u} F :=
  G.mk F ⟨x.1, x.2⁻¹⟩

@[to_additive]
/--
theorem `colimitInvAux_eq_of_rel` / 定理 `colimitInvAux_eq_of_rel`

English:
theorem colimitInvAux_eq_of_rel
  statement: (x y : Σ j, F.obj j)
  proof: by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv]; rw [map_inv]; rw [inv_inj]
  exact hfg

中文:
定理 colimitInvAux_eq_of_rel
  结论: (x y : Σ j, F.obj j)
  证明: by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv]; rw [map_inv]; rw [inv_inj]
  exact hfg

Depends on / 依赖: G.mk_eq, inv_inj, map_inv, mk_eq
-/
theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget GrpCat) x y) :
    colimitInvAux.{v, u} F x = colimitInvAux F y := by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv]; rw [map_inv]; rw [inv_inj]
  exact hfg

/-- Taking inverses in the colimit. See also `colimitInvAux`. -/
@[to_additive /-- Negation in the colimit. See also `colimitNegAux`. -/]
/--
Instance `colimitInv` / 实例 `colimitInv`

English:
instance colimitInv
  signature: : Inv (G.{v, u} F) where
  body: by
    refine Quot.lift (colimitInvAux.{v, u} F) ?_ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

@[to_additive (attr := simp)]

中文:
实例 colimitInv
  签名: : Inv (G.{v, u} F) where
  定义体: by
    refine Quot.lift (colimitInvAux.{v, u} F) ?_ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

@[to_additive (attr := simp)]

Depends on / 依赖: FilteredColimit, Quot.lift, Types.FilteredColimit.rel_of_colimitTypeRel, colimitInvAux, colimitInvAux_eq_of_rel, rel_of_colimitTypeRel
-/
instance colimitInv : Inv (G.{v, u} F) where
  inv x := by
    refine Quot.lift (colimitInvAux.{v, u} F) ?_ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

@[to_additive (attr := simp)]
/--
theorem `colimit_inv_mk_eq` / 定理 `colimit_inv_mk_eq`

English:
theorem colimit_inv_mk_eq
  given: (x : Σ j, F.obj j)
  statement: (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩
  proof: rfl

@[to_additive]

中文:
定理 colimit_inv_mk_eq
  条件: (x : Σ j, F.obj j)
  结论: (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩
  证明: rfl

@[to_additive]
-/
theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩ :=
  rfl

@[to_additive]
/--
Instance `colimitGroup` / 实例 `colimitGroup`

English:
instance colimitGroup
  signature: : Group (G.{v, u} F)
  body: { colimitInv.{v, u} F, (G.{v, u} F).str with
    inv_mul_cancel := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      change (G.mk _ _)⁻¹ * G.mk _ _ = _
      obtain ⟨j, x⟩ := x
      simp [colimit_inv_mk_eq, colimit_mul_mk_eq F ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq

中文:
实例 colimitGroup
  签名: : Group (G.{v, u} F)
  定义体: { colimitInv.{v, u} F, (G.{v, u} F).str with
    inv_mul_cancel := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      change (G.mk _ _)⁻¹ * G.mk _ _ = _
      obtain ⟨j, x⟩ := x
      simp [colimit_inv_mk_eq, colimit_mul_mk_eq F ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq

Depends on / 依赖: G.mk, Quot.inductionOn, colimitInv, colimit_inv_mk_eq, colimit_mul_mk_eq, colimit_one_eq, inductionOn, inv_mul_cancel
-/
noncomputable instance colimitGroup : Group (G.{v, u} F) :=
  { colimitInv.{v, u} F, (G.{v, u} F).str with
    inv_mul_cancel := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      change (G.mk _ _)⁻¹ * G.mk _ _ = _
      obtain ⟨j, x⟩ := x
      simp [colimit_inv_mk_eq, colimit_mul_mk_eq F ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq F j] }

/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive /-- The bundled additive group giving the filtered colimit of a diagram. -/]
/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : GrpCat.{max v u}
  body: GrpCat.of (G.{v, u} F)

中文:
定义 colimit
  签名: : GrpCat.{max v u}
  定义体: GrpCat.of (G.{v, u} F)

Depends on / 依赖: GrpCat, GrpCat.of
-/
noncomputable def colimit : GrpCat.{max v u} :=
  GrpCat.of (G.{v, u} F)

/-- The cocone over the proposed colimit group. -/
@[to_additive /-- The cocone over the proposed colimit additive group. -/]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι.app J := GrpCat.ofHom ((MonCat.FilteredColimits.colimitCocone
    (F ⋙ forget₂ GrpCat MonCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ MonCat).map_injective
    ((MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ GrpCat MonCat)).ι.naturality f)

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι.app J := GrpCat.ofHom ((MonCat.FilteredColimits.colimitCocone
    (F ⋙ forget₂ GrpCat MonCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ MonCat).map_injective
    ((MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ GrpCat MonCat)).ι.naturality f)

Depends on / 依赖: colimit
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app J := GrpCat.ofHom ((MonCat.FilteredColimits.colimitCocone
    (F ⋙ forget₂ GrpCat MonCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ MonCat).map_injective
    ((MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ GrpCat MonCat)).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `GrpCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddGroup`. -/]
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit (colimitCocone.{v, u} F)
  body: isColimitOfReflects (forget₂ _ MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ GrpCat MonCat))

@[to_additive forget₂AddMon_preservesFilteredColimits]

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit (colimitCocone.{v, u} F)
  定义体: isColimitOfReflects (forget₂ _ MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ GrpCat MonCat))

@[to_additive forget₂AddMon_preservesFilteredColimits]

Depends on / 依赖: FilteredColimits, GrpCat, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, isColimitOfReflects
-/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ _ MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ GrpCat MonCat))

@[to_additive forget₂AddMon_preservesFilteredColimits]
/--
Instance `forget₂Mon_preservesFilteredColimits` / 实例 `forget₂Mon_preservesFilteredColimits`

English:
instance forget₂Mon_preservesFilteredColimits
  signature: :
  body: letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩

@[to_additive]

中文:
实例 forget₂Mon_preservesFilteredColimits
  签名: :
  定义体: letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩

@[to_additive]

Depends on / 依赖: Category, FilteredColimits, MonCat, MonCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits.{u} (forget₂ GrpCat.{u} MonCat.{u}) where
      preserves_filtered_colimits x hx1 _ :=
      letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩

@[to_additive]
/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: :
  body: Limits.comp_preservesFilteredColimits (forget₂ GrpCat MonCat) (forget MonCat.{u})

中文:
实例 forget_preservesFilteredColimits
  签名: :
  定义体: Limits.comp_preservesFilteredColimits (forget₂ GrpCat MonCat) (forget MonCat.{u})

Depends on / 依赖: GrpCat, Limits, Limits.comp_preservesFilteredColimits, MonCat, comp_preservesFilteredColimits, forget
-/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget GrpCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ GrpCat MonCat) (forget MonCat.{u})

end

end GrpCat.FilteredColimits

namespace CommGrpCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommGrpCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommGrpCat GrpCat` in the category `GrpCat`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive
  /-- The colimit of `F ⋙ forget₂ AddCommGrpCat AddGrpCat` in the category `AddGrpCat`.
  In the following, we will show that this has the structure of a _commutative_ additive group. -/]
/--
Definition of `G` / `G` 的定义

English:
abbreviation G
  signature: : GrpCat.{max v u}
  body: GrpCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGrpCat.{max v u} GrpCat.{max v u})

@[to_additive]

中文:
缩写 G
  签名: : GrpCat.{max v u}
  定义体: GrpCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGrpCat.{max v u} GrpCat.{max v u})

@[to_additive]

Depends on / 依赖: CommGrpCat, FilteredColimits, GrpCat, GrpCat.FilteredColimits.colimit, colimit
-/
noncomputable abbrev G : GrpCat.{max v u} :=
  GrpCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGrpCat.{max v u} GrpCat.{max v u})

@[to_additive]
/--
Instance `colimitCommGroup` / 实例 `colimitCommGroup`

English:
instance colimitCommGroup
  signature: : CommGroup.{max v u} (G.{v, u} F)
  body: { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGrpCat CommMonCat.{max v u}) with }

中文:
实例 colimitCommGroup
  签名: : CommGroup.{max v u} (G.{v, u} F)
  定义体: { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGrpCat CommMonCat.{max v u}) with }

Depends on / 依赖: CommGrpCat, CommMonCat, CommMonCat.FilteredColimits.colimitCommMonoid, FilteredColimits, colimitCommMonoid
-/
noncomputable instance colimitCommGroup : CommGroup.{max v u} (G.{v, u} F) :=
  { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGrpCat CommMonCat.{max v u}) with }

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive
/-- The bundled additive commutative group giving the filtered colimit of a diagram. -/]
/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : CommGrpCat
  body: CommGrpCat.of (G.{v, u} F)

中文:
定义 colimit
  签名: : CommGrpCat
  定义体: CommGrpCat.of (G.{v, u} F)

Depends on / 依赖: CommGrpCat, CommGrpCat.of
-/
noncomputable def colimit : CommGrpCat :=
  CommGrpCat.of (G.{v, u} F)

/-- The cocone over the proposed colimit commutative group. -/
@[to_additive /-- The cocone over the proposed colimit additive commutative group. -/]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit.{v, u} F
  ι.app J := CommGrpCat.ofHom
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ GrpCat).map_injective
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.naturality f)

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimit.{v, u} F
  ι.app J := CommGrpCat.ofHom
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ GrpCat).map_injective
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.naturality f)

Depends on / 依赖: colimit
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app J := CommGrpCat.ofHom
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ GrpCat).map_injective
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `CommGrpCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddCommGroup`. -/]
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: : IsColimit (colimitCocone.{v, u} F)
  body: isColimitOfReflects (forget₂ _ GrpCat)
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrpCat GrpCat))

@[to_additive]

中文:
定义 colimitCoconeIsColimit
  签名: : IsColimit (colimitCocone.{v, u} F)
  定义体: isColimitOfReflects (forget₂ _ GrpCat)
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrpCat GrpCat))

@[to_additive]

Depends on / 依赖: CommGrpCat, FilteredColimits, GrpCat, GrpCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, isColimitOfReflects
-/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ _ GrpCat)
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrpCat GrpCat))

@[to_additive]
/--
Instance `forget₂Group_preservesFilteredColimits` / 实例 `forget₂Group_preservesFilteredColimits`

English:
instance forget₂Group_preservesFilteredColimits
  signature: :
  body: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGrpCat GrpCat.{u})) }

@[to_additive]

中文:
实例 forget₂Group_preservesFilteredColimits
  签名: :
  定义体: letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGrpCat GrpCat.{u})) }

@[to_additive]

Depends on / 依赖: Category, CommGrpCat, FilteredColimits, GrpCat, GrpCat.FilteredColimits.colimitCoconeIsColimit, colimitCoconeIsColimit, preservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance forget₂Group_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommGrpCat GrpCat.{u}) where
  preserves_filtered_colimits J hJ1 _ :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGrpCat GrpCat.{u})) }

@[to_additive]
/--
Instance `forget_preservesFilteredColimits` / 实例 `forget_preservesFilteredColimits`

English:
instance forget_preservesFilteredColimits
  signature: :
  body: Limits.comp_preservesFilteredColimits (forget₂ CommGrpCat GrpCat) (forget GrpCat.{u})

中文:
实例 forget_preservesFilteredColimits
  签名: :
  定义体: Limits.comp_preservesFilteredColimits (forget₂ CommGrpCat GrpCat) (forget GrpCat.{u})

Depends on / 依赖: CommGrpCat, GrpCat, Limits, Limits.comp_preservesFilteredColimits, comp_preservesFilteredColimits, forget
-/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommGrpCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommGrpCat GrpCat) (forget GrpCat.{u})

end

end CommGrpCat.FilteredColimits
