/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!

# Residue fields of points

Any point `x` of a locally ringed space `X` comes with a natural residue field, namely the residue
field of the stalk at `x`. Moreover, for every open subset of `X` containing `x`, we have a
canonical evaluation map from `Γ(X, U)` to the residue field of `X` at `x`.

## Main definitions

The following are in the `AlgebraicGeometry.LocallyRingedSpace` namespace:

- `residueField`: the residue field of the stalk at `x`.
- `evaluation`: for open subsets `U` of `X` containing `x`, the evaluation map from sections over
  `U` to the residue field at `x`.
- `evaluationMap`: a morphism of locally ringed spaces induces a morphism, i.e. extension, of
  residue fields.

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) {U : Opens X}

/--
Definition of `residueField` / `residueField` 的定义

English:
definition residueField
  signature: (x : X)
  body: CommRingCat.of IsLocalRing.ResidueField (X.presheaf.stalk x)

中文:
定义 residueField
  签名: (x : X)
  定义体: CommRingCat.of IsLocalRing.ResidueField (X.presheaf.stalk x)

Depends on / 依赖: CommRingCat, CommRingCat.of, IsLocalRing, IsLocalRing.ResidueField, ResidueField, X.presheaf.stalk, presheaf
-/
def residueField (x : X) : CommRingCat :=
CommRingCat.of IsLocalRing.ResidueField (X.presheaf.stalk x)

instance (x : X) : Field (X.residueField x) :=
inferInstanceAs Field (IsLocalRing.ResidueField (X.presheaf.stalk x))

/--
Definition of `residue` / `residue` 的定义

English:
definition residue
  signature: (X : LocallyRingedSpace.{u}) (x : X)
  body: CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

中文:
定义 residue
  签名: (X : LocallyRingedSpace.{u}) (x : X)
  定义体: CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalRing, IsLocalRing.residue, X.presheaf.stalk, presheaf, residue
-/
def residue (X : LocallyRingedSpace.{u}) (x : X) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

/--
lemma `residue_surjective` / 引理 `residue_surjective`

English:
lemma residue_surjective
  given: (x : X)
  statement: Function.Surjective (X.residue x)
  proof: Ideal.Quotient.mk_surjective

中文:
引理 residue_surjective
  条件: (x : X)
  结论: Function.Surjective (X.residue x)
  证明: Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
lemma residue_surjective (x : X) : Function.Surjective (X.residue x) :=
  Ideal.Quotient.mk_surjective

instance (x : X) : Epi (X.residue x) :=
  ConcreteCategory.epi_of_surjective _ (X.residue_surjective x)

/--
Definition of `evaluation` / `evaluation` 的定义

English:
definition evaluation
  signature: (x : U)
  body: X.presheaf.germ U x.1 x.2 ≫ X.residue _

中文:
定义 evaluation
  签名: (x : U)
  定义体: X.presheaf.germ U x.1 x.2 ≫ X.residue _

Depends on / 依赖: X.presheaf.germ, X.residue, presheaf, residue
-/
def evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x :=
  X.presheaf.germ U x.1 x.2 ≫ X.residue _

/--
Definition of `Γevaluation` / `Γevaluation` 的定义

English:
definition Γevaluation
  signature: (x : X)
  body: X.evaluation ⟨x, show x in ⊤ from trivial⟩

中文:
定义 Γevaluation
  签名: (x : X)
  定义体: X.evaluation ⟨x, show x in ⊤ from trivial⟩

Depends on / 依赖: X.evaluation, evaluation
-/
def Γevaluation (x : X) : X.presheaf.obj (op ⊤) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x in ⊤ from trivial⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `evaluation_eq_zero_iff_notMem_basicOpen` / 引理 `evaluation_eq_zero_iff_notMem_basicOpen`

English:
lemma evaluation_eq_zero_iff_notMem_basicOpen
  given: (x : U) (f : X.presheaf.obj (op U))
  proof: by
  rw [X.toRingedSpace.mem_basicOpen f x.1 x.2]; rw [← not_iff_not]; rw [not_not]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _)

中文:
引理 evaluation_eq_zero_iff_notMem_basicOpen
  条件: (x : U) (f : X.presheaf.obj (op U))
  证明: by
  rw [X.toRingedSpace.mem_basicOpen f x.1 x.2]; rw [← not_iff_not]; rw [not_not]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _)

Depends on / 依赖: IsLocalRing, IsLocalRing.residue_ne_zero_iff_isUnit, X.toRingedSpace.mem_basicOpen, mem_basicOpen, not_iff_not, not_not, residue_ne_zero_iff_isUnit, toRingedSpace
-/
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f := by
  rw [X.toRingedSpace.mem_basicOpen f x.1 x.2]; rw [← not_iff_not]; rw [not_not]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _)

/--
lemma `evaluation_ne_zero_iff_mem_basicOpen` / 引理 `evaluation_ne_zero_iff_mem_basicOpen`

English:
lemma evaluation_ne_zero_iff_mem_basicOpen
  given: (x : U) (f : X.presheaf.obj (op U))
  proof: by
  simp

中文:
引理 evaluation_ne_zero_iff_mem_basicOpen
  条件: (x : U) (f : X.presheaf.obj (op U))
  证明: by
  simp
-/
lemma evaluation_ne_zero_iff_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f != 0 ↔ x.val in X.toRingedSpace.basicOpen f := by
  simp

/--
lemma `basicOpen_eq_bot_iff_forall_evaluation_eq_zero` / 引理 `basicOpen_eq_bot_iff_forall_evaluation_eq_zero`

English:
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero
  given: (f : X.presheaf.obj (op U))
  proof: by
  simp only [evaluation_eq_zero_iff_notMem_basicOpen, Subtype.forall]
  exact ⟨fun h => h ▸ fun a _ hc => hc,
fun h => eq_bot_iff.mpr fun a ha => h a (X.toRingedSpace.basicOpen_le f ha) ha⟩

@[simp]

中文:
引理 basicOpen_eq_bot_iff_forall_evaluation_eq_zero
  条件: (f : X.presheaf.obj (op U))
  证明: by
  simp only [evaluation_eq_zero_iff_notMem_basicOpen, Subtype.forall]
  exact ⟨fun h => h ▸ fun a _ hc => hc,
fun h => eq_bot_iff.mpr fun a ha => h a (X.toRingedSpace.basicOpen_le f ha) ha⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.forall, X.toRingedSpace.basicOpen_le, basicOpen_le, eq_bot_iff, eq_bot_iff.mpr, evaluation_eq_zero_iff_notMem_basicOpen, toRingedSpace
-/
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.toRingedSpace.basicOpen f = ⊥ ↔ forall (x : U), X.evaluation x f = 0 := by
  simp only [evaluation_eq_zero_iff_notMem_basicOpen, Subtype.forall]
  exact ⟨fun h => h ▸ fun a _ hc => hc,
fun h => eq_bot_iff.mpr fun a ha => h a (X.toRingedSpace.basicOpen_le f ha) ha⟩

@[simp]
/--
lemma `Γevaluation_eq_zero_iff_notMem_basicOpen` / 引理 `Γevaluation_eq_zero_iff_notMem_basicOpen`

English:
lemma Γevaluation_eq_zero_iff_notMem_basicOpen
  given: (x : X) (f : X.presheaf.obj (op ⊤))
  proof: evaluation_eq_zero_iff_notMem_basicOpen X ⟨x, show x in ⊤ by trivial⟩ f

中文:
引理 Γevaluation_eq_zero_iff_notMem_basicOpen
  条件: (x : X) (f : X.presheaf.obj (op ⊤))
  证明: evaluation_eq_zero_iff_notMem_basicOpen X ⟨x, show x in ⊤ by trivial⟩ f

Depends on / 依赖: evaluation_eq_zero_iff_notMem_basicOpen
-/
lemma Γevaluation_eq_zero_iff_notMem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f = 0 ↔ x ∉ X.toRingedSpace.basicOpen f :=
  evaluation_eq_zero_iff_notMem_basicOpen X ⟨x, show x in ⊤ by trivial⟩ f

/--
lemma `Γevaluation_ne_zero_iff_mem_basicOpen` / 引理 `Γevaluation_ne_zero_iff_mem_basicOpen`

English:
lemma Γevaluation_ne_zero_iff_mem_basicOpen
  given: (x : X) (f : X.presheaf.obj (op ⊤))
  proof: evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x in ⊤ by trivial⟩ f

中文:
引理 Γevaluation_ne_zero_iff_mem_basicOpen
  条件: (x : X) (f : X.presheaf.obj (op ⊤))
  证明: evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x in ⊤ by trivial⟩ f

Depends on / 依赖: evaluation_ne_zero_iff_mem_basicOpen
-/
lemma Γevaluation_ne_zero_iff_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f != 0 ↔ x in X.toRingedSpace.basicOpen f :=
  evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x in ⊤ by trivial⟩ f

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)

/--
Definition of `residueFieldMap` / `residueFieldMap` 的定义

English:
definition residueFieldMap
  signature: (x : X)
  body: CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)

@[reassoc]

中文:
定义 residueFieldMap
  签名: (x : X)
  定义体: CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)

@[reassoc]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalRing, IsLocalRing.ResidueField.map, ResidueField, f.stalkMap, stalkMap
-/
def residueFieldMap (x : X) : Y.residueField (f.base x) ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)

@[reassoc]
/--
lemma `residue_comp_residueFieldMap_eq_stalkMap_comp_residue` / 引理 `residue_comp_residueFieldMap_eq_stalkMap_comp_residue`

English:
lemma residue_comp_residueFieldMap_eq_stalkMap_comp_residue
  given: (x : X)
  proof: by
  simp [residueFieldMap]
  rfl

@[simp]

中文:
引理 residue_comp_residueFieldMap_eq_stalkMap_comp_residue
  条件: (x : X)
  证明: by
  simp [residueFieldMap]
  rfl

@[simp]

Depends on / 依赖: residueFieldMap
-/
lemma residue_comp_residueFieldMap_eq_stalkMap_comp_residue (x : X) :
    Y.residue _ ≫ residueFieldMap f x = f.stalkMap x ≫ X.residue _ := by
  simp [residueFieldMap]
  rfl

@[simp]
/--
lemma `residueFieldMap_id` / 引理 `residueFieldMap_id`

English:
lemma residueFieldMap_id
  given: (x : X)
  proof: by
  ext : 1
  simp only [residueFieldMap, stalkMap_id]
  apply IsLocalRing.ResidueField.map_id

中文:
引理 residueFieldMap_id
  条件: (x : X)
  证明: by
  ext : 1
  simp only [residueFieldMap, stalkMap_id]
  apply IsLocalRing.ResidueField.map_id

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.map_id, ResidueField, map_id, residueFieldMap, stalkMap_id
-/
lemma residueFieldMap_id (x : X) :
    residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) := by
  ext : 1
  simp only [residueFieldMap, stalkMap_id]
  apply IsLocalRing.ResidueField.map_id

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `residueFieldMap_comp` / 引理 `residueFieldMap_comp`

English:
lemma residueFieldMap_comp
  given: {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X)
  proof: by
  ext : 1
  simp only [residueFieldMap, stalkMap_comp]
  apply IsLocalRing.ResidueField.map_comp (Hom.stalkMap g (f.base x)).hom (Hom.stalkMap f x).hom

中文:
引理 residueFieldMap_comp
  条件: {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X)
  证明: by
  ext : 1
  simp only [residueFieldMap, stalkMap_comp]
  apply IsLocalRing.ResidueField.map_comp (Hom.stalkMap g (f.base x)).hom (Hom.stalkMap f x).hom

Depends on / 依赖: Hom.stalkMap, IsLocalRing, IsLocalRing.ResidueField.map_comp, ResidueField, f.base, map_comp, residueFieldMap, stalkMap, stalkMap_comp
-/
lemma residueFieldMap_comp {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X) :
    residueFieldMap (f ≫ g) x = residueFieldMap g (f.base x) ≫ residueFieldMap f x := by
  ext : 1
  simp only [residueFieldMap, stalkMap_comp]
  apply IsLocalRing.ResidueField.map_comp (Hom.stalkMap g (f.base x)).hom (Hom.stalkMap f x).hom

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `evaluation_naturality` / 引理 `evaluation_naturality`

English:
lemma evaluation_naturality
  given: {V : Opens Y} (x : (Opens.map f.base).obj V)
  proof: by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.residueFieldMap]
  rw [Category.assoc]
  ext a
  simp only [CommRingCat.comp_apply]
  erw [IsLocalRing.ResidueField.map_residue]
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  rfl

中文:
引理 evaluation_naturality
  条件: {V : Opens Y} (x : (Opens.map f.base).obj V)
  证明: by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.residueFieldMap]
  rw [Category.assoc]
  ext a
  simp only [CommRingCat.comp_apply]
  erw [IsLocalRing.ResidueField.map_residue]
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  rfl

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.comp_apply, IsLocalRing, IsLocalRing.ResidueField.map_residue, LocallyRingedSpace, LocallyRingedSpace.evaluation, LocallyRingedSpace.residueFieldMap, LocallyRingedSpace.stalkMap_germ_apply, ResidueField, comp_apply, evaluation, map_residue, residueFieldMap, stalkMap_germ_apply
-/
lemma evaluation_naturality {V : Opens Y} (x : (Opens.map f.base).obj V) :
    Y.evaluation ⟨f.base x, x.property⟩ ≫ residueFieldMap f x.val =
      f.c.app (op V) ≫ X.evaluation x := by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.residueFieldMap]
  rw [Category.assoc]
  ext a
  simp only [CommRingCat.comp_apply]
  erw [IsLocalRing.ResidueField.map_residue]
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  rfl

/--
lemma `evaluation_naturality_apply` / 引理 `evaluation_naturality_apply`

English:
lemma evaluation_naturality_apply
  statement: {V : Opens Y} (x : (Opens.map f.base).obj V)
  proof: by
  simpa using! congrFun (congrArg (DFunLike.coe ∘ CommRingCat.Hom.hom) <|
    evaluation_naturality f x) a

中文:
引理 evaluation_naturality_apply
  结论: {V : Opens Y} (x : (Opens.map f.base).obj V)
  证明: by
  simpa using! congrFun (congrArg (DFunLike.coe ∘ CommRingCat.Hom.hom) <|
    evaluation_naturality f x) a

Depends on / 依赖: CommRingCat, CommRingCat.Hom.hom, DFunLike, DFunLike.coe, evaluation_naturality
-/
lemma evaluation_naturality_apply {V : Opens Y} (x : (Opens.map f.base).obj V)
    (a : Y.presheaf.obj (op V)) :
    residueFieldMap f x.val (Y.evaluation ⟨f.base x, x.property⟩ a) =
      X.evaluation x (f.c.app (op V) a) := by
  simpa using! congrFun (congrArg (DFunLike.coe ∘ CommRingCat.Hom.hom) <|
    evaluation_naturality f x) a

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `Γevaluation_naturality` / 引理 `Γevaluation_naturality`

English:
lemma Γevaluation_naturality
  given: (x : X)
  proof: evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩

中文:
引理 Γevaluation_naturality
  条件: (x : X)
  证明: evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩

Depends on / 依赖: Opens.map_top, evaluation_naturality, map_top
-/
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.base x) ≫ residueFieldMap f x =
      f.c.app (op ⊤) ≫ X.Γevaluation x :=
  evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩

/--
lemma `Γevaluation_naturality_apply` / 引理 `Γevaluation_naturality_apply`

English:
lemma Γevaluation_naturality_apply
  given: (x : X) (a : Y.presheaf.obj (op ⊤))
  proof: evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a

中文:
引理 Γevaluation_naturality_apply
  条件: (x : X) (a : Y.presheaf.obj (op ⊤))
  证明: evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a

Depends on / 依赖: Opens.map_top, evaluation_naturality_apply, map_top
-/
lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    residueFieldMap f x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) :=
  evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a

end LocallyRingedSpace

end AlgebraicGeometry
