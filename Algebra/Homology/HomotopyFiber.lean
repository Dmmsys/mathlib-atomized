/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Opposite

/-!
# The homotopy fiber of a morphism of homological complexes

In this file, we construct the homotopy fiber of a morphism `φ : F ⟶ G`
between homological complexes. Moreover, we dualise the definition
of the cylinder (which is a particular case of a homotopy cofiber)
in order to define the path object of a homological complex.

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Opposite

variable {C : Type*} [Category* C] [Preadditive C]

namespace HomologicalComplex

attribute [local instance] ComplexShape.decidableRelSymm

variable {α : Type*} {c : ComplexShape α} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [DecidableRel c.Rel]

section

/--
Definition of `HasHomotopyFiber` / `HasHomotopyFiber` 的定义

English:
class HasHomotopyFiber
  parameters: (φ : F ⟶ G)
  axioms and operations (1):
    - hasBinaryBiproduct((φ) (i j : α) (hij : c.Rel i j)) : HasBinaryBiproduct (G.X i) (F.X j)

中文:
类 有HomotopyFiber
  参数: (φ : F ⟶ G)
  公理与运算 (1 个):
    - hasBinaryBiproduct((φ) (i j : α) (hij : c.关系 i j)) : 有BinaryBiproduct (G.X i) (F.X j)
-/
class HasHomotopyFiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (φ) (i j : α) (hij : c.Rel i j) : HasBinaryBiproduct (G.X i) (F.X j)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryBiproducts
  signature: C] : HasHomotopyFiber φ where
  body: inferInstance

中文:
实例 [有BinaryBiproducts
  签名: C] : 有HomotopyFiber φ where
  定义体: inferInstance
-/
instance [HasBinaryBiproducts C] : HasHomotopyFiber φ where
  hasBinaryBiproduct _ _ _ := inferInstance

variable [HasHomotopyFiber φ]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasHomotopyCofiber ((opFunctor C c).map φ.op)
  body: by
    have := HasHomotopyFiber.hasBinaryBiproduct φ j i hij
    dsimp
    infer_instance

中文:
实例 :
  签名: 有HomotopyCofiber ((opFunctor C c).map φ.op)
  定义体: by
    have := HasHomotopyFiber.hasBinaryBiproduct φ j i hij
    dsimp
    infer_instance

Depends on / 依赖: HasHomotopyFiber, HasHomotopyFiber.hasBinaryBiproduct, hasBinaryBiproduct, infer_instance
-/
instance : HasHomotopyCofiber ((opFunctor C c).map φ.op) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct φ j i hij
    dsimp
    infer_instance

/--
Definition of `homotopyFiber` / `homotopyFiber` 的定义

English:
definition homotopyFiber
  signature: : HomologicalComplex C c
  body: (unopFunctor C c.symm).obj (op (homotopyCofiber ((opFunctor C c).map φ.op)))

中文:
定义 homotopyFiber
  签名: : 同调复形 C c
  定义体: (unopFunctor C c.symm).obj (op (homotopyCofiber ((opFunctor C c).map φ.op)))

Depends on / 依赖: c.symm, homotopyCofiber, opFunctor, unopFunctor
-/
noncomputable def homotopyFiber : HomologicalComplex C c :=
  (unopFunctor C c.symm).obj (op (homotopyCofiber ((opFunctor C c).map φ.op)))

end

variable (K) [forall i, HasBinaryBiproduct (K.X i) (K.X i)]

set_option backward.defeqAttrib.useBackward true in
instance (i : α) : HasBinaryBiproduct (K.op.X i) (K.op.X i) := by
  dsimp; infer_instance

/--
Definition of `HasPathObject` / `HasPathObject` 的定义

English:
abbreviation HasPathObject
  body: HasHomotopyFiber (biprod.desc (𝟙 K) (-𝟙 K))

中文:
缩写 HasPathObject
  定义体: HasHomotopyFiber (biprod.desc (𝟙 K) (-𝟙 K))

Depends on / 依赖: HasHomotopyFiber, biprod, biprod.desc
-/
abbrev HasPathObject := HasHomotopyFiber (biprod.desc (𝟙 K) (-𝟙 K))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.HasPathObject]
  signature: :
  body: by
    have := HasHomotopyFiber.hasBinaryBiproduct (biprod.desc (𝟙 K) (-𝟙 K)) j i hij
    exact hasBinaryBiproduct_of_iso (Iso.refl _ : op (K.X j) ≅ K.op.X j)
      (show op ((K ⊞ K).X i) ≅ (K.op ⊞ K.op).X i from
        ((eval _ _ i).mapBiprod K K).op.symm ≪≫ biprod.opIso _ _ ≪≫
          ((eval _ 

中文:
实例 [K.HasPathObject]
  签名: :
  定义体: by
    have := HasHomotopyFiber.hasBinaryBiproduct (biprod.desc (𝟙 K) (-𝟙 K)) j i hij
    exact hasBinaryBiproduct_of_iso (Iso.refl _ : op (K.X j) ≅ K.op.X j)
      (show op ((K ⊞ K).X i) ≅ (K.op ⊞ K.op).X i from
        ((eval _ _ i).mapBiprod K K).op.symm ≪≫ biprod.opIso _ _ ≪≫
          ((eval _ 

Depends on / 依赖: HasHomotopyFiber, HasHomotopyFiber.hasBinaryBiproduct, Iso.refl, K.op, K.op.X, biprod, biprod.desc, biprod.opIso, hasBinaryBiproduct, hasBinaryBiproduct_of_iso, mapBiprod, op.symm
-/
instance [K.HasPathObject] :
    HasHomotopyCofiber (biprod.lift (𝟙 K.op) (-𝟙 K.op)) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct (biprod.desc (𝟙 K) (-𝟙 K)) j i hij
    exact hasBinaryBiproduct_of_iso (Iso.refl _ : op (K.X j) ≅ K.op.X j)
      (show op ((K ⊞ K).X i) ≅ (K.op ⊞ K.op).X i from
        ((eval _ _ i).mapBiprod K K).op.symm ≪≫ biprod.opIso _ _ ≪≫
          ((eval _ _ i).mapBiprod K.op K.op).symm)

variable [K.HasPathObject]

/-- The path object of a homological complex is defined here by dualizing
the cylinder object of `K.op`. -/
@[no_expose]
/--
Definition of `pathObject` / `pathObject` 的定义

English:
definition pathObject
  body: (unopFunctor C c.symm).obj (op K.op.cylinder)

中文:
定义 pathObject
  定义体: (unopFunctor C c.symm).obj (op K.op.cylinder)

Depends on / 依赖: K.op.cylinder, c.symm, cylinder, unopFunctor
-/
noncomputable def pathObject := (unopFunctor C c.symm).obj (op K.op.cylinder)

namespace pathObject

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isZero_X` / 引理 `isZero_X`

English:
lemma isZero_X
  given: (i : α) (h₁ : IsZero (K.X i)) (h₂ : forall (j : α), c.Rel j i -> IsZero (K.X j))
  proof: by
  apply IsZero.unop
  dsimp [pathObject]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj => IsZero.op (h₂ _ hj))
  exact IsZero.of_iso (by simpa using h₁.op)
    ((eval Cᵒᵖ c.symm i).mapBiprod K.op K.op)

中文:
引理 isZero_X
  条件: (i : α) (h₁ : 是零 (K.X i)) (h₂ : 对任意 (j : α), c.关系 j i -> 是零 (K.X j))
  证明: by
  apply IsZero.unop
  dsimp [pathObject]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj => IsZero.op (h₂ _ hj))
  exact IsZero.of_iso (by simpa using h₁.op)
    ((eval Cᵒᵖ c.symm i).mapBiprod K.op K.op)

Depends on / 依赖: IsZero, IsZero.of_iso, IsZero.op, IsZero.unop, K.op, c.symm, homotopyCofiber, homotopyCofiber.isZero_X, isZero_X, mapBiprod, of_iso, pathObject
-/
lemma isZero_X (i : α) (h₁ : IsZero (K.X i)) (h₂ : forall (j : α), c.Rel j i -> IsZero (K.X j)) :
    IsZero (K.pathObject.X i) := by
  apply IsZero.unop
  dsimp [pathObject]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj => IsZero.op (h₂ _ hj))
  exact IsZero.of_iso (by simpa using h₁.op)
    ((eval Cᵒᵖ c.symm i).mapBiprod K.op K.op)

/-- The first projection `K.pathObject ⟶ K`. -/
@[no_expose]
/--
Definition of `π₀` / `π₀` 的定义

English:
definition π₀
  signature: : K.pathObject ⟶ K
  body: (unopFunctor C c.symm).map (cylinder.ι₀ K.op).op

中文:
定义 π₀
  签名: : K.pathObject ⟶ K
  定义体: (unopFunctor C c.symm).map (cylinder.ι₀ K.op).op

Depends on / 依赖: K.op, c.symm, cylinder, unopFunctor
-/
noncomputable def π₀ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₀ K.op).op

/-- The second projection `K.pathObject ⟶ K`. -/
@[no_expose]
/--
Definition of `π₁` / `π₁` 的定义

English:
definition π₁
  signature: : K.pathObject ⟶ K
  body: (unopFunctor C c.symm).map (cylinder.ι₁ K.op).op

中文:
定义 π₁
  签名: : K.pathObject ⟶ K
  定义体: (unopFunctor C c.symm).map (cylinder.ι₁ K.op).op

Depends on / 依赖: K.op, c.symm, cylinder, unopFunctor
-/
noncomputable def π₁ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₁ K.op).op

/-- The inclusion `K ⟶ K.pathObject`. -/
@[no_expose]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : K ⟶ K.pathObject
  body: (unopFunctor C c.symm).map (cylinder.π K.op).op

@[reassoc (attr := simp)]

中文:
定义 ι
  签名: : K ⟶ K.pathObject
  定义体: (unopFunctor C c.symm).map (cylinder.π K.op).op

@[reassoc (attr := simp)]

Depends on / 依赖: K.op, c.symm, cylinder, unopFunctor
-/
noncomputable def ι : K ⟶ K.pathObject :=
  (unopFunctor C c.symm).map (cylinder.π K.op).op

@[reassoc (attr := simp)]
/--
lemma `π₀_ι` / 引理 `π₀_ι`

English:
lemma π₀_ι
  statement: ι K ≫ π₀ K = 𝟙 K
  proof: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_π K.op))

@[reassoc (attr := simp)]

中文:
引理 π₀_ι
  结论: ι K ≫ π₀ K = 𝟙 K
  证明: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_π K.op))

@[reassoc (attr := simp)]

Depends on / 依赖: K.op, Quiver, Quiver.Hom.op_inj, cylinder, map_injective, opFunctor, op_inj
-/
lemma π₀_ι : ι K ≫ π₀ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_π K.op))

@[reassoc (attr := simp)]
/--
lemma `π₁_ι` / 引理 `π₁_ι`

English:
lemma π₁_ι
  statement: ι K ≫ π₁ K = 𝟙 K
  proof: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_π K.op))

中文:
引理 π₁_ι
  结论: ι K ≫ π₁ K = 𝟙 K
  证明: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_π K.op))

Depends on / 依赖: K.op, Quiver, Quiver.Hom.op_inj, cylinder, map_injective, opFunctor, op_inj
-/
lemma π₁_ι : ι K ≫ π₁ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_π K.op))

/-- The homotopy between `π₀ K ≫ ι K` and `𝟙 K.pathObject`. -/
@[no_expose]
/--
Definition of `π₀CompιHomotopy` / `π₀CompιHomotopy` 的定义

English:
definition π₀CompιHomotopy
  signature: (hc : forall (i : α), exists j, c.Rel i j)
  body: (cylinder.πCompι₀Homotopy K.op hc).unop

中文:
定义 π₀CompιHomotopy
  签名: (hc : 对任意 (i : α), 存在 j, c.关系 i j)
  定义体: (cylinder.πCompι₀Homotopy K.op hc).unop

Depends on / 依赖: K.op, cylinder
-/
noncomputable def π₀CompιHomotopy (hc : forall (i : α), exists j, c.Rel i j) :
    Homotopy (π₀ K ≫ ι K) (𝟙 K.pathObject) :=
  (cylinder.πCompι₀Homotopy K.op hc).unop

/-- The homotopy equivalence between `K` and `K.pathObject`. -/
@[simps]
/--
Definition of `homotopyEquiv` / `homotopyEquiv` 的定义

English:
definition homotopyEquiv
  signature: (hc : forall (i : α), exists j, c.Rel i j)
  body: ι K
  inv := π₀ K
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := π₀CompιHomotopy K hc

中文:
定义 homotopyEquiv
  签名: (hc : 对任意 (i : α), 存在 j, c.关系 i j)
  定义体: ι K
  inv := π₀ K
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := π₀CompιHomotopy K hc
-/
noncomputable def homotopyEquiv (hc : forall (i : α), exists j, c.Rel i j) :
    HomotopyEquiv K K.pathObject where
  hom := ι K
  inv := π₀ K
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := π₀CompιHomotopy K hc

/-- The homotopy between `pathObject.ι₀ K` and `pathObject.ι₁ K`. -/
@[no_expose]
/--
Definition of `homotopy₀₁` / `homotopy₀₁` 的定义

English:
definition homotopy₀₁
  signature: (hc : forall (i : α), exists j, c.Rel i j)
  body: (cylinder.homotopy₀₁ K.op hc).unop

中文:
定义 homotopy₀₁
  签名: (hc : 对任意 (i : α), 存在 j, c.关系 i j)
  定义体: (cylinder.homotopy₀₁ K.op hc).unop

Depends on / 依赖: K.op, cylinder, cylinder.homotopy
-/
noncomputable def homotopy₀₁ (hc : forall (i : α), exists j, c.Rel i j) : Homotopy (π₀ K) (π₁ K) :=
  (cylinder.homotopy₀₁ K.op hc).unop

section

variable {K} (φ₀ φ₁ : F ⟶ K) (h : Homotopy φ₀ φ₁)

/-- The morphism `F ⟶ K.pathObject` that is induced by two morphisms `φ₀ φ₁ : F ⟶ K`
and a homotopy `h : Homotopy φ₀ φ₁`. -/
@[no_expose]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : F ⟶ K.pathObject
  body: letI φ : K.op.cylinder ⟶ (opFunctor C c).obj (op F) :=
    cylinder.desc ((opFunctor C c).map φ₀.op)
      ((opFunctor C c).map φ₁.op) h.op
  (unopFunctor C c.symm).map φ.op

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: : F ⟶ K.pathObject
  定义体: letI φ : K.op.cylinder ⟶ (opFunctor C c).obj (op F) :=
    cylinder.desc ((opFunctor C c).map φ₀.op)
      ((opFunctor C c).map φ₁.op) h.op
  (unopFunctor C c.symm).map φ.op

@[reassoc (attr := simp)]

Depends on / 依赖: K.op.cylinder, c.symm, cylinder, cylinder.desc, h.op, opFunctor, unopFunctor
-/
noncomputable def lift : F ⟶ K.pathObject :=
  letI φ : K.op.cylinder ⟶ (opFunctor C c).obj (op F) :=
    cylinder.desc ((opFunctor C c).map φ₀.op)
      ((opFunctor C c).map φ₁.op) h.op
  (unopFunctor C c.symm).map φ.op

@[reassoc (attr := simp)]
/--
lemma `lift_π₀` / 引理 `lift_π₀`

English:
lemma lift_π₀
  statement: lift φ₀ φ₁ h ≫ π₀ K = φ₀
  proof: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_desc _ _ _))

@[reassoc (attr := simp)]

中文:
引理 lift_π₀
  结论: lift φ₀ φ₁ h ≫ π₀ K = φ₀
  证明: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_desc _ _ _))

@[reassoc (attr := simp)]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, cylinder, map_injective, opFunctor, op_inj
-/
lemma lift_π₀ : lift φ₀ φ₁ h ≫ π₀ K = φ₀ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_desc _ _ _))

@[reassoc (attr := simp)]
/--
lemma `lift_π₁` / 引理 `lift_π₁`

English:
lemma lift_π₁
  statement: lift φ₀ φ₁ h ≫ π₁ K = φ₁
  proof: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_desc _ _ _))

中文:
引理 lift_π₁
  结论: lift φ₀ φ₁ h ≫ π₁ K = φ₁
  证明: Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_desc _ _ _))

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, cylinder, map_injective, opFunctor, op_inj
-/
lemma lift_π₁ : lift φ₀ φ₁ h ≫ π₁ K = φ₁ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_desc _ _ _))

end

section

variable (F) {D : Type*} [Category* D] [Preadditive D] (H : C ⥤ D) [H.Additive]
  [forall (i : α), HasBinaryBiproduct (((H.mapHomologicalComplex c).obj K).X i)
    (((H.mapHomologicalComplex c).obj K).X i)]
  [((H.mapHomologicalComplex c).obj K).HasPathObject]

variable
  [forall (i : α),
    HasBinaryBiproduct (((H.op.mapHomologicalComplex c.symm).obj K.op).X i)
      (((H.op.mapHomologicalComplex c.symm).obj K.op).X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 ((H.op.mapHomologicalComplex c.symm).obj K.op))
    (-𝟙 ((H.op.mapHomologicalComplex c.symm).obj K.op)))]
  [HasHomotopyCofiber ((H.op.mapHomologicalComplex c.symm).map (biprod.lift (𝟙 K.op) (-𝟙 K.op)))]
  [forall (i : α), HasBinaryBiproduct (K.op.X i) (K.op.X i)]

variable (hc : forall (i : α), exists j, c.Rel i j)

/-- The isomorphism expressing the commutation between taking
the path object of a homological complex and applying an additive functor. -/
@[no_expose]
/--
Definition of `mapHomologicalComplexObjIso` / `mapHomologicalComplexObjIso` 的定义

English:
definition mapHomologicalComplexObjIso
  signature: :
  body: (unopFunctor _ _).mapIso (cylinder.mapHomologicalComplexObjIso K.op H.op hc).op.symm

@[reassoc (attr := simp)]

中文:
定义 mapHomologicalComplexObjIso
  签名: :
  定义体: (unopFunctor _ _).mapIso (cylinder.mapHomologicalComplexObjIso K.op H.op hc).op.symm

@[reassoc (attr := simp)]

Depends on / 依赖: H.op, K.op, cylinder, cylinder.mapHomologicalComplexObjIso, mapHomologicalComplexObjIso, mapIso, op.symm, unopFunctor
-/
noncomputable def mapHomologicalComplexObjIso :
    (H.mapHomologicalComplex c).obj (K.pathObject) ≅
      pathObject ((H.mapHomologicalComplex c).obj K) :=
  (unopFunctor _ _).mapIso (cylinder.mapHomologicalComplexObjIso K.op H.op hc).op.symm

@[reassoc (attr := simp)]
/--
lemma `mapHomologicalComplexObjIso_inv_map_π₀` / 引理 `mapHomologicalComplexObjIso_inv_map_π₀`

English:
lemma mapHomologicalComplexObjIso_inv_map_π₀
  proof: Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₀_mapHomologicalComplexObjIso_hom K.op H.op hc))

@[reassoc (attr := simp)]

中文:
引理 mapHomologicalComplexObjIso_inv_map_π₀
  证明: Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₀_mapHomologicalComplexObjIso_hom K.op H.op hc))

@[reassoc (attr := simp)]

Depends on / 依赖: H.op, K.op, Quiver, Quiver.Hom.op_inj, cylinder, cylinder.map_, map_injective, opFunctor, op_inj
-/
lemma mapHomologicalComplexObjIso_inv_map_π₀ :
    (mapHomologicalComplexObjIso K H hc).inv ≫ (H.mapHomologicalComplex c).map (π₀ K) =
      π₀ _ :=
  Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₀_mapHomologicalComplexObjIso_hom K.op H.op hc))

@[reassoc (attr := simp)]
/--
lemma `mapHomologicalComplexObjIso_inv_map_π₁` / 引理 `mapHomologicalComplexObjIso_inv_map_π₁`

English:
lemma mapHomologicalComplexObjIso_inv_map_π₁
  proof: Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₁_mapHomologicalComplexObjIso_hom K.op H.op hc))

中文:
引理 mapHomologicalComplexObjIso_inv_map_π₁
  证明: Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₁_mapHomologicalComplexObjIso_hom K.op H.op hc))

Depends on / 依赖: H.op, K.op, Quiver, Quiver.Hom.op_inj, cylinder, cylinder.map_, map_injective, opFunctor, op_inj
-/
lemma mapHomologicalComplexObjIso_inv_map_π₁ :
    (mapHomologicalComplexObjIso K H hc).inv ≫ (H.mapHomologicalComplex c).map (π₁ K) =
      π₁ _ :=
  Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₁_mapHomologicalComplexObjIso_hom K.op H.op hc))

end

end pathObject

end HomologicalComplex
