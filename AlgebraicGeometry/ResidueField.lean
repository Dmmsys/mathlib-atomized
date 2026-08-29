/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!

# Residue fields of points

## Main definitions

The following are in the `AlgebraicGeometry.Scheme` namespace:

- `AlgebraicGeometry.Scheme.residueField`: The residue field of the stalk at `x`.
- `AlgebraicGeometry.Scheme.evaluation`: For open subsets `U` of `X` containing `x`,
  the evaluation map from sections over `U` to the residue field at `x`.
- `AlgebraicGeometry.Scheme.Hom.residueFieldMap`: A morphism of schemes induce a homomorphism of
  residue fields.
- `AlgebraicGeometry.Scheme.fromSpecResidueField`: The canonical map `Spec κ(x) ⟶ X`.
- `AlgebraicGeometry.Scheme.SpecToEquivOfField`: morphisms `Spec K ⟶ X` for a field `K` correspond
  to pairs of `x : X` with embedding `κ(x) ⟶ K`.


-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {U : X.Opens}

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

instance (x : X) : Unique (Spec (X.residueField x)) := inferInstanceAs (Unique (Spec <| .of _))

/--
Definition of `residue` / `residue` 的定义

English:
definition residue
  signature: (X : Scheme.{u}) (x)
  body: CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

中文:
定义 residue
  签名: (X : 概形.{u}) (x)
  定义体: CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalRing, IsLocalRing.residue, X.presheaf.stalk, presheaf, residue
-/
def residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

/-- See `AlgebraicGeometry.IsClosedImmersion.SpecMap_residue` for the stronger result that
`Spec.map (X.residue x)` is a closed immersion. -/
instance {X : Scheme.{u}} (x) : IsPreimmersion (Spec.map (X.residue x)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding
    (RingHom.surjectiveOnStalks_of_surjective (Ideal.Quotient.mk_surjective))

@[simp]
/--
lemma `SpecMap_residue_apply` / 引理 `SpecMap_residue_apply`

English:
lemma SpecMap_residue_apply
  given: {X : Scheme.{u}} (x : X) (s : Spec (X.residueField x))
  proof: IsLocalRing.PrimeSpectrum.comap_residue _ s

中文:
引理 SpecMap_residue_apply
  条件: {X : 概形.{u}} (x : X) (s : Spec (X.residueField x))
  证明: IsLocalRing.PrimeSpectrum.comap_residue _ s

Depends on / 依赖: IsLocalRing, IsLocalRing.PrimeSpectrum.comap_residue, PrimeSpectrum, comap_residue
-/
lemma SpecMap_residue_apply {X : Scheme.{u}} (x : X) (s : Spec (X.residueField x)) :
    Spec.map (X.residue x) s = closedPoint (X.presheaf.stalk x) :=
  IsLocalRing.PrimeSpectrum.comap_residue _ s

/--
lemma `residue_surjective` / 引理 `residue_surjective`

English:
lemma residue_surjective
  given: (X : Scheme.{u}) (x)
  statement: Function.Surjective (X.residue x)
  proof: Ideal.Quotient.mk_surjective

中文:
引理 residue_surjective
  条件: (X : 概形.{u}) (x)
  结论: 函数.满射 (X.residue x)
  证明: Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
lemma residue_surjective (X : Scheme.{u}) (x) : Function.Surjective (X.residue x) :=
  Ideal.Quotient.mk_surjective

instance (X : Scheme.{u}) (x) : Epi (X.residue x) :=
  ConcreteCategory.epi_of_surjective _ (X.residue_surjective x)

/--
Definition of `descResidueField` / `descResidueField` 的定义

English:
definition descResidueField
  signature: {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
  body: CommRingCat.ofHom (IsLocalRing.ResidueField.lift (S := K) f.hom)

@[reassoc (attr := simp)]

中文:
定义 descResidueField
  签名: {K : 类型u} [域 K] {X : 概形.{u}} {x : X}
  定义体: CommRingCat.ofHom (IsLocalRing.ResidueField.lift (S := K) f.hom)

@[reassoc (attr := simp)]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalRing, IsLocalRing.ResidueField.lift, ResidueField, f.hom
-/
def descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residueField x ⟶ .of K :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.lift (S := K) f.hom)

@[reassoc (attr := simp)]
/--
lemma `residue_descResidueField` / 引理 `residue_descResidueField`

English:
lemma residue_descResidueField
  statement: {K : Type u} [Field K] {X : Scheme.{u}} {x}
  proof: CommRingCat.hom_ext RingHom.ext fun _ => rfl

中文:
引理 residue_descResidueField
  结论: {K : 类型u} [域 K] {X : 概形.{u}} {x}
  证明: CommRingCat.hom_ext RingHom.ext fun _ => rfl

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext, RingHom, RingHom.ext, hom_ext
-/
lemma residue_descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residue x ≫ X.descResidueField f = f :=
CommRingCat.hom_ext RingHom.ext fun _ => rfl

/--
Definition of `evaluation` / `evaluation` 的定义

English:
definition evaluation
  signature: (U : X.Opens) (x : X) (hx : x in U)
  body: X.presheaf.germ U x hx ≫ X.residue _

@[reassoc]

中文:
定义 evaluation
  签名: (U : X.Opens) (x : X) (hx : x in U)
  定义体: X.presheaf.germ U x hx ≫ X.residue _

@[reassoc]

Depends on / 依赖: X.presheaf.germ, X.residue, presheaf, residue
-/
def evaluation (U : X.Opens) (x : X) (hx : x in U) : Γ(X, U) ⟶ X.residueField x :=
  X.presheaf.germ U x hx ≫ X.residue _

@[reassoc]
/--
lemma `germ_residue` / 引理 `germ_residue`

English:
lemma germ_residue
  given: (x hx)
  statement: X.presheaf.germ U x hx ≫ X.residue x = X.evaluation U x hx
  proof: rfl

中文:
引理 germ_residue
  条件: (x hx)
  结论: X.presheaf.germ U x hx ≫ X.residue x = X.evaluation U x hx
  证明: rfl
-/
lemma germ_residue (x hx) : X.presheaf.germ U x hx ≫ X.residue x = X.evaluation U x hx := rfl

/--
Definition of `Γevaluation` / `Γevaluation` 的定义

English:
abbreviation Γevaluation
  signature: (x : X)
  body: X.evaluation ⊤ x trivial

@[simp]

中文:
缩写 Γevaluation
  签名: (x : X)
  定义体: X.evaluation ⊤ x trivial

@[simp]

Depends on / 依赖: X.evaluation, evaluation
-/
abbrev Γevaluation (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  X.evaluation ⊤ x trivial

@[simp]
/--
lemma `evaluation_eq_zero_iff_notMem_basicOpen` / 引理 `evaluation_eq_zero_iff_notMem_basicOpen`

English:
lemma evaluation_eq_zero_iff_notMem_basicOpen
  given: (x : X) (hx : x in U) (f : Γ(X, U))
  proof: X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f

中文:
引理 evaluation_eq_zero_iff_notMem_basicOpen
  条件: (x : X) (hx : x in U) (f : Γ(X, U))
  证明: X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f

Depends on / 依赖: X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen, evaluation_eq_zero_iff_notMem_basicOpen, toLocallyRingedSpace
-/
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : X) (hx : x in U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f :=
  X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f

/--
lemma `evaluation_ne_zero_iff_mem_basicOpen` / 引理 `evaluation_ne_zero_iff_mem_basicOpen`

English:
lemma evaluation_ne_zero_iff_mem_basicOpen
  given: (x : X) (hx : x in U) (f : Γ(X, U))
  proof: by
  simp

中文:
引理 evaluation_ne_zero_iff_mem_basicOpen
  条件: (x : X) (hx : x in U) (f : Γ(X, U))
  证明: by
  simp
-/
lemma evaluation_ne_zero_iff_mem_basicOpen (x : X) (hx : x in U) (f : Γ(X, U)) :
    X.evaluation U x hx f != 0 ↔ x in X.basicOpen f := by
  simp

/--
lemma `basicOpen_eq_bot_iff_forall_evaluation_eq_zero` / 引理 `basicOpen_eq_bot_iff_forall_evaluation_eq_zero`

English:
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero
  given: (f : X.presheaf.obj (op U))
  proof: X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero f

中文:
引理 basicOpen_eq_bot_iff_对任意_evaluation_eq_zero
  条件: (f : X.presheaf.obj (op U))
  证明: X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero f

Depends on / 依赖: X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero, basicOpen_eq_bot_iff_forall_evaluation_eq_zero, toLocallyRingedSpace
-/
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.basicOpen f = ⊥ ↔ forall (x : U), X.evaluation U x x.property f = 0 :=
  X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero f

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
Definition of `Hom.residueFieldMap` / `Hom.residueFieldMap` 的定义

English:
definition Hom.residueFieldMap
  signature: (f : X ⟶ Y) (x : X)
  body: CommRingCat.ofHom IsLocalRing.ResidueField.map (f.stalkMap x).hom

@[reassoc]

中文:
定义 态射.residueFieldMap
  签名: (f : X ⟶ Y) (x : X)
  定义体: CommRingCat.ofHom IsLocalRing.ResidueField.map (f.stalkMap x).hom

@[reassoc]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsLocalRing, IsLocalRing.ResidueField.map, ResidueField, f.stalkMap, stalkMap
-/
def Hom.residueFieldMap (f : X ⟶ Y) (x : X) :
    Y.residueField (f x) ⟶ X.residueField x :=
CommRingCat.ofHom IsLocalRing.ResidueField.map (f.stalkMap x).hom

@[reassoc]
/--
lemma `residue_residueFieldMap` / 引理 `residue_residueFieldMap`

English:
lemma residue_residueFieldMap
  given: (x : X)
  proof: by
  simp [Hom.residueFieldMap]
  rfl

@[simp]

中文:
引理 residue_residueFieldMap
  条件: (x : X)
  证明: by
  simp [Hom.residueFieldMap]
  rfl

@[simp]

Depends on / 依赖: Hom.residueFieldMap, residueFieldMap
-/
lemma residue_residueFieldMap (x : X) :
    Y.residue (f x) ≫ f.residueFieldMap x = f.stalkMap x ≫ X.residue x := by
  simp [Hom.residueFieldMap]
  rfl

@[simp]
/--
lemma `residueFieldMap_id` / 引理 `residueFieldMap_id`

English:
lemma residueFieldMap_id
  given: (x : X)
  proof: LocallyRingedSpace.residueFieldMap_id _

@[simp]

中文:
引理 residueFieldMap_id
  条件: (x : X)
  证明: LocallyRingedSpace.residueFieldMap_id _

@[simp]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.residueFieldMap_id, residueFieldMap_id
-/
lemma residueFieldMap_id (x : X) :
    Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  LocallyRingedSpace.residueFieldMap_id _

@[simp]
/--
lemma `residueFieldMap_comp` / 引理 `residueFieldMap_comp`

English:
lemma residueFieldMap_comp
  given: {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X)
  proof: LocallyRingedSpace.residueFieldMap_comp _ _ _

中文:
引理 residueFieldMap_comp
  条件: {Z : 概形.{u}} (g : Y ⟶ Z) (x : X)
  证明: LocallyRingedSpace.residueFieldMap_comp _ _ _

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.residueFieldMap_comp, residueFieldMap_comp
-/
lemma residueFieldMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x = g.residueFieldMap (f x) ≫ f.residueFieldMap x :=
  LocallyRingedSpace.residueFieldMap_comp _ _ _

/--
Definition of `Hom.residueDegree` / `Hom.residueDegree` 的定义

English:
definition Hom.residueDegree
  signature: (f : X ⟶ Y) (x : X)
  body: letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

@[simp]

中文:
定义 态射.residueDegree
  签名: (f : X ⟶ Y) (x : X)
  定义体: letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

@[simp]

Depends on / 依赖: Module, Module.finrank, X.residueField, Y.residueField, f.residueFieldMap, finrank, hom.toAlgebra, residueField, residueFieldMap, toAlgebra
-/
def Hom.residueDegree (f : X ⟶ Y) (x : X) : Nat :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

@[simp]
/--
lemma `Hom.residueDegree_id` / 引理 `Hom.residueDegree_id`

English:
lemma Hom.residueDegree_id
  given: (x : X)
  statement: (𝟙 _ : X ⟶ X).residueDegree x = 1
  proof: by
  dsimp [residueDegree]
  rw [residueFieldMap_id]
  exact CommSemiring.finrank_self _

@[reassoc]

中文:
引理 态射.residueDegree_id
  条件: (x : X)
  结论: (𝟙 _ : X ⟶ X).residueDegree x = 1
  证明: by
  dsimp [residueDegree]
  rw [residueFieldMap_id]
  exact CommSemiring.finrank_self _

@[reassoc]

Depends on / 依赖: CommSemiring, CommSemiring.finrank_self, finrank_self, residueDegree, residueFieldMap_id
-/
lemma Hom.residueDegree_id (x : X) : (𝟙 _ : X ⟶ X).residueDegree x = 1 := by
  dsimp [residueDegree]
  rw [residueFieldMap_id]
  exact CommSemiring.finrank_self _

@[reassoc]
/--
lemma `evaluation_naturality` / 引理 `evaluation_naturality`

English:
lemma evaluation_naturality
  given: {V : Opens Y} (x : X) (hx : f x in V)
  proof: LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩

中文:
引理 evaluation_naturality
  条件: {V : Opens Y} (x : X) (hx : f x in V)
  证明: LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.evaluation_naturality, evaluation_naturality
-/
lemma evaluation_naturality {V : Opens Y} (x : X) (hx : f x in V) :
    Y.evaluation V (f x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx :=
  LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩

/--
lemma `evaluation_naturality_apply` / 引理 `evaluation_naturality_apply`

English:
lemma evaluation_naturality_apply
  given: {V : Opens Y} (x : X) (hx : f x in V) (s)
  proof: LocallyRingedSpace.evaluation_naturality_apply f.1 ⟨x, hx⟩ s

@[reassoc]

中文:
引理 evaluation_naturality_apply
  条件: {V : Opens Y} (x : X) (hx : f x in V) (s)
  证明: LocallyRingedSpace.evaluation_naturality_apply f.1 ⟨x, hx⟩ s

@[reassoc]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.evaluation_naturality_apply, evaluation_naturality_apply
-/
lemma evaluation_naturality_apply {V : Opens Y} (x : X) (hx : f x in V) (s) :
    f.residueFieldMap x (Y.evaluation V (f x) hx s) =
      X.evaluation (f ⁻¹ᵁ V) x hx (f.app V s) :=
  LocallyRingedSpace.evaluation_naturality_apply f.1 ⟨x, hx⟩ s

@[reassoc]
/--
lemma `Γevaluation_naturality` / 引理 `Γevaluation_naturality`

English:
lemma Γevaluation_naturality
  given: (x : X)
  proof: LocallyRingedSpace.Γevaluation_naturality f.toLRSHom x

中文:
引理 Γevaluation_naturality
  条件: (x : X)
  证明: LocallyRingedSpace.Γevaluation_naturality f.toLRSHom x

Depends on / 依赖: LocallyRingedSpace, f.toLRSHom, toLRSHom
-/
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f x) ≫ f.residueFieldMap x = f.appTop ≫ X.Γevaluation x :=
  LocallyRingedSpace.Γevaluation_naturality f.toLRSHom x

/--
lemma `Γevaluation_naturality_apply` / 引理 `Γevaluation_naturality_apply`

English:
lemma Γevaluation_naturality_apply
  given: (x : X) (a : Y.presheaf.obj (op ⊤))
  proof: LocallyRingedSpace.Γevaluation_naturality_apply f.toLRSHom x a

中文:
引理 Γevaluation_naturality_apply
  条件: (x : X) (a : Y.presheaf.obj (op ⊤))
  证明: LocallyRingedSpace.Γevaluation_naturality_apply f.toLRSHom x a

Depends on / 依赖: LocallyRingedSpace, f.toLRSHom, toLRSHom
-/
lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f x) a) = X.Γevaluation x (f.appTop a) :=
  LocallyRingedSpace.Γevaluation_naturality_apply f.toLRSHom x a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOpenImmersion
  signature: f] (x) : IsIso (f.residueFieldMap x)
  body: (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

中文:
实例 [是开浸入
  签名: f] (x) : 是同构 (f.residueFieldMap x)
  定义体: (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.mapEquiv, ResidueField, commRingCatIsoToRingEquiv, f.stalkMap, isIso_hom, mapEquiv, stalkMap, toCommRingCatIso, toCommRingCatIso.isIso_hom
-/
instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

section congr

-- replace this def if hard to work with
/--
Definition of `residueFieldCongr` / `residueFieldCongr` 的定义

English:
definition residueFieldCongr
  signature: {x y : X} (h : x = y)
  body: eqToIso (by subst h; rfl)

@[simp]

中文:
定义 residueFieldCongr
  签名: {x y : X} (h : x = y)
  定义体: eqToIso (by subst h; rfl)

@[simp]

Depends on / 依赖: eqToIso
-/
def residueFieldCongr {x y : X} (h : x = y) :
    X.residueField x ≅ X.residueField y :=
  eqToIso (by subst h; rfl)

@[simp]
/--
lemma `residueFieldCongr_refl` / 引理 `residueFieldCongr_refl`

English:
lemma residueFieldCongr_refl
  given: {x : X}
  proof: rfl

@[simp]

中文:
引理 residueFieldCongr_refl
  条件: {x : X}
  证明: rfl

@[simp]
-/
lemma residueFieldCongr_refl {x : X} :
    X.residueFieldCongr (refl x) = Iso.refl _ := rfl

@[simp]
/--
lemma `residueFieldCongr_symm` / 引理 `residueFieldCongr_symm`

English:
lemma residueFieldCongr_symm
  given: {x y : X} (e : x = y)
  proof: rfl

@[simp]

中文:
引理 residueFieldCongr_symm
  条件: {x y : X} (e : x = y)
  证明: rfl

@[simp]
-/
lemma residueFieldCongr_symm {x y : X} (e : x = y) :
    (X.residueFieldCongr e).symm = X.residueFieldCongr e.symm := rfl

@[simp]
/--
lemma `residueFieldCongr_inv` / 引理 `residueFieldCongr_inv`

English:
lemma residueFieldCongr_inv
  given: {x y : X} (e : x = y)
  proof: rfl

@[simp]

中文:
引理 residueFieldCongr_inv
  条件: {x y : X} (e : x = y)
  证明: rfl

@[simp]
-/
lemma residueFieldCongr_inv {x y : X} (e : x = y) :
    (X.residueFieldCongr e).inv = (X.residueFieldCongr e.symm).hom := rfl

@[simp]
/--
lemma `residueFieldCongr_trans` / 引理 `residueFieldCongr_trans`

English:
lemma residueFieldCongr_trans
  given: {x y z : X} (e : x = y) (e' : y = z)
  proof: by
  subst e e'
  rfl

@[reassoc (attr := simp)]

中文:
引理 residueFieldCongr_trans
  条件: {x y z : X} (e : x = y) (e' : y = z)
  证明: by
  subst e e'
  rfl

@[reassoc (attr := simp)]
-/
lemma residueFieldCongr_trans {x y z : X} (e : x = y) (e' : y = z) :
    X.residueFieldCongr e ≪≫ X.residueFieldCongr e' = X.residueFieldCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
/--
lemma `residueFieldCongr_trans_hom` / 引理 `residueFieldCongr_trans_hom`

English:
lemma residueFieldCongr_trans_hom
  given: (X : Scheme) {x y z : X} (e : x = y) (e' : y = z)
  proof: by
  subst e e'
  rfl

@[reassoc]

中文:
引理 residueFieldCongr_trans_hom
  条件: (X : 概形) {x y z : X} (e : x = y) (e' : y = z)
  证明: by
  subst e e'
  rfl

@[reassoc]
-/
lemma residueFieldCongr_trans_hom (X : Scheme) {x y z : X} (e : x = y) (e' : y = z) :
    (X.residueFieldCongr e).hom ≫ (X.residueFieldCongr e').hom =
      (X.residueFieldCongr (e.trans e')).hom := by
  subst e e'
  rfl

@[reassoc]
/--
lemma `residue_residueFieldCongr` / 引理 `residue_residueFieldCongr`

English:
lemma residue_residueFieldCongr
  given: (X : Scheme) {x y : X} (h : x = y)
  proof: by
  subst h
  simp

中文:
引理 residue_residueFieldCongr
  条件: (X : 概形) {x y : X} (h : x = y)
  证明: by
  subst h
  simp
-/
lemma residue_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.residue x ≫ (X.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.residue y := by
  subst h
  simp

/--
lemma `Hom.residueFieldMap_congr` / 引理 `Hom.residueFieldMap_congr`

English:
lemma Hom.residueFieldMap_congr
  given: {f g : X ⟶ Y} (e : f = g) (x : X)
  proof: by
  subst e; simp

@[reassoc]

中文:
引理 态射.residueFieldMap_congr
  条件: {f g : X ⟶ Y} (e : f = g) (x : X)
  证明: by
  subst e; simp

@[reassoc]
-/
lemma Hom.residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x = (Y.residueFieldCongr (by subst e; rfl)).hom ≫ g.residueFieldMap x := by
  subst e; simp

@[reassoc]
/--
lemma `Hom.residueFieldMap_congr'` / 引理 `Hom.residueFieldMap_congr'`

English:
lemma Hom.residueFieldMap_congr'
  given: {f : X ⟶ Y} {x₁ x₂ : X} (e : x₁ = x₂)
  proof: by
  subst e
  simp

中文:
引理 态射.residueFieldMap_congr'
  条件: {f : X ⟶ Y} {x₁ x₂ : X} (e : x₁ = x₂)
  证明: by
  subst e
  simp
-/
lemma Hom.residueFieldMap_congr' {f : X ⟶ Y} {x₁ x₂ : X} (e : x₁ = x₂) :
    f.residueFieldMap x₁ ≫ (X.residueFieldCongr e).hom =
      (Y.residueFieldCongr (congrArg f e)).hom ≫ f.residueFieldMap x₂ := by
  subst e
  simp

end congr

section fromResidueField

/--
Definition of `fromSpecResidueField` / `fromSpecResidueField` 的定义

English:
definition fromSpecResidueField
  signature: (X : Scheme) (x : X)
  body: Spec.map (X.residue x) ≫ X.fromSpecStalk x

中文:
定义 fromSpecResidueField
  签名: (X : 概形) (x : X)
  定义体: Spec.map (X.residue x) ≫ X.fromSpecStalk x

Depends on / 依赖: Spec.map, X.fromSpecStalk, X.residue, fromSpecStalk, residue
-/
def fromSpecResidueField (X : Scheme) (x : X) :
    Spec (X.residueField x) ⟶ X :=
  Spec.map (X.residue x) ≫ X.fromSpecStalk x

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecResidueField x) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [IsPreimmersion.comp_iff]
  infer_instance

@[simps] noncomputable
instance (x : X) : (Spec (X.residueField x)).Over X := ⟨X.fromSpecResidueField x⟩

noncomputable
instance (x : X) : (Spec (X.residueField x)).CanonicallyOver X where

@[reassoc (attr := simp)]
/--
lemma `residueFieldCongr_fromSpecResidueField` / 引理 `residueFieldCongr_fromSpecResidueField`

English:
lemma residueFieldCongr_fromSpecResidueField
  given: {x y : X} (h : x = y)
  proof: by
  subst h; simp

中文:
引理 residueFieldCongr_fromSpecResidueField
  条件: {x y : X} (h : x = y)
  证明: by
  subst h; simp
-/
lemma residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) :
    Spec.map (X.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ =
      X.fromSpecResidueField _ := by
  subst h; simp

instance {x y : X} (h : x = y) : (Spec.map (X.residueFieldCongr h).hom).IsOver X where

@[reassoc (attr := simp)]
/--
lemma `Hom.SpecMap_residueFieldMap_fromSpecResidueField` / 引理 `Hom.SpecMap_residueFieldMap_fromSpecResidueField`

English:
lemma Hom.SpecMap_residueFieldMap_fromSpecResidueField
  given: (x : X)
  proof: by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc]; rw [← SpecMap_stalkMap_fromSpecStalk]; rw [← Spec.map_comp_assoc]; rw [← Spec.map_comp_assoc]
  rfl

.IsOver Y where instance [X.Over Y] (x : X) : Spec.map ((X ↘ Y).residueFieldMap x)

@[simp]

中文:
引理 态射.SpecMap_residueFieldMap_fromSpecResidueField
  条件: (x : X)
  证明: by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc]; rw [← SpecMap_stalkMap_fromSpecStalk]; rw [← Spec.map_comp_assoc]; rw [← Spec.map_comp_assoc]
  rfl

.IsOver Y where instance [X.Over Y] (x : X) : Spec.map ((X ↘ Y).residueFieldMap x)

@[simp]

Depends on / 依赖: Category, Category.assoc, Spec.map_comp_assoc, SpecMap_stalkMap_fromSpecStalk, fromSpecResidueField, map_comp_assoc
-/
lemma Hom.SpecMap_residueFieldMap_fromSpecResidueField (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc]; rw [← SpecMap_stalkMap_fromSpecStalk]; rw [← Spec.map_comp_assoc]; rw [← Spec.map_comp_assoc]
  rfl

.IsOver Y where instance [X.Over Y] (x : X) : Spec.map ((X ↘ Y).residueFieldMap x)

@[simp]
/--
lemma `fromSpecResidueField_apply` / 引理 `fromSpecResidueField_apply`

English:
lemma fromSpecResidueField_apply
  given: (x : X.carrier) (s : Spec (X.residueField x))
  proof: by
  simp [fromSpecResidueField]

中文:
引理 fromSpecResidueField_apply
  条件: (x : X.carrier) (s : Spec (X.residueField x))
  证明: by
  simp [fromSpecResidueField]

Depends on / 依赖: fromSpecResidueField
-/
lemma fromSpecResidueField_apply (x : X.carrier) (s : Spec (X.residueField x)) :
    X.fromSpecResidueField x s = x := by
  simp [fromSpecResidueField]

/--
lemma `range_fromSpecResidueField` / 引理 `range_fromSpecResidueField`

English:
lemma range_fromSpecResidueField
  given: (x : X.carrier)
  proof: by
  simp

中文:
引理 range_fromSpecResidueField
  条件: (x : X.carrier)
  证明: by
  simp
-/
lemma range_fromSpecResidueField (x : X.carrier) :
    Set.range (X.fromSpecResidueField x) = {x} := by
  simp

/--
lemma `descResidueField_fromSpecResidueField` / 引理 `descResidueField_fromSpecResidueField`

English:
lemma descResidueField_fromSpecResidueField
  statement: {K : Type*} [Field K] (X : Scheme) {x}
  proof: by
  simp [fromSpecResidueField, ← Spec.map_comp_assoc]

中文:
引理 descResidueField_fromSpecResidueField
  结论: {K : 类型} [域 K] (X : 概形) {x}
  证明: by
  simp [fromSpecResidueField, ← Spec.map_comp_assoc]

Depends on / 依赖: Spec.map_comp_assoc, fromSpecResidueField, map_comp_assoc
-/
lemma descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    Spec.map (X.descResidueField f) ≫
      X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x := by
  simp [fromSpecResidueField, ← Spec.map_comp_assoc]

/--
lemma `descResidueField_stalkClosedPointTo_fromSpecResidueField` / 引理 `descResidueField_stalkClosedPointTo_fromSpecResidueField`

English:
lemma descResidueField_stalkClosedPointTo_fromSpecResidueField
  proof: by
  rw [X.descResidueField_fromSpecResidueField]; rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

中文:
引理 descResidueField_stalkClosedPointTo_fromSpecResidueField
  证明: by
  rw [X.descResidueField_fromSpecResidueField]; rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

Depends on / 依赖: Scheme, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Spec_stalkClosedPointTo_fromSpecStalk, X.descResidueField_fromSpecResidueField, descResidueField_fromSpecResidueField
-/
lemma descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) :
    Spec.map (descResidueField (Scheme.stalkClosedPointTo f)) ≫
      X.fromSpecResidueField (f (closedPoint K)) = f := by
  rw [X.descResidueField_fromSpecResidueField]; rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

end fromResidueField

section Spec

variable (R : CommRingCat) (x : Spec R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue fields of `Spec R` are isomorphic to `Ideal.ResidueField`. -/
noncomputable
/--
Definition of `Spec.residueFieldIso` / `Spec.residueFieldIso` 的定义

English:
definition Spec.residueFieldIso
  signature: :
  body: (IsLocalRing.ResidueField.mapEquiv
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv).toCommRingCatIso

中文:
定义 Spec.residueFieldIso
  签名: :
  定义体: (IsLocalRing.ResidueField.mapEquiv
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv).toCommRingCatIso

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField.mapEquiv, ResidueField, Spec.stalkIso, commRingCatIsoToRingEquiv, mapEquiv, stalkIso, toCommRingCatIso
-/
def Spec.residueFieldIso :
    (Spec R).residueField x ≅ .of x.asIdeal.ResidueField :=
  (IsLocalRing.ResidueField.mapEquiv
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv).toCommRingCatIso

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `Spec.algebraMap_residueFieldIso_inv` / 引理 `Spec.algebraMap_residueFieldIso_inv`

English:
lemma Spec.algebraMap_residueFieldIso_inv
  proof: by
  rw [← Spec.algebraMap_stalkIso_inv_assoc]; rfl

@[reassoc (attr := simp)]

中文:
引理 Spec.algebraMap_residueFieldIso_inv
  证明: by
  rw [← Spec.algebraMap_stalkIso_inv_assoc]; rfl

@[reassoc (attr := simp)]

Depends on / 依赖: Spec.algebraMap_stalkIso_inv_assoc, algebraMap_stalkIso_inv_assoc
-/
lemma Spec.algebraMap_residueFieldIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (residueFieldIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial ≫ (Spec R).residue x := by
  rw [← Spec.algebraMap_stalkIso_inv_assoc]; rfl

@[reassoc (attr := simp)]
/--
lemma `Spec.residue_residueFieldIso_hom` / 引理 `Spec.residue_residueFieldIso_hom`

English:
lemma Spec.residue_residueFieldIso_hom
  proof: rfl

中文:
引理 Spec.residue_residueFieldIso_hom
  证明: rfl
-/
lemma Spec.residue_residueFieldIso_hom :
    (Spec R).residue x ≫ (residueFieldIso R x).hom =
      (Spec.stalkIso R x).hom ≫ CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` / 引理 `Spec.map_residueFieldIso_inv_eq_fromSpecResidueField`

English:
lemma Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
  proof: by
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rw [Spec.map_inj]
  simp [← Scheme.Spec.algebraMap_residueFieldIso_inv]

中文:
引理 Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
  证明: by
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rw [Spec.map_inj]
  simp [← Scheme.Spec.algebraMap_residueFieldIso_inv]

Depends on / 依赖: Scheme, Scheme.Spec.algebraMap_residueFieldIso_inv, Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp, Spec.map_inj, algebraMap_residueFieldIso_inv, fromSpecResidueField, fromSpecStalk_eq, map_comp, map_inj
-/
lemma Spec.map_residueFieldIso_inv_eq_fromSpecResidueField :
    Spec.map (residueFieldIso _ _).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) =
    (Spec R).fromSpecResidueField x := by
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rw [Spec.map_inj]
  simp [← Scheme.Spec.algebraMap_residueFieldIso_inv]

end Spec

/--
lemma `SpecToEquivOfField_eq_iff` / 引理 `SpecToEquivOfField_eq_iff`

English:
lemma SpecToEquivOfField_eq_iff
  statement: {K : Type*} [Field K] {X : Scheme}
  proof: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨f, _⟩ := f₁
    obtain ⟨g, _⟩ := f₂
    rintro ⟨(rfl : f = g), h⟩
    simpa

中文:
引理 SpecToEquivOfField_eq_iff
  结论: {K : 类型} [域 K] {X : 概形}
  证明: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨f, _⟩ := f₁
    obtain ⟨g, _⟩ := f₂
    rintro ⟨(rfl : f = g), h⟩
    simpa
-/
lemma SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme}
    {f₁ f₂ : Σ x : X.carrier, X.residueField x ⟶ .of K} :
    f₁ = f₂ ↔ exists e : f₁.1 = f₂.1, f₁.2 = (X.residueFieldCongr e).hom ≫ f₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨f, _⟩ := f₁
    obtain ⟨g, _⟩ := f₂
    rintro ⟨(rfl : f = g), h⟩
    simpa

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field `K` and a scheme `X`, the morphisms `Spec K ⟶ X` bijectively correspond
to pairs of points `x` of `X` and embeddings `κ(x) ⟶ K`. -/
@[simps]
/--
Definition of `SpecToEquivOfField` / `SpecToEquivOfField` 的定义

English:
definition SpecToEquivOfField
  signature: (K : Type u) [Field K] (X : Scheme.{u})
  body: ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv f := by
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.Hom.comp

中文:
定义 SpecToEquivOfField
  签名: (K : 类型u) [域 K] (X : 概形.{u})
  定义体: ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv f := by
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.Hom.comp

Depends on / 依赖: CommRingCat, CommRingCat.coe_of, Function, Function.comp_apply, Scheme, Scheme.Hom.comp_base, Scheme.descResidueFiel, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, Scheme.fromSpecResidueField_apply, Scheme.stalkClosedPointTo, Spec.map, Spec.map_comp, Spec.map_inj, SpecToEquivOfField_eq_iff, TopCat, TopCat.coe_comp, X.descResidueField, X.fromSpecResidueField, cancel_mono, coe_comp
-/
def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv f := by
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      Scheme.fromSpecResidueField_apply, exists_true_left]
    rw [← Spec.map_inj]; rw [Spec.map_comp]; rw [← cancel_mono (X.fromSpecResidueField _)]
    grind [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField,
      Scheme.fromSpecResidueField_apply,
      Scheme.residueFieldCongr_fromSpecResidueField]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `descResidueField_stalkClosedPointTo_comp` / 引理 `descResidueField_stalkClosedPointTo_comp`

English:
lemma descResidueField_stalkClosedPointTo_comp
  given: {K : Type u} [Field K] (g : Spec (.of K) ⟶ X)
  proof: by
  simp [← cancel_epi (Y.residue _), stalkClosedPointTo_comp, residue_residueFieldMap_assoc]

中文:
引理 descResidueField_stalkClosedPointTo_comp
  条件: {K : 类型u} [域 K] (g : Spec (.of K) ⟶ X)
  证明: by
  simp [← cancel_epi (Y.residue _), stalkClosedPointTo_comp, residue_residueFieldMap_assoc]

Depends on / 依赖: Y.residue, cancel_epi, residue, residue_residueFieldMap_assoc, stalkClosedPointTo_comp
-/
lemma descResidueField_stalkClosedPointTo_comp {K : Type u} [Field K] (g : Spec (.of K) ⟶ X) :
    dsimp% descResidueField (stalkClosedPointTo (g ≫ f)) =
      Hom.residueFieldMap f (g (closedPoint K)) ≫ descResidueField (stalkClosedPointTo g) := by
  simp [← cancel_epi (Y.residue _), stalkClosedPointTo_comp, residue_residueFieldMap_assoc]

end Scheme

end AlgebraicGeometry
