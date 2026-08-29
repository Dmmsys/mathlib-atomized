/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Affine space

## Main definitions

- `AlgebraicGeometry.AffineSpace`: `𝔸(n; S)` is the affine `n`-space over `S`.
- `AlgebraicGeometry.AffineSpace.coord`: The standard coordinate functions on the affine space.
- `AlgebraicGeometry.AffineSpace.homOfVector`:
  The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions.
- `AlgebraicGeometry.AffineSpace.homOverEquiv`:
  `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections.
- `AlgebraicGeometry.AffineSpace.SpecIso`: `𝔸(n; Spec R) ≅ Spec R[n]`

-/

@[expose] public section

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe u

variable (n : Type u) (S : Scheme.{u})

local notation3 "Int[" n "]" => CommRingCat.of (MvPolynomial n (ULift Int))

/--
Definition of `AffineSpace` / `AffineSpace` 的定义

English:
definition AffineSpace
  signature: (n : Type u) (S : Scheme.{u})
  body: pullback (terminal.from S) (terminal.from (Spec Int[n]))

中文:
定义 仿射空间
  签名: (n : 类型u) (S : 概形.{u})
  定义体: pullback (terminal.from S) (terminal.from (Spec Int[n]))

Depends on / 依赖: Scheme, Scheme.Hom.resLE, infer_instance, pullback, terminal, terminal.from
-/
def AffineSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Spec Int[n]))

namespace AffineSpace

/-- `𝔸(n; S)` is the affine `n`-space over `S`. -/
scoped[AlgebraicGeometry] notation "𝔸(" n "; " S ")" => AffineSpace n S

variable {n} in
/--
lemma `of_mvPolynomial_int_ext` / 引理 `of_mvPolynomial_int_ext`

English:
lemma of_mvPolynomial_int_ext
  given: {R} {f g : Int[n] ⟶ R} (h : forall i, f (.X i) = g (.X i))
  statement: f = g
  proof: by
  suffices f.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
      g.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    ext x
    · obtain ⟨x⟩ := x
      simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (C x)
    · simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (X x)
  ext1
  · exact RingHom.ext_int _ _
  · simpa using! h _


@[simps -isSimp]

中文:
引理 of_mvPolynomial_int_ext
  条件: {R} {f g : 整数[n] ⟶ R} (h : 对任意 i, f (.X i) = g (.X i))
  结论: f = g
  证明: by
  suffices f.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
      g.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    ext x
    · obtain ⟨x⟩ := x
      simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (C x)
    · simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (X x)
  ext1
  · exact RingHom.ext_int _ _
  · simpa using! h _


@[simps -isSimp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, MvPolynomial, MvPolynomial.mapEquiv, RingHom, RingHom.ext_int, ULift.ringEquiv.symm, congr_fun, eq_intCast, ext_int, f.hom.comp, g.hom.comp, mapEquiv, map_intCast, ringEquiv, toRingHom
-/
lemma of_mvPolynomial_int_ext {R} {f g : Int[n] ⟶ R} (h : forall i, f (.X i) = g (.X i)) : f = g := by
  suffices f.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
      g.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    ext x
    · obtain ⟨x⟩ := x
      simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (C x)
    · simpa [-map_intCast, -eq_intCast] using! DFunLike.congr_fun this (X x)
  ext1
  · exact RingHom.ext_int _ _
  · simpa using! h _


@[simps -isSimp]
/--
Instance `over` / 实例 `over`

English:
instance over
  signature: : 𝔸(n; S).CanonicallyOver S where
  body: pullback.fst _ _

中文:
实例 over
  签名: : 𝔸(n; S).CanonicallyOver S where
  定义体: pullback.fst _ _

Depends on / 依赖: SmoothOfRelativeDimension, pullback, pullback.fst
-/
instance over : 𝔸(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/--
Definition of `toSpecMvPoly` / `toSpecMvPoly` 的定义

English:
definition toSpecMvPoly
  signature: : 𝔸(n; S) ⟶ Spec Int[n]
  body: pullback.snd _ _

中文:
定义 toSpecMvPoly
  签名: : 𝔸(n; S) ⟶ Spec 整数[n]
  定义体: pullback.snd _ _

Depends on / 依赖: pullback, pullback.snd
-/
def toSpecMvPoly : 𝔸(n; S) ⟶ Spec Int[n] := pullback.snd _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Morphisms into `Spec ℤ[n]` are equivalent the choice of `n` global sections.
Use `homOverEquiv` instead.
-/
@[simps]
/--
Definition of `toSpecMvPolyIntEquiv` / `toSpecMvPolyIntEquiv` 的定义

English:
definition toSpecMvPolyIntEquiv
  signature: {X : Scheme.{u}}
  body: f.appTop ((Scheme.ΓSpecIso Int[n]).inv (.X i))
  invFun v := X.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((algebraMap Int _).comp ULift.ringEquiv.toRingHom) v))
  left_inv f := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_symm_apply]; rw [Adjunction.homEquiv_symm_apply]
    dsimp
    simp only [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    apply of_mvPolynomial_int_ext
    intro i
    rw [ConcreteCategory.hom_ofHom]; rw [coe_eval₂Hom]; rw [eval₂_X]
    rfl
  right_inv v := by ext; simp

中文:
定义 toSpecMvPoly整数Equiv
  签名: {X : 概形.{u}}
  定义体: f.appTop ((Scheme.ΓSpecIso Int[n]).inv (.X i))
  invFun v := X.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((algebraMap Int _).comp ULift.ringEquiv.toRingHom) v))
  left_inv f := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_symm_apply]; rw [Adjunction.homEquiv_symm_apply]
    dsimp
    simp only [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    apply of_mvPolynomial_int_ext
    intro i
    rw [ConcreteCategory.hom_ofHom]; rw [coe_eval₂Hom]; rw [eval₂_X]
    rfl
  right_inv v := by ext; simp

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.eq_affineLocally, LocallyOfFinitePresentation, Scheme, Smooth, affineLocally_le, appTop, eq_affineLocally, f.appTop, finitePresentation, hf.finitePresentation
-/
def toSpecMvPolyIntEquiv {X : Scheme.{u}} : (X ⟶ Spec Int[n]) ≃ (n -> Γ(X, ⊤)) where
  toFun f i := f.appTop ((Scheme.ΓSpecIso Int[n]).inv (.X i))
  invFun v := X.toSpecΓ ≫ Spec.map
    (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((algebraMap Int _).comp ULift.ringEquiv.toRingHom) v))
  left_inv f := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_symm_apply]; rw [Adjunction.homEquiv_symm_apply]
    dsimp
    simp only [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    apply of_mvPolynomial_int_ext
    intro i
    rw [ConcreteCategory.hom_ofHom]; rw [coe_eval₂Hom]; rw [eval₂_X]
    rfl
  right_inv v := by ext; simp

/--
lemma `toSpecMvPolyIntEquiv_comp` / 引理 `toSpecMvPolyIntEquiv_comp`

English:
lemma toSpecMvPolyIntEquiv_comp
  given: {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec Int[n]) (i)
  proof: rfl

中文:
引理 toSpecMvPoly整数Equiv_comp
  条件: {X Y : 概形} (f : X ⟶ Y) (g : Y ⟶ Spec 整数[n]) (i)
  证明: rfl
-/
lemma toSpecMvPolyIntEquiv_comp {X Y : Scheme} (f : X ⟶ Y) (g : Y ⟶ Spec Int[n]) (i) :
    toSpecMvPolyIntEquiv n (f ≫ g) i = f.appTop (toSpecMvPolyIntEquiv n g i) := rfl

variable {n} in
/--
Definition of `coord` / `coord` 的定义

English:
definition coord
  signature: (i : n)
  body: toSpecMvPolyIntEquiv _ (toSpecMvPoly n S) i

中文:
定义 coord
  签名: (i : n)
  定义体: toSpecMvPolyIntEquiv _ (toSpecMvPoly n S) i

Depends on / 依赖: toSpecMvPoly, toSpecMvPolyIntEquiv
-/
def coord (i : n) : Γ(𝔸(n; S), ⊤) := toSpecMvPolyIntEquiv _ (toSpecMvPoly n S) i

section homOfVector

variable {n S}

/--
Definition of `homOfVector` / `homOfVector` 的定义

English:
definition homOfVector
  signature: {X : Scheme.{u}} (f : X ⟶ S) (v : n -> Γ(X, ⊤))
  body: pullback.lift f ((toSpecMvPolyIntEquiv n).symm v) (by simp)

中文:
定义 homOfVector
  签名: {X : 概形.{u}} (f : X ⟶ S) (v : n -> Γ(X, ⊤))
  定义体: pullback.lift f ((toSpecMvPolyIntEquiv n).symm v) (by simp)

Depends on / 依赖: pullback, pullback.lift, toSpecMvPolyIntEquiv
-/
def homOfVector {X : Scheme.{u}} (f : X ⟶ S) (v : n -> Γ(X, ⊤)) : X ⟶ 𝔸(n; S) :=
  pullback.lift f ((toSpecMvPolyIntEquiv n).symm v) (by simp)

variable {X : Scheme.{u}} (f : X ⟶ S) (v : n -> Γ(X, ⊤))

@[reassoc (attr := simp)]
/--
lemma `homOfVector_over` / 引理 `homOfVector_over`

English:
lemma homOfVector_over
  statement: homOfVector f v ≫ 𝔸(n; S) ↘ S = f
  proof: pullback.lift_fst _ _ _

@[reassoc]

中文:
引理 homOfVector_over
  结论: homOfVector f v ≫ 𝔸(n; S) ↘ S = f
  证明: pullback.lift_fst _ _ _

@[reassoc]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
lemma homOfVector_over : homOfVector f v ≫ 𝔸(n; S) ↘ S = f :=
  pullback.lift_fst _ _ _

@[reassoc]
/--
lemma `homOfVector_toSpecMvPoly` / 引理 `homOfVector_toSpecMvPoly`

English:
lemma homOfVector_toSpecMvPoly
  proof: pullback.lift_snd _ _ _

@[simp]

中文:
引理 homOfVector_toSpecMvPoly
  证明: pullback.lift_snd _ _ _

@[simp]

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
lemma homOfVector_toSpecMvPoly :
    homOfVector f v ≫ toSpecMvPoly n S = (toSpecMvPolyIntEquiv n).symm v :=
  pullback.lift_snd _ _ _

@[simp]
/--
lemma `homOfVector_appTop_coord` / 引理 `homOfVector_appTop_coord`

English:
lemma homOfVector_appTop_coord
  given: (i)
  proof: by
  rw [coord]; rw [← toSpecMvPolyIntEquiv_comp]; rw [homOfVector_toSpecMvPoly]; rw [Equiv.apply_symm_apply]

@[ext 1100]

中文:
引理 homOfVector_appTop_coord
  条件: (i)
  证明: by
  rw [coord]; rw [← toSpecMvPolyIntEquiv_comp]; rw [homOfVector_toSpecMvPoly]; rw [Equiv.apply_symm_apply]

@[ext 1100]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, homOfVector_toSpecMvPoly, toSpecMvPolyIntEquiv_comp
-/
lemma homOfVector_appTop_coord (i) :
    (homOfVector f v).appTop (coord S i) = v i := by
  rw [coord]; rw [← toSpecMvPolyIntEquiv_comp]; rw [homOfVector_toSpecMvPoly]; rw [Equiv.apply_symm_apply]

@[ext 1100]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {f g : X ⟶ 𝔸(n; S)}
  proof: by
  apply pullback.hom_ext h₁
  change f ≫ toSpecMvPoly _ _ = g ≫ toSpecMvPoly _ _
  apply (toSpecMvPolyIntEquiv n).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp]; rw [toSpecMvPolyIntEquiv_comp]
  exact h₂ i

中文:
引理 hom_ext
  结论: {f g : X ⟶ 𝔸(n; S)}
  证明: by
  apply pullback.hom_ext h₁
  change f ≫ toSpecMvPoly _ _ = g ≫ toSpecMvPoly _ _
  apply (toSpecMvPolyIntEquiv n).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp]; rw [toSpecMvPolyIntEquiv_comp]
  exact h₂ i

Depends on / 依赖: hom_ext, injective, pullback, pullback.hom_ext, toSpecMvPoly, toSpecMvPolyIntEquiv, toSpecMvPolyIntEquiv_comp
-/
lemma hom_ext {f g : X ⟶ 𝔸(n; S)}
    (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S)
    (h₂ : forall i, f.appTop (coord S i) = g.appTop (coord S i)) : f = g := by
  apply pullback.hom_ext h₁
  change f ≫ toSpecMvPoly _ _ = g ≫ toSpecMvPoly _ _
  apply (toSpecMvPolyIntEquiv n).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp]; rw [toSpecMvPolyIntEquiv_comp]
  exact h₂ i

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `comp_homOfVector` / 引理 `comp_homOfVector`

English:
lemma comp_homOfVector
  given: {X Y : Scheme} (v : n -> Γ(Y, ⊤)) (f : X ⟶ Y) (g : Y ⟶ S)
  proof: by
  ext1 <;> simp

中文:
引理 comp_homOfVector
  条件: {X Y : 概形} (v : n -> Γ(Y, ⊤)) (f : X ⟶ Y) (g : Y ⟶ S)
  证明: by
  ext1 <;> simp
-/
lemma comp_homOfVector {X Y : Scheme} (v : n -> Γ(Y, ⊤)) (f : X ⟶ Y) (g : Y ⟶ S) :
    f ≫ homOfVector g v = homOfVector (f ≫ g) (f.appTop ∘ v) := by
  ext1 <;> simp

end homOfVector

variable {n}

instance {X : Scheme.{u}} [X.Over S] (v : n -> Γ(X, ⊤)) :
    (homOfVector (X ↘ S) v).IsOver S where

/-- `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections. -/
@[simps]
/--
Definition of `homOverEquiv` / `homOverEquiv` 的定义

English:
definition homOverEquiv
  signature: {X : Scheme.{u}} [X.Over S]
  body: f.1.appTop (coord S i)
  invFun v := ⟨homOfVector (X ↘ S) v, inferInstance⟩
  left_inv f := by
    ext : 2
    · simp [f.2.1]
    · rw [homOfVector_appTop_coord]
  right_inv v := by ext i; simp [-TopologicalSpace.Opens.map_top, homOfVector_appTop_coord]

中文:
定义 homOverEquiv
  签名: {X : 概形.{u}} [X.Over S]
  定义体: f.1.appTop (coord S i)
  invFun v := ⟨homOfVector (X ↘ S) v, inferInstance⟩
  left_inv f := by
    ext : 2
    · simp [f.2.1]
    · rw [homOfVector_appTop_coord]
  right_inv v := by ext i; simp [-TopologicalSpace.Opens.map_top, homOfVector_appTop_coord]

Depends on / 依赖: appTop
-/
def homOverEquiv {X : Scheme.{u}} [X.Over S] :
    { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n -> Γ(X, ⊤)) where
  toFun f i := f.1.appTop (coord S i)
  invFun v := ⟨homOfVector (X ↘ S) v, inferInstance⟩
  left_inv f := by
    ext : 2
    · simp [f.2.1]
    · rw [homOfVector_appTop_coord]
  right_inv v := by ext i; simp [-TopologicalSpace.Opens.map_top, homOfVector_appTop_coord]

set_option backward.isDefEq.respectTransparency.types false in
variable (n) in
/--
The affine space over an affine base is isomorphic to the spectrum of the polynomial ring.
Also see `AffineSpace.SpecIso`.
-/
@[simps -isSimp hom inv]
/--
Definition of `isoOfIsAffine` / `isoOfIsAffine` 的定义

English:
definition isoOfIsAffine
  signature: [IsAffine S]
  body: 𝔸(n; S).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)))
      inv := homOfVector (Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv)
        ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(S, ⊤)))).inv ∘ MvPolynomial.X)
      hom_inv_id := by
        ext1
        · simp only [Category.assoc, homOfVector_over, Category.id_comp]
          rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [eval₂Hom_comp_C]; rw [CommRingCat.ofHom_hom]; rw [← Scheme.toSpecΓ_naturality_assoc]
          simp [Scheme.isoSpec]
        · simp
      inv_hom_id := by
        apply ext_of_isAffine
        simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
          TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, Scheme.toSpecΓ_appTop,
          Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.Hom.id_app, ← Iso.eq_inv_comp,
          Category.comp_id]
        ext : 1
        apply ringHom_ext'
        · change _ = (CommRingCat.ofHom C ≫ _).hom
          rw [CommRingCat.hom_comp]; rw [RingHom.comp_assoc]; rw [CommRingCat.hom_ofHom]; rw [eval₂Hom_comp_C]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_ext_iff]; rw [← cancel_mono (Scheme.ΓSpecIso _).hom]
          rw [← Scheme.Hom.comp_appTop]; rw [homOfVector_over]; rw [Scheme.Hom.comp_appTop]
          simp only [Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.of_carrier,
            ← Scheme.toSpecΓ_appTop]
          rw [← Scheme.Hom.comp_appTop_assoc]; rw [Scheme.isoSpec]; rw [asIso_inv]; rw [IsIso.hom_inv_id]
          simp
        · intro i
          rw [CommRingCat.comp_apply]; rw [ConcreteCategory.hom_ofHom]; rw [coe_eval₂Hom]
          simp only [eval₂_X]
          exact homOfVector_appTop_coord _ _ _

@[simp]

中文:
定义 isoOfIsAffine
  签名: [是仿射 S]
  定义体: 𝔸(n; S).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)))
      inv := homOfVector (Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv)
        ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(S, ⊤)))).inv ∘ MvPolynomial.X)
      hom_inv_id := by
        ext1
        · simp only [Category.assoc, homOfVector_over, Category.id_comp]
          rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [eval₂Hom_comp_C]; rw [CommRingCat.ofHom_hom]; rw [← Scheme.toSpecΓ_naturality_assoc]
          simp [Scheme.isoSpec]
        · simp
      inv_hom_id := by
        apply ext_of_isAffine
        simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
          TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, Scheme.toSpecΓ_appTop,
          Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.Hom.id_app, ← Iso.eq_inv_comp,
          Category.comp_id]
        ext : 1
        apply ringHom_ext'
        · change _ = (CommRingCat.ofHom C ≫ _).hom
          rw [CommRingCat.hom_comp]; rw [RingHom.comp_assoc]; rw [CommRingCat.hom_ofHom]; rw [eval₂Hom_comp_C]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_ext_iff]; rw [← cancel_mono (Scheme.ΓSpecIso _).hom]
          rw [← Scheme.Hom.comp_appTop]; rw [homOfVector_over]; rw [Scheme.Hom.comp_appTop]
          simp only [Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.of_carrier,
            ← Scheme.toSpecΓ_appTop]
          rw [← Scheme.Hom.comp_appTop_assoc]; rw [Scheme.isoSpec]; rw [asIso_inv]; rw [IsIso.hom_inv_id]
          simp
        · intro i
          rw [CommRingCat.comp_apply]; rw [ConcreteCategory.hom_ofHom]; rw [coe_eval₂Hom]
          simp only [eval₂_X]
          exact homOfVector_appTop_coord _ _ _

@[simp]

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Spec.map
-/
def isoOfIsAffine [IsAffine S] :
𝔸(n; S) ≅ Spec .of MvPolynomial n Γ(S, ⊤) where
      hom := 𝔸(n; S).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)))
      inv := homOfVector (Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv)
        ((Scheme.ΓSpecIso (.of (MvPolynomial n Γ(S, ⊤)))).inv ∘ MvPolynomial.X)
      hom_inv_id := by
        ext1
        · simp only [Category.assoc, homOfVector_over, Category.id_comp]
          rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [eval₂Hom_comp_C]; rw [CommRingCat.ofHom_hom]; rw [← Scheme.toSpecΓ_naturality_assoc]
          simp [Scheme.isoSpec]
        · simp
      inv_hom_id := by
        apply ext_of_isAffine
        simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
          TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, Scheme.toSpecΓ_appTop,
          Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.Hom.id_app, ← Iso.eq_inv_comp,
          Category.comp_id]
        ext : 1
        apply ringHom_ext'
        · change _ = (CommRingCat.ofHom C ≫ _).hom
          rw [CommRingCat.hom_comp]; rw [RingHom.comp_assoc]; rw [CommRingCat.hom_ofHom]; rw [eval₂Hom_comp_C]; rw [← CommRingCat.hom_comp]; rw [← CommRingCat.hom_ext_iff]; rw [← cancel_mono (Scheme.ΓSpecIso _).hom]
          rw [← Scheme.Hom.comp_appTop]; rw [homOfVector_over]; rw [Scheme.Hom.comp_appTop]
          simp only [Category.assoc, Scheme.ΓSpecIso_naturality, CommRingCat.of_carrier,
            ← Scheme.toSpecΓ_appTop]
          rw [← Scheme.Hom.comp_appTop_assoc]; rw [Scheme.isoSpec]; rw [asIso_inv]; rw [IsIso.hom_inv_id]
          simp
        · intro i
          rw [CommRingCat.comp_apply]; rw [ConcreteCategory.hom_ofHom]; rw [coe_eval₂Hom]
          simp only [eval₂_X]
          exact homOfVector_appTop_coord _ _ _

@[simp]
/--
lemma `isoOfIsAffine_hom_appTop` / 引理 `isoOfIsAffine_hom_appTop`

English:
lemma isoOfIsAffine_hom_appTop
  given: [IsAffine S]
  proof: by
  simp [isoOfIsAffine_hom]

中文:
引理 isoOfIsAffine_hom_appTop
  条件: [是仿射 S]
  证明: by
  simp [isoOfIsAffine_hom]

Depends on / 依赖: isoOfIsAffine_hom
-/
lemma isoOfIsAffine_hom_appTop [IsAffine S] :
    (isoOfIsAffine n S).hom.appTop =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom
        (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (coord S)) := by
  simp [isoOfIsAffine_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `isoOfIsAffine_inv_appTop_coord` / 引理 `isoOfIsAffine_inv_appTop_coord`

English:
lemma isoOfIsAffine_inv_appTop_coord
  given: [IsAffine S] (i)
  proof: homOfVector_appTop_coord _ _ _

中文:
引理 isoOfIsAffine_inv_appTop_coord
  条件: [是仿射 S] (i)
  证明: homOfVector_appTop_coord _ _ _

Depends on / 依赖: homOfVector_appTop_coord
-/
lemma isoOfIsAffine_inv_appTop_coord [IsAffine S] (i) :
    (isoOfIsAffine n S).inv.appTop (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) :=
  homOfVector_appTop_coord _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `isoOfIsAffine_inv_over` / 引理 `isoOfIsAffine_inv_over`

English:
lemma isoOfIsAffine_inv_over
  given: [IsAffine S]
  proof: pullback.lift_fst _ _ _

中文:
引理 isoOfIsAffine_inv_over
  条件: [是仿射 S]
  证明: pullback.lift_fst _ _ _

Depends on / 依赖: IsOpenImmersion, SurjectiveOnStalks, lift_fst, pullback, pullback.lift_fst
-/
lemma isoOfIsAffine_inv_over [IsAffine S] :
    (isoOfIsAffine n S).inv ≫ 𝔸(n; S) ↘ S = Spec.map (CommRingCat.ofHom C) ≫ S.isoSpec.inv :=
  pullback.lift_fst _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAffine
  signature: S] : IsAffine 𝔸(n; S)
  body: .of_isIso (isoOfIsAffine n S).hom

中文:
实例 [是仿射
  签名: S] : 是仿射 𝔸(n; S)
  定义体: .of_isIso (isoOfIsAffine n S).hom

Depends on / 依赖: isoOfIsAffine, of_isIso
-/
instance [IsAffine S] : IsAffine 𝔸(n; S) := .of_isIso (isoOfIsAffine n S).hom

variable (n) in
/--
Definition of `SpecIso` / `SpecIso` 的定义

English:
definition SpecIso
  signature: (R : CommRingCat.{u})
  body: isoOfIsAffine _ _ ≪≫ Scheme.Spec.mapIso (MvPolynomial.mapEquiv _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).toCommRingCatIso.op

中文:
定义 SpecIso
  签名: (R : 交换环范畴.{u})
  定义体: isoOfIsAffine _ _ ≪≫ Scheme.Spec.mapIso (MvPolynomial.mapEquiv _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).toCommRingCatIso.op

Depends on / 依赖: MvPolynomial, MvPolynomial.mapEquiv, Scheme, Scheme.Spec.mapIso, commRingCatIsoToRingEquiv, isoOfIsAffine, mapEquiv, mapIso, symm.commRingCatIsoToRingEquiv, toCommRingCatIso, toCommRingCatIso.op
-/
def SpecIso (R : CommRingCat.{u}) :
𝔸(n; Spec R) ≅ Spec .of MvPolynomial n R :=
  isoOfIsAffine _ _ ≪≫ Scheme.Spec.mapIso (MvPolynomial.mapEquiv _
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv).toCommRingCatIso.op

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `SpecIso_hom_appTop` / 引理 `SpecIso_hom_appTop`

English:
lemma SpecIso_hom_appTop
  given: (R : CommRingCat.{u})
  proof: by
  ext i
  simp [SpecIso]

中文:
引理 SpecIso_hom_appTop
  条件: (R : 交换环范畴.{u})
  证明: by
  ext i
  simp [SpecIso]

Depends on / 依赖: SpecIso
-/
lemma SpecIso_hom_appTop (R : CommRingCat.{u}) :
    (SpecIso n R).hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (eval₂Hom ((Scheme.ΓSpecIso _).inv ≫
        (𝔸(n; Spec R) ↘ Spec R).appTop).hom (coord (Spec R))) := by
  ext i
  simp [SpecIso]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `SpecIso_inv_appTop_coord` / 引理 `SpecIso_inv_appTop_coord`

English:
lemma SpecIso_inv_appTop_coord
  given: (R : CommRingCat.{u}) (i)
  proof: by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  rw [isoOfIsAffine_inv_appTop_coord]; rw [← CommRingCat.comp_apply]; rw [← Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.comp_apply]
  congr 1
  exact map_X _ _

中文:
引理 SpecIso_inv_appTop_coord
  条件: (R : 交换环范畴.{u}) (i)
  证明: by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  rw [isoOfIsAffine_inv_appTop_coord]; rw [← CommRingCat.comp_apply]; rw [← Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.comp_apply]
  congr 1
  exact map_X _ _

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, Functor, Functor.mapIso_inv, Iso.op_inv, Iso.trans_inv, Quiver, Quiver.Hom.unop_op, Scheme, Scheme.Hom.comp_app, Scheme.Spec_map, SpecIso, Spec_map, TopologicalSpace, TopologicalSpace.Opens.map_top, comp_app, comp_apply, isoOfIsAffine_inv_appTop_coord, mapIso_inv, map_X
-/
lemma SpecIso_inv_appTop_coord (R : CommRingCat.{u}) (i) :
    (SpecIso n R).inv.appTop (coord _ i) = (Scheme.ΓSpecIso (.of _)).inv (.X i) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  rw [isoOfIsAffine_inv_appTop_coord]; rw [← CommRingCat.comp_apply]; rw [← Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.comp_apply]
  congr 1
  exact map_X _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `SpecIso_inv_over` / 引理 `SpecIso_inv_over`

English:
lemma SpecIso_inv_over
  given: (R : CommRingCat.{u})
  proof: by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc, isoOfIsAffine_inv_over, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  congr 1
  rw [Iso.inv_comp_eq]
  ext : 2
  exact map_C _ _

中文:
引理 SpecIso_inv_over
  条件: (R : 交换环范畴.{u})
  证明: by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc, isoOfIsAffine_inv_over, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  congr 1
  rw [Iso.inv_comp_eq]
  ext : 2
  exact map_C _ _

Depends on / 依赖: Category, Category.assoc, Functor, Functor.mapIso_inv, Iso.inv_comp_eq, Iso.op_inv, Iso.trans_inv, Quiver, Quiver.Hom.unop_op, Scheme, Scheme.Spec_map, Scheme.isoSpec_Spec_inv, Spec.map_comp, SpecIso, Spec_map, inv_comp_eq, isoOfIsAffine_inv_over, isoSpec_Spec_inv, mapIso_inv, map_C
-/
lemma SpecIso_inv_over (R : CommRingCat.{u}) :
    (SpecIso n R).inv ≫ 𝔸(n; Spec R) ↘ Spec R = Spec.map (CommRingCat.ofHom C) := by
  simp only [SpecIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc, isoOfIsAffine_inv_over, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  congr 1
  rw [Iso.inv_comp_eq]
  ext : 2
  exact map_C _ _

section functorial

variable (n) in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {S T : Scheme.{u}} (f : S ⟶ T)
  body: homOfVector (𝔸(n; S) ↘ S ≫ f) (coord S)

@[reassoc (attr := simp)]

中文:
定义 map
  签名: {S T : 概形.{u}} (f : S ⟶ T)
  定义体: homOfVector (𝔸(n; S) ↘ S ≫ f) (coord S)

@[reassoc (attr := simp)]

Depends on / 依赖: homOfVector
-/
def map {S T : Scheme.{u}} (f : S ⟶ T) : 𝔸(n; S) ⟶ 𝔸(n; T) :=
  homOfVector (𝔸(n; S) ↘ S ≫ f) (coord S)

@[reassoc (attr := simp)]
/--
lemma `map_over` / 引理 `map_over`

English:
lemma map_over
  given: {S T : Scheme.{u}} (f : S ⟶ T)
  statement: map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
  proof: pullback.lift_fst _ _ _

@[simp]

中文:
引理 map_over
  条件: {S T : 概形.{u}} (f : S ⟶ T)
  结论: map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f
  证明: pullback.lift_fst _ _ _

@[simp]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) : map n f ≫ 𝔸(n; T) ↘ T = 𝔸(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

@[simp]
/--
lemma `map_appTop_coord` / 引理 `map_appTop_coord`

English:
lemma map_appTop_coord
  given: {S T : Scheme.{u}} (f : S ⟶ T) (i)
  proof: homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]

中文:
引理 map_appTop_coord
  条件: {S T : 概形.{u}} (f : S ⟶ T) (i)
  证明: homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: homOfVector_appTop_coord
-/
lemma map_appTop_coord {S T : Scheme.{u}} (f : S ⟶ T) (i) :
    (map n f).appTop (coord T i) = coord S i :=
  homOfVector_appTop_coord _ _ _

@[reassoc (attr := simp)]
/--
lemma `map_toSpecMvPoly` / 引理 `map_toSpecMvPoly`

English:
lemma map_toSpecMvPoly
  given: {S T : Scheme.{u}} (f : S ⟶ T)
  proof: by
  apply (toSpecMvPolyIntEquiv _).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp]; rw [← coord]; rw [map_appTop_coord]; rw [coord]

@[simp]

中文:
引理 map_toSpecMvPoly
  条件: {S T : 概形.{u}} (f : S ⟶ T)
  证明: by
  apply (toSpecMvPolyIntEquiv _).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp]; rw [← coord]; rw [map_appTop_coord]; rw [coord]

@[simp]

Depends on / 依赖: injective, map_appTop_coord, toSpecMvPolyIntEquiv, toSpecMvPolyIntEquiv_comp
-/
lemma map_toSpecMvPoly {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toSpecMvPoly n T = toSpecMvPoly n S := by
  apply (toSpecMvPolyIntEquiv _).injective
  ext i
  rw [toSpecMvPolyIntEquiv_comp]; rw [← coord]; rw [map_appTop_coord]; rw [coord]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map n (𝟙 S) = 𝟙 𝔸(n; S)
  proof: by
  ext1 <;> simp

中文:
引理 map_id
  结论: map n (𝟙 S) = 𝟙 𝔸(n; S)
  证明: by
  ext1 <;> simp
-/
lemma map_id : map n (𝟙 S) = 𝟙 𝔸(n; S) := by
  ext1 <;> simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc, simp]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {S S' S'' : Scheme} (f : S ⟶ S') (g : S' ⟶ S'')
  proof: by
  ext1
  · simp
  · simp

中文:
引理 map_comp
  条件: {S S' S'' : 概形} (f : S ⟶ S') (g : S' ⟶ S'')
  证明: by
  ext1
  · simp
  · simp
-/
lemma map_comp {S S' S'' : Scheme} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1
  · simp
  · simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `map_SpecMap` / 引理 `map_SpecMap`

English:
lemma map_SpecMap
  given: {R S : CommRingCat.{u}} (φ : R ⟶ S)
  proof: by
  rw [← Iso.inv_comp_eq]
  ext1
  · simp only [map_over, Category.assoc, SpecIso_inv_over, SpecIso_inv_over_assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [map_comp_C]; rw [CommRingCat.ofHom_comp]; rw [CommRingCat.ofHom_hom]
  · simp only [TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
    conv_lhs => enter [2]; tactic => exact map_appTop_coord _ _
    conv_rhs => enter [2]; tactic => exact SpecIso_inv_appTop_coord _ _
    rw [SpecIso_inv_appTop_coord]; rw [← CommRingCat.comp_apply]; rw [← Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.comp_apply]; rw [ConcreteCategory.hom_ofHom]; rw [map_X]

中文:
引理 map_SpecMap
  条件: {R S : 交换环范畴.{u}} (φ : R ⟶ S)
  证明: by
  rw [← Iso.inv_comp_eq]
  ext1
  · simp only [map_over, Category.assoc, SpecIso_inv_over, SpecIso_inv_over_assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [map_comp_C]; rw [CommRingCat.ofHom_comp]; rw [CommRingCat.ofHom_hom]
  · simp only [TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
    conv_lhs => enter [2]; tactic => exact map_appTop_coord _ _
    conv_rhs => enter [2]; tactic => exact SpecIso_inv_appTop_coord _ _
    rw [SpecIso_inv_appTop_coord]; rw [← CommRingCat.comp_apply]; rw [← Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.comp_apply]; rw [ConcreteCategory.hom_ofHom]; rw [map_X]

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.comp_, CommRingCat.comp_apply, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Iso.inv_comp_eq, Scheme, Scheme.Hom.comp_app, Spec.map_comp, SpecIso_inv_appTop_coord, SpecIso_inv_over, SpecIso_inv_over_assoc, TopologicalSpace, TopologicalSpace.Opens.map_top, comp_, comp_app, comp_apply, conv_lhs
-/
lemma map_SpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    map n (Spec.map φ) =
      (SpecIso n S).hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.map φ.hom)) ≫
        (SpecIso n R).inv := by
  rw [← Iso.inv_comp_eq]
  ext1
  · simp only [map_over, Category.assoc, SpecIso_inv_over, SpecIso_inv_over_assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [map_comp_C]; rw [CommRingCat.ofHom_comp]; rw [CommRingCat.ofHom_hom]
  · simp only [TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, CommRingCat.comp_apply]
    conv_lhs => enter [2]; tactic => exact map_appTop_coord _ _
    conv_rhs => enter [2]; tactic => exact SpecIso_inv_appTop_coord _ _
    rw [SpecIso_inv_appTop_coord]; rw [← CommRingCat.comp_apply]; rw [← Scheme.ΓSpecIso_inv_naturality]; rw [CommRingCat.comp_apply]; rw [ConcreteCategory.hom_ofHom]; rw [map_X]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapSpecMap` / `mapSpecMap` 的定义

English:
definition mapSpecMap
  signature: {R S : CommRingCat.{u}} (φ : R ⟶ S)
  body: Arrow.isoMk (SpecIso n S) (SpecIso n R) (by have := (SpecIso n R).inv_hom_id; simp [map_SpecMap])

中文:
定义 mapSpecMap
  签名: {R S : 交换环范畴.{u}} (φ : R ⟶ S)
  定义体: Arrow.isoMk (SpecIso n S) (SpecIso n R) (by have := (SpecIso n R).inv_hom_id; simp [map_SpecMap])
-/
def mapSpecMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Arrow.mk (map n (Spec.map φ)) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := n) φ.hom))) :=
  Arrow.isoMk (SpecIso n S) (SpecIso n R) (by have := (SpecIso n R).inv_hom_id; simp [map_SpecMap])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback_map` / 引理 `isPullback_map`

English:
lemma isPullback_map
  given: {S T : Scheme.{u}} (f : S ⟶ T)
  proof: by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (map_over f)).mp ?_
  simp only [terminal.comp_from, ]
  convert! (IsPullback.of_hasPullback _ _).flip
  rw [← toSpecMvPoly]; rw [← toSpecMvPoly]; rw [map_toSpecMvPoly]

中文:
引理 isPullback_map
  条件: {S T : 概形.{u}} (f : S ⟶ T)
  证明: by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (map_over f)).mp ?_
  simp only [terminal.comp_from, ]
  convert! (IsPullback.of_hasPullback _ _).flip
  rw [← toSpecMvPoly]; rw [← toSpecMvPoly]; rw [map_toSpecMvPoly]

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsPullback.paste_horiz_iff, comp_from, convert, map_over, map_toSpecMvPoly, of_hasPullback, paste_horiz_iff, terminal, terminal.comp_from, toSpecMvPoly
-/
lemma isPullback_map {S T : Scheme.{u}} (f : S ⟶ T) :
    IsPullback (map n f) (𝔸(n; S) ↘ S) (𝔸(n; T) ↘ T) f := by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (map_over f)).mp ?_
  simp only [terminal.comp_from, ]
  convert! (IsPullback.of_hasPullback _ _).flip
  rw [← toSpecMvPoly]; rw [← toSpecMvPoly]; rw [map_toSpecMvPoly]

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: {n m : Type u} (i : m -> n) (S : Scheme.{u})
  body: homOfVector (𝔸(n; S) ↘ S) (coord S ∘ i)

@[simp, reassoc]

中文:
定义 reindex
  签名: {n m : 类型u} (i : m -> n) (S : 概形.{u})
  定义体: homOfVector (𝔸(n; S) ↘ S) (coord S ∘ i)

@[simp, reassoc]

Depends on / 依赖: homOfVector
-/
def reindex {n m : Type u} (i : m -> n) (S : Scheme.{u}) : 𝔸(n; S) ⟶ 𝔸(m; S) :=
  homOfVector (𝔸(n; S) ↘ S) (coord S ∘ i)

@[simp, reassoc]
/--
lemma `reindex_over` / 引理 `reindex_over`

English:
lemma reindex_over
  given: {n m : Type u} (i : m -> n) (S : Scheme.{u})
  proof: pullback.lift_fst _ _ _

@[simp]

中文:
引理 reindex_over
  条件: {n m : 类型u} (i : m -> n) (S : 概形.{u})
  证明: pullback.lift_fst _ _ _

@[simp]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
lemma reindex_over {n m : Type u} (i : m -> n) (S : Scheme.{u}) :
    reindex i S ≫ 𝔸(m; S) ↘ S = 𝔸(n; S) ↘ S :=
  pullback.lift_fst _ _ _

@[simp]
/--
lemma `reindex_appTop_coord` / 引理 `reindex_appTop_coord`

English:
lemma reindex_appTop_coord
  given: {n m : Type u} (i : m -> n) (S : Scheme.{u}) (j : m)
  proof: homOfVector_appTop_coord _ _ _

@[simp]

中文:
引理 reindex_appTop_coord
  条件: {n m : 类型u} (i : m -> n) (S : 概形.{u}) (j : m)
  证明: homOfVector_appTop_coord _ _ _

@[simp]

Depends on / 依赖: Surjective, f.homeomorph.surjective, homOfVector_appTop_coord, homeomorph, surjective
-/
lemma reindex_appTop_coord {n m : Type u} (i : m -> n) (S : Scheme.{u}) (j : m) :
    (reindex i S).appTop (coord S j) = coord S (i j) :=
  homOfVector_appTop_coord _ _ _

@[simp]
/--
lemma `reindex_id` / 引理 `reindex_id`

English:
lemma reindex_id
  statement: reindex id S = 𝟙 𝔸(n; S)
  proof: by
  ext1 <;> simp

中文:
引理 reindex_id
  结论: reindex id S = 𝟙 𝔸(n; S)
  证明: by
  ext1 <;> simp
-/
lemma reindex_id : reindex id S = 𝟙 𝔸(n; S) := by
  ext1 <;> simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/--
lemma `reindex_comp` / 引理 `reindex_comp`

English:
lemma reindex_comp
  given: {n₁ n₂ n₃ : Type u} (i : n₁ ⟶ n₂) (j : n₂ ⟶ n₃) (S : Scheme.{u})
  proof: by
  ext k <;> simp

中文:
引理 reindex_comp
  条件: {n₁ n₂ n₃ : 类型u} (i : n₁ ⟶ n₂) (j : n₂ ⟶ n₃) (S : 概形.{u})
  证明: by
  ext k <;> simp
-/
lemma reindex_comp {n₁ n₂ n₃ : Type u} (i : n₁ ⟶ n₂) (j : n₂ ⟶ n₃) (S : Scheme.{u}) :
    reindex (i ≫ j) S = reindex j S ≫ reindex i S := by
  ext k <;> simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `map_reindex` / 引理 `map_reindex`

English:
lemma map_reindex
  given: {n₁ n₂ : Type u} (i : n₁ -> n₂) {S T : Scheme.{u}} (f : S ⟶ T)
  proof: by
  apply hom_ext <;> simp

中文:
引理 map_reindex
  条件: {n₁ n₂ : 类型u} (i : n₁ -> n₂) {S T : 概形.{u}} (f : S ⟶ T)
  证明: by
  apply hom_ext <;> simp

Depends on / 依赖: Nonempty, Subsingleton, hom_ext
-/
lemma map_reindex {n₁ n₂ : Type u} (i : n₁ -> n₂) {S T : Scheme.{u}} (f : S ⟶ T) :
    map n₂ f ≫ reindex i T = reindex i S ≫ map n₁ f := by
  apply hom_ext <;> simp

/-- The affine space as a functor. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : (Type u)ᵒᵖ ⥤ Scheme.{u} ⥤ Scheme.{u} where
  body: { obj := AffineSpace n.unop, map := map n.unop, map_id := map_id, map_comp := map_comp }
  map {n m} i := { app := reindex i.unop, naturality := fun _ _ => map_reindex i.unop }
  map_id n := by ext : 2; exact reindex_id _
  map_comp f g := by ext : 2; dsimp; exact reindex_comp _ _ _

中文:
定义 functor
  签名: : (类型u)ᵒᵖ ⥤ 概形.{u} ⥤ 概形.{u} where
  定义体: { obj := AffineSpace n.unop, map := map n.unop, map_id := map_id, map_comp := map_comp }
  map {n m} i := { app := reindex i.unop, naturality := fun _ _ => map_reindex i.unop }
  map_id n := by ext : 2; exact reindex_id _
  map_comp f g := by ext : 2; dsimp; exact reindex_comp _ _ _

Depends on / 依赖: AffineSpace, map_comp, map_id, n.unop
-/
def functor : (Type u)ᵒᵖ ⥤ Scheme.{u} ⥤ Scheme.{u} where
  obj n := { obj := AffineSpace n.unop, map := map n.unop, map_id := map_id, map_comp := map_comp }
  map {n m} i := { app := reindex i.unop, naturality := fun _ _ => map_reindex i.unop }
  map_id n := by ext : 2; exact reindex_id _
  map_comp f g := by ext : 2; dsimp; exact reindex_comp _ _ _

end functorial
section instances

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAffineHom (𝔸(n; S) ↘ S)
  body: MorphismProperty.pullback_fst _ _ inferInstance

中文:
实例 :
  签名: 是仿射态射 (𝔸(n; S) ↘ S)
  定义体: MorphismProperty.pullback_fst _ _ inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance : IsAffineHom (𝔸(n; S) ↘ S) := MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Surjective (𝔸(n; S) ↘ S)
  body: MorphismProperty.pullback_fst _ _ by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]; rw [MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)]
  exact ⟨MvPolynomial.comap_C_surjective⟩

中文:
实例 :
  签名: 满射 (𝔸(n; S) ↘ S)
  定义体: MorphismProperty.pullback_fst _ _ by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]; rw [MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)]
  exact ⟨MvPolynomial.comap_C_surjective⟩

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, MorphismProperty.pullback_fst, MvPolynomial, MvPolynomial.comap_C_surjective, Spec.map, Surjective, cancel_right_of_respectsIso, comap_C_surjective, comp_from, isIso_of_isTerminal, pullback_fst, specULiftZIsTerminal, terminal, terminal.comp_from, terminal.from, terminalIsTerminal
-/
instance : Surjective (𝔸(n; S) ↘ S) := MorphismProperty.pullback_fst _ _ by
  have := isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]; rw [MorphismProperty.cancel_right_of_respectsIso (P := @Surjective)]
  exact ⟨MvPolynomial.comap_C_surjective⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: n] : LocallyOfFinitePresentation (𝔸(n; S) ↘ S)
  body: MorphismProperty.pullback_fst _ _ by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]; rw [MorphismProperty.cancel_right_of_respectsIso (P := @LocallyOfFinitePresentation)]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]; rw [RingHom.FinitePresentation]
  convert! (inferInstance : Algebra.FinitePresentation (ULift Int) Int[n])
  exact Algebra.algebra_ext _ _ fun _ => rfl

中文:
实例 [有限
  签名: n] : 局部有限呈现 (𝔸(n; S) ↘ S)
  定义体: MorphismProperty.pullback_fst _ _ by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]; rw [MorphismProperty.cancel_right_of_respectsIso (P := @LocallyOfFinitePresentation)]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]; rw [RingHom.FinitePresentation]
  convert! (inferInstance : Algebra.FinitePresentation (ULift Int) Int[n])
  exact Algebra.algebra_ext _ _ fun _ => rfl

Depends on / 依赖: Algebra, Algebra.FinitePresentation, Algebra.algebra_ext, CommRingCat, CommRingCat.ofHom, FinitePresentation, HasRingHomProperty, HasRingHomProperty.Spec_iff, LocallyOfFinitePresentation, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, MorphismProperty.pullback_fst, RingHom, RingHom.FinitePresentation, Spec.map, Spec_iff, algebra_ext, cancel_right_of_respectsIso, comp_from, convert
-/
instance [Finite n] : LocallyOfFinitePresentation (𝔸(n; S) ↘ S) :=
MorphismProperty.pullback_fst _ _ by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]; rw [MorphismProperty.cancel_right_of_respectsIso (P := @LocallyOfFinitePresentation)]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]; rw [RingHom.FinitePresentation]
  convert! (inferInstance : Algebra.FinitePresentation (ULift Int) Int[n])
  exact Algebra.algebra_ext _ _ fun _ => rfl

/--
lemma `isOpenMap_over` / 引理 `isOpenMap_over`

English:
lemma isOpenMap_over
  statement: IsOpenMap (𝔸(n; S) ↘ S)
  proof: by
  change topologically @IsOpenMap _
  wlog hS : exists R, S = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover
      (P := topologically @IsOpenMap) S.affineCover).mpr ?_
    intro i
    have := this (n := n) (S.affineCover.X i) ⟨_, rfl⟩
    rwa [← (isPullback_map (n := n) (S.affineCover.f i)).isoPullback_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)] at this
  obtain ⟨R, rfl⟩ := hS
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)
    (SpecIso n R).inv]; rw [SpecIso_inv_over]
  exact MvPolynomial.isOpenMap_comap_C

中文:
引理 isOpenMap_over
  结论: 是开映射 (𝔸(n; S) ↘ S)
  证明: by
  change topologically @IsOpenMap _
  wlog hS : exists R, S = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover
      (P := topologically @IsOpenMap) S.affineCover).mpr ?_
    intro i
    have := this (n := n) (S.affineCover.X i) ⟨_, rfl⟩
    rwa [← (isPullback_map (n := n) (S.affineCover.f i)).isoPullback_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)] at this
  obtain ⟨R, rfl⟩ := hS
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)
    (SpecIso n R).inv]; rw [SpecIso_inv_over]
  exact MvPolynomial.isOpenMap_comap_C

Depends on / 依赖: IsOpenMap, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, MorphismProperty, MorphismProperty.cancel_left_of_respectsIso, S.affineCover, S.affineCover.X, S.affineCover.f, affineCover, cancel_left_of_respectsIso, iff_of_openCover, isPullback_map, isoPullback_hom_snd, topologically
-/
lemma isOpenMap_over : IsOpenMap (𝔸(n; S) ↘ S) := by
  change topologically @IsOpenMap _
  wlog hS : exists R, S = Spec R
  · refine (IsZariskiLocalAtTarget.iff_of_openCover
      (P := topologically @IsOpenMap) S.affineCover).mpr ?_
    intro i
    have := this (n := n) (S.affineCover.X i) ⟨_, rfl⟩
    rwa [← (isPullback_map (n := n) (S.affineCover.f i)).isoPullback_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)] at this
  obtain ⟨R, rfl⟩ := hS
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := topologically @IsOpenMap)
    (SpecIso n R).inv]; rw [SpecIso_inv_over]
  exact MvPolynomial.isOpenMap_comap_C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GeometricallyIrreducible (𝔸(n; S) ↘ S)
  body: by
  rw [geometricallyIrreducible_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

中文:
实例 :
  签名: 几何不可约 (𝔸(n; S) ↘ S)
  定义体: by
  rw [geometricallyIrreducible_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

Depends on / 依赖: ObjectProperty, ObjectProperty.prop_of_iso, SpecIso, geometricallyIrreducible_iff, h.isoIsPullback, infer_instance, introv, isPullback_map, isoIsPullback, prop_of_iso
-/
instance : GeometricallyIrreducible (𝔸(n; S) ↘ S) := by
  rw [geometricallyIrreducible_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IrreducibleSpace
  signature: S] : IrreducibleSpace 𝔸(n; S)
  body: GeometricallyIrreducible.irreducibleSpace (𝔸(n; S) ↘ S) (isOpenMap_over S)

中文:
实例 [不可约空间
  签名: S] : 不可约空间 𝔸(n; S)
  定义体: GeometricallyIrreducible.irreducibleSpace (𝔸(n; S) ↘ S) (isOpenMap_over S)

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.irreducibleSpace, irreducibleSpace, isOpenMap_over
-/
instance [IrreducibleSpace S] : IrreducibleSpace 𝔸(n; S) :=
  GeometricallyIrreducible.irreducibleSpace (𝔸(n; S) ↘ S) (isOpenMap_over S)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GeometricallyReduced (𝔸(n; S) ↘ S)
  body: by
  rw [geometricallyReduced_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

中文:
实例 :
  签名: 几何既约 (𝔸(n; S) ↘ S)
  定义体: by
  rw [geometricallyReduced_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

Depends on / 依赖: ObjectProperty, ObjectProperty.prop_of_iso, SpecIso, geometricallyReduced_iff, h.isoIsPullback, infer_instance, introv, isPullback_map, isoIsPullback, prop_of_iso
-/
instance : GeometricallyReduced (𝔸(n; S) ↘ S) := by
  rw [geometricallyReduced_iff]
  introv K h
  apply ObjectProperty.prop_of_iso _
    ((h.isoIsPullback _ _ (isPullback_map _)) ≪≫ (SpecIso n (.of K))).symm
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : IsReduced S] : IsReduced 𝔸(n; S)
  body: by
  wlog hS : exists R, S = Spec R
  · rw [IsReduced.iff_of_openCover _ (S.affineCover.pullback₁ (𝔸(n; S) ↘ S))]
    intro i
    have : IsReduced 𝔸(n; S.affineCover.X i) := this _ ⟨_, rfl⟩
    exact isReduced_of_isOpenImmersion ((isPullback_map _).isoPullback.inv)
  obtain ⟨R, rfl⟩ := hS
  rw [affine_isReduced_iff] at h
  exact isReduced_of_isOpenImmersion (SpecIso n R).hom

中文:
实例 [h
  签名: : 是既约 S] : 是既约 𝔸(n; S)
  定义体: by
  wlog hS : exists R, S = Spec R
  · rw [IsReduced.iff_of_openCover _ (S.affineCover.pullback₁ (𝔸(n; S) ↘ S))]
    intro i
    have : IsReduced 𝔸(n; S.affineCover.X i) := this _ ⟨_, rfl⟩
    exact isReduced_of_isOpenImmersion ((isPullback_map _).isoPullback.inv)
  obtain ⟨R, rfl⟩ := hS
  rw [affine_isReduced_iff] at h
  exact isReduced_of_isOpenImmersion (SpecIso n R).hom

Depends on / 依赖: IsReduced, IsReduced.iff_of_openCover, S.affineCover.X, S.affineCover.pullback, SpecIso, affineCover, affine_isReduced_iff, iff_of_openCover, isPullback_map, isReduced_of_isOpenImmersion, isoPullback, isoPullback.inv
-/
instance [h : IsReduced S] : IsReduced 𝔸(n; S) := by
  wlog hS : exists R, S = Spec R
  · rw [IsReduced.iff_of_openCover _ (S.affineCover.pullback₁ (𝔸(n; S) ↘ S))]
    intro i
    have : IsReduced 𝔸(n; S.affineCover.X i) := this _ ⟨_, rfl⟩
    exact isReduced_of_isOpenImmersion ((isPullback_map _).isoPullback.inv)
  obtain ⟨R, rfl⟩ := hS
  rw [affine_isReduced_iff] at h
  exact isReduced_of_isOpenImmersion (SpecIso n R).hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GeometricallyIntegral (𝔸(n; S) ↘ S)
  body: .of_geometricallyReduced_of_geometricallyIrreducible _

中文:
实例 :
  签名: 几何整 (𝔸(n; S) ↘ S)
  定义体: .of_geometricallyReduced_of_geometricallyIrreducible _

Depends on / 依赖: Surjective, Surjective.sigmaDesc_of_union_range_eq_univ, iUnion_range, of_geometricallyReduced_of_geometricallyIrreducible, sigmaDesc_of_union_range_eq_univ
-/
instance : GeometricallyIntegral (𝔸(n; S) ↘ S) :=
  .of_geometricallyReduced_of_geometricallyIrreducible _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: S] : IsIntegral 𝔸(n; S)
  body: isIntegral_of_irreducibleSpace_of_isReduced _

中文:
实例 [是整
  签名: S] : 是整 𝔸(n; S)
  定义体: isIntegral_of_irreducibleSpace_of_isReduced _

Depends on / 依赖: isIntegral_of_irreducibleSpace_of_isReduced
-/
instance [IsIntegral S] : IsIntegral 𝔸(n; S) := isIntegral_of_irreducibleSpace_of_isReduced _

set_option backward.isDefEq.respectTransparency.types false in
open MorphismProperty in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: n] : IsIso (𝔸(n; S) ↘ S)
  body: pullback_fst
(P := isomorphisms _) _ _ by
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]
  apply IsStableUnderComposition.comp_mem
  · rw [HasAffineProperty.iff_of_isAffine (P := isomorphisms _), ← isomorphisms,
      ← arrow_mk_iso_iff (isomorphisms _) (arrowIsoΓSpecOfIsAffine _)]
    exact ⟨inferInstance, (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨C_injective n _, C_surjective _⟩⟩
  · exact isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)

中文:
实例 [是空
  签名: n] : 是同构 (𝔸(n; S) ↘ S)
  定义体: pullback_fst
(P := isomorphisms _) _ _ by
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]
  apply IsStableUnderComposition.comp_mem
  · rw [HasAffineProperty.iff_of_isAffine (P := isomorphisms _), ← isomorphisms,
      ← arrow_mk_iso_iff (isomorphisms _) (arrowIsoΓSpecOfIsAffine _)]
    exact ⟨inferInstance, (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨C_injective n _, C_surjective _⟩⟩
  · exact isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)

Depends on / 依赖: pullback_fst
-/
instance [IsEmpty n] : IsIso (𝔸(n; S) ↘ S) := pullback_fst
(P := isomorphisms _) _ _ by
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom C))]
  apply IsStableUnderComposition.comp_mem
  · rw [HasAffineProperty.iff_of_isAffine (P := isomorphisms _), ← isomorphisms,
      ← arrow_mk_iso_iff (isomorphisms _) (arrowIsoΓSpecOfIsAffine _)]
    exact ⟨inferInstance, (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨C_injective n _, C_surjective _⟩⟩
  · exact isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal (terminal.from _)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIntegralHom_over_iff_isEmpty` / 引理 `isIntegralHom_over_iff_isEmpty`

English:
lemma isIntegralHom_over_iff_isEmpty
  statement: IsIntegralHom (𝔸(n; S) ↘ S) ↔ IsEmpty S ∨ IsEmpty n
  proof: by
  constructor
  · intro h
    cases isEmpty_or_nonempty S
    · exact .inl ‹_›
    refine .inr ?_
    wlog hS : exists R, S = Spec R
    · obtain ⟨x⟩ := ‹Nonempty S›
      obtain ⟨y, hy⟩ := S.affineCover.covers x
      exact this (S.affineCover.X _) (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_map (S.affineCover.f _)) h) ⟨y⟩ ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hS
    have : Nontrivial R := (subsingleton_or_nontrivial R).resolve_left fun H =>
        not_isEmpty_of_nonempty (Spec R) (inferInstanceAs (IsEmpty (PrimeSpectrum R)))
    constructor
    intro i
    have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso.{u}
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom (SpecIso n R).inv]; rw [SpecIso_inv_over]; rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)] at h
    obtain ⟨p : Polynomial R, hp, hp'⟩ :=
      (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
        (arrowIsoΓSpecOfIsAffine _)).mpr h.2 (X i)
    have : (rename fun _ => i).comp (uniqueAlgEquiv.{_, u} _ PUnit).symm.toAlgHom p = 0 := by
      simp [← hp', ← algebraMap_eq]
    rw [AlgHom.comp_apply]; rw [map_eq_zero_iff _ (rename_injective _ (fun _ _ _ => rfl))] at this
    simp only [AlgEquiv.coe_toAlgHom, EmbeddingLike.map_eq_zero_iff] at this
    simp [this] at hp
  · rintro (_ | _) <;> infer_instance

中文:
引理 is整数egralHom_over_iff_isEmpty
  结论: 是整态射 (𝔸(n; S) ↘ S) ↔ 是空 S ∨ 是空 n
  证明: by
  constructor
  · intro h
    cases isEmpty_or_nonempty S
    · exact .inl ‹_›
    refine .inr ?_
    wlog hS : exists R, S = Spec R
    · obtain ⟨x⟩ := ‹Nonempty S›
      obtain ⟨y, hy⟩ := S.affineCover.covers x
      exact this (S.affineCover.X _) (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_map (S.affineCover.f _)) h) ⟨y⟩ ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hS
    have : Nontrivial R := (subsingleton_or_nontrivial R).resolve_left fun H =>
        not_isEmpty_of_nonempty (Spec R) (inferInstanceAs (IsEmpty (PrimeSpectrum R)))
    constructor
    intro i
    have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso.{u}
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom (SpecIso n R).inv]; rw [SpecIso_inv_over]; rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)] at h
    obtain ⟨p : Polynomial R, hp, hp'⟩ :=
      (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
        (arrowIsoΓSpecOfIsAffine _)).mpr h.2 (X i)
    have : (rename fun _ => i).comp (uniqueAlgEquiv.{_, u} _ PUnit).symm.toAlgHom p = 0 := by
      simp [← hp', ← algebraMap_eq]
    rw [AlgHom.comp_apply]; rw [map_eq_zero_iff _ (rename_injective _ (fun _ _ _ => rfl))] at this
    simp only [AlgEquiv.coe_toAlgHom, EmbeddingLike.map_eq_zero_iff] at this
    simp [this] at hp
  · rintro (_ | _) <;> infer_instance

Depends on / 依赖: IsEmpty, IsStableUnderBaseChange, MorphismProperty, MorphismProperty.IsStableUnderBaseChange.of_isPullback, Nonempty, Nontrivial, PrimeSpectrum, S.affineCover.X, S.affineCover.covers, S.affineCover.f, Unique, affineCover, covers, isEmpty_or_nonempty, isPullback_map, not_isEmpty_of_nonempty, of_isPullback, resolve_left, subsingleton_or_nontrivial
-/
lemma isIntegralHom_over_iff_isEmpty : IsIntegralHom (𝔸(n; S) ↘ S) ↔ IsEmpty S ∨ IsEmpty n := by
  constructor
  · intro h
    cases isEmpty_or_nonempty S
    · exact .inl ‹_›
    refine .inr ?_
    wlog hS : exists R, S = Spec R
    · obtain ⟨x⟩ := ‹Nonempty S›
      obtain ⟨y, hy⟩ := S.affineCover.covers x
      exact this (S.affineCover.X _) (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_map (S.affineCover.f _)) h) ⟨y⟩ ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hS
    have : Nontrivial R := (subsingleton_or_nontrivial R).resolve_left fun H =>
        not_isEmpty_of_nonempty (Spec R) (inferInstanceAs (IsEmpty (PrimeSpectrum R)))
    constructor
    intro i
    have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso.{u}
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom (SpecIso n R).inv]; rw [SpecIso_inv_over]; rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)] at h
    obtain ⟨p : Polynomial R, hp, hp'⟩ :=
      (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
        (arrowIsoΓSpecOfIsAffine _)).mpr h.2 (X i)
    have : (rename fun _ => i).comp (uniqueAlgEquiv.{_, u} _ PUnit).symm.toAlgHom p = 0 := by
      simp [← hp', ← algebraMap_eq]
    rw [AlgHom.comp_apply]; rw [map_eq_zero_iff _ (rename_injective _ (fun _ _ _ => rfl))] at this
    simp only [AlgEquiv.coe_toAlgHom, EmbeddingLike.map_eq_zero_iff] at this
    simp [this] at hp
  · rintro (_ | _) <;> infer_instance

/--
lemma `not_isIntegralHom` / 引理 `not_isIntegralHom`

English:
lemma not_isIntegralHom
  given: [Nonempty S] [Nonempty n]
  statement: ¬ IsIntegralHom (𝔸(n; S) ↘ S)
  proof: by
  simp [isIntegralHom_over_iff_isEmpty]

中文:
引理 not_is整数egralHom
  条件: [非空 S] [非空 n]
  结论: ¬ 是整态射 (𝔸(n; S) ↘ S)
  证明: by
  simp [isIntegralHom_over_iff_isEmpty]

Depends on / 依赖: isIntegralHom_over_iff_isEmpty
-/
lemma not_isIntegralHom [Nonempty S] [Nonempty n] : ¬ IsIntegralHom (𝔸(n; S) ↘ S) := by
  simp [isIntegralHom_over_iff_isEmpty]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `spec_le_iff` / 引理 `spec_le_iff`

English:
lemma spec_le_iff
  given: (R : CommRingCat) (p q : Spec R)
  statement: p <= q ↔ q.asIdeal <= p.asIdeal
  proof: by
  aesop (add simp PrimeSpectrum.le_iff_specializes)

中文:
引理 spec_le_iff
  条件: (R : 交换环范畴) (p q : Spec R)
  结论: p <= q ↔ q.asIdeal <= p.asIdeal
  证明: by
  aesop (add simp PrimeSpectrum.le_iff_specializes)

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.le_iff_specializes, le_iff_specializes
-/
lemma spec_le_iff (R : CommRingCat) (p q : Spec R) : p <= q ↔ q.asIdeal <= p.asIdeal := by
  aesop (add simp PrimeSpectrum.le_iff_specializes)

/--
One should bear this equality in mind when breaking the `Spec R/ PrimeSpectrum R` abstraction
boundary, since these instances are not definitionally equal.
-/
example (R : CommRingCat) :
    inferInstance (α := Preorder (Spec R)) = inferInstance (α := Preorder (PrimeSpectrum R)ᵒᵈ) := by
  aesop (add simp spec_le_iff)

end instances

end AffineSpace

end AlgebraicGeometry
