/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and homological complexes

This file contains simplifications lemmas for categories
`Karoubi (HomologicalComplex C c)` and the construction of an equivalence
of categories `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`.

When the category `C` is idempotent complete, it is shown that
`HomologicalComplex (Karoubi C) c` is also idempotent complete.

-/

@[expose] public section


namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}

namespace Idempotents

namespace Karoubi

namespace HomologicalComplex

variable {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc]
/--
theorem `p_comp_d` / 定理 `p_comp_d`

English:
theorem p_comp_d
  statement: P.p.f n ≫ f.f.f n = f.f.f n
  proof: HomologicalComplex.congr_hom (p_comp f) n

@[simp, reassoc]

中文:
定理 p_comp_d
  结论: P.p.f n ≫ f.f.f n = f.f.f n
  证明: HomologicalComplex.congr_hom (p_comp f) n

@[simp, reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, congr_hom, p_comp
-/
theorem p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
  HomologicalComplex.congr_hom (p_comp f) n

@[simp, reassoc]
/--
theorem `comp_p_d` / 定理 `comp_p_d`

English:
theorem comp_p_d
  statement: f.f.f n ≫ Q.p.f n = f.f.f n
  proof: HomologicalComplex.congr_hom (comp_p f) n

@[reassoc]

中文:
定理 comp_p_d
  结论: f.f.f n ≫ Q.p.f n = f.f.f n
  证明: HomologicalComplex.congr_hom (comp_p f) n

@[reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, comp_p, congr_hom
-/
theorem comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
  HomologicalComplex.congr_hom (comp_p f) n

@[reassoc]
/--
theorem `p_comm_f` / 定理 `p_comm_f`

English:
theorem p_comm_f
  statement: P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n
  proof: HomologicalComplex.congr_hom (p_comm f) n

中文:
定理 p_comm_f
  结论: P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n
  证明: HomologicalComplex.congr_hom (p_comm f) n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, congr_hom, p_comm
-/
theorem p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
  HomologicalComplex.congr_hom (p_comm f) n

variable (P)

@[simp, reassoc]
/--
theorem `p_idem` / 定理 `p_idem`

English:
theorem p_idem
  statement: P.p.f n ≫ P.p.f n = P.p.f n
  proof: HomologicalComplex.congr_hom P.idem n

中文:
定理 p_idem
  结论: P.p.f n ≫ P.p.f n = P.p.f n
  证明: HomologicalComplex.congr_hom P.idem n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.congr_hom, P.idem, congr_hom
-/
theorem p_idem : P.p.f n ≫ P.p.f n = P.p.f n :=
  HomologicalComplex.congr_hom P.idem n

end HomologicalComplex

end Karoubi

open Karoubi

namespace KaroubiHomologicalComplexEquivalence

namespace Functor

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`,
on objects. -/
@[simps]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (P : Karoubi (HomologicalComplex C c))
  body: ⟨P.X.X n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j := { f := P.p.f i ≫ P.X.d i j }
  shape i j hij := by simp only [hom_eq_zero_iff]; cat_disch

中文:
定义 obj
  签名: (P : Karoubi (同调复形 C c))
  定义体: ⟨P.X.X n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j := { f := P.p.f i ≫ P.X.d i j }
  shape i j hij := by simp only [hom_eq_zero_iff]; cat_disch

Depends on / 依赖: HomologicalComplex, HomologicalComplex.comp_f, HomologicalComplex.congr_hom, P.X.X, P.X.d, P.idem, P.p.f, cat_disch, comp_f, congr_hom, hom_eq_zero_iff
-/
def obj (P : Karoubi (HomologicalComplex C c)) : HomologicalComplex (Karoubi C) c where
  X n :=
    ⟨P.X.X n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j := { f := P.p.f i ≫ P.X.d i j }
  shape i j hij := by simp only [hom_eq_zero_iff]; cat_disch

set_option backward.defeqAttrib.useBackward true in
/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`,
on morphisms. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q)
  body: { f := f.f.f n }

中文:
定义 map
  签名: {P Q : Karoubi (同调复形 C c)} (f : P ⟶ Q)
  定义体: { f := f.f.f n }

Depends on / 依赖: f.f.f
-/
def map {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  f n :=
    { f := f.f.f n }

end Functor

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c where
  body: Functor.obj
  map f := Functor.map f

中文:
定义 functor
  签名: : Karoubi (同调复形 C c) ⥤ 同调复形 (Karoubi C) c where
  定义体: Functor.obj
  map f := Functor.map f

Depends on / 依赖: Functor, Functor.obj
-/
def functor : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c where
  obj := Functor.obj
  map f := Functor.map f

namespace Inverse

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`,
on objects -/
@[simps]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (K : HomologicalComplex (Karoubi C) c)
  body: { X := fun n => (K.X n).X
      d := fun i j => (K.d i j).f
      shape := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k _ _ => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p := { f := fun n => (K.X n).p }

中文:
定义 obj
  签名: (K : 同调复形 (Karoubi C) c)
  定义体: { X := fun n => (K.X n).X
      d := fun i j => (K.d i j).f
      shape := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k _ _ => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p := { f := fun n => (K.X n).p }

Depends on / 依赖: K.d_comp_d, K.shape, comp_f, d_comp_d, hom_eq_zero_iff, hom_eq_zero_iff.mp
-/
def obj (K : HomologicalComplex (Karoubi C) c) : Karoubi (HomologicalComplex C c) where
  X :=
    { X := fun n => (K.X n).X
      d := fun i j => (K.d i j).f
      shape := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k _ _ => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p := { f := fun n => (K.X n).p }

set_option backward.defeqAttrib.useBackward true in
/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`,
on morphisms -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L)
  body: { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using! hom_ext_iff.mp (f.comm' i j hij) }

中文:
定义 map
  签名: {K L : 同调复形 (Karoubi C) c} (f : K ⟶ L)
  定义体: { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using! hom_ext_iff.mp (f.comm' i j hij) }

Depends on / 依赖: comp_f, f.comm, hom_ext_iff, hom_ext_iff.mp
-/
def map {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L where
  f :=
    { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using! hom_ext_iff.mp (f.comm' i j hij) }

end Inverse

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c) where
  body: Inverse.obj
  map f := Inverse.map f

中文:
定义 inverse
  签名: : 同调复形 (Karoubi C) c ⥤ Karoubi (同调复形 C c) where
  定义体: Inverse.obj
  map f := Inverse.map f

Depends on / 依赖: Inverse, Inverse.obj
-/
def inverse : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c) where
  obj := Inverse.obj
  map f := Inverse.map f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c)
  body: eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by cat_disch) (by simp))
    (by cat_disch))

中文:
定义 counitIso
  签名: : inverse ⋙ functor ≅ 𝟭 (同调复形 (Karoubi C) c)
  定义体: eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by cat_disch) (by simp))
    (by cat_disch))

Depends on / 依赖: Functor, Functor.ext, HomologicalComplex, HomologicalComplex.ext, cat_disch, eqToIso
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c) :=
  eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by cat_disch) (by simp))
    (by cat_disch))

set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse where
  body: { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d,
          HomologicalComplex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d, HomologicalComplex.p_comp_d] }
  hom_inv_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]
  inv_hom_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]

中文:
定义 unitIso
  签名: : 𝟭 (Karoubi (同调复形 C c)) ≅ functor ⋙ inverse where
  定义体: { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d,
          HomologicalComplex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d, HomologicalComplex.p_comp_d] }
  hom_inv_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]
  inv_hom_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]

Depends on / 依赖: Homologi, HomologicalComplex, HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc, HomologicalComplex.comp_p_d, HomologicalComplex.p_comp_d, HomologicalComplex.p_idem, P.p.f, comm_assoc, comp_p_d, naturality, p_comp_d, p_idem
-/
def unitIso : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse where
  hom :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d,
          HomologicalComplex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d, HomologicalComplex.p_comp_d] }
  hom_inv_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]
  inv_hom_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]

end KaroubiHomologicalComplexEquivalence

variable (C) (c)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps]
/--
Definition of `karoubiHomologicalComplexEquivalence` / `karoubiHomologicalComplexEquivalence` 的定义

English:
definition karoubiHomologicalComplexEquivalence
  signature: :
  body: KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso

中文:
定义 karoubiHomologicalComplexEquivalence
  签名: :
  定义体: KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso

Depends on / 依赖: KaroubiHomologicalComplexEquivalence, KaroubiHomologicalComplexEquivalence.functor, functor
-/
def karoubiHomologicalComplexEquivalence :
    Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c where
  functor := KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso

variable (α : Type*) [AddRightCancelSemigroup α] [One α]

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α`. -/
@[simps!]
/--
Definition of `karoubiChainComplexEquivalence` / `karoubiChainComplexEquivalence` 的定义

English:
definition karoubiChainComplexEquivalence
  signature: : Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α
  body: karoubiHomologicalComplexEquivalence C (ComplexShape.down α)

中文:
定义 karoubiChainComplexEquivalence
  签名: : Karoubi (链复形 C α) ≌ 链复形 (Karoubi C) α
  定义体: karoubiHomologicalComplexEquivalence C (ComplexShape.down α)

Depends on / 依赖: ComplexShape, ComplexShape.down, karoubiHomologicalComplexEquivalence
-/
def karoubiChainComplexEquivalence : Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.down α)

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α`. -/
@[simps!]
/--
Definition of `karoubiCochainComplexEquivalence` / `karoubiCochainComplexEquivalence` 的定义

English:
definition karoubiCochainComplexEquivalence
  signature: :
  body: karoubiHomologicalComplexEquivalence C (ComplexShape.up α)

中文:
定义 karoubiCochainComplexEquivalence
  签名: :
  定义体: karoubiHomologicalComplexEquivalence C (ComplexShape.up α)

Depends on / 依赖: ComplexShape, ComplexShape.up, karoubiHomologicalComplexEquivalence
-/
def karoubiCochainComplexEquivalence :
    Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.up α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIdempotentComplete
  signature: C] : IsIdempotentComplete (HomologicalComplex C c)
  body: by
  rw [isIdempotentComplete_iff_of_equivalence
      ((toKaroubiEquivalence C).mapHomologicalComplex c)]; rw [← isIdempotentComplete_iff_of_equivalence (karoubiHomologicalComplexEquivalence C c)]
  infer_instance

中文:
实例 [是IdempotentComplete
  签名: C] : 是IdempotentComplete (同调复形 C c)
  定义体: by
  rw [isIdempotentComplete_iff_of_equivalence
      ((toKaroubiEquivalence C).mapHomologicalComplex c)]; rw [← isIdempotentComplete_iff_of_equivalence (karoubiHomologicalComplexEquivalence C c)]
  infer_instance

Depends on / 依赖: infer_instance, isIdempotentComplete_iff_of_equivalence, karoubiHomologicalComplexEquivalence, mapHomologicalComplex, toKaroubiEquivalence
-/
instance [IsIdempotentComplete C] : IsIdempotentComplete (HomologicalComplex C c) := by
  rw [isIdempotentComplete_iff_of_equivalence
      ((toKaroubiEquivalence C).mapHomologicalComplex c)]; rw [← isIdempotentComplete_iff_of_equivalence (karoubiHomologicalComplexEquivalence C c)]
  infer_instance

end Idempotents

end CategoryTheory
