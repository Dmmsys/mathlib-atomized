/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.SpectralSequence.ComplexShape

/-!
# Spectral sequences

In this file, we define the category `SpectralSequence C c r₀` of spectral sequences
in an abelian category `C` with `Eᵣ`-pages defined from `r₀ : ℤ` having differentials
given by complex shapes `c : ℤ → ComplexShape κ`, where `κ` is the index type
for the objects on each page (e.g. `κ := ℤ × ℤ` or `κ := ℕ × ℕ`).
A spectral sequence is defined as the data of a sequence of homological complexes
(the pages) and a sequence of isomorphisms between the homology of a page and the
next page.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category C] [Abelian C]
  {κ : Type*} (c : Int -> ComplexShape κ) (r₀ : Int)

/--
Definition of `SpectralSequence` / `SpectralSequence` 的定义

English:
structure SpectralSequence
  parameters: where
  axioms and operations (2):
    - page((r : Int) (hr : r₀ <= r := by lia)) : HomologicalComplex C (c r)
    - iso((r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : (page r).homology pq ≅ (page r').X pq

中文:
结构 SpectralSequence
  参数: where
  公理与运算 (2 个):
    - page((r : 整数) (hr : r₀ <= r := by lia)) : HomologicalComplex C (c r)
    - iso((r r' : 整数) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : (page r).homology pq ≅ (page r').X pq

Depends on / 依赖: HomologicalComplex
-/
structure SpectralSequence where
  /-- the `r`th page of a spectral sequence is an homological complex -/
  page (r : Int) (hr : r₀ <= r := by lia) : HomologicalComplex C (c r)
  /-- the isomorphism between the homology of the `r`-th page at an object `pq : κ`
  and the corresponding object on the next page -/
  iso (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence

variable {C c r₀}

/-- A morphism of spectral sequences is a sequence of morphisms between the
pages which commutes with the isomorphisms in homology. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (E E' : SpectralSequence C c r₀)
  axioms and operations (2):
    - hom((r : Int) (hr : r₀ <= r := by lia)) : E.page r ⟶ E'.page r
    - comm((r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom = (E.iso r r' pq).hom ≫ (hom r').f pq  [default: by cat_disch]

中文:
结构 Hom
  参数: (E E' : SpectralSequence C c r₀)
  公理与运算 (2 个):
    - hom((r : 整数) (hr : r₀ <= r := by lia)) : E.page r ⟶ E'.page r
    - comm((r r' : 整数) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia)) : HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom = (E.iso r r' pq).hom ≫ (hom r').f pq  [默认: by cat_disch]

Depends on / 依赖: E.iso, E.page, HomologicalComplex, HomologicalComplex.homologyMap, cat_disch, homologyMap
-/
structure Hom (E E' : SpectralSequence C c r₀) where
  /-- the morphism of homological complexes between the `r`th pages -/
  hom (r : Int) (hr : r₀ <= r := by lia) : E.page r ⟶ E'.page r
  comm (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
    HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom =
      (E.iso r r' pq).hom ≫ (hom r').f pq := by cat_disch

/--
Definition of `pageXIsoOfEq` / `pageXIsoOfEq` 的定义

English:
definition pageXIsoOfEq
  signature: (E : SpectralSequence C c r₀) (pq : κ) (r r' : Int) (h : r = r' := by lia)
  body: eqToIso (by subst h; rfl)

中文:
定义 pageXIsoOfEq
  签名: (E : SpectralSequence C c r₀) (pq : κ) (r r' : 整数) (h : r = r' := by lia)
  定义体: eqToIso (by subst h; rfl)

Depends on / 依赖: E.page, eqToIso
-/
def pageXIsoOfEq (E : SpectralSequence C c r₀) (pq : κ) (r r' : Int) (h : r = r' := by lia)
    (hr : r₀ <= r := by lia) :
    (E.page r).X pq ≅ (E.page r').X pq :=
  eqToIso (by subst h; rfl)

attribute [reassoc (attr := simp)] Hom.comm

@[simps! id_hom comp_hom]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SpectralSequence C c r₀)
  body: Hom
  id _ := { hom _ _ := 𝟙 _ }
  comp f g :=
    { hom r hr := f.hom r ≫ g.hom r
      comm r r' hrr' pq hr := by
        simp [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r'] }

@[ext]

中文:
实例 :
  签名: Category (SpectralSequence C c r₀)
  定义体: Hom
  id _ := { hom _ _ := 𝟙 _ }
  comp f g :=
    { hom r hr := f.hom r ≫ g.hom r
      comm r r' hrr' pq hr := by
        simp [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r'] }

@[ext]
-/
instance : Category (SpectralSequence C c r₀) where
  Hom := Hom
  id _ := { hom _ _ := 𝟙 _ }
  comp f g :=
    { hom r hr := f.hom r ≫ g.hom r
      comm r r' hrr' pq hr := by
        simp [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r'] }

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {E E' : SpectralSequence C c r₀} {f f' : E ⟶ E'}
  proof: Hom.ext (by grind)

中文:
引理 hom_ext
  结论: {E E' : SpectralSequence C c r₀} {f f' : E ⟶ E'}
  证明: Hom.ext (by grind)

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {E E' : SpectralSequence C c r₀} {f f' : E ⟶ E'}
    (h : forall (r : Int) (hr : r₀ <= r), f.hom r = f'.hom r) :
    f = f' :=
  Hom.ext (by grind)

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

variable (C c r₀)

/-- The functor `SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r)` which
sends a spectral sequence to its `r`th page. -/
@[simps]
/--
Definition of `pageFunctor` / `pageFunctor` 的定义

English:
definition pageFunctor
  signature: (r : Int) (hr : r₀ <= r := by lia)
  body: E.page r
  map f := f.hom r

中文:
定义 pageFunctor
  签名: (r : 整数) (hr : r₀ <= r := by lia)
  定义体: E.page r
  map f := f.hom r

Depends on / 依赖: E.page, HomologicalComplex, SpectralSequence, f.hom
-/
def pageFunctor (r : Int) (hr : r₀ <= r := by lia) :
    SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r) where
  obj E := E.page r
  map f := f.hom r

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between the homology of a spectral sequence on the
object `pq : κ` of the `r`th page and the corresponding object on the next page. -/
@[simps!]
/--
Definition of `pageHomologyNatIso` / `pageHomologyNatIso` 的定义

English:
definition pageHomologyNatIso
  body: NatIso.ofComponents (fun E => E.iso r r' pq)

中文:
定义 pageHomologyNatIso
  定义体: NatIso.ofComponents (fun E => E.iso r r' pq)

Depends on / 依赖: E.iso, HomologicalComplex, HomologicalComplex.eval, HomologicalComplex.homologyFunctor, NatIso, NatIso.ofComponents, homologyFunctor, ofComponents, pageFunctor
-/
noncomputable def pageHomologyNatIso
    (r r' : Int) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ <= r := by lia) :
    pageFunctor C c r₀ r ⋙ HomologicalComplex.homologyFunctor _ _ pq ≅
      pageFunctor C c r₀ r' ⋙ HomologicalComplex.eval _ _ pq :=
  NatIso.ofComponents (fun E => E.iso r r' pq)

end SpectralSequence

/--
Definition of `CohomologicalSpectralSequence` / `CohomologicalSpectralSequence` 的定义

English:
abbreviation CohomologicalSpectralSequence
  body: SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : Int × Int))

中文:
缩写 CohomologicalSpectralSequence
  定义体: SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : Int × Int))

Depends on / 依赖: ComplexShape, ComplexShape.up, SpectralSequence
-/
abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : Int × Int))

/--
Definition of `E₂CohomologicalSpectralSequence` / `E₂CohomologicalSpectralSequence` 的定义

English:
abbreviation E₂CohomologicalSpectralSequence
  body: CohomologicalSpectralSequence C 2

中文:
缩写 E₂CohomologicalSpectralSequence
  定义体: CohomologicalSpectralSequence C 2

Depends on / 依赖: CohomologicalSpectralSequence
-/
abbrev E₂CohomologicalSpectralSequence := CohomologicalSpectralSequence C 2

/--
Definition of `CohomologicalSpectralSequenceNat` / `CohomologicalSpectralSequenceNat` 的定义

English:
abbreviation CohomologicalSpectralSequenceNat
  body: SpectralSequence C (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

中文:
缩写 CohomologicalSpectralSequenceNat
  定义体: SpectralSequence C (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

Depends on / 依赖: ComplexShape, ComplexShape.spectralSequenceNat, SpectralSequence, spectralSequenceNat
-/
abbrev CohomologicalSpectralSequenceNat :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

/--
Definition of `E₂CohomologicalSpectralSequenceNat` / `E₂CohomologicalSpectralSequenceNat` 的定义

English:
abbreviation E₂CohomologicalSpectralSequenceNat
  body: CohomologicalSpectralSequenceNat C 2

中文:
缩写 E₂CohomologicalSpectralSequenceNat
  定义体: CohomologicalSpectralSequenceNat C 2

Depends on / 依赖: CohomologicalSpectralSequenceNat
-/
abbrev E₂CohomologicalSpectralSequenceNat :=
  CohomologicalSpectralSequenceNat C 2

/--
Definition of `CohomologicalSpectralSequenceFin` / `CohomologicalSpectralSequenceFin` 的定义

English:
abbreviation CohomologicalSpectralSequenceFin
  signature: (l : Nat)
  body: SpectralSequence C (fun r => ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

中文:
缩写 CohomologicalSpectralSequenceFin
  签名: (l : 自然数)
  定义体: SpectralSequence C (fun r => ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

Depends on / 依赖: ComplexShape, ComplexShape.spectralSequenceFin, SpectralSequence, spectralSequenceFin
-/
abbrev CohomologicalSpectralSequenceFin (l : Nat) :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

/--
Definition of `E₂CohomologicalSpectralSequenceFin` / `E₂CohomologicalSpectralSequenceFin` 的定义

English:
abbreviation E₂CohomologicalSpectralSequenceFin
  signature: (l : Nat)
  body: CohomologicalSpectralSequenceFin C 2 l

中文:
缩写 E₂CohomologicalSpectralSequenceFin
  签名: (l : 自然数)
  定义体: CohomologicalSpectralSequenceFin C 2 l

Depends on / 依赖: CohomologicalSpectralSequenceFin
-/
abbrev E₂CohomologicalSpectralSequenceFin (l : Nat) :=
  CohomologicalSpectralSequenceFin C 2 l

end CategoryTheory
