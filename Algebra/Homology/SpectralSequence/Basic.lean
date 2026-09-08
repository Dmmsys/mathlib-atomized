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
  {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

/-- Given an abelian category `C`, a sequence of complex shapes `c : ℤ → ComplexShape κ`
and a starting page `r₀ : ℤ`, a spectral sequence involves pages which are homological
complexes and isomorphisms saying that the homology of a page identifies to the next page. -/
/-
**CategoryTheory.SpectralSequence** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：SpectralSequence where /-- the `r`th page of a spectral sequence is an hom
ological complex -/ page (r : Int) (hr : r₀ <= r
参数：r : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an abelian category `C`, a sequence of complex shapes `c : ℤ → ComplexShap
e κ`
and a starting page `r₀ : ℤ`, a spectral sequence involves pages which are homol
ogical
complexes and isomorphisms saying that the homology of a page identifies to the 
next page.
-/
structure SpectralSequence where
  /-- the `r`th page of a spectral sequence is an homological complex -/
  page (r : ℤ) (hr : r₀ ≤ r := by lia) : HomologicalComplex C (c r)
  /-- the isomorphism between the homology of the `r`-th page at an object `pq : κ`
  and the corresponding object on the next page -/
  iso (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence

variable {C c r₀}

/-- A morphism of spectral sequences is a sequence of morphisms between the
pages which commutes with the isomorphisms in homology. -/
@[ext]
/-
**CategoryTheory.SpectralSequence.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.
SpectralSequence`。
形式化陈述：Hom (E E' : SpectralSequence C c r₀) where /-- the morphism of homological
 complexes between the `r`th pages -/ hom (r : Int) (hr : r₀ <= r
参数：E E' : SpectralSequence C c r₀；r : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of spectral sequences is a sequence of morphisms between the
pages which commutes with the isomorphisms in homology.
-/
structure Hom (E E' : SpectralSequence C c r₀) where
  /-- the morphism of homological complexes between the `r`th pages -/
  hom (r : ℤ) (hr : r₀ ≤ r := by lia) : E.page r ⟶ E'.page r
  comm (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom =
      (E.iso r r' pq).hom ≫ (hom r').f pq := by cat_disch

/-- If `E` is a spectral sequence, and `r = r'`, this is the
isomorphism `(E.page r).X pq ≅ (E.page r').X pq`. -/
/-
**CategoryTheory.SpectralSequence.pageXIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.SpectralSequence`。
形式化陈述：pageXIsoOfEq (E : SpectralSequence C c r₀) (pq : κ) (r r' : Int) (h : r = 
r'
参数：E : SpectralSequence C c r₀；pq : κ；r r' : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a spectral sequence, and `r = r'`, this is the
isomorphism `(E.page r).X pq ≅ (E.page r').X pq`.
-/
def pageXIsoOfEq (E : SpectralSequence C c r₀) (pq : κ) (r r' : ℤ) (h : r = r' := by lia)
    (hr : r₀ ≤ r := by lia) :
    (E.page r).X pq ≅ (E.page r').X pq :=
  eqToIso (by subst h; rfl)

attribute [reassoc (attr := simp)] Hom.comm

@[simps! id_hom comp_hom]
/-
**CategoryTheory.SpectralSequence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Spe
ctralSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (SpectralSequence C c r₀) where
  Hom := Hom
  id _ := { hom _ _ := 𝟙 _ }
  comp f g :=
    { hom r hr := f.hom r ≫ g.hom r
      comm r r' hrr' pq hr := by
        simp [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r'] }

@[ext]
/-
**CategoryTheory.SpectralSequence.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.SpectralSequence`。
形式化陈述：hom_ext {E E' : SpectralSequence C c r₀} {f f' : E ⟶ E'} (h : forall (r : 
Int) (hr : r₀ <= r), f.hom r = f'.hom r) : f = f'
参数：h : forall (r : Int) (hr : r₀ <= r), f.hom r = f'.hom r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SpectralSequence.Hom.ext`：∀ {C : Type u_1} {inst : Catego
ryTheory.Category.{u_3, u_1} C} {inst_1 : CategoryTheory.Abelian C} {κ : Type u_
2}   {c : ℤ → ComplexShape κ}…
-/
lemma hom_ext {E E' : SpectralSequence C c r₀} {f f' : E ⟶ E'}
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r), f.hom r = f'.hom r) :
    f = f' :=
  Hom.ext (by grind)

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

variable (C c r₀)

/-- The functor `SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r)` which
sends a spectral sequence to its `r`th page. -/
@[simps]
/-
**CategoryTheory.SpectralSequence.pageFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SpectralSequence`。
形式化陈述：pageFunctor (r : Int) (hr : r₀ <= r
参数：r : Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r)` which
sends a spectral sequence to its `r`th page.
-/
def pageFunctor (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r) where
  obj E := E.page r
  map f := f.hom r

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between the homology of a spectral sequence on the
object `pq : κ` of the `r`th page and the corresponding object on the next page. -/
@[simps!]
/-
**CategoryTheory.SpectralSequence.pageHomologyNatIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.SpectralSequence`。
形式化陈述：pageHomologyNatIso (r r' : Int) (pq : κ) (hrr' : r + 1 = r'
参数：r r' : Int；pq : κ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The natural isomorphism between the homology of a spectral sequence on the
object `pq : κ` of the `r`th page and the corresponding object on the next page.
-/
noncomputable def pageHomologyNatIso
    (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    pageFunctor C c r₀ r ⋙ HomologicalComplex.homologyFunctor _ _ pq ≅
      pageFunctor C c r₀ r' ⋙ HomologicalComplex.eval _ _ pq :=
  NatIso.ofComponents (fun E ↦ E.iso r r' pq)

end SpectralSequence

/-- A cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page. -/
/-
**CategoryTheory.CohomologicalSpectralSequence** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：CohomologicalSpectralSequence
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page.
-/
abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))

/-- A `E₂`-cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
/-
**CategoryTheory.E** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `E₂`-cohomological spectral sequence has differentials given by the
vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`.
-/
abbrev E₂CohomologicalSpectralSequence := CohomologicalSpectralSequence C 2

/-- A first quadrant cohomological spectral sequence has differentials
given by the vector `(r, 1 - r)` on the `r`th page. -/
/-
**CategoryTheory.CohomologicalSpectralSequenceNat** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory`。
形式化陈述：CohomologicalSpectralSequenceNat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first quadrant cohomological spectral sequence has differentials
given by the vector `(r, 1 - r)` on the `r`th page.
-/
abbrev CohomologicalSpectralSequenceNat :=
  SpectralSequence C (fun r ↦ ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

/-- A first quadrant `E₂`-cohomological spectral sequence has differentials
given by the vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
/-
**CategoryTheory.E** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first quadrant `E₂`-cohomological spectral sequence has differentials
given by the vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`.
-/
abbrev E₂CohomologicalSpectralSequenceNat :=
  CohomologicalSpectralSequenceNat C 2

/-- A cohomological spectral sequence lying on finitely many rows
has differentials given by the vector `(r, 1 - r)` on the `r`th page. -/
/-
**CategoryTheory.CohomologicalSpectralSequenceFin** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory`。
形式化陈述：CohomologicalSpectralSequenceFin (l : Nat)
参数：l : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cohomological spectral sequence lying on finitely many rows
has differentials given by the vector `(r, 1 - r)` on the `r`th page.
-/
abbrev CohomologicalSpectralSequenceFin (l : ℕ) :=
  SpectralSequence C (fun r ↦ ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

/-- A `E₂`-cohomological spectral sequence lying on finitely many rows
has differentials given by the vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`. -/
/-
**CategoryTheory.E** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `E₂`-cohomological spectral sequence lying on finitely many rows
has differentials given by the vector `(r, 1 - r)` on the `r`th page for `2 ≤ r`
.
-/
abbrev E₂CohomologicalSpectralSequenceFin (l : ℕ) :=
  CohomologicalSpectralSequenceFin C 2 l

end CategoryTheory

