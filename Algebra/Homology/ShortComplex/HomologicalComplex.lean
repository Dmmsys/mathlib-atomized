/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Tactic.NormNum

/-!
# The short complexes attached to homological complexes

In this file, we define a functor
`shortComplexFunctor C c i : HomologicalComplex C c ⥤ ShortComplex C`.
By definition, the image of a homological complex `K` by this functor
is the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`.

The homology `K.homology i` of a homological complex `K` in degree `i` is defined as
the homology of the short complex `(shortComplexFunctor C c i).obj K`, which can be
abbreviated as `K.sc i`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k` for arbitrary indices `i`, `j` and `k`. -/
@[simps]
/--
Definition of `shortComplexFunctor'` / `shortComplexFunctor'` 的定义

English:
definition shortComplexFunctor'
  signature: (i j k : ι)
  body: ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

中文:
定义 shortComplexFunctor'
  签名: (i j k : ι)
  定义体: ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

Depends on / 依赖: K.d_comp_d, ShortComplex, ShortComplex.mk, d_comp_d
-/
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

/-- The functor `HomologicalComplex C c ⥤ ShortComplex C` which sends a homological
complex `K` to the short complex `K.X (c.prev i) ⟶ K.X i ⟶ K.X (c.next i)`. -/
@[simps!]
/--
Definition of `shortComplexFunctor` / `shortComplexFunctor` 的定义

English:
definition shortComplexFunctor
  signature: (i : ι)
  body: shortComplexFunctor' C c (c.prev i) i (c.next i)

中文:
定义 shortComplexFunctor
  签名: (i : ι)
  定义体: shortComplexFunctor' C c (c.prev i) i (c.next i)

Depends on / 依赖: c.next, c.prev, shortComplexFunctor
-/
noncomputable def shortComplexFunctor (i : ι) :=
  shortComplexFunctor' C c (c.prev i) i (c.next i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k`
when `c.prev j = i` and `c.next j = k`. -/
@[simps!]
/--
Definition of `natIsoSc'` / `natIsoSc'` 的定义

English:
definition natIsoSc'
  signature: (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  body: NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by simp) (by simp)) (by cat_disch)

中文:
定义 natIsoSc'
  签名: (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  定义体: NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by simp) (by simp)) (by cat_disch)

Depends on / 依赖: Iso.refl, K.XIsoOfEq, NatIso, NatIso.ofComponents, ShortComplex, ShortComplex.isoMk, XIsoOfEq, cat_disch, ofComponents
-/
noncomputable def natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by simp) (by simp)) (by cat_disch)

variable {C c}

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

/--
Definition of `sc'` / `sc'` 的定义

English:
abbreviation sc'
  body: (shortComplexFunctor' C c i j k).obj K

中文:
缩写 sc'
  定义体: (shortComplexFunctor' C c i j k).obj K

Depends on / 依赖: shortComplexFunctor
-/
abbrev sc' := (shortComplexFunctor' C c i j k).obj K

/--
Definition of `sc` / `sc` 的定义

English:
abbreviation sc
  body: (shortComplexFunctor C c i).obj K

中文:
缩写 sc
  定义体: (shortComplexFunctor C c i).obj K

Depends on / 依赖: shortComplexFunctor
-/
noncomputable abbrev sc := (shortComplexFunctor C c i).obj K

/--
Definition of `isoSc'` / `isoSc'` 的定义

English:
abbreviation isoSc'
  signature: (hi : c.prev j = i) (hk : c.next j = k)
  body: (natIsoSc' C c i j k hi hk).app K

中文:
缩写 isoSc'
  签名: (hi : c.prev j = i) (hk : c.next j = k)
  定义体: (natIsoSc' C c i j k hi hk).app K

Depends on / 依赖: natIsoSc
-/
noncomputable abbrev isoSc' (hi : c.prev j = i) (hk : c.next j = k) :
    K.sc j ≅ K.sc' i j k := (natIsoSc' C c i j k hi hk).app K

/--
Definition of `HasHomology` / `HasHomology` 的定义

English:
abbreviation HasHomology
  body: (K.sc i).HasHomology

中文:
缩写 有同调
  定义体: (K.sc i).HasHomology

Depends on / 依赖: HasHomology, K.sc
-/
abbrev HasHomology := (K.sc i).HasHomology

variable {K L} in
include iso in
/--
lemma `hasHomology_of_iso` / 引理 `hasHomology_of_iso`

English:
lemma hasHomology_of_iso
  given: [K.HasHomology i]
  statement: L.HasHomology i
  proof: ShortComplex.hasHomology_of_iso
    ((shortComplexFunctor _ _ i).mapIso iso : K.sc i ≅ L.sc i)

中文:
引理 hasHomology_of_iso
  条件: [K.有同调 i]
  结论: L.有同调 i
  证明: ShortComplex.hasHomology_of_iso
    ((shortComplexFunctor _ _ i).mapIso iso : K.sc i ≅ L.sc i)

Depends on / 依赖: K.sc, L.sc, ShortComplex, ShortComplex.hasHomology_of_iso, hasHomology_of_iso, mapIso, shortComplexFunctor
-/
lemma hasHomology_of_iso [K.HasHomology i] : L.HasHomology i :=
  ShortComplex.hasHomology_of_iso
    ((shortComplexFunctor _ _ i).mapIso iso : K.sc i ≅ L.sc i)

section

variable [K.HasHomology i]

/--
Definition of `homology` / `homology` 的定义

English:
definition homology
  body: (K.sc i).homology

中文:
定义 homology
  定义体: (K.sc i).homology

Depends on / 依赖: K.sc, homology
-/
noncomputable def homology := (K.sc i).homology

/--
Definition of `cycles` / `cycles` 的定义

English:
definition cycles
  body: (K.sc i).cycles

中文:
定义 cycles
  定义体: (K.sc i).cycles

Depends on / 依赖: K.sc, cycles
-/
noncomputable def cycles := (K.sc i).cycles

/--
Definition of `iCycles` / `iCycles` 的定义

English:
definition iCycles
  signature: : K.cycles i ⟶ K.X i
  body: (K.sc i).iCycles

中文:
定义 iCycles
  签名: : K.cycles i ⟶ K.X i
  定义体: (K.sc i).iCycles

Depends on / 依赖: K.sc, iCycles
-/
noncomputable def iCycles : K.cycles i ⟶ K.X i := (K.sc i).iCycles

/--
Definition of `homologyπ` / `homologyπ` 的定义

English:
definition homologyπ
  signature: : K.cycles i ⟶ K.homology i
  body: (K.sc i).homologyπ

中文:
定义 homologyπ
  签名: : K.cycles i ⟶ K.homology i
  定义体: (K.sc i).homologyπ

Depends on / 依赖: K.sc
-/
noncomputable def homologyπ : K.cycles i ⟶ K.homology i := (K.sc i).homologyπ

variable {i}

/--
Definition of `liftCycles` / `liftCycles` 的定义

English:
definition liftCycles
  signature: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  body: (K.sc i).liftCycles k (by subst hj; exact hk)

中文:
定义 liftCycles
  签名: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  定义体: (K.sc i).liftCycles k (by subst hj; exact hk)

Depends on / 依赖: K.sc, liftCycles
-/
noncomputable def liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  (K.sc i).liftCycles k (by subst hj; exact hk)

/--
Definition of `liftCycles'` / `liftCycles'` 的定义

English:
abbreviation liftCycles'
  signature: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
  body: K.liftCycles k j (c.next_eq' hj) hk

中文:
缩写 liftCycles'
  签名: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.关系 i j)
  定义体: K.liftCycles k j (c.next_eq' hj) hk

Depends on / 依赖: K.liftCycles, c.next_eq, liftCycles, next_eq
-/
noncomputable abbrev liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.cycles i :=
  K.liftCycles k j (c.next_eq' hj) hk

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `liftCycles_i` / 引理 `liftCycles_i`

English:
lemma liftCycles_i
  statement: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  proof: by
  dsimp [liftCycles, iCycles]
  simp

中文:
引理 liftCycles_i
  结论: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  证明: by
  dsimp [liftCycles, iCycles]
  simp

Depends on / 依赖: iCycles, liftCycles
-/
lemma liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k := by
  dsimp [liftCycles, iCycles]
  simp

variable (i)

/--
Definition of `toCycles` / `toCycles` 的定义

English:
definition toCycles
  signature: [K.HasHomology j]
  body: K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

@[reassoc (attr := simp)]

中文:
定义 toCycles
  签名: [K.有同调 j]
  定义体: K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

@[reassoc (attr := simp)]

Depends on / 依赖: K.d_comp_d, K.liftCycles, c.next, d_comp_d, liftCycles
-/
noncomputable def toCycles [K.HasHomology j] :
    K.X i ⟶ K.cycles j :=
  K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

@[reassoc (attr := simp)]
/--
lemma `iCycles_d` / 引理 `iCycles_d`

English:
lemma iCycles_d
  statement: K.iCycles i ≫ K.d i j = 0
  proof: by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  · rw [K.shape _ _ hij, comp_zero]

中文:
引理 iCycles_d
  结论: K.iCycles i ≫ K.d i j = 0
  证明: by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  · rw [K.shape _ _ hij, comp_zero]

Depends on / 依赖: K.sc, K.shape, c.Rel, c.next_eq, comp_zero, iCycles_g, next_eq
-/
lemma iCycles_d : K.iCycles i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  · rw [K.shape _ _ hij, comp_zero]

/--
Definition of `cyclesIsKernel` / `cyclesIsKernel` 的定义

English:
definition cyclesIsKernel
  signature: (hj : c.next i = j)
  body: by
  obtain rfl := hj
  exact (K.sc i).cyclesIsKernel

中文:
定义 cyclesIsKernel
  签名: (hj : c.next i = j)
  定义体: by
  obtain rfl := hj
  exact (K.sc i).cyclesIsKernel

Depends on / 依赖: K.sc, cyclesIsKernel
-/
noncomputable def cyclesIsKernel (hj : c.next i = j) :
    IsLimit (KernelFork.ofι (K.iCycles i) (K.iCycles_d i j)) := by
  obtain rfl := hj
  exact (K.sc i).cyclesIsKernel

end

@[reassoc (attr := simp)]
/--
lemma `toCycles_i` / 引理 `toCycles_i`

English:
lemma toCycles_i
  given: [K.HasHomology j]
  proof: liftCycles_i _ _ _ _ _

中文:
引理 toCycles_i
  条件: [K.有同调 j]
  证明: liftCycles_i _ _ _ _ _

Depends on / 依赖: liftCycles_i
-/
lemma toCycles_i [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

section
variable [K.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (K.iCycles i)
  body: by
  dsimp only [iCycles]
  infer_instance

中文:
实例 :
  签名: 单态射 (K.iCycles i)
  定义体: by
  dsimp only [iCycles]
  infer_instance

Depends on / 依赖: iCycles, infer_instance
-/
instance : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (K.homologyπ i)
  body: by
  dsimp only [homologyπ]
  infer_instance

中文:
实例 :
  签名: 满态射 (K.homologyπ i)
  定义体: by
  dsimp only [homologyπ]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

end

@[reassoc (attr := simp)]
/--
lemma `d_toCycles` / 引理 `d_toCycles`

English:
lemma d_toCycles
  given: [K.HasHomology k]
  proof: by
  simp only [← cancel_mono (K.iCycles k), assoc, toCycles_i, d_comp_d, zero_comp]

中文:
引理 d_toCycles
  条件: [K.有同调 k]
  证明: by
  simp only [← cancel_mono (K.iCycles k), assoc, toCycles_i, d_comp_d, zero_comp]

Depends on / 依赖: K.iCycles, cancel_mono, d_comp_d, iCycles, toCycles_i, zero_comp
-/
lemma d_toCycles [K.HasHomology k] :
    K.d i j ≫ K.toCycles j k = 0 := by
  simp only [← cancel_mono (K.iCycles k), assoc, toCycles_i, d_comp_d, zero_comp]

variable {i j} in
/--
lemma `toCycles_eq_zero` / 引理 `toCycles_eq_zero`

English:
lemma toCycles_eq_zero
  given: [K.HasHomology j] (hij : ¬ c.Rel i j)
  proof: by
  rw [← cancel_mono (K.iCycles j)]; rw [toCycles_i]; rw [zero_comp]; rw [K.shape _ _ hij]

中文:
引理 toCycles_eq_zero
  条件: [K.有同调 j] (hij : ¬ c.关系 i j)
  证明: by
  rw [← cancel_mono (K.iCycles j)]; rw [toCycles_i]; rw [zero_comp]; rw [K.shape _ _ hij]

Depends on / 依赖: K.iCycles, K.shape, cancel_mono, iCycles, toCycles_i, zero_comp
-/
lemma toCycles_eq_zero [K.HasHomology j] (hij : ¬ c.Rel i j) :
    K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j)]; rw [toCycles_i]; rw [zero_comp]; rw [K.shape _ _ hij]

variable {i}

section
variable [K.HasHomology i]

@[reassoc]
/--
lemma `comp_liftCycles` / 引理 `comp_liftCycles`

English:
lemma comp_liftCycles
  statement: {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  proof: by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

@[reassoc]

中文:
引理 comp_liftCycles
  结论: {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  证明: by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

@[reassoc]

Depends on / 依赖: K.iCycles, cancel_mono, iCycles, liftCycles_i
-/
lemma comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (α : A' ⟶ A) :
    α ≫ K.liftCycles k j hj hk = K.liftCycles (α ≫ k) j hj (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

@[reassoc]
/--
lemma `liftCycles_homologyπ_eq_zero_of_boundary` / 引理 `liftCycles_homologyπ_eq_zero_of_boundary`

English:
lemma liftCycles_homologyπ_eq_zero_of_boundary
  statement: {A : C} (k : A ⟶ K.X i) (j : ι)
  proof: by
  by_cases h : c.Rel i' i
  · obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  · have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h]; rw [comp_zero] at hx
      rw [← cancel_mono (K.iCycles i)]; rw [zero_comp]; rw [liftCycles_i]; rw [hx]
    rw [this]; rw [zero_comp]

中文:
引理 liftCycles_homologyπ_eq_zero_of_boundary
  结论: {A : C} (k : A ⟶ K.X i) (j : ι)
  证明: by
  by_cases h : c.Rel i' i
  · obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  · have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h]; rw [comp_zero] at hx
      rw [← cancel_mono (K.iCycles i)]; rw [zero_comp]; rw [liftCycles_i]; rw [hx]
    rw [this]; rw [zero_comp]

Depends on / 依赖: K.d_comp_d, K.iCycles, K.sc, K.shape, c.Rel, c.prev_eq, cancel_mono, comp_zero, d_comp_d, iCycles, liftCycles, liftCycles_i, prev_eq, zero_comp
-/
lemma liftCycles_homologyπ_eq_zero_of_boundary {A : C} (k : A ⟶ K.X i) (j : ι)
    (hj : c.next i = j) {i' : ι} (x : A ⟶ K.X i') (hx : k = x ≫ K.d i' i) :
    K.liftCycles k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) ≫ K.homologyπ i = 0 := by
  by_cases h : c.Rel i' i
  · obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  · have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h]; rw [comp_zero] at hx
      rw [← cancel_mono (K.iCycles i)]; rw [zero_comp]; rw [liftCycles_i]; rw [hx]
    rw [this]; rw [zero_comp]

end

variable (i)

@[reassoc (attr := simp)]
/--
lemma `toCycles_comp_homologyπ` / 引理 `toCycles_comp_homologyπ`

English:
lemma toCycles_comp_homologyπ
  given: [K.HasHomology j]
  proof: K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

中文:
引理 toCycles_comp_homologyπ
  条件: [K.有同调 j]
  证明: K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

Depends on / 依赖: K.liftCycles_homology, c.next
-/
lemma toCycles_comp_homologyπ [K.HasHomology j] :
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

/--
Definition of `homologyIsCokernel` / `homologyIsCokernel` 的定义

English:
definition homologyIsCokernel
  signature: (hi : c.prev j = i) [K.HasHomology j]
  body: by
  subst hi
  exact (K.sc j).homologyIsCokernel

中文:
定义 homologyIsCokernel
  签名: (hi : c.prev j = i) [K.有同调 j]
  定义体: by
  subst hi
  exact (K.sc j).homologyIsCokernel

Depends on / 依赖: K.sc, homologyIsCokernel
-/
noncomputable def homologyIsCokernel (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j)) := by
  subst hi
  exact (K.sc j).homologyIsCokernel

section
variable [K.HasHomology i]

/--
Definition of `opcycles` / `opcycles` 的定义

English:
definition opcycles
  body: (K.sc i).opcycles

中文:
定义 opcycles
  定义体: (K.sc i).opcycles

Depends on / 依赖: ComplexShape, ComplexShape.spectralSequenceFin_rel_iff, E.isZero_H_map_mk, Int.le.dest, K.sc, Nat.add_one_le_of_lt, Nat.le.dest, Prod.forall, add_one_le_of_lt, isIso_homOfLE, not_and, opcycles, spectralSequenceFin_rel_iff
-/
noncomputable def opcycles := (K.sc i).opcycles

/--
Definition of `pOpcycles` / `pOpcycles` 的定义

English:
definition pOpcycles
  signature: : K.X i ⟶ K.opcycles i
  body: (K.sc i).pOpcycles

中文:
定义 pOpcycles
  签名: : K.X i ⟶ K.opcycles i
  定义体: (K.sc i).pOpcycles

Depends on / 依赖: K.sc, pOpcycles
-/
noncomputable def pOpcycles : K.X i ⟶ K.opcycles i := (K.sc i).pOpcycles

/--
Definition of `homologyι` / `homologyι` 的定义

English:
definition homologyι
  signature: : K.homology i ⟶ K.opcycles i
  body: (K.sc i).homologyι

中文:
定义 homologyι
  签名: : K.homology i ⟶ K.opcycles i
  定义体: (K.sc i).homologyι

Depends on / 依赖: K.sc
-/
noncomputable def homologyι : K.homology i ⟶ K.opcycles i := (K.sc i).homologyι

variable {i}

/--
Definition of `descOpcycles` / `descOpcycles` 的定义

English:
definition descOpcycles
  signature: {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  body: (K.sc i).descOpcycles k (by subst hj; exact hk)

中文:
定义 descOpcycles
  签名: {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  定义体: (K.sc i).descOpcycles k (by subst hj; exact hk)

Depends on / 依赖: K.sc, descOpcycles
-/
noncomputable def descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  (K.sc i).descOpcycles k (by subst hj; exact hk)

/--
Definition of `descOpcycles'` / `descOpcycles'` 的定义

English:
abbreviation descOpcycles'
  signature: {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
  body: K.descOpcycles k j (c.prev_eq' hj) hk

中文:
缩写 descOpcycles'
  签名: {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.关系 j i)
  定义体: K.descOpcycles k j (c.prev_eq' hj) hk

Depends on / 依赖: K.descOpcycles, c.prev_eq, descOpcycles, prev_eq
-/
noncomputable abbrev descOpcycles' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
    (hk : K.d j i ≫ k = 0) : K.opcycles i ⟶ A :=
  K.descOpcycles k j (c.prev_eq' hj) hk

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `p_descOpcycles` / 引理 `p_descOpcycles`

English:
lemma p_descOpcycles
  statement: {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  proof: by
  dsimp [descOpcycles, pOpcycles]
  simp

中文:
引理 p_descOpcycles
  结论: {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  证明: by
  dsimp [descOpcycles, pOpcycles]
  simp

Depends on / 依赖: descOpcycles, pOpcycles
-/
lemma p_descOpcycles {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pOpcycles i ≫ K.descOpcycles k j hj hk = k := by
  dsimp [descOpcycles, pOpcycles]
  simp

variable (i)

/--
Definition of `fromOpcycles` / `fromOpcycles` 的定义

English:
definition fromOpcycles
  signature: : K.opcycles i ⟶ K.X j
  body: K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

omit [K.HasHomology i] in
@[reassoc (attr := simp)]

中文:
定义 fromOpcycles
  签名: : K.opcycles i ⟶ K.X j
  定义体: K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

omit [K.HasHomology i] in
@[reassoc (attr := simp)]

Depends on / 依赖: K.d_comp_d, K.descOpcycles, c.prev, d_comp_d, descOpcycles
-/
noncomputable def fromOpcycles : K.opcycles i ⟶ K.X j :=
  K.descOpcycles (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

omit [K.HasHomology i] in
@[reassoc (attr := simp)]
/--
lemma `d_pOpcycles` / 引理 `d_pOpcycles`

English:
lemma d_pOpcycles
  given: [K.HasHomology j]
  statement: K.d i j ≫ K.pOpcycles j = 0
  proof: by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (K.sc j).f_pOpcycles
  · rw [K.shape _ _ hij, zero_comp]

中文:
引理 d_pOpcycles
  条件: [K.有同调 j]
  结论: K.d i j ≫ K.pOpcycles j = 0
  证明: by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (K.sc j).f_pOpcycles
  · rw [K.shape _ _ hij, zero_comp]

Depends on / 依赖: K.sc, K.shape, c.Rel, c.prev_eq, f_pOpcycles, prev_eq, zero_comp
-/
lemma d_pOpcycles [K.HasHomology j] : K.d i j ≫ K.pOpcycles j = 0 := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.prev_eq' hij
    exact (K.sc j).f_pOpcycles
  · rw [K.shape _ _ hij, zero_comp]

/--
Definition of `opcyclesIsCokernel` / `opcyclesIsCokernel` 的定义

English:
definition opcyclesIsCokernel
  signature: (hi : c.prev j = i) [K.HasHomology j]
  body: by
  obtain rfl := hi
  exact (K.sc j).opcyclesIsCokernel

@[reassoc (attr := simp)]

中文:
定义 opcyclesIsCokernel
  签名: (hi : c.prev j = i) [K.有同调 j]
  定义体: by
  obtain rfl := hi
  exact (K.sc j).opcyclesIsCokernel

@[reassoc (attr := simp)]

Depends on / 依赖: K.sc, X.map, opcyclesIsCokernel
-/
noncomputable def opcyclesIsCokernel (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.pOpcycles j) (K.d_pOpcycles i j)) := by
  obtain rfl := hi
  exact (K.sc j).opcyclesIsCokernel

@[reassoc (attr := simp)]
/--
lemma `p_fromOpcycles` / 引理 `p_fromOpcycles`

English:
lemma p_fromOpcycles
  proof: p_descOpcycles _ _ _ _ _

中文:
引理 p_fromOpcycles
  证明: p_descOpcycles _ _ _ _ _

Depends on / 依赖: p_descOpcycles
-/
lemma p_fromOpcycles :
    K.pOpcycles i ≫ K.fromOpcycles i j = K.d i j :=
  p_descOpcycles _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (K.pOpcycles i)
  body: by
  dsimp only [pOpcycles]
  infer_instance

中文:
实例 :
  签名: 满态射 (K.pOpcycles i)
  定义体: by
  dsimp only [pOpcycles]
  infer_instance

Depends on / 依赖: infer_instance, pOpcycles
-/
instance : Epi (K.pOpcycles i) := by
  dsimp only [pOpcycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (K.homologyι i)
  body: by
  dsimp only [homologyι]
  infer_instance

@[reassoc (attr := simp)]

中文:
实例 :
  签名: 单态射 (K.homologyι i)
  定义体: by
  dsimp only [homologyι]
  infer_instance

@[reassoc (attr := simp)]

Depends on / 依赖: X.map, infer_instance
-/
instance : Mono (K.homologyι i) := by
  dsimp only [homologyι]
  infer_instance

@[reassoc (attr := simp)]
/--
lemma `fromOpcycles_d` / 引理 `fromOpcycles_d`

English:
lemma fromOpcycles_d
  proof: by
  simp only [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_comp_d, comp_zero]

中文:
引理 fromOpcycles_d
  证明: by
  simp only [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_comp_d, comp_zero]

Depends on / 依赖: K.pOpcycles, cancel_epi, comp_zero, d_comp_d, pOpcycles, p_fromOpcycles_assoc
-/
lemma fromOpcycles_d :
    K.fromOpcycles i j ≫ K.d j k = 0 := by
  simp only [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_comp_d, comp_zero]

variable {i j} in
/--
lemma `fromOpcycles_eq_zero` / 引理 `fromOpcycles_eq_zero`

English:
lemma fromOpcycles_eq_zero
  given: (hij : ¬ c.Rel i j)
  proof: by
  rw [← cancel_epi (K.pOpcycles i)]; rw [p_fromOpcycles]; rw [comp_zero]; rw [K.shape _ _ hij]

中文:
引理 fromOpcycles_eq_zero
  条件: (hij : ¬ c.关系 i j)
  证明: by
  rw [← cancel_epi (K.pOpcycles i)]; rw [p_fromOpcycles]; rw [comp_zero]; rw [K.shape _ _ hij]

Depends on / 依赖: K.pOpcycles, K.shape, cancel_epi, comp_zero, pOpcycles, p_fromOpcycles
-/
lemma fromOpcycles_eq_zero (hij : ¬ c.Rel i j) :
    K.fromOpcycles i j = 0 := by
  rw [← cancel_epi (K.pOpcycles i)]; rw [p_fromOpcycles]; rw [comp_zero]; rw [K.shape _ _ hij]

variable {i}

@[reassoc]
/--
lemma `descOpcycles_comp` / 引理 `descOpcycles_comp`

English:
lemma descOpcycles_comp
  statement: {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  proof: by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, p_descOpcycles]

@[reassoc]

中文:
引理 descOpcycles_comp
  结论: {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  证明: by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, p_descOpcycles]

@[reassoc]

Depends on / 依赖: K.pOpcycles, cancel_epi, pOpcycles, p_descOpcycles, p_descOpcycles_assoc
-/
lemma descOpcycles_comp {A A' : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) (α : A ⟶ A') :
    K.descOpcycles k j hj hk ≫ α = K.descOpcycles (k ≫ α) j hj
      (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_descOpcycles_assoc, p_descOpcycles]

@[reassoc]
/--
lemma `homologyι_descOpcycles_eq_zero_of_boundary` / 引理 `homologyι_descOpcycles_eq_zero_of_boundary`

English:
lemma homologyι_descOpcycles_eq_zero_of_boundary
  statement: {A : C} (k : K.X i ⟶ A) (j : ι)
  proof: by
  by_cases h : c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h]; rw [zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i)]; rw [comp_zero]; rw [p_descOpcycles]; rw [hx]
    rw [this]; rw [comp_zero]

中文:
引理 homologyι_descOpcycles_eq_zero_of_boundary
  结论: {A : C} (k : K.X i ⟶ A) (j : ι)
  证明: by
  by_cases h : c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h]; rw [zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i)]; rw [comp_zero]; rw [p_descOpcycles]; rw [hx]
    rw [this]; rw [comp_zero]

Depends on / 依赖: K.d_comp_d_assoc, K.descOpcycles, K.pOpcycles, K.sc, K.shape, c.Rel, c.next_eq, cancel_epi, comp_zero, d_comp_d_assoc, descOpcycles, next_eq, pOpcycles, p_descOpcycles, zero_comp
-/
lemma homologyι_descOpcycles_eq_zero_of_boundary {A : C} (k : K.X i ⟶ A) (j : ι)
    (hj : c.prev i = j) {i' : ι} (x : K.X i' ⟶ A) (hx : k = K.d i i' ≫ x) :
    K.homologyι i ≫ K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
  by_cases h : c.Rel i i'
  · obtain rfl := c.next_eq' h
    exact (K.sc i).homologyι_descOpcycles_eq_zero_of_boundary _ x hx
  · have : K.descOpcycles k j hj (by rw [hx, K.d_comp_d_assoc, zero_comp]) = 0 := by
      rw [K.shape _ _ h]; rw [zero_comp] at hx
      rw [← cancel_epi (K.pOpcycles i)]; rw [comp_zero]; rw [p_descOpcycles]; rw [hx]
    rw [this]; rw [comp_zero]

variable (i)

@[reassoc (attr := simp)]
/--
lemma `homologyι_comp_fromOpcycles` / 引理 `homologyι_comp_fromOpcycles`

English:
lemma homologyι_comp_fromOpcycles
  proof: K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

中文:
引理 homologyι_comp_fromOpcycles
  证明: K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

Depends on / 依赖: K.homology
-/
lemma homologyι_comp_fromOpcycles :
    K.homologyι i ≫ K.fromOpcycles i j = 0 :=
  K.homologyι_descOpcycles_eq_zero_of_boundary (K.d i j) _ rfl (𝟙 _) (by simp)

/--
Definition of `homologyIsKernel` / `homologyIsKernel` 的定义

English:
definition homologyIsKernel
  signature: (hi : c.next i = j)
  body: by
  subst hi
  exact (K.sc i).homologyIsKernel

中文:
定义 homologyIsKernel
  签名: (hi : c.next i = j)
  定义体: by
  subst hi
  exact (K.sc i).homologyIsKernel

Depends on / 依赖: K.sc, homologyIsKernel
-/
noncomputable def homologyIsKernel (hi : c.next i = j) :
    IsLimit (KernelFork.ofι (K.homologyι i) (K.homologyι_comp_fromOpcycles i j)) := by
  subst hi
  exact (K.sc i).homologyIsKernel

variable {K L M}
variable [L.HasHomology i] [M.HasHomology i]

/--
Definition of `homologyMap` / `homologyMap` 的定义

English:
definition homologyMap
  signature: : K.homology i ⟶ L.homology i
  body: ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

中文:
定义 homologyMap
  签名: : K.homology i ⟶ L.homology i
  定义体: ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap, homologyMap, shortComplexFunctor
-/
noncomputable def homologyMap : K.homology i ⟶ L.homology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

/--
Definition of `cyclesMap` / `cyclesMap` 的定义

English:
definition cyclesMap
  signature: : K.cycles i ⟶ L.cycles i
  body: ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

中文:
定义 cyclesMap
  签名: : K.cycles i ⟶ L.cycles i
  定义体: ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap, cyclesMap, shortComplexFunctor
-/
noncomputable def cyclesMap : K.cycles i ⟶ L.cycles i :=
  ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

/--
Definition of `opcyclesMap` / `opcyclesMap` 的定义

English:
definition opcyclesMap
  signature: : K.opcycles i ⟶ L.opcycles i
  body: ShortComplex.opcyclesMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]

中文:
定义 opcyclesMap
  签名: : K.opcycles i ⟶ L.opcycles i
  定义体: ShortComplex.opcyclesMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]

Depends on / 依赖: ShortComplex, ShortComplex.opcyclesMap, opcyclesMap, shortComplexFunctor
-/
noncomputable def opcyclesMap : K.opcycles i ⟶ L.opcycles i :=
  ShortComplex.opcyclesMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]
/--
lemma `cyclesMap_i` / 引理 `cyclesMap_i`

English:
lemma cyclesMap_i
  statement: cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i
  proof: ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]

中文:
引理 cyclesMap_i
  结论: cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i
  证明: ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap_i, cyclesMap_i
-/
lemma cyclesMap_i : cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i :=
  ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]
/--
lemma `p_opcyclesMap` / 引理 `p_opcyclesMap`

English:
lemma p_opcyclesMap
  statement: K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i
  proof: ShortComplex.p_opcyclesMap _

中文:
引理 p_opcyclesMap
  结论: K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i
  证明: ShortComplex.p_opcyclesMap _

Depends on / 依赖: ShortComplex, ShortComplex.p_opcyclesMap, p_opcyclesMap
-/
lemma p_opcyclesMap : K.pOpcycles i ≫ opcyclesMap φ i = φ.f i ≫ L.pOpcycles i :=
  ShortComplex.p_opcyclesMap _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: (φ.f i)] : Mono (cyclesMap φ i)
  body: mono_of_mono_fac (cyclesMap_i φ i)

中文:
实例 [单态射
  签名: (φ.f i)] : 单态射 (cyclesMap φ i)
  定义体: mono_of_mono_fac (cyclesMap_i φ i)

Depends on / 依赖: cyclesMap_i, mono_of_mono_fac
-/
instance [Mono (φ.f i)] : Mono (cyclesMap φ i) := mono_of_mono_fac (cyclesMap_i φ i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Epi
  signature: (φ.f i)] : Epi (opcyclesMap φ i)
  body: epi_of_epi_fac (p_opcyclesMap φ i)

中文:
实例 [满态射
  签名: (φ.f i)] : 满态射 (opcyclesMap φ i)
  定义体: epi_of_epi_fac (p_opcyclesMap φ i)

Depends on / 依赖: epi_of_epi_fac, p_opcyclesMap
-/
instance [Epi (φ.f i)] : Epi (opcyclesMap φ i) := epi_of_epi_fac (p_opcyclesMap φ i)

variable (K)

@[simp]
/--
lemma `homologyMap_id` / 引理 `homologyMap_id`

English:
lemma homologyMap_id
  statement: homologyMap (𝟙 K) i = 𝟙 _
  proof: ShortComplex.homologyMap_id _

@[simp]

中文:
引理 homologyMap_id
  结论: homologyMap (𝟙 K) i = 𝟙 _
  证明: ShortComplex.homologyMap_id _

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_id, homologyMap_id
-/
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

@[simp]
/--
lemma `cyclesMap_id` / 引理 `cyclesMap_id`

English:
lemma cyclesMap_id
  statement: cyclesMap (𝟙 K) i = 𝟙 _
  proof: ShortComplex.cyclesMap_id _

@[simp]

中文:
引理 cyclesMap_id
  结论: cyclesMap (𝟙 K) i = 𝟙 _
  证明: ShortComplex.cyclesMap_id _

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap_id, cyclesMap_id
-/
lemma cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.cyclesMap_id _

@[simp]
/--
lemma `opcyclesMap_id` / 引理 `opcyclesMap_id`

English:
lemma opcyclesMap_id
  statement: opcyclesMap (𝟙 K) i = 𝟙 _
  proof: ShortComplex.opcyclesMap_id _

中文:
引理 opcyclesMap_id
  结论: opcyclesMap (𝟙 K) i = 𝟙 _
  证明: ShortComplex.opcyclesMap_id _

Depends on / 依赖: ShortComplex, ShortComplex.opcyclesMap_id, opcyclesMap_id
-/
lemma opcyclesMap_id : opcyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.opcyclesMap_id _

variable {K}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homologyMap_comp` / 引理 `homologyMap_comp`

English:
lemma homologyMap_comp
  statement: homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i
  proof: by
  dsimp [homologyMap]
  rw [Functor.map_comp]; rw [ShortComplex.homologyMap_comp]

中文:
引理 homologyMap_comp
  结论: homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i
  证明: by
  dsimp [homologyMap]
  rw [Functor.map_comp]; rw [ShortComplex.homologyMap_comp]

Depends on / 依赖: Functor, Functor.map_comp, ShortComplex, ShortComplex.homologyMap_comp, homologyMap, homologyMap_comp, map_comp
-/
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp]; rw [ShortComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `cyclesMap_comp` / 引理 `cyclesMap_comp`

English:
lemma cyclesMap_comp
  statement: cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i
  proof: by
  dsimp [cyclesMap]
  rw [Functor.map_comp]; rw [ShortComplex.cyclesMap_comp]

中文:
引理 cyclesMap_comp
  结论: cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i
  证明: by
  dsimp [cyclesMap]
  rw [Functor.map_comp]; rw [ShortComplex.cyclesMap_comp]

Depends on / 依赖: Functor, Functor.map_comp, ShortComplex, ShortComplex.cyclesMap_comp, cyclesMap, cyclesMap_comp, map_comp
-/
lemma cyclesMap_comp : cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i := by
  dsimp [cyclesMap]
  rw [Functor.map_comp]; rw [ShortComplex.cyclesMap_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `opcyclesMap_comp` / 引理 `opcyclesMap_comp`

English:
lemma opcyclesMap_comp
  statement: opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i
  proof: by
  dsimp [opcyclesMap]
  rw [Functor.map_comp]; rw [ShortComplex.opcyclesMap_comp]

中文:
引理 opcyclesMap_comp
  结论: opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i
  证明: by
  dsimp [opcyclesMap]
  rw [Functor.map_comp]; rw [ShortComplex.opcyclesMap_comp]

Depends on / 依赖: Functor, Functor.map_comp, ShortComplex, ShortComplex.opcyclesMap_comp, map_comp, opcyclesMap, opcyclesMap_comp
-/
lemma opcyclesMap_comp : opcyclesMap (φ ≫ ψ) i = opcyclesMap φ i ≫ opcyclesMap ψ i := by
  dsimp [opcyclesMap]
  rw [Functor.map_comp]; rw [ShortComplex.opcyclesMap_comp]

variable (K L)

@[simp]
/--
lemma `homologyMap_zero` / 引理 `homologyMap_zero`

English:
lemma homologyMap_zero
  statement: homologyMap (0 : K ⟶ L) i = 0
  proof: ShortComplex.homologyMap_zero _ _

@[simp]

中文:
引理 homologyMap_zero
  结论: homologyMap (0 : K ⟶ L) i = 0
  证明: ShortComplex.homologyMap_zero _ _

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_zero, homologyMap_zero
-/
lemma homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.homologyMap_zero _ _

@[simp]
/--
lemma `cyclesMap_zero` / 引理 `cyclesMap_zero`

English:
lemma cyclesMap_zero
  statement: cyclesMap (0 : K ⟶ L) i = 0
  proof: ShortComplex.cyclesMap_zero _ _

@[simp]

中文:
引理 cyclesMap_zero
  结论: cyclesMap (0 : K ⟶ L) i = 0
  证明: ShortComplex.cyclesMap_zero _ _

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap_zero, cyclesMap_zero
-/
lemma cyclesMap_zero : cyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.cyclesMap_zero _ _

@[simp]
/--
lemma `opcyclesMap_zero` / 引理 `opcyclesMap_zero`

English:
lemma opcyclesMap_zero
  statement: opcyclesMap (0 : K ⟶ L) i = 0
  proof: ShortComplex.opcyclesMap_zero _ _

中文:
引理 opcyclesMap_zero
  结论: opcyclesMap (0 : K ⟶ L) i = 0
  证明: ShortComplex.opcyclesMap_zero _ _

Depends on / 依赖: ShortComplex, ShortComplex.opcyclesMap_zero, opcyclesMap_zero
-/
lemma opcyclesMap_zero : opcyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.opcyclesMap_zero _ _

variable {K L}

@[reassoc (attr := simp)]
/--
lemma `homologyπ_naturality` / 引理 `homologyπ_naturality`

English:
lemma homologyπ_naturality
  proof: ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]

中文:
引理 homologyπ_naturality
  证明: ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]

Depends on / 依赖: ShortComplex, ShortComplex.homology
-/
lemma homologyπ_naturality :
    K.homologyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i :=
  ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]
/--
lemma `homologyι_naturality` / 引理 `homologyι_naturality`

English:
lemma homologyι_naturality
  proof: ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]

中文:
引理 homologyι_naturality
  证明: ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]

Depends on / 依赖: ShortComplex, ShortComplex.homology
-/
lemma homologyι_naturality :
    homologyMap φ i ≫ L.homologyι i = K.homologyι i ≫ opcyclesMap φ i :=
  ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]
/--
lemma `homology_π_ι` / 引理 `homology_π_ι`

English:
lemma homology_π_ι
  proof: (K.sc i).homology_π_ι

中文:
引理 homology_π_ι
  证明: (K.sc i).homology_π_ι

Depends on / 依赖: K.sc
-/
lemma homology_π_ι :
    K.homologyπ i ≫ K.homologyι i = K.iCycles i ≫ K.pOpcycles i :=
  (K.sc i).homology_π_ι

/-- The isomorphism `K.homology i ≅ L.homology i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
/--
Definition of `homologyMapIso` / `homologyMapIso` 的定义

English:
definition homologyMapIso
  signature: : K.homology i ≅ L.homology i where
  body: homologyMap iso.hom i
  inv := homologyMap iso.inv i
  hom_inv_id := by simp [← homologyMap_comp]
  inv_hom_id := by simp [← homologyMap_comp]

中文:
定义 homologyMapIso
  签名: : K.homology i ≅ L.homology i where
  定义体: homologyMap iso.hom i
  inv := homologyMap iso.inv i
  hom_inv_id := by simp [← homologyMap_comp]
  inv_hom_id := by simp [← homologyMap_comp]

Depends on / 依赖: homologyMap, iso.hom
-/
noncomputable def homologyMapIso : K.homology i ≅ L.homology i where
  hom := homologyMap iso.hom i
  inv := homologyMap iso.inv i
  hom_inv_id := by simp [← homologyMap_comp]
  inv_hom_id := by simp [← homologyMap_comp]

/-- The isomorphism `K.cycles i ≅ L.cycles i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
/--
Definition of `cyclesMapIso` / `cyclesMapIso` 的定义

English:
definition cyclesMapIso
  signature: : K.cycles i ≅ L.cycles i where
  body: cyclesMap iso.hom i
  inv := cyclesMap iso.inv i
  hom_inv_id := by simp [← cyclesMap_comp]
  inv_hom_id := by simp [← cyclesMap_comp]

中文:
定义 cyclesMapIso
  签名: : K.cycles i ≅ L.cycles i where
  定义体: cyclesMap iso.hom i
  inv := cyclesMap iso.inv i
  hom_inv_id := by simp [← cyclesMap_comp]
  inv_hom_id := by simp [← cyclesMap_comp]

Depends on / 依赖: cyclesMap, iso.hom
-/
noncomputable def cyclesMapIso : K.cycles i ≅ L.cycles i where
  hom := cyclesMap iso.hom i
  inv := cyclesMap iso.inv i
  hom_inv_id := by simp [← cyclesMap_comp]
  inv_hom_id := by simp [← cyclesMap_comp]

/-- The isomorphism `K.opcycles i ≅ L.opcycles i` induced by an isomorphism
in `HomologicalComplex`. -/
@[simps]
/--
Definition of `opcyclesMapIso` / `opcyclesMapIso` 的定义

English:
definition opcyclesMapIso
  signature: : K.opcycles i ≅ L.opcycles i where
  body: opcyclesMap iso.hom i
  inv := opcyclesMap iso.inv i
  hom_inv_id := by simp [← opcyclesMap_comp]
  inv_hom_id := by simp [← opcyclesMap_comp]

中文:
定义 opcyclesMapIso
  签名: : K.opcycles i ≅ L.opcycles i where
  定义体: opcyclesMap iso.hom i
  inv := opcyclesMap iso.inv i
  hom_inv_id := by simp [← opcyclesMap_comp]
  inv_hom_id := by simp [← opcyclesMap_comp]

Depends on / 依赖: iso.hom, opcyclesMap
-/
noncomputable def opcyclesMapIso : K.opcycles i ≅ L.opcycles i where
  hom := opcyclesMap iso.hom i
  inv := opcyclesMap iso.inv i
  hom_inv_id := by simp [← opcyclesMap_comp]
  inv_hom_id := by simp [← opcyclesMap_comp]

variable {i}

@[reassoc (attr := simp)]
/--
lemma `opcyclesMap_comp_descOpcycles` / 引理 `opcyclesMap_comp_descOpcycles`

English:
lemma opcyclesMap_comp_descOpcycles
  statement: {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  proof: by
  simp only [← cancel_epi (K.pOpcycles i), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]

中文:
引理 opcyclesMap_comp_descOpcycles
  结论: {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
  证明: by
  simp only [← cancel_epi (K.pOpcycles i), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]

Depends on / 依赖: K.pOpcycles, cancel_epi, pOpcycles, p_descOpcycles, p_opcyclesMap_assoc
-/
lemma opcyclesMap_comp_descOpcycles {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : L.d j i ≫ k = 0) (φ : K ⟶ L) :
    opcyclesMap φ i ≫ L.descOpcycles k j hj hk = K.descOpcycles (φ.f i ≫ k) j hj
      (by rw [← φ.comm_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (K.pOpcycles i), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]
/--
lemma `liftCycles_comp_cyclesMap` / 引理 `liftCycles_comp_cyclesMap`

English:
lemma liftCycles_comp_cyclesMap
  statement: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  proof: by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

中文:
引理 liftCycles_comp_cyclesMap
  结论: {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
  证明: by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

Depends on / 依赖: L.iCycles, cancel_mono, cyclesMap_i, iCycles, infer_instance, liftCycles_i, liftCycles_i_assoc
-/
lemma liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) :
    K.liftCycles k j hj hk ≫ cyclesMap φ i = L.liftCycles (k ≫ φ.f i) j hj
      (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

section

variable (C c i)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

/-- The `i`th homology functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: [CategoryWithHomology C]
  body: K.homology i
  map f := homologyMap f i

中文:
定义 homologyFunctor
  签名: [带同调范畴 C]
  定义体: K.homology i
  map f := homologyMap f i

Depends on / 依赖: K.homology, homology
-/
noncomputable def homologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.homology i
  map f := homologyMap f i

/-- The homology functor to graded objects. -/
@[simps]
/--
Definition of `gradedHomologyFunctor` / `gradedHomologyFunctor` 的定义

English:
definition gradedHomologyFunctor
  signature: [CategoryWithHomology C]
  body: K.homology i
  map f i := homologyMap f i

中文:
定义 gradedHomologyFunctor
  签名: [带同调范畴 C]
  定义体: K.homology i
  map f i := homologyMap f i

Depends on / 依赖: K.homology, homology
-/
noncomputable def gradedHomologyFunctor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ GradedObject ι C where
  obj K i := K.homology i
  map f i := homologyMap f i

/-- The `i`th cycles functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
/--
Definition of `cyclesFunctor` / `cyclesFunctor` 的定义

English:
definition cyclesFunctor
  signature: [CategoryWithHomology C]
  body: K.cycles i
  map f := cyclesMap f i

中文:
定义 cyclesFunctor
  签名: [带同调范畴 C]
  定义体: K.cycles i
  map f := cyclesMap f i

Depends on / 依赖: K.cycles, cycles
-/
noncomputable def cyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.cycles i
  map f := cyclesMap f i

/-- The `i`th opcycles functor `HomologicalComplex C c ⥤ C`. -/
@[simps]
/--
Definition of `opcyclesFunctor` / `opcyclesFunctor` 的定义

English:
definition opcyclesFunctor
  signature: [CategoryWithHomology C]
  body: K.opcycles i
  map f := opcyclesMap f i

中文:
定义 opcyclesFunctor
  签名: [带同调范畴 C]
  定义体: K.opcycles i
  map f := opcyclesMap f i

Depends on / 依赖: K.opcycles, opcycles
-/
noncomputable def opcyclesFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.opcycles i
  map f := opcyclesMap f i

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.homologyπ i : K.cycles i ⟶ K.homology i`
for all `K : HomologicalComplex C c`. -/
@[simps]
/--
Definition of `natTransHomologyπ` / `natTransHomologyπ` 的定义

English:
definition natTransHomologyπ
  signature: [CategoryWithHomology C]
  body: K.homologyπ i

中文:
定义 natTransHomologyπ
  签名: [带同调范畴 C]
  定义体: K.homologyπ i

Depends on / 依赖: K.homology
-/
noncomputable def natTransHomologyπ [CategoryWithHomology C] :
    cyclesFunctor C c i ⟶ homologyFunctor C c i where
  app K := K.homologyπ i

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.homologyι i : K.homology i ⟶ K.opcycles i`
for all `K : HomologicalComplex C c`. -/
@[simps]
/--
Definition of `natTransHomologyι` / `natTransHomologyι` 的定义

English:
definition natTransHomologyι
  signature: [CategoryWithHomology C]
  body: K.homologyι i

中文:
定义 natTransHomologyι
  签名: [带同调范畴 C]
  定义体: K.homologyι i

Depends on / 依赖: K.homology
-/
noncomputable def natTransHomologyι [CategoryWithHomology C] :
    homologyFunctor C c i ⟶ opcyclesFunctor C c i where
  app K := K.homologyι i

/-- The natural isomorphism `K.homology i ≅ (K.sc i).homology`
for all homological complexes `K`. -/
@[simps!]
/--
Definition of `homologyFunctorIso` / `homologyFunctorIso` 的定义

English:
definition homologyFunctorIso
  signature: [CategoryWithHomology C]
  body: Iso.refl _

中文:
定义 homologyFunctorIso
  签名: [带同调范畴 C]
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def homologyFunctorIso [CategoryWithHomology C] :
    homologyFunctor C c i ≅
      shortComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C :=
  Iso.refl _

/--
Definition of `homologyFunctorIso'` / `homologyFunctorIso'` 的定义

English:
definition homologyFunctorIso'
  signature: [CategoryWithHomology C]
  body: homologyFunctorIso C c j ≪≫ Functor.isoWhiskerRight (natIsoSc' C c i j k hi hk) _

中文:
定义 homologyFunctorIso'
  签名: [带同调范畴 C]
  定义体: homologyFunctorIso C c j ≪≫ Functor.isoWhiskerRight (natIsoSc' C c i j k hi hk) _

Depends on / 依赖: Functor, Functor.isoWhiskerRight, homologyFunctorIso, isoWhiskerRight, natIsoSc
-/
noncomputable def homologyFunctorIso' [CategoryWithHomology C]
    (hi : c.prev j = i) (hk : c.next j = k) :
    homologyFunctor C c j ≅
      shortComplexFunctor' C c i j k ⋙ ShortComplex.homologyFunctor C :=
  homologyFunctorIso C c j ≪≫ Functor.isoWhiskerRight (natIsoSc' C c i j k hi hk) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : (homologyFunctor C c i).PreservesZeroMorphisms where

中文:
实例 [带同调范畴
  签名: C] : (homologyFunctor C c i).保持ZeroMorphisms where
-/
instance [CategoryWithHomology C] : (homologyFunctor C c i).PreservesZeroMorphisms where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : (opcyclesFunctor C c i).PreservesZeroMorphisms where

中文:
实例 [带同调范畴
  签名: C] : (opcyclesFunctor C c i).保持ZeroMorphisms where
-/
instance [CategoryWithHomology C] : (opcyclesFunctor C c i).PreservesZeroMorphisms where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : (cyclesFunctor C c i).PreservesZeroMorphisms where

中文:
实例 [带同调范畴
  签名: C] : (cyclesFunctor C c i).保持ZeroMorphisms where
-/
instance [CategoryWithHomology C] : (cyclesFunctor C c i).PreservesZeroMorphisms where

end

end

section

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]
include hj h

/--
lemma `isIso_iCycles` / 引理 `isIso_iCycles`

English:
lemma isIso_iCycles
  statement: IsIso (K.iCycles i)
  proof: by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

中文:
引理 isIso_iCycles
  结论: 是同构 (K.iCycles i)
  证明: by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

Depends on / 依赖: ShortComplex, ShortComplex.isIso_iCycles, isIso_iCycles
-/
lemma isIso_iCycles : IsIso (K.iCycles i) := by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

/-- The canonical isomorphism `K.cycles i ≅ K.X i` when the differential from `i` is zero. -/
@[simps! hom]
/--
Definition of `iCyclesIso` / `iCyclesIso` 的定义

English:
definition iCyclesIso
  signature: : K.cycles i ≅ K.X i
  body: have := K.isIso_iCycles i j hj h
  asIso (K.iCycles i)

@[reassoc (attr := simp)]

中文:
定义 iCyclesIso
  签名: : K.cycles i ≅ K.X i
  定义体: have := K.isIso_iCycles i j hj h
  asIso (K.iCycles i)

@[reassoc (attr := simp)]

Depends on / 依赖: K.iCycles, K.isIso_iCycles, iCycles, infer_instance, isIso_iCycles
-/
noncomputable def iCyclesIso : K.cycles i ≅ K.X i :=
  have := K.isIso_iCycles i j hj h
  asIso (K.iCycles i)

@[reassoc (attr := simp)]
/--
lemma `iCyclesIso_hom_inv_id` / 引理 `iCyclesIso_hom_inv_id`

English:
lemma iCyclesIso_hom_inv_id
  proof: (K.iCyclesIso i j hj h).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 iCyclesIso_hom_inv_id
  证明: (K.iCyclesIso i j hj h).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: K.iCyclesIso, hom_inv_id, iCyclesIso
-/
lemma iCyclesIso_hom_inv_id :
    K.iCycles i ≫ (K.iCyclesIso i j hj h).inv = 𝟙 _ :=
  (K.iCyclesIso i j hj h).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `iCyclesIso_inv_hom_id` / 引理 `iCyclesIso_inv_hom_id`

English:
lemma iCyclesIso_inv_hom_id
  proof: (K.iCyclesIso i j hj h).inv_hom_id

中文:
引理 iCyclesIso_inv_hom_id
  证明: (K.iCyclesIso i j hj h).inv_hom_id

Depends on / 依赖: K.iCyclesIso, iCyclesIso, infer_instance, inv_hom_id
-/
lemma iCyclesIso_inv_hom_id :
    (K.iCyclesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _ :=
  (K.iCyclesIso i j hj h).inv_hom_id

/--
lemma `isIso_homologyι` / 引理 `isIso_homologyι`

English:
lemma isIso_homologyι
  statement: IsIso (K.homologyι i)
  proof: ShortComplex.isIso_homologyι _ (by cat_disch)

中文:
引理 isIso_homologyι
  结论: 是同构 (K.homologyι i)
  证明: ShortComplex.isIso_homologyι _ (by cat_disch)

Depends on / 依赖: ShortComplex, ShortComplex.isIso_homology, cat_disch
-/
lemma isIso_homologyι : IsIso (K.homologyι i) :=
  ShortComplex.isIso_homologyι _ (by cat_disch)

/-- The canonical isomorphism `K.homology i ≅ K.opcycles i`
when the differential from `i` is zero. -/
@[simps! hom]
/--
Definition of `isoHomologyι` / `isoHomologyι` 的定义

English:
definition isoHomologyι
  signature: : K.homology i ≅ K.opcycles i
  body: have := K.isIso_homologyι i j hj h
  asIso (K.homologyι i)

@[reassoc (attr := simp)]

中文:
定义 isoHomologyι
  签名: : K.homology i ≅ K.opcycles i
  定义体: have := K.isIso_homologyι i j hj h
  asIso (K.homologyι i)

@[reassoc (attr := simp)]

Depends on / 依赖: K.homology, K.isIso_homology
-/
noncomputable def isoHomologyι : K.homology i ≅ K.opcycles i :=
  have := K.isIso_homologyι i j hj h
  asIso (K.homologyι i)

@[reassoc (attr := simp)]
/--
lemma `isoHomologyι_hom_inv_id` / 引理 `isoHomologyι_hom_inv_id`

English:
lemma isoHomologyι_hom_inv_id
  proof: (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoHomologyι_hom_inv_id
  证明: (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: K.isoHomology, hom_inv_id
-/
lemma isoHomologyι_hom_inv_id :
    K.homologyι i ≫ (K.isoHomologyι i j hj h).inv = 𝟙 _ :=
  (K.isoHomologyι i j hj h).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoHomologyι_inv_hom_id` / 引理 `isoHomologyι_inv_hom_id`

English:
lemma isoHomologyι_inv_hom_id
  proof: (K.isoHomologyι i j hj h).inv_hom_id

中文:
引理 isoHomologyι_inv_hom_id
  证明: (K.isoHomologyι i j hj h).inv_hom_id

Depends on / 依赖: K.isoHomology, inv_hom_id
-/
lemma isoHomologyι_inv_hom_id :
    (K.isoHomologyι i j hj h).inv ≫ K.homologyι i = 𝟙 _ :=
  (K.isoHomologyι i j hj h).inv_hom_id

end

section

variable (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j]
include hi h

/--
lemma `isIso_pOpcycles` / 引理 `isIso_pOpcycles`

English:
lemma isIso_pOpcycles
  statement: IsIso (K.pOpcycles j)
  proof: by
  obtain rfl := hi
  exact ShortComplex.isIso_pOpcycles _ h

中文:
引理 isIso_pOpcycles
  结论: 是同构 (K.pOpcycles j)
  证明: by
  obtain rfl := hi
  exact ShortComplex.isIso_pOpcycles _ h

Depends on / 依赖: ShortComplex, ShortComplex.isIso_pOpcycles, infer_instance, isIso_pOpcycles
-/
lemma isIso_pOpcycles : IsIso (K.pOpcycles j) := by
  obtain rfl := hi
  exact ShortComplex.isIso_pOpcycles _ h

/-- The canonical isomorphism `K.X j ≅ K.opCycles j` when the differential to `j` is zero. -/
@[simps! hom]
/--
Definition of `pOpcyclesIso` / `pOpcyclesIso` 的定义

English:
definition pOpcyclesIso
  signature: : K.X j ≅ K.opcycles j
  body: have := K.isIso_pOpcycles i j hi h
  asIso (K.pOpcycles j)

@[reassoc (attr := simp)]

中文:
定义 pOpcyclesIso
  签名: : K.X j ≅ K.opcycles j
  定义体: have := K.isIso_pOpcycles i j hi h
  asIso (K.pOpcycles j)

@[reassoc (attr := simp)]

Depends on / 依赖: K.isIso_pOpcycles, K.pOpcycles, isIso_pOpcycles, pOpcycles
-/
noncomputable def pOpcyclesIso : K.X j ≅ K.opcycles j :=
  have := K.isIso_pOpcycles i j hi h
  asIso (K.pOpcycles j)

@[reassoc (attr := simp)]
/--
lemma `pOpcyclesIso_hom_inv_id` / 引理 `pOpcyclesIso_hom_inv_id`

English:
lemma pOpcyclesIso_hom_inv_id
  proof: (K.pOpcyclesIso i j hi h).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 pOpcyclesIso_hom_inv_id
  证明: (K.pOpcyclesIso i j hi h).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: K.pOpcyclesIso, hom_inv_id, pOpcyclesIso
-/
lemma pOpcyclesIso_hom_inv_id :
    K.pOpcycles j ≫ (K.pOpcyclesIso i j hi h).inv = 𝟙 _ :=
  (K.pOpcyclesIso i j hi h).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `pOpcyclesIso_inv_hom_id` / 引理 `pOpcyclesIso_inv_hom_id`

English:
lemma pOpcyclesIso_inv_hom_id
  proof: (K.pOpcyclesIso i j hi h).inv_hom_id

中文:
引理 pOpcyclesIso_inv_hom_id
  证明: (K.pOpcyclesIso i j hi h).inv_hom_id

Depends on / 依赖: K.pOpcyclesIso, inv_hom_id, pOpcyclesIso
-/
lemma pOpcyclesIso_inv_hom_id :
    (K.pOpcyclesIso i j hi h).inv ≫ K.pOpcycles j = 𝟙 _ :=
  (K.pOpcyclesIso i j hi h).inv_hom_id

/--
lemma `isIso_homologyπ` / 引理 `isIso_homologyπ`

English:
lemma isIso_homologyπ
  statement: IsIso (K.homologyπ j)
  proof: ShortComplex.isIso_homologyπ _ (by cat_disch)

中文:
引理 isIso_homologyπ
  结论: 是同构 (K.homologyπ j)
  证明: ShortComplex.isIso_homologyπ _ (by cat_disch)

Depends on / 依赖: ShortComplex, ShortComplex.isIso_homology, cat_disch
-/
lemma isIso_homologyπ : IsIso (K.homologyπ j) :=
  ShortComplex.isIso_homologyπ _ (by cat_disch)

/-- The canonical isomorphism `K.cycles j ≅ K.homology j`
when the differential to `j` is zero. -/
@[simps! hom]
/--
Definition of `isoHomologyπ` / `isoHomologyπ` 的定义

English:
definition isoHomologyπ
  signature: : K.cycles j ≅ K.homology j
  body: have := K.isIso_homologyπ i j hi h
  asIso (K.homologyπ j)

@[reassoc (attr := simp)]

中文:
定义 isoHomologyπ
  签名: : K.cycles j ≅ K.homology j
  定义体: have := K.isIso_homologyπ i j hi h
  asIso (K.homologyπ j)

@[reassoc (attr := simp)]

Depends on / 依赖: K.homology, K.isIso_homology
-/
noncomputable def isoHomologyπ : K.cycles j ≅ K.homology j :=
  have := K.isIso_homologyπ i j hi h
  asIso (K.homologyπ j)

@[reassoc (attr := simp)]
/--
lemma `isoHomologyπ_hom_inv_id` / 引理 `isoHomologyπ_hom_inv_id`

English:
lemma isoHomologyπ_hom_inv_id
  proof: (K.isoHomologyπ i j hi h).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoHomologyπ_hom_inv_id
  证明: (K.isoHomologyπ i j hi h).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: K.isoHomology, hom_inv_id
-/
lemma isoHomologyπ_hom_inv_id :
    K.homologyπ j ≫ (K.isoHomologyπ i j hi h).inv = 𝟙 _ :=
  (K.isoHomologyπ i j hi h).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoHomologyπ_inv_hom_id` / 引理 `isoHomologyπ_inv_hom_id`

English:
lemma isoHomologyπ_inv_hom_id
  proof: (K.isoHomologyπ i j hi h).inv_hom_id

中文:
引理 isoHomologyπ_inv_hom_id
  证明: (K.isoHomologyπ i j hi h).inv_hom_id

Depends on / 依赖: K.isoHomology, inv_hom_id
-/
lemma isoHomologyπ_inv_hom_id :
    (K.isoHomologyπ i j hi h).inv ≫ K.homologyπ j = 𝟙 _ :=
  (K.isoHomologyπ i j hi h).inv_hom_id

end

section

variable {K L}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `epi_homologyMap_of_epi_of_not_rel` / 引理 `epi_homologyMap_of_epi_of_not_rel`

English:
lemma epi_homologyMap_of_epi_of_not_rel
  statement: (φ : K ⟶ L) (i : ι)
  proof: ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyι i _ rfl (shape _ _ _ (by tauto))))).2
      (MorphismProperty.epimorphisms.infer_property (opcyclesMap φ i))

中文:
引理 epi_homologyMap_of_epi_of_not_rel
  结论: (φ : K ⟶ L) (i : ι)
  证明: ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyι i _ rfl (shape _ _ _ (by tauto))))).2
      (MorphismProperty.epimorphisms.infer_property (opcyclesMap φ i))

Depends on / 依赖: Arrow.isoMk, K.isoHomology, L.isoHomology, MorphismProperty, MorphismProperty.epimorphisms, MorphismProperty.epimorphisms.infer_property, arrow_mk_iso_iff, epimorphisms, infer_property, opcyclesMap
-/
lemma epi_homologyMap_of_epi_of_not_rel (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [Epi (φ.f i)] (hi : forall j, ¬ c.Rel i j) :
    Epi (homologyMap φ i) :=
  ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyι i _ rfl (shape _ _ _ (by tauto))))).2
      (MorphismProperty.epimorphisms.infer_property (opcyclesMap φ i))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_homologyMap_of_mono_of_not_rel` / 引理 `mono_homologyMap_of_mono_of_not_rel`

English:
lemma mono_homologyMap_of_mono_of_not_rel
  statement: (φ : K ⟶ L) (j : ι)
  proof: ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyπ _ j rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyπ _ j rfl (shape _ _ _ (by tauto))))).1
      (MorphismProperty.monomorphisms.infer_property (cyclesMap φ j))

中文:
引理 mono_homologyMap_of_mono_of_not_rel
  结论: (φ : K ⟶ L) (j : ι)
  证明: ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyπ _ j rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyπ _ j rfl (shape _ _ _ (by tauto))))).1
      (MorphismProperty.monomorphisms.infer_property (cyclesMap φ j))

Depends on / 依赖: Arrow.isoMk, K.isoHomology, L.isoHomology, MorphismProperty, MorphismProperty.monomorphisms, MorphismProperty.monomorphisms.infer_property, arrow_mk_iso_iff, cyclesMap, infer_property, monomorphisms
-/
lemma mono_homologyMap_of_mono_of_not_rel (φ : K ⟶ L) (j : ι)
    [K.HasHomology j] [L.HasHomology j] [Mono (φ.f j)] (hj : forall i, ¬ c.Rel i j) :
    Mono (homologyMap φ j) :=
  ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyπ _ j rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyπ _ j rfl (shape _ _ _ (by tauto))))).1
      (MorphismProperty.monomorphisms.infer_property (cyclesMap φ j))

end

/--
Definition of `ExactAt` / `ExactAt` 的定义

English:
definition ExactAt
  body: (K.sc i).Exact

中文:
定义 ExactAt
  定义体: (K.sc i).Exact

Depends on / 依赖: K.sc
-/
def ExactAt := (K.sc i).Exact

/--
lemma `exactAt_iff` / 引理 `exactAt_iff`

English:
lemma exactAt_iff
  proof: by rfl

中文:
引理 exactAt_iff
  证明: by rfl

Depends on / 依赖: X.p_opcyclesToE, epi_of_epi_fac, p_opcyclesToE
-/
lemma exactAt_iff :
    K.ExactAt i ↔ (K.sc i).Exact := by rfl

variable {K i} in
/--
lemma `ExactAt.of_iso` / 引理 `ExactAt.of_iso`

English:
lemma ExactAt.of_iso
  given: (hK : K.ExactAt i) {L : HomologicalComplex C c} (e : K ≅ L)
  proof: by
  rw [exactAt_iff] at hK ⊢
  exact ShortComplex.exact_of_iso ((shortComplexFunctor C c i).mapIso e) hK

中文:
引理 ExactAt.of_iso
  条件: (hK : K.ExactAt i) {L : 同调复形 C c} (e : K ≅ L)
  证明: by
  rw [exactAt_iff] at hK ⊢
  exact ShortComplex.exact_of_iso ((shortComplexFunctor C c i).mapIso e) hK

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_iso, exactAt_iff, exact_of_iso, mapIso, shortComplexFunctor
-/
lemma ExactAt.of_iso (hK : K.ExactAt i) {L : HomologicalComplex C c} (e : K ≅ L) :
    L.ExactAt i := by
  rw [exactAt_iff] at hK ⊢
  exact ShortComplex.exact_of_iso ((shortComplexFunctor C c i).mapIso e) hK

variable {K i} in
/--
lemma `ExactAt.of_isZero` / 引理 `ExactAt.of_isZero`

English:
lemma ExactAt.of_isZero
  given: (h : IsZero (K.X i))
  statement: K.ExactAt i
  proof: ShortComplex.exact_of_isZero_X₂ _ h

中文:
引理 ExactAt.of_isZero
  条件: (h : 是零 (K.X i))
  结论: K.ExactAt i
  证明: ShortComplex.exact_of_isZero_X₂ _ h

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_isZero_X, infer_instance
-/
lemma ExactAt.of_isZero (h : IsZero (K.X i)) : K.ExactAt i :=
  ShortComplex.exact_of_isZero_X₂ _ h

/--
lemma `exactAt_iff'` / 引理 `exactAt_iff'`

English:
lemma exactAt_iff'
  given: (hi : c.prev j = i) (hk : c.next j = k)
  proof: ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)

中文:
引理 exactAt_iff'
  条件: (hi : c.prev j = i) (hk : c.next j = k)
  证明: ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)

Depends on / 依赖: K.isoSc, ShortComplex, ShortComplex.exact_iff_of_iso, exact_iff_of_iso
-/
lemma exactAt_iff' (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ (K.sc' i j k).Exact :=
  ShortComplex.exact_iff_of_iso (K.isoSc' i j k hi hk)

/--
lemma `exactAt_iff_isZero_homology` / 引理 `exactAt_iff_isZero_homology`

English:
lemma exactAt_iff_isZero_homology
  given: [K.HasHomology i]
  proof: by
  dsimp [homology]
  rw [exactAt_iff]; rw [ShortComplex.exact_iff_isZero_homology]

中文:
引理 exactAt_iff_isZero_homology
  条件: [K.有同调 i]
  证明: by
  dsimp [homology]
  rw [exactAt_iff]; rw [ShortComplex.exact_iff_isZero_homology]

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_isZero_homology, exactAt_iff, exact_iff_isZero_homology, homology
-/
lemma exactAt_iff_isZero_homology [K.HasHomology i] :
    K.ExactAt i ↔ IsZero (K.homology i) := by
  dsimp [homology]
  rw [exactAt_iff]; rw [ShortComplex.exact_iff_isZero_homology]

variable {K i} in
/--
lemma `ExactAt.isZero_homology` / 引理 `ExactAt.isZero_homology`

English:
lemma ExactAt.isZero_homology
  given: [K.HasHomology i] (h : K.ExactAt i)
  proof: by
  rwa [← exactAt_iff_isZero_homology]

中文:
引理 ExactAt.isZero_homology
  条件: [K.有同调 i] (h : K.ExactAt i)
  证明: by
  rwa [← exactAt_iff_isZero_homology]

Depends on / 依赖: exactAt_iff_isZero_homology
-/
lemma ExactAt.isZero_homology [K.HasHomology i] (h : K.ExactAt i) :
    IsZero (K.homology i) := by
  rwa [← exactAt_iff_isZero_homology]

/--
Definition of `Acyclic` / `Acyclic` 的定义

English:
definition Acyclic
  body: forall i, K.ExactAt i

中文:
定义 非循环
  定义体: forall i, K.ExactAt i

Depends on / 依赖: ExactAt, K.ExactAt
-/
def Acyclic := forall i, K.ExactAt i

/--
lemma `acyclic_iff` / 引理 `acyclic_iff`

English:
lemma acyclic_iff
  proof: by rfl

中文:
引理 acyclic_iff
  证明: by rfl

Depends on / 依赖: EToCycles_i, X.EToCycles_i, mono_of_mono_fac
-/
lemma acyclic_iff :
    K.Acyclic ↔ forall i, K.ExactAt i := by rfl

/--
lemma `acyclic_of_isZero` / 引理 `acyclic_of_isZero`

English:
lemma acyclic_of_isZero
  given: (hK : IsZero K)
  proof: by
  rw [acyclic_iff]
  intro i
  apply ShortComplex.exact_of_isZero_X₂
  exact (eval _ _ i).map_isZero hK

中文:
引理 acyclic_of_isZero
  条件: (hK : 是零 K)
  证明: by
  rw [acyclic_iff]
  intro i
  apply ShortComplex.exact_of_isZero_X₂
  exact (eval _ _ i).map_isZero hK

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_isZero_X, acyclic_iff, map_isZero
-/
lemma acyclic_of_isZero (hK : IsZero K) :
    K.Acyclic := by
  rw [acyclic_iff]
  intro i
  apply ShortComplex.exact_of_isZero_X₂
  exact (eval _ _ i).map_isZero hK

end HomologicalComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : ChainComplex C Nat) (φ : K ⟶ L) [K.HasHomology 0]

/--
Instance `isIso_iCycles₀` / 实例 `isIso_iCycles₀`

English:
instance isIso_iCycles₀
  signature: : IsIso (K.iCycles 0)
  body: K.isIso_iCycles 0 0 (by simp) (by simp)

中文:
实例 isIso_iCycles₀
  签名: : 是同构 (K.iCycles 0)
  定义体: K.isIso_iCycles 0 0 (by simp) (by simp)

Depends on / 依赖: K.isIso_iCycles, infer_instance, isIso_iCycles
-/
instance isIso_iCycles₀ : IsIso (K.iCycles 0) :=
  K.isIso_iCycles 0 0 (by simp) (by simp)

/--
Definition of `cycles₀Iso` / `cycles₀Iso` 的定义

English:
abbreviation cycles₀Iso
  signature: : K.cycles 0 ≅ K.X 0
  body: K.iCyclesIso 0 0 (by simp) (by simp)

中文:
缩写 cycles₀Iso
  签名: : K.cycles 0 ≅ K.X 0
  定义体: K.iCyclesIso 0 0 (by simp) (by simp)

Depends on / 依赖: K.iCyclesIso, iCyclesIso
-/
noncomputable abbrev cycles₀Iso : K.cycles 0 ≅ K.X 0 :=
  K.iCyclesIso 0 0 (by simp) (by simp)

/--
Instance `isIso_homologyι₀` / 实例 `isIso_homologyι₀`

English:
instance isIso_homologyι₀
  signature: :
  body: K.isIso_homologyι 0 _ rfl (by simp)

中文:
实例 isIso_homologyι₀
  签名: :
  定义体: K.isIso_homologyι 0 _ rfl (by simp)

Depends on / 依赖: K.isIso_homology
-/
instance isIso_homologyι₀ :
    IsIso (K.homologyι 0) :=
  K.isIso_homologyι 0 _ rfl (by simp)

/--
Definition of `isoHomologyι₀` / `isoHomologyι₀` 的定义

English:
abbreviation isoHomologyι₀
  signature: : K.homology 0 ≅ K.opcycles 0
  body: K.isoHomologyι 0 _ rfl (by simp)

中文:
缩写 isoHomologyι₀
  签名: : K.homology 0 ≅ K.opcycles 0
  定义体: K.isoHomologyι 0 _ rfl (by simp)

Depends on / 依赖: K.isoHomology
-/
noncomputable abbrev isoHomologyι₀ : K.homology 0 ≅ K.opcycles 0 :=
  K.isoHomologyι 0 _ rfl (by simp)

variable {K L}

@[reassoc (attr := simp)]
/--
lemma `isoHomologyι₀_inv_naturality` / 引理 `isoHomologyι₀_inv_naturality`

English:
lemma isoHomologyι₀_inv_naturality
  given: [L.HasHomology 0]
  proof: by
  simp only [assoc, ← cancel_mono (L.homologyι 0),
    HomologicalComplex.homologyι_naturality, HomologicalComplex.isoHomologyι_inv_hom_id_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, comp_id]

中文:
引理 isoHomologyι₀_inv_naturality
  条件: [L.有同调 0]
  证明: by
  simp only [assoc, ← cancel_mono (L.homologyι 0),
    HomologicalComplex.homologyι_naturality, HomologicalComplex.isoHomologyι_inv_hom_id_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, comp_id]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology, HomologicalComplex.isoHomology, L.homology, cancel_mono, comp_id
-/
lemma isoHomologyι₀_inv_naturality [L.HasHomology 0] :
    K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.opcyclesMap φ 0 ≫ L.isoHomologyι₀.inv := by
  simp only [assoc, ← cancel_mono (L.homologyι 0),
    HomologicalComplex.homologyι_naturality, HomologicalComplex.isoHomologyι_inv_hom_id_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, comp_id]

end ChainComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : CochainComplex C Nat) (φ : K ⟶ L) [K.HasHomology 0]

/--
Instance `isIso_pOpcycles₀` / 实例 `isIso_pOpcycles₀`

English:
instance isIso_pOpcycles₀
  signature: : IsIso (K.pOpcycles 0)
  body: K.isIso_pOpcycles 0 0 (by simp) (by simp)

中文:
实例 isIso_pOpcycles₀
  签名: : 是同构 (K.pOpcycles 0)
  定义体: K.isIso_pOpcycles 0 0 (by simp) (by simp)

Depends on / 依赖: K.isIso_pOpcycles, isIso_pOpcycles
-/
instance isIso_pOpcycles₀ : IsIso (K.pOpcycles 0) :=
  K.isIso_pOpcycles 0 0 (by simp) (by simp)

/--
Definition of `opcycles₀Iso` / `opcycles₀Iso` 的定义

English:
abbreviation opcycles₀Iso
  signature: : K.X 0 ≅ K.opcycles 0
  body: K.pOpcyclesIso 0 0 (by simp) (by simp)

中文:
缩写 opcycles₀Iso
  签名: : K.X 0 ≅ K.opcycles 0
  定义体: K.pOpcyclesIso 0 0 (by simp) (by simp)

Depends on / 依赖: K.pOpcyclesIso, pOpcyclesIso
-/
noncomputable abbrev opcycles₀Iso : K.X 0 ≅ K.opcycles 0 :=
  K.pOpcyclesIso 0 0 (by simp) (by simp)

/--
Instance `isIso_homologyπ₀` / 实例 `isIso_homologyπ₀`

English:
instance isIso_homologyπ₀
  signature: :
  body: K.isIso_homologyπ _ 0 rfl (by simp)

中文:
实例 isIso_homologyπ₀
  签名: :
  定义体: K.isIso_homologyπ _ 0 rfl (by simp)

Depends on / 依赖: K.isIso_homology
-/
instance isIso_homologyπ₀ :
    IsIso (K.homologyπ 0) :=
  K.isIso_homologyπ _ 0 rfl (by simp)

/--
Definition of `isoHomologyπ₀` / `isoHomologyπ₀` 的定义

English:
abbreviation isoHomologyπ₀
  signature: : K.cycles 0 ≅ K.homology 0
  body: K.isoHomologyπ _ 0 rfl (by simp)

中文:
缩写 isoHomologyπ₀
  签名: : K.cycles 0 ≅ K.homology 0
  定义体: K.isoHomologyπ _ 0 rfl (by simp)

Depends on / 依赖: K.isoHomology
-/
noncomputable abbrev isoHomologyπ₀ : K.cycles 0 ≅ K.homology 0 :=
  K.isoHomologyπ _ 0 rfl (by simp)

variable {K L}

@[reassoc (attr := simp)]
/--
lemma `isoHomologyπ₀_inv_naturality` / 引理 `isoHomologyπ₀_inv_naturality`

English:
lemma isoHomologyπ₀_inv_naturality
  given: [L.HasHomology 0]
  proof: by
  simp only [← cancel_epi (K.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id, comp_id,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

中文:
引理 isoHomologyπ₀_inv_naturality
  条件: [L.有同调 0]
  证明: by
  simp only [← cancel_epi (K.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id, comp_id,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homology, HomologicalComplex.isoHomology, K.homology, cancel_epi, comp_id
-/
lemma isoHomologyπ₀_inv_naturality [L.HasHomology 0] :
    HomologicalComplex.homologyMap φ 0 ≫ L.isoHomologyπ₀.inv =
      K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap φ 0 := by
  simp only [← cancel_epi (K.homologyπ 0), HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id, comp_id,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

end CochainComplex

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (φ ψ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `homologyMap_neg` / 引理 `homologyMap_neg`

English:
lemma homologyMap_neg
  statement: homologyMap (-φ) i = -homologyMap φ i
  proof: by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

中文:
引理 homologyMap_neg
  结论: homologyMap (-φ) i = -homologyMap φ i
  证明: by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_neg, homologyMap, homologyMap_neg
-/
lemma homologyMap_neg : homologyMap (-φ) i = -homologyMap φ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `homologyMap_add` / 引理 `homologyMap_add`

English:
lemma homologyMap_add
  statement: homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i
  proof: by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

中文:
引理 homologyMap_add
  结论: homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i
  证明: by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_add, homologyMap, homologyMap_add
-/
lemma homologyMap_add : homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `homologyMap_sub` / 引理 `homologyMap_sub`

English:
lemma homologyMap_sub
  statement: homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ i
  proof: by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl

中文:
引理 homologyMap_sub
  结论: homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ i
  证明: by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_sub, homologyMap, homologyMap_sub
-/
lemma homologyMap_sub : homologyMap (φ - ψ) i = homologyMap φ i - homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : (homologyFunctor C c i).Additive where

中文:
实例 [带同调范畴
  签名: C] : (homologyFunctor C c i).加性 where
-/
instance [CategoryWithHomology C] : (homologyFunctor C c i).Additive where

end HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_liftCycles_iff` / 引理 `isIso_liftCycles_iff`

English:
lemma isIso_liftCycles_iff
  statement: (K : CochainComplex C Nat) {X : C} (φ : X ⟶ K.X 0)
  proof: by
  suffices forall (i : Nat) (hx : (ComplexShape.up Nat).next 0 = i)
    (hφ : φ ≫ K.d 0 i = 0), IsIso (K.liftCycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) ⟶ K.sc 0 :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_liftCycles α rfl rfl (by simp)).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros α rfl rfl (by simp))

中文:
引理 isIso_liftCycles_iff
  结论: (K : 上链复形 C 自然数) {X : C} (φ : X ⟶ K.X 0)
  证明: by
  suffices forall (i : Nat) (hx : (ComplexShape.up Nat).next 0 = i)
    (hφ : φ ≫ K.d 0 i = 0), IsIso (K.liftCycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) ⟶ K.sc 0 :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_liftCycles α rfl rfl (by simp)).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros α rfl rfl (by simp))

Depends on / 依赖: ComplexShape, ComplexShape.up, K.liftCycles, K.sc, ShortComplex, ShortComplex.mk, ShortComplex.quasiIso_iff_isIso_liftCycles, ShortComplex.quasiIso_iff_of_zeros, liftCycles, quasiIso_iff_isIso_liftCycles, quasiIso_iff_of_zeros, symm.trans
-/
lemma isIso_liftCycles_iff (K : CochainComplex C Nat) {X : C} (φ : X ⟶ K.X 0)
    [K.HasHomology 0] (hφ : φ ≫ K.d 0 1 = 0) :
    IsIso (K.liftCycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ := by
  suffices forall (i : Nat) (hx : (ComplexShape.up Nat).next 0 = i)
    (hφ : φ ≫ K.d 0 i = 0), IsIso (K.liftCycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Mono φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) ⟶ K.sc 0 :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_liftCycles α rfl rfl (by simp)).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros α rfl rfl (by simp))

end CochainComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_descOpcycles_iff` / 引理 `isIso_descOpcycles_iff`

English:
lemma isIso_descOpcycles_iff
  statement: (K : ChainComplex C Nat) {X : C} (φ : K.X 0 ⟶ X)
  proof: by
  suffices forall (i : Nat) (hx : (ComplexShape.down Nat).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

中文:
引理 isIso_descOpcycles_iff
  结论: (K : 链复形 C 自然数) {X : C} (φ : K.X 0 ⟶ X)
  证明: by
  suffices forall (i : Nat) (hx : (ComplexShape.down Nat).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

Depends on / 依赖: ComplexShape, ComplexShape.down, K.descOpcycles, K.sc, ShortComplex, ShortComplex.mk, ShortComplex.quasiIso_iff_isIso_descOpcycles, ShortComplex.quasiIso_iff_of_zeros, descOpcycles, quasiIso_iff_isIso_descOpcycles, quasiIso_iff_of_zeros, symm.trans
-/
lemma isIso_descOpcycles_iff (K : ChainComplex C Nat) {X : C} (φ : K.X 0 ⟶ X)
    [K.HasHomology 0] (hφ : K.d 1 0 ≫ φ = 0) :
    IsIso (K.descOpcycles φ 1 (by simp) hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ := by
  suffices forall (i : Nat) (hx : (ComplexShape.down Nat).prev 0 = i)
    (hφ : K.d i 0 ≫ φ = 0), IsIso (K.descOpcycles φ i hx hφ) ↔
      (ShortComplex.mk _ _ hφ).Exact ∧ Epi φ from this 1 (by simp) hφ
  rintro _ rfl hφ
  let α : K.sc 0 ⟶ ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp) :=
    { τ₁ := 0
      τ₂ := φ
      τ₃ := 0 }
  exact (ShortComplex.quasiIso_iff_isIso_descOpcycles α (by simp) rfl rfl).symm.trans
    (ShortComplex.quasiIso_iff_of_zeros' α (by simp) rfl rfl)

end ChainComplex

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)
  (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  [K.HasHomology j] [(K.sc' i j k).HasHomology]

/--
Definition of `cyclesIsoSc'` / `cyclesIsoSc'` 的定义

English:
definition cyclesIsoSc'
  signature: : K.cycles j ≅ (K.sc' i j k).cycles
  body: ShortComplex.cyclesMapIso (K.isoSc' i j k hi hk)

中文:
定义 cyclesIsoSc'
  签名: : K.cycles j ≅ (K.sc' i j k).cycles
  定义体: ShortComplex.cyclesMapIso (K.isoSc' i j k hi hk)

Depends on / 依赖: K.isoSc, ShortComplex, ShortComplex.cyclesMapIso, cyclesMapIso
-/
noncomputable def cyclesIsoSc' : K.cycles j ≅ (K.sc' i j k).cycles :=
  ShortComplex.cyclesMapIso (K.isoSc' i j k hi hk)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `cyclesIsoSc'_hom_iCycles` / 引理 `cyclesIsoSc'_hom_iCycles`

English:
lemma cyclesIsoSc'_hom_iCycles
  proof: by
  dsimp [cyclesIsoSc']
  simp only [ShortComplex.cyclesMap_i, shortComplexFunctor_obj_X₂, shortComplexFunctor'_obj_X₂,
    natIsoSc'_hom_app_τ₂, comp_id]
  rfl

中文:
引理 cyclesIsoSc'_hom_iCycles
  证明: by
  dsimp [cyclesIsoSc']
  simp only [ShortComplex.cyclesMap_i, shortComplexFunctor_obj_X₂, shortComplexFunctor'_obj_X₂,
    natIsoSc'_hom_app_τ₂, comp_id]
  rfl

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Functor, Functor.map_id, Preadditive, Preadditive.mono_iff_cancel_zero, X.fromOpcycles, X.opcyclesMap_fromOpcycles, cancel_mono, cat_disch, comp_id, fromOpcycles, map_id, mono_iff_cancel_zero, opcyclesMap_fromOpcycles, replace, zero_comp
-/
lemma cyclesIsoSc'_hom_iCycles :
    (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).iCycles = K.iCycles j := by
  dsimp [cyclesIsoSc']
  simp only [ShortComplex.cyclesMap_i, shortComplexFunctor_obj_X₂, shortComplexFunctor'_obj_X₂,
    natIsoSc'_hom_app_τ₂, comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `cyclesIsoSc'_inv_iCycles` / 引理 `cyclesIsoSc'_inv_iCycles`

English:
lemma cyclesIsoSc'_inv_iCycles
  proof: by
  simp [cyclesIsoSc', iCycles]

中文:
引理 cyclesIsoSc'_inv_iCycles
  证明: by
  simp [cyclesIsoSc', iCycles]

Depends on / 依赖: infer_instance
-/
lemma cyclesIsoSc'_inv_iCycles :
    (K.cyclesIsoSc' i j k hi hk).inv ≫ K.iCycles j = (K.sc' i j k).iCycles := by
  simp [cyclesIsoSc', iCycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toCycles_cyclesIsoSc'_hom` / 引理 `toCycles_cyclesIsoSc'_hom`

English:
lemma toCycles_cyclesIsoSc'_hom
  proof: by
  simp only [← cancel_mono (K.sc' i j k).iCycles, assoc, cyclesIsoSc'_hom_iCycles,
    toCycles_i, ShortComplex.toCycles_i, shortComplexFunctor'_obj_f]

中文:
引理 toCycles_cyclesIsoSc'_hom
  证明: by
  simp only [← cancel_mono (K.sc' i j k).iCycles, assoc, cyclesIsoSc'_hom_iCycles,
    toCycles_i, ShortComplex.toCycles_i, shortComplexFunctor'_obj_f]

Depends on / 依赖: K.sc, ShortComplex, ShortComplex.toCycles_i, _hom_iCycles, _obj_f, cancel_mono, cyclesIsoSc, iCycles, shortComplexFunctor, toCycles_i
-/
lemma toCycles_cyclesIsoSc'_hom :
    K.toCycles i j ≫ (K.cyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).toCycles := by
  simp only [← cancel_mono (K.sc' i j k).iCycles, assoc, cyclesIsoSc'_hom_iCycles,
    toCycles_i, ShortComplex.toCycles_i, shortComplexFunctor'_obj_f]

/--
Definition of `opcyclesIsoSc'` / `opcyclesIsoSc'` 的定义

English:
definition opcyclesIsoSc'
  signature: : K.opcycles j ≅ (K.sc' i j k).opcycles
  body: ShortComplex.opcyclesMapIso (K.isoSc' i j k hi hk)

中文:
定义 opcyclesIsoSc'
  签名: : K.opcycles j ≅ (K.sc' i j k).opcycles
  定义体: ShortComplex.opcyclesMapIso (K.isoSc' i j k hi hk)

Depends on / 依赖: K.isoSc, ShortComplex, ShortComplex.opcyclesMapIso, opcyclesMapIso
-/
noncomputable def opcyclesIsoSc' : K.opcycles j ≅ (K.sc' i j k).opcycles :=
  ShortComplex.opcyclesMapIso (K.isoSc' i j k hi hk)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pOpcycles_opcyclesIsoSc'_inv` / 引理 `pOpcycles_opcyclesIsoSc'_inv`

English:
lemma pOpcycles_opcyclesIsoSc'_inv
  proof: by
  dsimp [opcyclesIsoSc']
  simp only [ShortComplex.p_opcyclesMap, shortComplexFunctor'_obj_X₂, shortComplexFunctor_obj_X₂,
    natIsoSc'_inv_app_τ₂, id_comp]
  rfl

中文:
引理 pOpcycles_opcyclesIsoSc'_inv
  证明: by
  dsimp [opcyclesIsoSc']
  simp only [ShortComplex.p_opcyclesMap, shortComplexFunctor'_obj_X₂, shortComplexFunctor_obj_X₂,
    natIsoSc'_inv_app_τ₂, id_comp]
  rfl

Depends on / 依赖: ShortComplex, ShortComplex.p_opcyclesMap, id_comp, natIsoSc, opcyclesIsoSc, p_opcyclesMap, shortComplexFunctor
-/
lemma pOpcycles_opcyclesIsoSc'_inv :
    (K.sc' i j k).pOpcycles ≫ (K.opcyclesIsoSc' i j k hi hk).inv = K.pOpcycles j := by
  dsimp [opcyclesIsoSc']
  simp only [ShortComplex.p_opcyclesMap, shortComplexFunctor'_obj_X₂, shortComplexFunctor_obj_X₂,
    natIsoSc'_inv_app_τ₂, id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pOpcycles_opcyclesIsoSc'_hom` / 引理 `pOpcycles_opcyclesIsoSc'_hom`

English:
lemma pOpcycles_opcyclesIsoSc'_hom
  proof: by
  simp [opcyclesIsoSc', pOpcycles]

中文:
引理 pOpcycles_opcyclesIsoSc'_hom
  证明: by
  simp [opcyclesIsoSc', pOpcycles]
-/
lemma pOpcycles_opcyclesIsoSc'_hom :
    K.pOpcycles j ≫ (K.opcyclesIsoSc' i j k hi hk).hom = (K.sc' i j k).pOpcycles := by
  simp [opcyclesIsoSc', pOpcycles]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoSc'_inv_fromOpcycles` / 引理 `opcyclesIsoSc'_inv_fromOpcycles`

English:
lemma opcyclesIsoSc'_inv_fromOpcycles
  proof: by
  simp only [← cancel_epi (K.sc' i j k).pOpcycles, pOpcycles_opcyclesIsoSc'_inv_assoc,
    p_fromOpcycles, ShortComplex.p_fromOpcycles, shortComplexFunctor'_obj_g]

中文:
引理 opcyclesIsoSc'_inv_fromOpcycles
  证明: by
  simp only [← cancel_epi (K.sc' i j k).pOpcycles, pOpcycles_opcyclesIsoSc'_inv_assoc,
    p_fromOpcycles, ShortComplex.p_fromOpcycles, shortComplexFunctor'_obj_g]
-/
lemma opcyclesIsoSc'_inv_fromOpcycles :
    (K.opcyclesIsoSc' i j k hi hk).inv ≫ K.fromOpcycles j k =
      (K.sc' i j k).fromOpcycles := by
  simp only [← cancel_epi (K.sc' i j k).pOpcycles, pOpcycles_opcyclesIsoSc'_inv_assoc,
    p_fromOpcycles, ShortComplex.p_fromOpcycles, shortComplexFunctor'_obj_g]

/--
Definition of `homologyIsoSc'` / `homologyIsoSc'` 的定义

English:
definition homologyIsoSc'
  signature: : K.homology j ≅ (K.sc' i j k).homology
  body: ShortComplex.homologyMapIso (K.isoSc' i j k hi hk)

@[simp]

中文:
定义 homologyIsoSc'
  签名: : K.homology j ≅ (K.sc' i j k).homology
  定义体: ShortComplex.homologyMapIso (K.isoSc' i j k hi hk)

@[simp]

Depends on / 依赖: K.isoSc, ShortComplex, ShortComplex.homologyMapIso, homologyMapIso
-/
noncomputable def homologyIsoSc' : K.homology j ≅ (K.sc' i j k).homology :=
  ShortComplex.homologyMapIso (K.isoSc' i j k hi hk)

@[simp]
/--
lemma `homology_sc'_eq_homology` / 引理 `homology_sc'_eq_homology`

English:
lemma homology_sc'_eq_homology
  given: [(K.sc' (c.prev j) j (c.next j)).HasHomology]
  proof: rfl

中文:
引理 homology_sc'_eq_homology
  条件: [(K.sc' (c.prev j) j (c.next j)).有同调]
  证明: rfl
-/
lemma homology_sc'_eq_homology [(K.sc' (c.prev j) j (c.next j)).HasHomology] :
    (K.sc' (c.prev j) j (c.next j)).homology = K.homology j := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `homologyIsoSc'_eq_refl` / 引理 `homologyIsoSc'_eq_refl`

English:
lemma homologyIsoSc'_eq_refl
  proof: by
  ext : 1
  apply ShortComplex.homologyMap_id

@[reassoc (attr := simp)]

中文:
引理 homologyIsoSc'_eq_refl
  证明: by
  ext : 1
  apply ShortComplex.homologyMap_id

@[reassoc (attr := simp)]
-/
lemma homologyIsoSc'_eq_refl
    [(K.sc' (c.prev j) j (c.next j)).HasHomology] :
    dsimp% K.homologyIsoSc' _ j _ rfl rfl = Iso.refl _ := by
  ext : 1
  apply ShortComplex.homologyMap_id

@[reassoc (attr := simp)]
/--
lemma `π_homologyIsoSc'_hom` / 引理 `π_homologyIsoSc'_hom`

English:
lemma π_homologyIsoSc'_hom
  proof: by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]

中文:
引理 π_homologyIsoSc'_hom
  证明: by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]

Depends on / 依赖: ShortComplex, ShortComplex.homology
-/
lemma π_homologyIsoSc'_hom :
    K.homologyπ j ≫ (K.homologyIsoSc' i j k hi hk).hom =
      (K.cyclesIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyπ := by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
/--
lemma `π_homologyIsoSc'_inv` / 引理 `π_homologyIsoSc'_inv`

English:
lemma π_homologyIsoSc'_inv
  proof: by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]

中文:
引理 π_homologyIsoSc'_inv
  证明: by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
-/
lemma π_homologyIsoSc'_inv :
    (K.sc' i j k).homologyπ ≫ (K.homologyIsoSc' i j k hi hk).inv =
      (K.cyclesIsoSc' i j k hi hk).inv ≫ K.homologyπ j := by
  apply ShortComplex.homologyπ_naturality

@[reassoc (attr := simp)]
/--
lemma `homologyIsoSc'_hom_ι` / 引理 `homologyIsoSc'_hom_ι`

English:
lemma homologyIsoSc'_hom_ι
  proof: by
  apply ShortComplex.homologyι_naturality

@[reassoc (attr := simp)]

中文:
引理 homologyIsoSc'_hom_ι
  证明: by
  apply ShortComplex.homologyι_naturality

@[reassoc (attr := simp)]
-/
lemma homologyIsoSc'_hom_ι :
    (K.homologyIsoSc' i j k hi hk).hom ≫ (K.sc' i j k).homologyι =
      K.homologyι j ≫ (K.opcyclesIsoSc' i j k hi hk).hom := by
  apply ShortComplex.homologyι_naturality

@[reassoc (attr := simp)]
/--
lemma `homologyIsoSc'_inv_ι` / 引理 `homologyIsoSc'_inv_ι`

English:
lemma homologyIsoSc'_inv_ι
  proof: by
  apply ShortComplex.homologyι_naturality

中文:
引理 homologyIsoSc'_inv_ι
  证明: by
  apply ShortComplex.homologyι_naturality
-/
lemma homologyIsoSc'_inv_ι :
    (K.homologyIsoSc' i j k hi hk).inv ≫ K.homologyι j =
      (K.sc' i j k).homologyι ≫ (K.opcyclesIsoSc' i j k hi hk).inv := by
  apply ShortComplex.homologyι_naturality

end HomologicalComplex
