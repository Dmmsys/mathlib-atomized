/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-! # The homotopy cofiber of a morphism of homological complexes

In this file, we construct the homotopy cofiber of a morphism `φ : F ⟶ G`
between homological complexes in `HomologicalComplex C c`. In degree `i`,
it is isomorphic to `(F.X j) ⊞ (G.X i)` if there is a `j` such that `c.Rel i j`,
and `G.X i` otherwise. (This is also known as the mapping cone of `φ`. Under
the name `CochainComplex.mappingCone`, a specific API shall be developed
for the case of cochain complexes indexed by `ℤ`.)

When we assume `hc : ∀ j, ∃ i, c.Rel i j` (which holds in the case of chain complexes,
or cochain complexes indexed by `ℤ`), then for any homological complex `K`,
there is a bijection `HomologicalComplex.homotopyCofiber.descEquiv φ K hc`
between `homotopyCofiber φ ⟶ K` and the tuples `(α, hα)` with
`α : G ⟶ K` and `hα : Homotopy (φ ≫ α) 0`.

We shall also study the cylinder of a homological complex `K`: this is the
homotopy cofiber of the morphism `biprod.lift (𝟙 K) (-𝟙 K) : K ⟶ K ⊞ K`.
Then, a morphism `K.cylinder ⟶ M` is determined by the data of two
morphisms `φ₀ φ₁ : K ⟶ M` and a homotopy `h : Homotopy φ₀ φ₁`,
see `cylinder.desc`. There is also a homotopy equivalence
`cylinder.homotopyEquiv K : HomotopyEquiv K.cylinder K`. From the construction of
the cylinder, we deduce the lemma `Homotopy.map_eq_of_inverts_homotopyEquivalences`
which asserts that if a functor inverts homotopy equivalences, then the images of
two homotopic maps are equal.

-/

@[expose] public section


open CategoryTheory Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

/--
Definition of `HasHomotopyCofiber` / `HasHomotopyCofiber` 的定义

English:
class HasHomotopyCofiber
  parameters: (φ : F ⟶ G)
  axioms and operations (1):
    - hasBinaryBiproduct((i j : ι) (hij : c.Rel i j)) : HasBinaryBiproduct (F.X j) (G.X i)

中文:
类 有HomotopyCofiber
  参数: (φ : F ⟶ G)
  公理与运算 (1 个):
    - hasBinaryBiproduct((i j : ι) (hij : c.关系 i j)) : 有BinaryBiproduct (F.X j) (G.X i)
-/
class HasHomotopyCofiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (i j : ι) (hij : c.Rel i j) : HasBinaryBiproduct (F.X j) (G.X i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryBiproducts
  signature: C] : HasHomotopyCofiber φ where
  body: inferInstance

中文:
实例 [有BinaryBiproducts
  签名: C] : 有HomotopyCofiber φ where
  定义体: inferInstance
-/
instance [HasBinaryBiproducts C] : HasHomotopyCofiber φ where
  hasBinaryBiproduct _ _ _ := inferInstance

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

namespace homotopyCofiber

/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: (i : ι)
  body: if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (F.X (c.next i)) ⊞ (G.X i)
  else G.X i

中文:
定义 X
  签名: (i : ι)
  定义体: if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (F.X (c.next i)) ⊞ (G.X i)
  else G.X i

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, c.Rel, c.next, hasBinaryBiproduct
-/
noncomputable def X (i : ι) : C :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (F.X (c.next i)) ⊞ (G.X i)
  else G.X i

/--
Definition of `XIsoBiprod` / `XIsoBiprod` 的定义

English:
definition XIsoBiprod
  signature: (i j : ι) (hij : c.Rel i j) [HasBinaryBiproduct (F.X j) (G.X i)]
  body: eqToIso (by
    obtain rfl := c.next_eq' hij
    apply dif_pos hij)

中文:
定义 XIsoBiprod
  签名: (i j : ι) (hij : c.关系 i j) [有BinaryBiproduct (F.X j) (G.X i)]
  定义体: eqToIso (by
    obtain rfl := c.next_eq' hij
    apply dif_pos hij)

Depends on / 依赖: c.next_eq, dif_pos, eqToIso, next_eq
-/
noncomputable def XIsoBiprod (i j : ι) (hij : c.Rel i j) [HasBinaryBiproduct (F.X j) (G.X i)] :
    X φ i ≅ F.X j ⊞ G.X i :=
  eqToIso (by
    obtain rfl := c.next_eq' hij
    apply dif_pos hij)

/--
Definition of `XIso` / `XIso` 的定义

English:
definition XIso
  signature: (i : ι) (hi : ¬ c.Rel i (c.next i))
  body: eqToIso (dif_neg hi)

中文:
定义 XIso
  签名: (i : ι) (hi : ¬ c.关系 i (c.next i))
  定义体: eqToIso (dif_neg hi)

Depends on / 依赖: dif_neg, eqToIso
-/
noncomputable def XIso (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    X φ i ≅ G.X i :=
  eqToIso (dif_neg hi)

/--
lemma `isZero_X` / 引理 `isZero_X`

English:
lemma isZero_X
  statement: (i : ι) (hG : IsZero (G.X i))
  proof: by
  by_cases h : c.Rel i (c.next i)
  · have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ h
    refine IsZero.of_iso ?_ (XIsoBiprod φ _ _ h)
    simp only [biprod_isZero_iff]
    exact ⟨hF _ h, hG⟩
  · exact hG.of_iso (XIso φ i h)

中文:
引理 isZero_X
  结论: (i : ι) (hG : 是零 (G.X i))
  证明: by
  by_cases h : c.Rel i (c.next i)
  · have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ h
    refine IsZero.of_iso ?_ (XIsoBiprod φ _ _ h)
    simp only [biprod_isZero_iff]
    exact ⟨hF _ h, hG⟩
  · exact hG.of_iso (XIso φ i h)

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, IsZero, IsZero.of_iso, XIsoBiprod, biprod_isZero_iff, c.Rel, c.next, hG.of_iso, hasBinaryBiproduct, of_iso
-/
lemma isZero_X (i : ι) (hG : IsZero (G.X i))
    (hF : forall (j : ι), c.Rel i j -> IsZero (F.X j)) :
    IsZero (X φ i) := by
  by_cases h : c.Rel i (c.next i)
  · have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ h
    refine IsZero.of_iso ?_ (XIsoBiprod φ _ _ h)
    simp only [biprod_isZero_iff]
    exact ⟨hF _ h, hG⟩
  · exact hG.of_iso (XIso φ i h)

/--
Definition of `sndX` / `sndX` 的定义

English:
definition sndX
  signature: (i : ι)
  body: if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (XIsoBiprod φ _ _ hi).hom ≫ biprod.snd
  else
    (XIso φ i hi).hom

中文:
定义 sndX
  签名: (i : ι)
  定义体: if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (XIsoBiprod φ _ _ hi).hom ≫ biprod.snd
  else
    (XIso φ i hi).hom

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, _smul, biprod, biprod.snd, c.Rel, c.next, hasBinaryBiproduct, leftHomologyMap
-/
noncomputable def sndX (i : ι) : X φ i ⟶ G.X i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    (XIsoBiprod φ _ _ hi).hom ≫ biprod.snd
  else
    (XIso φ i hi).hom

/--
Definition of `inrX` / `inrX` 的定义

English:
definition inrX
  signature: (i : ι)
  body: if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    biprod.inr ≫ (XIsoBiprod φ _ _ hi).inv
  else
    (XIso φ i hi).inv

@[reassoc (attr := simp)]

中文:
定义 inrX
  签名: (i : ι)
  定义体: if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    biprod.inr ≫ (XIsoBiprod φ _ _ hi).inv
  else
    (XIso φ i hi).inv

@[reassoc (attr := simp)]

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, biprod, biprod.inr, c.Rel, c.next, hasBinaryBiproduct
-/
noncomputable def inrX (i : ι) : G.X i ⟶ X φ i :=
  if hi : c.Rel i (c.next i)
  then
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    biprod.inr ≫ (XIsoBiprod φ _ _ hi).inv
  else
    (XIso φ i hi).inv

@[reassoc (attr := simp)]
/--
lemma `inrX_sndX` / 引理 `inrX_sndX`

English:
lemma inrX_sndX
  given: (i : ι)
  statement: inrX φ i ≫ sndX φ i = 𝟙 _
  proof: by
  dsimp [sndX, inrX]
  split_ifs with hi <;> simp

@[reassoc]

中文:
引理 inrX_sndX
  条件: (i : ι)
  结论: inrX φ i ≫ sndX φ i = 𝟙 _
  证明: by
  dsimp [sndX, inrX]
  split_ifs with hi <;> simp

@[reassoc]

Depends on / 依赖: split_ifs
-/
lemma inrX_sndX (i : ι) : inrX φ i ≫ sndX φ i = 𝟙 _ := by
  dsimp [sndX, inrX]
  split_ifs with hi <;> simp

@[reassoc]
/--
lemma `sndX_inrX` / 引理 `sndX_inrX`

English:
lemma sndX_inrX
  given: (i : ι) (hi : ¬ c.Rel i (c.next i))
  proof: by
  dsimp [sndX, inrX]
  simp only [dif_neg hi, Iso.hom_inv_id]

中文:
引理 sndX_inrX
  条件: (i : ι) (hi : ¬ c.关系 i (c.next i))
  证明: by
  dsimp [sndX, inrX]
  simp only [dif_neg hi, Iso.hom_inv_id]

Depends on / 依赖: Iso.hom_inv_id, dif_neg, hom_inv_id
-/
lemma sndX_inrX (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    sndX φ i ≫ inrX φ i = 𝟙 _ := by
  dsimp [sndX, inrX]
  simp only [dif_neg hi, Iso.hom_inv_id]

/--
Definition of `fstX` / `fstX` 的定义

English:
definition fstX
  signature: (i j : ι) (hij : c.Rel i j)
  body: haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  (XIsoBiprod φ i j hij).hom ≫ biprod.fst

中文:
定义 fstX
  签名: (i j : ι) (hij : c.关系 i j)
  定义体: haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  (XIsoBiprod φ i j hij).hom ≫ biprod.fst

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, biprod, biprod.fst, hasBinaryBiproduct
-/
noncomputable def fstX (i j : ι) (hij : c.Rel i j) : X φ i ⟶ F.X j :=
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  (XIsoBiprod φ i j hij).hom ≫ biprod.fst

/--
Definition of `inlX` / `inlX` 的定义

English:
definition inlX
  signature: (i j : ι) (hij : c.Rel j i)
  body: haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  biprod.inl ≫ (XIsoBiprod φ j i hij).inv

@[reassoc (attr := simp)]

中文:
定义 inlX
  签名: (i j : ι) (hij : c.关系 j i)
  定义体: haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  biprod.inl ≫ (XIsoBiprod φ j i hij).inv

@[reassoc (attr := simp)]

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, biprod, biprod.inl, hasBinaryBiproduct
-/
noncomputable def inlX (i j : ι) (hij : c.Rel j i) : F.X i ⟶ X φ j :=
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  biprod.inl ≫ (XIsoBiprod φ j i hij).inv

@[reassoc (attr := simp)]
/--
lemma `inlX_fstX` / 引理 `inlX_fstX`

English:
lemma inlX_fstX
  given: (i j : ι) (hij : c.Rel j i)
  proof: by
  simp [inlX, fstX]

@[reassoc (attr := simp)]

中文:
引理 inlX_fstX
  条件: (i j : ι) (hij : c.关系 j i)
  证明: by
  simp [inlX, fstX]

@[reassoc (attr := simp)]
-/
lemma inlX_fstX (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ fstX φ j i hij = 𝟙 _ := by
  simp [inlX, fstX]

@[reassoc (attr := simp)]
/--
lemma `inlX_sndX` / 引理 `inlX_sndX`

English:
lemma inlX_sndX
  given: (i j : ι) (hij : c.Rel j i)
  proof: by
  obtain rfl := c.next_eq' hij
  simp [inlX, sndX, dif_pos hij]

@[reassoc (attr := simp)]

中文:
引理 inlX_sndX
  条件: (i j : ι) (hij : c.关系 j i)
  证明: by
  obtain rfl := c.next_eq' hij
  simp [inlX, sndX, dif_pos hij]

@[reassoc (attr := simp)]

Depends on / 依赖: c.next_eq, dif_pos, next_eq
-/
lemma inlX_sndX (i j : ι) (hij : c.Rel j i) :
    inlX φ i j hij ≫ sndX φ j = 0 := by
  obtain rfl := c.next_eq' hij
  simp [inlX, sndX, dif_pos hij]

@[reassoc (attr := simp)]
/--
lemma `inrX_fstX` / 引理 `inrX_fstX`

English:
lemma inrX_fstX
  given: (i j : ι) (hij : c.Rel i j)
  proof: by
  obtain rfl := c.next_eq' hij
  simp [inrX, fstX, dif_pos hij]

@[reassoc (attr := simp)]

中文:
引理 inrX_fstX
  条件: (i j : ι) (hij : c.关系 i j)
  证明: by
  obtain rfl := c.next_eq' hij
  simp [inrX, fstX, dif_pos hij]

@[reassoc (attr := simp)]

Depends on / 依赖: c.next_eq, dif_pos, next_eq
-/
lemma inrX_fstX (i j : ι) (hij : c.Rel i j) :
    inrX φ i ≫ fstX φ i j hij = 0 := by
  obtain rfl := c.next_eq' hij
  simp [inrX, fstX, dif_pos hij]

@[reassoc (attr := simp)]
/--
lemma `inlX_XIsoBiprod_hom` / 引理 `inlX_XIsoBiprod_hom`

English:
lemma inlX_XIsoBiprod_hom
  given: (i j : ι) (hij : c.Rel j i)
  proof: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inlX φ i j hij ≫ (XIsoBiprod φ j i hij).hom = biprod.inl := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inlX]

@[reassoc (attr := simp)]

中文:
引理 inlX_XIsoBiprod_hom
  条件: (i j : ι) (hij : c.关系 j i)
  证明: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inlX φ i j hij ≫ (XIsoBiprod φ j i hij).hom = biprod.inl := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inlX]

@[reassoc (attr := simp)]

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, hasBinaryBiproduct
-/
lemma inlX_XIsoBiprod_hom (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inlX φ i j hij ≫ (XIsoBiprod φ j i hij).hom = biprod.inl := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inlX]

@[reassoc (attr := simp)]
/--
lemma `inl_XIsoBiprod_inv` / 引理 `inl_XIsoBiprod_inv`

English:
lemma inl_XIsoBiprod_inv
  given: (i j : ι) (hij : c.Rel j i)
  proof: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inl ≫ (XIsoBiprod φ j i hij).inv = inlX φ i j hij := by
  simp [inlX]

@[reassoc (attr := simp)]

中文:
引理 inl_XIsoBiprod_inv
  条件: (i j : ι) (hij : c.关系 j i)
  证明: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inl ≫ (XIsoBiprod φ j i hij).inv = inlX φ i j hij := by
  simp [inlX]

@[reassoc (attr := simp)]

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, hasBinaryBiproduct
-/
lemma inl_XIsoBiprod_inv (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inl ≫ (XIsoBiprod φ j i hij).inv = inlX φ i j hij := by
  simp [inlX]

@[reassoc (attr := simp)]
/--
lemma `inrX_XIsoBiprod_hom` / 引理 `inrX_XIsoBiprod_hom`

English:
lemma inrX_XIsoBiprod_hom
  given: (i j : ι) (hij : c.Rel j i)
  proof: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inrX φ j ≫ (XIsoBiprod φ j i hij).hom = biprod.inr := by
  obtain rfl := c.next_eq' hij
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inrX, XIsoBiprod, dif_pos hij]

@[reassoc (attr := simp)]

中文:
引理 inrX_XIsoBiprod_hom
  条件: (i j : ι) (hij : c.关系 j i)
  证明: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inrX φ j ≫ (XIsoBiprod φ j i hij).hom = biprod.inr := by
  obtain rfl := c.next_eq' hij
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inrX, XIsoBiprod, dif_pos hij]

@[reassoc (attr := simp)]

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, hasBinaryBiproduct
-/
lemma inrX_XIsoBiprod_hom (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    inrX φ j ≫ (XIsoBiprod φ j i hij).hom = biprod.inr := by
  obtain rfl := c.next_eq' hij
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  simp [inrX, XIsoBiprod, dif_pos hij]

@[reassoc (attr := simp)]
/--
lemma `inr_XIsoBiprod_inv` / 引理 `inr_XIsoBiprod_inv`

English:
lemma inr_XIsoBiprod_inv
  given: (i j : ι) (hij : c.Rel j i)
  proof: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inr ≫ (XIsoBiprod φ j i hij).inv = inrX φ j := by
  rw [← inrX_XIsoBiprod_hom φ i j hij]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

中文:
引理 inr_XIsoBiprod_inv
  条件: (i j : ι) (hij : c.关系 j i)
  证明: HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inr ≫ (XIsoBiprod φ j i hij).inv = inrX φ j := by
  rw [← inrX_XIsoBiprod_hom φ i j hij]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, hasBinaryBiproduct
-/
lemma inr_XIsoBiprod_inv (i j : ι) (hij : c.Rel j i) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
    biprod.inr ≫ (XIsoBiprod φ j i hij).inv = inrX φ j := by
  rw [← inrX_XIsoBiprod_hom φ i j hij]; rw [Category.assoc]; rw [Iso.hom_inv_id]; rw [Category.comp_id]

/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (i j : ι)
  body: if hij : c.Rel i j
  then
    (if hj : c.Rel j (c.next j) then -fstX φ i j hij ≫ F.d _ _ ≫ inlX φ _ _ hj else 0) +
      fstX φ i j hij ≫ φ.f j ≫ inrX φ j + sndX φ i ≫ G.d i j ≫ inrX φ j
  else
    0

中文:
定义 d
  签名: (i j : ι)
  定义体: if hij : c.Rel i j
  then
    (if hj : c.Rel j (c.next j) then -fstX φ i j hij ≫ F.d _ _ ≫ inlX φ _ _ hj else 0) +
      fstX φ i j hij ≫ φ.f j ≫ inrX φ j + sndX φ i ≫ G.d i j ≫ inrX φ j
  else
    0

Depends on / 依赖: c.Rel, c.next
-/
noncomputable def d (i j : ι) : X φ i ⟶ X φ j :=
  if hij : c.Rel i j
  then
    (if hj : c.Rel j (c.next j) then -fstX φ i j hij ≫ F.d _ _ ≫ inlX φ _ _ hj else 0) +
      fstX φ i j hij ≫ φ.f j ≫ inrX φ j + sndX φ i ≫ G.d i j ≫ inrX φ j
  else
    0

/--
lemma `ext_to_X` / 引理 `ext_to_X`

English:
lemma ext_to_X
  statement: (i j : ι) (hij : c.Rel i j) {A : C} {f g : A ⟶ X φ i}
  proof: by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_mono (XIsoBiprod φ i j hij).hom]
  apply biprod.hom_ext
  · simpa using! h₁
  · obtain rfl := c.next_eq' hij
    simpa [sndX, dif_pos hij] using! h₂

中文:
引理 ext_to_X
  结论: (i j : ι) (hij : c.关系 i j) {A : C} {f g : A ⟶ X φ i}
  证明: by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_mono (XIsoBiprod φ i j hij).hom]
  apply biprod.hom_ext
  · simpa using! h₁
  · obtain rfl := c.next_eq' hij
    simpa [sndX, dif_pos hij] using! h₂

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, biprod, biprod.hom_ext, c.next_eq, cancel_mono, dif_pos, hasBinaryBiproduct, hom_ext, next_eq
-/
lemma ext_to_X (i j : ι) (hij : c.Rel i j) {A : C} {f g : A ⟶ X φ i}
    (h₁ : f ≫ fstX φ i j hij = g ≫ fstX φ i j hij) (h₂ : f ≫ sndX φ i = g ≫ sndX φ i) :
    f = g := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_mono (XIsoBiprod φ i j hij).hom]
  apply biprod.hom_ext
  · simpa using! h₁
  · obtain rfl := c.next_eq' hij
    simpa [sndX, dif_pos hij] using! h₂

/--
lemma `ext_to_X'` / 引理 `ext_to_X'`

English:
lemma ext_to_X'
  statement: (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i}
  proof: by
  rw [← cancel_mono (XIso φ i hi).hom]
  simpa only [sndX, dif_neg hi] using h

中文:
引理 ext_to_X'
  结论: (i : ι) (hi : ¬ c.关系 i (c.next i)) {A : C} {f g : A ⟶ X φ i}
  证明: by
  rw [← cancel_mono (XIso φ i hi).hom]
  simpa only [sndX, dif_neg hi] using h

Depends on / 依赖: cancel_mono, dif_neg
-/
lemma ext_to_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : A ⟶ X φ i}
    (h : f ≫ sndX φ i = g ≫ sndX φ i) : f = g := by
  rw [← cancel_mono (XIso φ i hi).hom]
  simpa only [sndX, dif_neg hi] using h

/--
lemma `ext_from_X` / 引理 `ext_from_X`

English:
lemma ext_from_X
  statement: (i j : ι) (hij : c.Rel j i) {A : C} {f g : X φ j ⟶ A}
  proof: by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_epi (XIsoBiprod φ j i hij).inv]
  apply biprod.hom_ext'
  · simpa
  · obtain rfl := c.next_eq' hij
    simpa [-inr_XIsoBiprod_inv, -inr_XIsoBiprod_inv_assoc, inrX, dif_pos hij] using h₂

中文:
引理 ext_from_X
  结论: (i j : ι) (hij : c.关系 j i) {A : C} {f g : X φ j ⟶ A}
  证明: by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_epi (XIsoBiprod φ j i hij).inv]
  apply biprod.hom_ext'
  · simpa
  · obtain rfl := c.next_eq' hij
    simpa [-inr_XIsoBiprod_inv, -inr_XIsoBiprod_inv_assoc, inrX, dif_pos hij] using h₂

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, biprod, biprod.hom_ext, c.next_eq, cancel_epi, dif_pos, hasBinaryBiproduct, hom_ext, inr_XIsoBiprod_inv, inr_XIsoBiprod_inv_assoc, next_eq
-/
lemma ext_from_X (i j : ι) (hij : c.Rel j i) {A : C} {f g : X φ j ⟶ A}
    (h₁ : inlX φ i j hij ≫ f = inlX φ i j hij ≫ g) (h₂ : inrX φ j ≫ f = inrX φ j ≫ g) :
    f = g := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_epi (XIsoBiprod φ j i hij).inv]
  apply biprod.hom_ext'
  · simpa
  · obtain rfl := c.next_eq' hij
    simpa [-inr_XIsoBiprod_inv, -inr_XIsoBiprod_inv_assoc, inrX, dif_pos hij] using h₂

/--
lemma `ext_from_X'` / 引理 `ext_from_X'`

English:
lemma ext_from_X'
  statement: (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A}
  proof: by
  rw [← cancel_epi (XIso φ i hi).inv]
  simpa only [inrX, dif_neg hi] using h

@[reassoc]

中文:
引理 ext_from_X'
  结论: (i : ι) (hi : ¬ c.关系 i (c.next i)) {A : C} {f g : X φ i ⟶ A}
  证明: by
  rw [← cancel_epi (XIso φ i hi).inv]
  simpa only [inrX, dif_neg hi] using h

@[reassoc]

Depends on / 依赖: cancel_epi, dif_neg
-/
lemma ext_from_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : X φ i ⟶ A}
    (h : inrX φ i ≫ f = inrX φ i ≫ g) : f = g := by
  rw [← cancel_epi (XIso φ i hi).inv]
  simpa only [inrX, dif_neg hi] using h

@[reassoc]
/--
lemma `d_fstX` / 引理 `d_fstX`

English:
lemma d_fstX
  given: (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k)
  proof: by
  obtain rfl := c.next_eq' hjk
  simp [d, dif_pos hij, dif_pos hjk]

@[reassoc]

中文:
引理 d_fstX
  条件: (i j k : ι) (hij : c.关系 i j) (hjk : c.关系 j k)
  证明: by
  obtain rfl := c.next_eq' hjk
  simp [d, dif_pos hij, dif_pos hjk]

@[reassoc]

Depends on / 依赖: c.next_eq, dif_pos, next_eq
-/
lemma d_fstX (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    d φ i j ≫ fstX φ j k hjk = -fstX φ i j hij ≫ F.d j k := by
  obtain rfl := c.next_eq' hjk
  simp [d, dif_pos hij, dif_pos hjk]

@[reassoc]
/--
lemma `d_sndX` / 引理 `d_sndX`

English:
lemma d_sndX
  given: (i j : ι) (hij : c.Rel i j)
  proof: by
  dsimp [d]
  split_ifs with hij <;> simp

@[reassoc]

中文:
引理 d_sndX
  条件: (i j : ι) (hij : c.关系 i j)
  证明: by
  dsimp [d]
  split_ifs with hij <;> simp

@[reassoc]

Depends on / 依赖: split_ifs
-/
lemma d_sndX (i j : ι) (hij : c.Rel i j) :
    d φ i j ≫ sndX φ j = fstX φ i j hij ≫ φ.f j + sndX φ i ≫ G.d i j := by
  dsimp [d]
  split_ifs with hij <;> simp

@[reassoc]
/--
lemma `inlX_d` / 引理 `inlX_d`

English:
lemma inlX_d
  given: (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k)
  proof: by
  apply ext_to_X φ j k hjk
  · simp [d_fstX φ _ _ _ hij hjk]
  · simp [d_sndX φ _ _ hij]

@[reassoc]

中文:
引理 inlX_d
  条件: (i j k : ι) (hij : c.关系 i j) (hjk : c.关系 j k)
  证明: by
  apply ext_to_X φ j k hjk
  · simp [d_fstX φ _ _ _ hij hjk]
  · simp [d_sndX φ _ _ hij]

@[reassoc]

Depends on / 依赖: d_fstX, d_sndX, ext_to_X
-/
lemma inlX_d (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    inlX φ j i hij ≫ d φ i j = -F.d j k ≫ inlX φ k j hjk + φ.f j ≫ inrX φ j := by
  apply ext_to_X φ j k hjk
  · simp [d_fstX φ _ _ _ hij hjk]
  · simp [d_sndX φ _ _ hij]

@[reassoc]
/--
lemma `inlX_d'` / 引理 `inlX_d'`

English:
lemma inlX_d'
  given: (i j : ι) (hij : c.Rel i j) (hj : ¬ c.Rel j (c.next j))
  proof: by
  apply ext_to_X' _ _ hj
  simp [d_sndX φ i j hij]

中文:
引理 inlX_d'
  条件: (i j : ι) (hij : c.关系 i j) (hj : ¬ c.关系 j (c.next j))
  证明: by
  apply ext_to_X' _ _ hj
  simp [d_sndX φ i j hij]

Depends on / 依赖: d_sndX, ext_to_X
-/
lemma inlX_d' (i j : ι) (hij : c.Rel i j) (hj : ¬ c.Rel j (c.next j)) :
    inlX φ j i hij ≫ d φ i j = φ.f j ≫ inrX φ j := by
  apply ext_to_X' _ _ hj
  simp [d_sndX φ i j hij]

/--
lemma `shape` / 引理 `shape`

English:
lemma shape
  given: (i j : ι) (hij : ¬ c.Rel i j)
  proof: dif_neg hij

@[reassoc (attr := simp)]

中文:
引理 shape
  条件: (i j : ι) (hij : ¬ c.关系 i j)
  证明: dif_neg hij

@[reassoc (attr := simp)]

Depends on / 依赖: dif_neg
-/
lemma shape (i j : ι) (hij : ¬ c.Rel i j) :
    d φ i j = 0 :=
  dif_neg hij

@[reassoc (attr := simp)]
/--
lemma `inrX_d` / 引理 `inrX_d`

English:
lemma inrX_d
  given: (i j : ι)
  proof: by
  by_cases hij : c.Rel i j
  · by_cases hj : c.Rel j (c.next j)
    · apply ext_to_X _ _ _ hj
      · simp [d_fstX φ _ _ _ hij]
      · simp [d_sndX φ _ _ hij]
    · apply ext_to_X' _ _ hj
      simp [d_sndX φ _ _ hij]
  · rw [shape φ _ _ hij, G.shape _ _ hij, zero_comp, comp_zero]

中文:
引理 inrX_d
  条件: (i j : ι)
  证明: by
  by_cases hij : c.Rel i j
  · by_cases hj : c.Rel j (c.next j)
    · apply ext_to_X _ _ _ hj
      · simp [d_fstX φ _ _ _ hij]
      · simp [d_sndX φ _ _ hij]
    · apply ext_to_X' _ _ hj
      simp [d_sndX φ _ _ hij]
  · rw [shape φ _ _ hij, G.shape _ _ hij, zero_comp, comp_zero]

Depends on / 依赖: G.shape, c.Rel, c.next, comp_zero, d_fstX, d_sndX, ext_to_X, zero_comp
-/
lemma inrX_d (i j : ι) :
    inrX φ i ≫ d φ i j = G.d i j ≫ inrX φ j := by
  by_cases hij : c.Rel i j
  · by_cases hj : c.Rel j (c.next j)
    · apply ext_to_X _ _ _ hj
      · simp [d_fstX φ _ _ _ hij]
      · simp [d_sndX φ _ _ hij]
    · apply ext_to_X' _ _ hj
      simp [d_sndX φ _ _ hij]
  · rw [shape φ _ _ hij, G.shape _ _ hij, zero_comp, comp_zero]

end homotopyCofiber

/-- The homotopy cofiber of a morphism of homological complexes,
also known as the mapping cone. -/
@[simps, implicit_reducible]
/--
Definition of `homotopyCofiber` / `homotopyCofiber` 的定义

English:
definition homotopyCofiber
  signature: : HomologicalComplex C c where
  body: homotopyCofiber.X φ i
  d i j := homotopyCofiber.d φ i j
  shape i j hij := homotopyCofiber.shape φ i j hij
  d_comp_d' i j k hij hjk := by
    apply homotopyCofiber.ext_from_X φ j i hij
    · simp only [comp_zero, homotopyCofiber.inlX_d_assoc φ i j k hij hjk,
        add_comp, assoc, homotopyCofibe

中文:
定义 homotopyCofiber
  签名: : 同调复形 C c where
  定义体: homotopyCofiber.X φ i
  d i j := homotopyCofiber.d φ i j
  shape i j hij := homotopyCofiber.shape φ i j hij
  d_comp_d' i j k hij hjk := by
    apply homotopyCofiber.ext_from_X φ j i hij
    · simp only [comp_zero, homotopyCofiber.inlX_d_assoc φ i j k hij hjk,
        add_comp, assoc, homotopyCofibe

Depends on / 依赖: homotopyCofiber, homotopyCofiber.X
-/
noncomputable def homotopyCofiber : HomologicalComplex C c where
  X i := homotopyCofiber.X φ i
  d i j := homotopyCofiber.d φ i j
  shape i j hij := homotopyCofiber.shape φ i j hij
  d_comp_d' i j k hij hjk := by
    apply homotopyCofiber.ext_from_X φ j i hij
    · simp only [comp_zero, homotopyCofiber.inlX_d_assoc φ i j k hij hjk,
        add_comp, assoc, homotopyCofiber.inrX_d, Hom.comm_assoc, neg_comp]
      by_cases hk : c.Rel k (c.next k)
      · simp [homotopyCofiber.inlX_d φ j k _ hjk hk]
      · simp [homotopyCofiber.inlX_d' φ j k hjk hk]
    · simp

namespace homotopyCofiber

set_option backward.defeqAttrib.useBackward true in
/-- The right inclusion `G ⟶ homotopyCofiber φ`. -/
@[simps!]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : G ⟶ homotopyCofiber φ where
  body: inrX φ i

中文:
定义 inr
  签名: : G ⟶ homotopyCofiber φ where
  定义体: inrX φ i
-/
noncomputable def inr : G ⟶ homotopyCofiber φ where
  f i := inrX φ i

section

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `inrCompHomotopy` / `inrCompHomotopy` 的定义

English:
definition inrCompHomotopy
  signature: (hc : forall j, exists i, c.Rel i j)
  body: if hij : c.Rel j i then inlX φ i j hij else 0
  zero _ _ hij := dif_neg hij
  comm j := by
    obtain ⟨i, hij⟩ := hc j
    rw [prevD_eq _ hij]; rw [dif_pos hij]
    by_cases hj : c.Rel j (c.next j)
    · simp only [comp_f, homotopyCofiber_d, zero_f, add_zero,
        inlX_d φ i j _ hij hj, dNext_eq 

中文:
定义 inrCompHomotopy
  签名: (hc : 对任意 j, 存在 i, c.关系 i j)
  定义体: if hij : c.Rel j i then inlX φ i j hij else 0
  zero _ _ hij := dif_neg hij
  comm j := by
    obtain ⟨i, hij⟩ := hc j
    rw [prevD_eq _ hij]; rw [dif_pos hij]
    by_cases hj : c.Rel j (c.next j)
    · simp only [comp_f, homotopyCofiber_d, zero_f, add_zero,
        inlX_d φ i j _ hij hj, dNext_eq 

Depends on / 依赖: add_neg_cancel_left, add_zero, c.Rel, c.next, comp_f, dNext_eq, dNext_eq_zero, dif_neg, dif_pos, homotopyCofiber_d, inlX_d, inr_f, prevD_eq, zero_add, zero_f
-/
noncomputable def inrCompHomotopy (hc : forall j, exists i, c.Rel i j) :
    Homotopy (φ ≫ inr φ) 0 where
  hom i j :=
    if hij : c.Rel j i then inlX φ i j hij else 0
  zero _ _ hij := dif_neg hij
  comm j := by
    obtain ⟨i, hij⟩ := hc j
    rw [prevD_eq _ hij]; rw [dif_pos hij]
    by_cases hj : c.Rel j (c.next j)
    · simp only [comp_f, homotopyCofiber_d, zero_f, add_zero,
        inlX_d φ i j _ hij hj, dNext_eq _ hj, dif_pos hj,
        add_neg_cancel_left, inr_f]
    · rw [dNext_eq_zero _ _ hj, zero_add, zero_f, add_zero, homotopyCofiber_d,
        inlX_d' _ _ _ _ hj, comp_f, inr_f]

variable (hc : forall j, exists i, c.Rel i j)

/--
lemma `inrCompHomotopy_hom` / 引理 `inrCompHomotopy_hom`

English:
lemma inrCompHomotopy_hom
  given: (i j : ι) (hij : c.Rel j i)
  proof: dif_pos hij

中文:
引理 inrCompHomotopy_hom
  条件: (i j : ι) (hij : c.关系 j i)
  证明: dif_pos hij

Depends on / 依赖: dif_pos
-/
lemma inrCompHomotopy_hom (i j : ι) (hij : c.Rel j i) :
    (inrCompHomotopy φ hc).hom i j = inlX φ i j hij := dif_pos hij

/--
lemma `inrCompHomotopy_hom_eq_zero` / 引理 `inrCompHomotopy_hom_eq_zero`

English:
lemma inrCompHomotopy_hom_eq_zero
  given: (i j : ι) (hij : ¬ c.Rel j i)
  proof: dif_neg hij

中文:
引理 inrCompHomotopy_hom_eq_zero
  条件: (i j : ι) (hij : ¬ c.关系 j i)
  证明: dif_neg hij

Depends on / 依赖: dif_neg
-/
lemma inrCompHomotopy_hom_eq_zero (i j : ι) (hij : ¬ c.Rel j i) :
    (inrCompHomotopy φ hc).hom i j = 0 := dif_neg hij

end

section

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: :
  body: if hj : c.Rel j (c.next j)
    then fstX φ j _ hj ≫ hα.hom _ j + sndX φ j ≫ α.f j
    else sndX φ j ≫ α.f j
  comm' j k hjk := by
    obtain rfl := c.next_eq' hjk
    simp [dif_pos hjk]
    have H := hα.comm (c.next j)
    simp only [comp_f, zero_f, add_zero, prevD_eq _ hjk] at H
    split_ifs with 

中文:
定义 desc
  签名: :
  定义体: if hj : c.Rel j (c.next j)
    then fstX φ j _ hj ≫ hα.hom _ j + sndX φ j ≫ α.f j
    else sndX φ j ≫ α.f j
  comm' j k hjk := by
    obtain rfl := c.next_eq' hjk
    simp [dif_pos hjk]
    have H := hα.comm (c.next j)
    simp only [comp_f, zero_f, add_zero, prevD_eq _ hjk] at H
    split_ifs with 

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, _apply, add_comp, add_zero, c.Rel, c.next, c.next_eq, comp_add, comp_f, dNext_eq_zero, d_fstX_assoc, d_sndX_assoc, dif_pos, neg_comp, next_eq, prevD_eq, split_ifs, zero_add, zero_f
-/
noncomputable def desc :
    homotopyCofiber φ ⟶ K where
  f j :=
    if hj : c.Rel j (c.next j)
    then fstX φ j _ hj ≫ hα.hom _ j + sndX φ j ≫ α.f j
    else sndX φ j ≫ α.f j
  comm' j k hjk := by
    obtain rfl := c.next_eq' hjk
    simp [dif_pos hjk]
    have H := hα.comm (c.next j)
    simp only [comp_f, zero_f, add_zero, prevD_eq _ hjk] at H
    split_ifs with hj
    · simp only [comp_add, d_sndX_assoc _ _ _ hjk, add_comp, assoc, H,
        d_fstX_assoc _ _ _ _ hjk, neg_comp, dNext, AddMonoidHom.mk'_apply]
      abel
    · simp only [d_sndX_assoc _ _ _ hjk, add_comp, assoc, H, dNext_eq_zero _ _ hj, zero_add]

/--
lemma `desc_f` / 引理 `desc_f`

English:
lemma desc_f
  given: (j k : ι) (hjk : c.Rel j k)
  proof: by
  obtain rfl := c.next_eq' hjk
  apply dif_pos hjk

中文:
引理 desc_f
  条件: (j k : ι) (hjk : c.关系 j k)
  证明: by
  obtain rfl := c.next_eq' hjk
  apply dif_pos hjk

Depends on / 依赖: c.next_eq, dif_pos, next_eq
-/
lemma desc_f (j k : ι) (hjk : c.Rel j k) :
    (desc φ α hα).f j = fstX φ j _ hjk ≫ hα.hom _ j + sndX φ j ≫ α.f j := by
  obtain rfl := c.next_eq' hjk
  apply dif_pos hjk

/--
lemma `desc_f'` / 引理 `desc_f'`

English:
lemma desc_f'
  given: (j : ι) (hj : ¬ c.Rel j (c.next j))
  proof: by
  apply dif_neg hj

中文:
引理 desc_f'
  条件: (j : ι) (hj : ¬ c.关系 j (c.next j))
  证明: by
  apply dif_neg hj

Depends on / 依赖: dif_neg
-/
lemma desc_f' (j : ι) (hj : ¬ c.Rel j (c.next j)) :
    (desc φ α hα).f j = sndX φ j ≫ α.f j := by
  apply dif_neg hj

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `inlX_desc_f` / 引理 `inlX_desc_f`

English:
lemma inlX_desc_f
  given: (i j : ι) (hjk : c.Rel j i)
  proof: by
  obtain rfl := c.next_eq' hjk
  dsimp [desc]
  rw [dif_pos hjk]; rw [comp_add]; rw [inlX_fstX_assoc]; rw [inlX_sndX_assoc]; rw [zero_comp]; rw [add_zero]

中文:
引理 inlX_desc_f
  条件: (i j : ι) (hjk : c.关系 j i)
  证明: by
  obtain rfl := c.next_eq' hjk
  dsimp [desc]
  rw [dif_pos hjk]; rw [comp_add]; rw [inlX_fstX_assoc]; rw [inlX_sndX_assoc]; rw [zero_comp]; rw [add_zero]

Depends on / 依赖: add_zero, c.next_eq, comp_add, dif_pos, inlX_fstX_assoc, inlX_sndX_assoc, next_eq, zero_comp
-/
lemma inlX_desc_f (i j : ι) (hjk : c.Rel j i) :
    inlX φ i j hjk ≫ (desc φ α hα).f j = hα.hom i j := by
  obtain rfl := c.next_eq' hjk
  dsimp [desc]
  rw [dif_pos hjk]; rw [comp_add]; rw [inlX_fstX_assoc]; rw [inlX_sndX_assoc]; rw [zero_comp]; rw [add_zero]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inrX_desc_f` / 引理 `inrX_desc_f`

English:
lemma inrX_desc_f
  given: (i : ι)
  proof: by
  dsimp [desc]
  split_ifs <;> simp

中文:
引理 inrX_desc_f
  条件: (i : ι)
  证明: by
  dsimp [desc]
  split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
lemma inrX_desc_f (i : ι) :
    inrX φ i ≫ (desc φ α hα).f i = α.f i := by
  dsimp [desc]
  split_ifs <;> simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inr_desc` / 引理 `inr_desc`

English:
lemma inr_desc
  proof: by cat_disch

中文:
引理 inr_desc
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma inr_desc :
    inr φ ≫ desc φ α hα = α := by cat_disch

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inrCompHomotopy_hom_desc_hom` / 引理 `inrCompHomotopy_hom_desc_hom`

English:
lemma inrCompHomotopy_hom_desc_hom
  given: (hc : forall j, exists i, c.Rel i j) (i j : ι)
  proof: by
  by_cases hij : c.Rel j i
  · dsimp
    simp only [inrCompHomotopy_hom φ hc i j hij, desc_f φ α hα _ _ hij,
      comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
  · simp only [Homotopy.zero _ _ _ hij, zero_comp]

中文:
引理 inrCompHomotopy_hom_desc_hom
  条件: (hc : 对任意 j, 存在 i, c.关系 i j) (i j : ι)
  证明: by
  by_cases hij : c.Rel j i
  · dsimp
    simp only [inrCompHomotopy_hom φ hc i j hij, desc_f φ α hα _ _ hij,
      comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
  · simp only [Homotopy.zero _ _ _ hij, zero_comp]

Depends on / 依赖: Homotopy, Homotopy.zero, add_zero, c.Rel, comp_add, desc_f, inlX_fstX_assoc, inlX_sndX_assoc, inrCompHomotopy_hom, zero_comp
-/
lemma inrCompHomotopy_hom_desc_hom (hc : forall j, exists i, c.Rel i j) (i j : ι) :
    (inrCompHomotopy φ hc).hom i j ≫ (desc φ α hα).f j = hα.hom i j := by
  by_cases hij : c.Rel j i
  · dsimp
    simp only [inrCompHomotopy_hom φ hc i j hij, desc_f φ α hα _ _ hij,
      comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
  · simp only [Homotopy.zero _ _ _ hij, zero_comp]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `eq_desc` / 引理 `eq_desc`

English:
lemma eq_desc
  given: (f : homotopyCofiber φ ⟶ K) (hc : forall j, exists i, c.Rel i j)
  proof: by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ _ _ hj
    · simp [inrCompHomotopy_hom _ _ _ _ hj]
    · simp
  · apply ext_from_X' φ _ hj
    simp

中文:
引理 eq_desc
  条件: (f : homotopyCofiber φ ⟶ K) (hc : 对任意 j, 存在 i, c.关系 i j)
  证明: by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ _ _ hj
    · simp [inrCompHomotopy_hom _ _ _ _ hj]
    · simp
  · apply ext_from_X' φ _ hj
    simp

Depends on / 依赖: c.Rel, c.next, ext_from_X, inrCompHomotopy_hom
-/
lemma eq_desc (f : homotopyCofiber φ ⟶ K) (hc : forall j, exists i, c.Rel i j) :
    f = desc φ (inr φ ≫ f) (Homotopy.trans (Homotopy.ofEq (by simp))
      (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))) := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply ext_from_X φ _ _ hj
    · simp [inrCompHomotopy_hom _ _ _ _ hj]
    · simp
  · apply ext_from_X' φ _ hj
    simp

end

omit [DecidableRel c.Rel] in
/--
lemma `descSigma_ext_iff` / 引理 `descSigma_ext_iff`

English:
lemma descSigma_ext_iff
  statement: {φ : F ⟶ G} {K : HomologicalComplex C c}
  proof: by
  constructor
  · rintro rfl
    tauto
  · obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    rintro ⟨rfl, h⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · simp only [Homotopy.zero _ _ _ hij]

中文:
引理 descSigma_ext_iff
  结论: {φ : F ⟶ G} {K : 同调复形 C c}
  证明: by
  constructor
  · rintro rfl
    tauto
  · obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    rintro ⟨rfl, h⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · simp only [Homotopy.zero _ _ _ hij]

Depends on / 依赖: Homotopy, Homotopy.zero, Sigma.mk.inj_iff, c.Rel, heq_eq_eq, inj_iff, true_and
-/
lemma descSigma_ext_iff {φ : F ⟶ G} {K : HomologicalComplex C c}
    (x y : Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) :
    x = y ↔ x.1 = y.1 ∧ (forall (i j : ι) (_ : c.Rel j i), x.2.hom i j = y.2.hom i j) := by
  constructor
  · rintro rfl
    tauto
  · obtain ⟨x₁, x₂⟩ := x
    obtain ⟨y₁, y₂⟩ := y
    rintro ⟨rfl, h⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    ext i j
    by_cases hij : c.Rel j i
    · exact h _ _ hij
    · simp only [Homotopy.zero _ _ _ hij]

/--
Definition of `descEquiv` / `descEquiv` 的定义

English:
definition descEquiv
  signature: (K : HomologicalComplex C c) (hc : forall j, exists i, c.Rel i j)
  body: fun ⟨α, hα⟩ => desc φ α hα
  invFun f := ⟨inr φ ≫ f, Homotopy.trans (Homotopy.ofEq (by simp))
    (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))⟩
  right_inv f := (eq_desc φ f hc).symm
  left_inv := fun ⟨α, hα⟩ => by
    rw [descSigma_ext_iff]
    cat_disch

中文:
定义 descEquiv
  签名: (K : 同调复形 C c) (hc : 对任意 j, 存在 i, c.关系 i j)
  定义体: fun ⟨α, hα⟩ => desc φ α hα
  invFun f := ⟨inr φ ≫ f, Homotopy.trans (Homotopy.ofEq (by simp))
    (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))⟩
  right_inv f := (eq_desc φ f hc).symm
  left_inv := fun ⟨α, hα⟩ => by
    rw [descSigma_ext_iff]
    cat_disch
-/
noncomputable def descEquiv (K : HomologicalComplex C c) (hc : forall j, exists i, c.Rel i j) :
    (Σ (α : G ⟶ K), Homotopy (φ ≫ α) 0) ≃ (homotopyCofiber φ ⟶ K) where
  toFun := fun ⟨α, hα⟩ => desc φ α hα
  invFun f := ⟨inr φ ≫ f, Homotopy.trans (Homotopy.ofEq (by simp))
    (((inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))⟩
  right_inv f := (eq_desc φ f hc).symm
  left_inv := fun ⟨α, hα⟩ => by
    rw [descSigma_ext_iff]
    cat_disch

section

variable {F' F'' G' G'' : HomologicalComplex C c} (φ' : F' ⟶ G') (φ'' : F'' ⟶ G'')
  [HasHomotopyCofiber φ'] [HasHomotopyCofiber φ'']
  (H : forall (j : ι), exists i, c.Rel i j)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapArrowHom` / `mapArrowHom` 的定义

English:
definition mapArrowHom
  signature: (α : Arrow.mk φ ⟶ Arrow.mk φ')
  body: desc _ (α.right ≫ homotopyCofiber.inr φ')
    ((Homotopy.ofEq (by
        simp [reassoc_of% dsimp% α.w])).trans (((inrCompHomotopy φ' H).compLeft α.left).trans
      (Homotopy.ofEq (by simp))))

中文:
定义 mapArrowHom
  签名: (α : 箭头.mk φ ⟶ 箭头.mk φ')
  定义体: desc _ (α.right ≫ homotopyCofiber.inr φ')
    ((Homotopy.ofEq (by
        simp [reassoc_of% dsimp% α.w])).trans (((inrCompHomotopy φ' H).compLeft α.left).trans
      (Homotopy.ofEq (by simp))))

Depends on / 依赖: Homotopy, Homotopy.ofEq, compLeft, homotopyCofiber, homotopyCofiber.inr, inrCompHomotopy, reassoc_of
-/
noncomputable def mapArrowHom (α : Arrow.mk φ ⟶ Arrow.mk φ') :
    homotopyCofiber φ ⟶ homotopyCofiber φ' :=
  desc _ (α.right ≫ homotopyCofiber.inr φ')
    ((Homotopy.ofEq (by
        simp [reassoc_of% dsimp% α.w])).trans (((inrCompHomotopy φ' H).compLeft α.left).trans
      (Homotopy.ofEq (by simp))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `mapArrowHom_id` / 引理 `mapArrowHom_id`

English:
lemma mapArrowHom_id
  statement: mapArrowHom φ φ H (𝟙 _) = 𝟙 _
  proof: by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

中文:
引理 mapArrowHom_id
  结论: mapArrowHom φ φ H (𝟙 _) = 𝟙 _
  证明: by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

Depends on / 依赖: all_goals, c.Rel, c.next, desc_f, ext_to_X, inrCompHomotopy_hom, mapArrowHom
-/
lemma mapArrowHom_id : mapArrowHom φ φ H (𝟙 _) = 𝟙 _ := by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapArrowHom_comp` / 引理 `mapArrowHom_comp`

English:
lemma mapArrowHom_comp
  proof: by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

中文:
引理 mapArrowHom_comp
  证明: by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

Depends on / 依赖: all_goals, c.Rel, c.next, desc_f, ext_to_X, inrCompHomotopy_hom, mapArrowHom
-/
lemma mapArrowHom_comp
    (α : Arrow.mk φ ⟶ Arrow.mk φ') (β : Arrow.mk φ' ⟶ Arrow.mk φ'') :
    mapArrowHom φ φ'' H (α ≫ β) = mapArrowHom φ φ' H α ≫ mapArrowHom φ' φ'' H β := by
  ext i
  dsimp
  by_cases hi : c.Rel i (c.next i)
  · refine ext_to_X _ _ _ hi ?_ ?_
    all_goals simp [mapArrowHom, desc_f _ _ _ _ _ hi, inrCompHomotopy_hom _ _ _ _ hi]
  · exact ext_to_X' _ _ hi (by simp [mapArrowHom, desc_f' _ _ _ _ hi])

/-- The isomorphism between homotopy cofibers that is induced by an
isomorphism of arrows. -/
@[simps]
/--
Definition of `mapArrowIso` / `mapArrowIso` 的定义

English:
definition mapArrowIso
  signature: (α : Arrow.mk φ ≅ Arrow.mk φ')
  body: mapArrowHom φ φ' H α.hom
  inv := mapArrowHom φ' φ H α.inv
  hom_inv_id := by rw [← mapArrowHom_comp, Iso.hom_inv_id, mapArrowHom_id]
  inv_hom_id := by rw [← mapArrowHom_comp, Iso.inv_hom_id, mapArrowHom_id]

中文:
定义 mapArrowIso
  签名: (α : 箭头.mk φ ≅ 箭头.mk φ')
  定义体: mapArrowHom φ φ' H α.hom
  inv := mapArrowHom φ' φ H α.inv
  hom_inv_id := by rw [← mapArrowHom_comp, Iso.hom_inv_id, mapArrowHom_id]
  inv_hom_id := by rw [← mapArrowHom_comp, Iso.inv_hom_id, mapArrowHom_id]

Depends on / 依赖: mapArrowHom
-/
noncomputable def mapArrowIso (α : Arrow.mk φ ≅ Arrow.mk φ') :
    homotopyCofiber φ ≅ homotopyCofiber φ' where
  hom := mapArrowHom φ φ' H α.hom
  inv := mapArrowHom φ' φ H α.inv
  hom_inv_id := by rw [← mapArrowHom_comp, Iso.hom_inv_id, mapArrowHom_id]
  inv_hom_id := by rw [← mapArrowHom_comp, Iso.inv_hom_id, mapArrowHom_id]

end

section

variable {D : Type*} [Category* D] [Preadditive D] (H : C ⥤ D) [H.Additive]
  [HasHomotopyCofiber ((H.mapHomologicalComplex c).map φ)]

/--
Definition of `mapHomologicalComplexObjXIso` / `mapHomologicalComplexObjXIso` 的定义

English:
definition mapHomologicalComplexObjXIso
  signature: (i : ι)
  body: if hi : c.Rel i (c.next i)
  then by
    haveI := preservesBinaryBiproducts_of_preservesBiproducts H
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    haveI := HasHomotopyCofiber.hasBinaryBiproduct ((H.mapHomologicalComplex c).map φ) _ _ hi
    exact H.mapIso (homotopyCofiber.XIsoBipro

中文:
定义 mapHomologicalComplexObjXIso
  签名: (i : ι)
  定义体: if hi : c.Rel i (c.next i)
  then by
    haveI := preservesBinaryBiproducts_of_preservesBiproducts H
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    haveI := HasHomotopyCofiber.hasBinaryBiproduct ((H.mapHomologicalComplex c).map φ) _ _ hi
    exact H.mapIso (homotopyCofiber.XIsoBipro

Depends on / 依赖: H.mapBiprod, H.mapHomologicalComplex, H.mapIso, HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, c.Rel, c.next, hasBinaryBiproduct, homotopyCofiber, homotopyCofiber.XIso, homotopyCofiber.XIsoBiprod, mapBiprod, mapHomologicalComplex, mapIso, preservesBinaryBiproducts_of_preservesBiproducts
-/
noncomputable def mapHomologicalComplexObjXIso (i : ι) :
    H.obj ((homotopyCofiber φ).X i) ≅
      (homotopyCofiber ((H.mapHomologicalComplex c).map φ)).X i :=
  if hi : c.Rel i (c.next i)
  then by
    haveI := preservesBinaryBiproducts_of_preservesBiproducts H
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hi
    haveI := HasHomotopyCofiber.hasBinaryBiproduct ((H.mapHomologicalComplex c).map φ) _ _ hi
    exact H.mapIso (homotopyCofiber.XIsoBiprod φ _ _ hi) ≪≫ H.mapBiprod _ _ ≪≫
      (homotopyCofiber.XIsoBiprod ((H.mapHomologicalComplex c).map φ) _ _ hi).symm
  else H.mapIso (homotopyCofiber.XIso φ i hi) ≪≫
    (homotopyCofiber.XIso ((H.mapHomologicalComplex c).map φ) i hi).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inlX_mapHomologicalComplexObjXIso_inv` / 引理 `inlX_mapHomologicalComplexObjXIso_inv`

English:
lemma inlX_mapHomologicalComplexObjXIso_inv
  proof: by
  obtain rfl := c.next_eq' hij
  simp [mapHomologicalComplexObjXIso, dif_pos hij, ← Functor.map_comp]

中文:
引理 inlX_mapHomologicalComplexObjXIso_inv
  证明: by
  obtain rfl := c.next_eq' hij
  simp [mapHomologicalComplexObjXIso, dif_pos hij, ← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, c.next_eq, dif_pos, mapHomologicalComplexObjXIso, map_comp, next_eq
-/
lemma inlX_mapHomologicalComplexObjXIso_inv
    (i j : ι) (hij : c.Rel j i) :
    inlX ((H.mapHomologicalComplex c).map φ) i j hij ≫
      (mapHomologicalComplexObjXIso φ H j).inv = H.map (inlX φ i j hij) := by
  obtain rfl := c.next_eq' hij
  simp [mapHomologicalComplexObjXIso, dif_pos hij, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inrX_mapHomologicalComplexObjXIso_inv` / 引理 `inrX_mapHomologicalComplexObjXIso_inv`

English:
lemma inrX_mapHomologicalComplexObjXIso_inv
  given: (i : ι)
  proof: by
  by_cases hi : c.Rel i (c.next i)
  · simp [mapHomologicalComplexObjXIso, dif_pos hi, ← Functor.map_comp]
  · dsimp [mapHomologicalComplexObjXIso, XIso, inrX]
    simp [dif_neg hi]

中文:
引理 inrX_mapHomologicalComplexObjXIso_inv
  条件: (i : ι)
  证明: by
  by_cases hi : c.Rel i (c.next i)
  · simp [mapHomologicalComplexObjXIso, dif_pos hi, ← Functor.map_comp]
  · dsimp [mapHomologicalComplexObjXIso, XIso, inrX]
    simp [dif_neg hi]

Depends on / 依赖: Functor, Functor.map_comp, LeftHomologyMapData, LeftHomologyMapData.neg_, c.Rel, c.next, dif_neg, dif_pos, leftHomologyMap, mapHomologicalComplexObjXIso, map_comp, neg.leftHomologyMap
-/
lemma inrX_mapHomologicalComplexObjXIso_inv (i : ι) :
    inrX ((H.mapHomologicalComplex c).map φ) i ≫
      (mapHomologicalComplexObjXIso φ H i).inv = H.map (inrX φ i) := by
  by_cases hi : c.Rel i (c.next i)
  · simp [mapHomologicalComplexObjXIso, dif_pos hi, ← Functor.map_comp]
  · dsimp [mapHomologicalComplexObjXIso, XIso, inrX]
    simp [dif_neg hi]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `map_inrX_mapHomologicalComplexObjXIso_hom` / 引理 `map_inrX_mapHomologicalComplexObjXIso_hom`

English:
lemma map_inrX_mapHomologicalComplexObjXIso_hom
  given: (i : ι)
  proof: by
  rw [← inrX_mapHomologicalComplexObjXIso_inv_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 map_inrX_mapHomologicalComplexObjXIso_hom
  条件: (i : ι)
  证明: by
  rw [← inrX_mapHomologicalComplexObjXIso_inv_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, LeftHomologyMapData, LeftHomologyMapData.neg_, comp_id, cyclesMap, inrX_mapHomologicalComplexObjXIso_inv_assoc, inv_hom_id, neg.cyclesMap
-/
lemma map_inrX_mapHomologicalComplexObjXIso_hom (i : ι) :
    H.map (inrX φ i) ≫ (mapHomologicalComplexObjXIso φ H i).hom =
      inrX ((H.mapHomologicalComplex c).map φ) i := by
  rw [← inrX_mapHomologicalComplexObjXIso_inv_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapHomologicalComplexObjIso` / `mapHomologicalComplexObjIso` 的定义

English:
definition mapHomologicalComplexObjIso
  signature: :
  body: Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun i => (mapHomologicalComplexObjXIso φ H i).symm)
    (fun i j hij => by
      dsimp
      apply ext_from_X _ _ _ hij
      · by_cases hj : c.Rel j (c.next j)
        · simp [← Functor.map_comp, inlX_d _ _ _ _ _ hj, inlX_d_assoc _ _ _ _ _ hj]
 

中文:
定义 mapHomologicalComplexObjIso
  签名: :
  定义体: Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun i => (mapHomologicalComplexObjXIso φ H i).symm)
    (fun i j hij => by
      dsimp
      apply ext_from_X _ _ _ hij
      · by_cases hj : c.Rel j (c.next j)
        · simp [← Functor.map_comp, inlX_d _ _ _ _ _ hj, inlX_d_assoc _ _ _ _ _ hj]
 

Depends on / 依赖: Functor, Functor.map_comp, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.symm, LeftHomologyMapData, LeftHomologyMapData.add_, _assoc, c.Rel, c.next, ext_from_X, inlX_d, inlX_d_assoc, isoOfComponents, leftHomologyMap, mapHomologicalComplexObjXIso, map_comp
-/
noncomputable def mapHomologicalComplexObjIso :
    (H.mapHomologicalComplex c).obj (homotopyCofiber φ) ≅
      homotopyCofiber ((H.mapHomologicalComplex c).map φ) :=
  Iso.symm (HomologicalComplex.Hom.isoOfComponents
    (fun i => (mapHomologicalComplexObjXIso φ H i).symm)
    (fun i j hij => by
      dsimp
      apply ext_from_X _ _ _ hij
      · by_cases hj : c.Rel j (c.next j)
        · simp [← Functor.map_comp, inlX_d _ _ _ _ _ hj, inlX_d_assoc _ _ _ _ _ hj]
        · simp [← Functor.map_comp, inlX_d' _ _ _ _ hj, inlX_d'_assoc _ _ _ _ hj]
      · simp [← Functor.map_comp]))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_mapHomologicalComplexObjIso_hom` / 引理 `inr_mapHomologicalComplexObjIso_hom`

English:
lemma inr_mapHomologicalComplexObjIso_hom
  proof: by
  ext
  simp [mapHomologicalComplexObjIso]

中文:
引理 inr_mapHomologicalComplexObjIso_hom
  证明: by
  ext
  simp [mapHomologicalComplexObjIso]

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.add_, cyclesMap, mapHomologicalComplexObjIso
-/
lemma inr_mapHomologicalComplexObjIso_hom :
    (H.mapHomologicalComplex c).map (inr φ) ≫
      (mapHomologicalComplexObjIso φ H).hom = inr _ := by
  ext
  simp [mapHomologicalComplexObjIso]

end

end homotopyCofiber

section

variable (K)
variable [forall i, HasBinaryBiproduct (K.X i) (K.X i)]

/--
Definition of `HasCylinder` / `HasCylinder` 的定义

English:
abbreviation HasCylinder
  signature: : Prop
  body: HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

中文:
缩写 HasCylinder
  签名: : 命题
  定义体: HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

Depends on / 依赖: HasHomotopyCofiber, _add, _neg, biprod, biprod.lift, leftHomologyMap, sub_eq_add_neg
-/
abbrev HasCylinder : Prop := HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

variable [K.HasCylinder]

/--
Definition of `cylinder` / `cylinder` 的定义

English:
abbreviation cylinder
  body: homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

中文:
缩写 cylinder
  定义体: homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

Depends on / 依赖: _add, _neg, biprod, biprod.lift, cyclesMap, homotopyCofiber, sub_eq_add_neg
-/
noncomputable abbrev cylinder := homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))

namespace cylinder

/--
Definition of `ι₀` / `ι₀` 的定义

English:
definition ι₀
  signature: : K ⟶ K.cylinder
  body: biprod.inl ≫ homotopyCofiber.inr _

中文:
定义 ι₀
  签名: : K ⟶ K.cylinder
  定义体: biprod.inl ≫ homotopyCofiber.inr _

Depends on / 依赖: biprod, biprod.inl, homotopyCofiber, homotopyCofiber.inr
-/
noncomputable def ι₀ : K ⟶ K.cylinder := biprod.inl ≫ homotopyCofiber.inr _

/--
Definition of `ι₁` / `ι₁` 的定义

English:
definition ι₁
  signature: : K ⟶ K.cylinder
  body: biprod.inr ≫ homotopyCofiber.inr _

中文:
定义 ι₁
  签名: : K ⟶ K.cylinder
  定义体: biprod.inr ≫ homotopyCofiber.inr _

Depends on / 依赖: biprod, biprod.inr, homotopyCofiber, homotopyCofiber.inr
-/
noncomputable def ι₁ : K ⟶ K.cylinder := biprod.inr ≫ homotopyCofiber.inr _

variable {K}

section

variable (φ₀ φ₁ : K ⟶ F) (h : Homotopy φ₀ φ₁)

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : K.cylinder ⟶ F
  body: homotopyCofiber.desc _ (biprod.desc φ₀ φ₁)
    (Homotopy.trans (Homotopy.ofEq (by
      simp only [biprod.lift_desc, id_comp, neg_comp, sub_eq_add_neg]))
      ((Homotopy.equivSubZero h)))

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: : K.cylinder ⟶ F
  定义体: homotopyCofiber.desc _ (biprod.desc φ₀ φ₁)
    (Homotopy.trans (Homotopy.ofEq (by
      simp only [biprod.lift_desc, id_comp, neg_comp, sub_eq_add_neg]))
      ((Homotopy.equivSubZero h)))

@[reassoc (attr := simp)]

Depends on / 依赖: Homotopy, Homotopy.equivSubZero, Homotopy.ofEq, Homotopy.trans, biprod, biprod.desc, biprod.lift_desc, equivSubZero, homotopyCofiber, homotopyCofiber.desc, id_comp, lift_desc, neg_comp, sub_eq_add_neg
-/
noncomputable def desc : K.cylinder ⟶ F :=
  homotopyCofiber.desc _ (biprod.desc φ₀ φ₁)
    (Homotopy.trans (Homotopy.ofEq (by
      simp only [biprod.lift_desc, id_comp, neg_comp, sub_eq_add_neg]))
      ((Homotopy.equivSubZero h)))

@[reassoc (attr := simp)]
/--
lemma `ι₀_desc` / 引理 `ι₀_desc`

English:
lemma ι₀_desc
  statement: ι₀ K ≫ desc φ₀ φ₁ h = φ₀
  proof: by simp [ι₀, desc]

@[reassoc (attr := simp)]

中文:
引理 ι₀_desc
  结论: ι₀ K ≫ desc φ₀ φ₁ h = φ₀
  证明: by simp [ι₀, desc]

@[reassoc (attr := simp)]
-/
lemma ι₀_desc : ι₀ K ≫ desc φ₀ φ₁ h = φ₀ := by simp [ι₀, desc]

@[reassoc (attr := simp)]
/--
lemma `ι₁_desc` / 引理 `ι₁_desc`

English:
lemma ι₁_desc
  statement: ι₁ K ≫ desc φ₀ φ₁ h = φ₁
  proof: by simp [ι₁, desc]

中文:
引理 ι₁_desc
  结论: ι₁ K ≫ desc φ₀ φ₁ h = φ₁
  证明: by simp [ι₁, desc]
-/
lemma ι₁_desc : ι₁ K ≫ desc φ₀ φ₁ h = φ₁ := by simp [ι₁, desc]

end

variable (K)

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : K.cylinder ⟶ K
  body: desc (𝟙 K) (𝟙 K) (Homotopy.refl _)

@[reassoc (attr := simp)]

中文:
定义 π
  签名: : K.cylinder ⟶ K
  定义体: desc (𝟙 K) (𝟙 K) (Homotopy.refl _)

@[reassoc (attr := simp)]

Depends on / 依赖: Homotopy, Homotopy.refl
-/
noncomputable def π : K.cylinder ⟶ K := desc (𝟙 K) (𝟙 K) (Homotopy.refl _)

@[reassoc (attr := simp)]
/--
lemma `ι₀_π` / 引理 `ι₀_π`

English:
lemma ι₀_π
  statement: ι₀ K ≫ π K = 𝟙 K
  proof: by simp [π]

@[reassoc (attr := simp)]

中文:
引理 ι₀_π
  结论: ι₀ K ≫ π K = 𝟙 K
  证明: by simp [π]

@[reassoc (attr := simp)]
-/
lemma ι₀_π : ι₀ K ≫ π K = 𝟙 K := by simp [π]

@[reassoc (attr := simp)]
/--
lemma `ι₁_π` / 引理 `ι₁_π`

English:
lemma ι₁_π
  statement: ι₁ K ≫ π K = 𝟙 K
  proof: by simp [π]

中文:
引理 ι₁_π
  结论: ι₁ K ≫ π K = 𝟙 K
  证明: by simp [π]
-/
lemma ι₁_π : ι₁ K ≫ π K = 𝟙 K := by simp [π]

/--
Definition of `inlX` / `inlX` 的定义

English:
abbreviation inlX
  signature: (i j : ι) (hij : c.Rel j i)
  body: homotopyCofiber.inlX (biprod.lift (𝟙 K) (-𝟙 K)) i j hij

中文:
缩写 inlX
  签名: (i j : ι) (hij : c.关系 j i)
  定义体: homotopyCofiber.inlX (biprod.lift (𝟙 K) (-𝟙 K)) i j hij

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.neg_, biprod, biprod.lift, homotopyCofiber, homotopyCofiber.inlX, neg.rightHomologyMap, rightHomologyMap
-/
noncomputable abbrev inlX (i j : ι) (hij : c.Rel j i) : K.X i ⟶ K.cylinder.X j :=
  homotopyCofiber.inlX (biprod.lift (𝟙 K) (-𝟙 K)) i j hij

/--
Definition of `inrX` / `inrX` 的定义

English:
abbreviation inrX
  signature: (i : ι)
  body: homotopyCofiber.inrX (biprod.lift (𝟙 K) (-𝟙 K)) i

中文:
缩写 inrX
  签名: (i : ι)
  定义体: homotopyCofiber.inrX (biprod.lift (𝟙 K) (-𝟙 K)) i

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.neg_, biprod, biprod.lift, homotopyCofiber, homotopyCofiber.inrX, neg.opcyclesMap, opcyclesMap
-/
noncomputable abbrev inrX (i : ι) : (K ⊞ K).X i ⟶ K.cylinder.X i :=
  homotopyCofiber.inrX (biprod.lift (𝟙 K) (-𝟙 K)) i

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inlX_π` / 引理 `inlX_π`

English:
lemma inlX_π
  given: (i j : ι) (hij : c.Rel j i)
  proof: by
  simp [HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, Homotopy.equivSubZero]

@[reassoc (attr := simp)]

中文:
引理 inlX_π
  条件: (i j : ι) (hij : c.关系 j i)
  证明: by
  simp [HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, Homotopy.equivSubZero]

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cylinder, HomologicalComplex.cylinder.desc, Homotopy, Homotopy.equivSubZero, RightHomologyMapData, RightHomologyMapData.add_, cylinder, equivSubZero, rightHomologyMap
-/
lemma inlX_π (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (π K).f j = 0 := by
  simp [HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, Homotopy.equivSubZero]

@[reassoc (attr := simp)]
/--
lemma `inrX_π` / 引理 `inrX_π`

English:
lemma inrX_π
  given: (i : ι)
  proof: homotopyCofiber.inrX_desc_f _ _ _ _

中文:
引理 inrX_π
  条件: (i : ι)
  证明: homotopyCofiber.inrX_desc_f _ _ _ _

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.add_, homotopyCofiber, homotopyCofiber.inrX_desc_f, inrX_desc_f, opcyclesMap
-/
lemma inrX_π (i : ι) :
    inrX K i ≫ (π K).f i = (biprod.desc (𝟙 _) (𝟙 K)).f i :=
  homotopyCofiber.inrX_desc_f _ _ _ _

section

variable (hc : forall j, exists i, c.Rel i j)

namespace πCompι₀Homotopy

/--
Definition of `nullHomotopicMap` / `nullHomotopicMap` 的定义

English:
definition nullHomotopicMap
  signature: : K.cylinder ⟶ K.cylinder
  body: Homotopy.nullHomotopicMap'
    (fun i j hij => homotopyCofiber.sndX (biprod.lift (𝟙 K) (-𝟙 K)) i ≫
      (biprod.snd : K ⊞ K ⟶ K).f i ≫ inlX K i j hij)

中文:
定义 nullHomotopicMap
  签名: : K.cylinder ⟶ K.cylinder
  定义体: Homotopy.nullHomotopicMap'
    (fun i j hij => homotopyCofiber.sndX (biprod.lift (𝟙 K) (-𝟙 K)) i ≫
      (biprod.snd : K ⊞ K ⟶ K).f i ≫ inlX K i j hij)

Depends on / 依赖: Homotopy, Homotopy.nullHomotopicMap, _add, _neg, biprod, biprod.lift, biprod.snd, homotopyCofiber, homotopyCofiber.sndX, nullHomotopicMap, rightHomologyMap, sub_eq_add_neg
-/
noncomputable def nullHomotopicMap : K.cylinder ⟶ K.cylinder :=
  Homotopy.nullHomotopicMap'
    (fun i j hij => homotopyCofiber.sndX (biprod.lift (𝟙 K) (-𝟙 K)) i ≫
      (biprod.snd : K ⊞ K ⟶ K).f i ≫ inlX K i j hij)

/--
Definition of `nullHomotopy` / `nullHomotopy` 的定义

English:
definition nullHomotopy
  signature: : Homotopy (nullHomotopicMap K) 0
  body: Homotopy.nullHomotopy' _

中文:
定义 nullHomotopy
  签名: : 同伦 (nullHomotopicMap K) 0
  定义体: Homotopy.nullHomotopy' _

Depends on / 依赖: Homotopy, Homotopy.nullHomotopy, _add, _neg, nullHomotopy, opcyclesMap, sub_eq_add_neg
-/
noncomputable def nullHomotopy : Homotopy (nullHomotopicMap K) 0 :=
  Homotopy.nullHomotopy' _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inlX_nullHomotopy_f` / 引理 `inlX_nullHomotopy_f`

English:
lemma inlX_nullHomotopy_f
  given: (i j : ι) (hij : c.Rel j i)
  proof: by
  dsimp [nullHomotopicMap]
  by_cases! hj : exists (k : ι), c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f hjk hij, homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.i

中文:
引理 inlX_nullHomotopy_f
  条件: (i j : ι) (hij : c.关系 j i)
  证明: by
  dsimp [nullHomotopicMap]
  by_cases! hj : exists (k : ι), c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f hjk hij, homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.i

Depends on / 依赖: HomologicalComplex, HomologicalComplex.comp_f_assoc, Homotopy, Homotopy.nullHomotopicMap, _f_of_not_rel, add_comp, add_zero, biprod, biprod.lift_snd, c.Rel, comp_add, comp_f_assoc, comp_id, comp_sub, d_sndX_assoc, homotopyCofiber, homotopyCofiber.d_sndX_assoc, homotopyCofiber.inlX_fstX_assoc, homotopyCofiber.inlX_sndX_assoc, homotopyCofiber_d
-/
lemma inlX_nullHomotopy_f (i j : ι) (hij : c.Rel j i) :
    inlX K i j hij ≫ (nullHomotopicMap K).f j =
      inlX K i j hij ≫ (π K ≫ ι₀ K - 𝟙 _).f j := by
  dsimp [nullHomotopicMap]
  by_cases! hj : exists (k : ι), c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f hjk hij, homotopyCofiber_d,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, homotopyCofiber.inlX_fstX_assoc,
      homotopyCofiber.inlX_sndX_assoc, zero_comp, add_zero, comp_sub, inlX_π_assoc, comp_id,
      zero_sub, ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f,
      neg_comp, id_comp]
  · simp only [Homotopy.nullHomotopicMap'_f_of_not_rel_right hij hj, homotopyCofiber_d, assoc,
    comp_sub, comp_id,
      homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, zero_comp, add_zero,
      homotopyCofiber.inlX_fstX_assoc, homotopyCofiber.inlX_sndX_assoc,
      ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f, neg_comp,
      id_comp, inlX_π_assoc, zero_sub]

include hc

set_option backward.isDefEq.respectTransparency false in
/--
lemma `inrX_nullHomotopy_f` / 引理 `inrX_nullHomotopy_f`

English:
lemma inrX_nullHomotopy_f
  given: (j : ι)
  proof: by
  have : biprod.lift (𝟙 K) (-𝟙 K) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  obtain ⟨i, hij⟩ := hc j
  dsimp [nullHomotopicMap]
  by_cases hj : exists (k : ι), c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Homotopy.nullHomotopicMap'_f hij hjk, homotopyCofiber_d

中文:
引理 inrX_nullHomotopy_f
  条件: (j : ι)
  证明: by
  have : biprod.lift (𝟙 K) (-𝟙 K) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  obtain ⟨i, hij⟩ := hc j
  dsimp [nullHomotopicMap]
  by_cases hj : exists (k : ι), c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Homotopy.nullHomotopicMap'_f hij hjk, homotopyCofiber_d

Depends on / 依赖: Hom.comm_assoc, Homotopy, Homotopy.nullHomotopicMap, add_neg_cancel_left, biprod, biprod.hom_ext, biprod.inl, biprod.inr, biprod.lift, c.Rel, cancel_epi, comm_assoc, comp_add, comp_id, comp_neg, comp_sub, hom_ext, homotopyCofiber, homotopyCofiber.inlX_d, homotopyCofiber.inrX_d_assoc
-/
lemma inrX_nullHomotopy_f (j : ι) :
    inrX K j ≫ (nullHomotopicMap K).f j = inrX K j ≫ (π K ≫ ι₀ K - 𝟙 _).f j := by
  have : biprod.lift (𝟙 K) (-𝟙 K) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  obtain ⟨i, hij⟩ := hc j
  dsimp [nullHomotopicMap]
  by_cases hj : exists (k : ι), c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Homotopy.nullHomotopicMap'_f hij hjk, homotopyCofiber_d, assoc, comp_add,
      homotopyCofiber.inrX_d_assoc, homotopyCofiber.inrX_sndX_assoc, comp_sub,
      inrX_π_assoc, comp_id, ← Hom.comm_assoc, homotopyCofiber.inlX_d _ _ _ _ _ hjk,
      comp_neg, add_neg_cancel_left]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp [ι₀]
    · simp only [inr_biprodXIso_inv_assoc, biprod_inr_snd_f_assoc, comp_sub,
        biprod_inr_desc_f_assoc, id_f, id_comp, ι₀, comp_f, this,
        sub_f_apply, sub_comp, homotopyCofiber.inr_f]
  · simp only [not_exists] at hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f_of_not_rel_left hij hj,
      homotopyCofiber_d, homotopyCofiber.inlX_d' _ _ _ _ (hj _), homotopyCofiber.inrX_sndX_assoc,
      comp_sub, inrX_π_assoc, comp_id, ι₀, comp_f, homotopyCofiber.inr_f]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp
    · simp [this]

/--
lemma `nullHomotopicMap_eq` / 引理 `nullHomotopicMap_eq`

English:
lemma nullHomotopicMap_eq
  statement: nullHomotopicMap K = π K ≫ ι₀ K - 𝟙 _
  proof: by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (biprod.lift (𝟙 K) (-𝟙 K)) (c.next i) i hi
      (inlX_nullHomotopy_f _ _ _ _) (inrX_nullHomotopy_f _ hc _)
  · exact homotopyCofiber.ext_from_X' (biprod.lift (𝟙 K) (-𝟙 K)) _ hi (inrX_nullHomotopy_f _ hc _)

中文:
引理 nullHomotopicMap_eq
  结论: nullHomotopicMap K = π K ≫ ι₀ K - 𝟙 _
  证明: by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (biprod.lift (𝟙 K) (-𝟙 K)) (c.next i) i hi
      (inlX_nullHomotopy_f _ _ _ _) (inrX_nullHomotopy_f _ hc _)
  · exact homotopyCofiber.ext_from_X' (biprod.lift (𝟙 K) (-𝟙 K)) _ hi (inrX_nullHomotopy_f _ hc _)

Depends on / 依赖: biprod, biprod.lift, c.Rel, c.next, ext_from_X, homotopyCofiber, homotopyCofiber.ext_from_X, inlX_nullHomotopy_f, inrX_nullHomotopy_f
-/
lemma nullHomotopicMap_eq : nullHomotopicMap K = π K ≫ ι₀ K - 𝟙 _ := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact homotopyCofiber.ext_from_X (biprod.lift (𝟙 K) (-𝟙 K)) (c.next i) i hi
      (inlX_nullHomotopy_f _ _ _ _) (inrX_nullHomotopy_f _ hc _)
  · exact homotopyCofiber.ext_from_X' (biprod.lift (𝟙 K) (-𝟙 K)) _ hi (inrX_nullHomotopy_f _ hc _)

end πCompι₀Homotopy

/--
Definition of `πCompι₀Homotopy` / `πCompι₀Homotopy` 的定义

English:
definition πCompι₀Homotopy
  signature: : Homotopy (π K ≫ ι₀ K) (𝟙 K.cylinder)
  body: Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (πCompι₀Homotopy.nullHomotopicMap_eq K hc).symm).trans
      (πCompι₀Homotopy.nullHomotopy K))

中文:
定义 πCompι₀Homotopy
  签名: : 同伦 (π K ≫ ι₀ K) (𝟙 K.cylinder)
  定义体: Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (πCompι₀Homotopy.nullHomotopicMap_eq K hc).symm).trans
      (πCompι₀Homotopy.nullHomotopy K))

Depends on / 依赖: Homotopy, Homotopy.equivSubZero.symm, Homotopy.nullHomotopicMap_eq, Homotopy.nullHomotopy, Homotopy.ofEq, equivSubZero, nullHomotopicMap_eq, nullHomotopy
-/
noncomputable def πCompι₀Homotopy : Homotopy (π K ≫ ι₀ K) (𝟙 K.cylinder) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (πCompι₀Homotopy.nullHomotopicMap_eq K hc).symm).trans
      (πCompι₀Homotopy.nullHomotopy K))

/-- The homotopy equivalence between `K.cylinder` and `K`. -/
@[simps]
/--
Definition of `homotopyEquiv` / `homotopyEquiv` 的定义

English:
definition homotopyEquiv
  signature: : HomotopyEquiv K.cylinder K where
  body: π K
  inv := ι₀ K
  homotopyHomInvId := πCompι₀Homotopy K hc
  homotopyInvHomId := Homotopy.ofEq (by simp)

中文:
定义 homotopyEquiv
  签名: : 同伦等价 K.cylinder K where
  定义体: π K
  inv := ι₀ K
  homotopyHomInvId := πCompι₀Homotopy K hc
  homotopyInvHomId := Homotopy.ofEq (by simp)
-/
noncomputable def homotopyEquiv : HomotopyEquiv K.cylinder K where
  hom := π K
  inv := ι₀ K
  homotopyHomInvId := πCompι₀Homotopy K hc
  homotopyInvHomId := Homotopy.ofEq (by simp)

/--
Definition of `homotopy₀₁` / `homotopy₀₁` 的定义

English:
definition homotopy₀₁
  signature: : Homotopy (ι₀ K) (ι₁ K)
  body: (Homotopy.ofEq (by simp)).trans (((πCompι₀Homotopy K hc).compLeft (ι₁ K)).trans
    (Homotopy.ofEq (by simp)))

include hc in

中文:
定义 homotopy₀₁
  签名: : 同伦 (ι₀ K) (ι₁ K)
  定义体: (Homotopy.ofEq (by simp)).trans (((πCompι₀Homotopy K hc).compLeft (ι₁ K)).trans
    (Homotopy.ofEq (by simp)))

include hc in

Depends on / 依赖: Homotopy, Homotopy.ofEq, compLeft
-/
noncomputable def homotopy₀₁ : Homotopy (ι₀ K) (ι₁ K) :=
  (Homotopy.ofEq (by simp)).trans (((πCompι₀Homotopy K hc).compLeft (ι₁ K)).trans
    (Homotopy.ofEq (by simp)))

include hc in
/--
lemma `map_ι₀_eq_map_ι₁` / 引理 `map_ι₀_eq_map_ι₁`

English:
lemma map_ι₀_eq_map_ι₁
  statement: {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
  proof: by
  have : IsIso (H.map (cylinder.π K)) := hH _ ⟨homotopyEquiv K hc, rfl⟩
  simp only [← cancel_mono (H.map (cylinder.π K)), ← H.map_comp, ι₀_π, H.map_id, ι₁_π]

中文:
引理 map_ι₀_eq_map_ι₁
  结论: {D : 类型} [范畴* D] (H : 同调复形 C c ⥤ D)
  证明: by
  have : IsIso (H.map (cylinder.π K)) := hH _ ⟨homotopyEquiv K hc, rfl⟩
  simp only [← cancel_mono (H.map (cylinder.π K)), ← H.map_comp, ι₀_π, H.map_id, ι₁_π]

Depends on / 依赖: H.map, H.map_comp, H.map_id, cancel_mono, cylinder, homotopyEquiv, map_comp, map_id
-/
lemma map_ι₀_eq_map_ι₁ {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map (ι₀ K) = H.map (ι₁ K) := by
  have : IsIso (H.map (cylinder.π K)) := hH _ ⟨homotopyEquiv K hc, rfl⟩
  simp only [← cancel_mono (H.map (cylinder.π K)), ← H.map_comp, ι₀_π, H.map_id, ι₁_π]

end


section

variable (F) {D : Type*} [Category* D] [Preadditive D] (H : C ⥤ D) [H.Additive]
  [forall i, HasBinaryBiproduct (F.X i) (F.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 F) (-𝟙 F))]
  [forall i, HasBinaryBiproduct (((H.mapHomologicalComplex c).obj F).X i)
    (((H.mapHomologicalComplex c).obj F).X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 ((H.mapHomologicalComplex c).obj F))
    (-𝟙 ((H.mapHomologicalComplex c).obj F)))]
  [HasHomotopyCofiber ((H.mapHomologicalComplex c).map (biprod.lift (𝟙 F) (-𝟙 F)))]
  (hc : forall (j : ι), exists i, c.Rel i j)

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapHomologicalComplexObjIso` / `mapHomologicalComplexObjIso` 的定义

English:
definition mapHomologicalComplexObjIso
  signature: :
  body: homotopyCofiber.mapHomologicalComplexObjIso _ H ≪≫
    homotopyCofiber.mapArrowIso _ _ hc
      (Arrow.isoMk (Iso.refl _) ((H.mapHomologicalComplex c).mapBiprod F F) (by
        apply biprod.hom_ext <;> simp [← Functor.map_comp]))

中文:
定义 mapHomologicalComplexObjIso
  签名: :
  定义体: homotopyCofiber.mapHomologicalComplexObjIso _ H ≪≫
    homotopyCofiber.mapArrowIso _ _ hc
      (Arrow.isoMk (Iso.refl _) ((H.mapHomologicalComplex c).mapBiprod F F) (by
        apply biprod.hom_ext <;> simp [← Functor.map_comp]))

Depends on / 依赖: Arrow.isoMk, Functor, Functor.map_comp, H.mapHomologicalComplex, Iso.refl, biprod, biprod.hom_ext, hom_ext, homotopyCofiber, homotopyCofiber.mapArrowIso, homotopyCofiber.mapHomologicalComplexObjIso, mapArrowIso, mapBiprod, mapHomologicalComplex, mapHomologicalComplexObjIso, map_comp
-/
noncomputable def mapHomologicalComplexObjIso :
    (H.mapHomologicalComplex c).obj (cylinder F) ≅
      cylinder ((H.mapHomologicalComplex c).obj F) :=
  homotopyCofiber.mapHomologicalComplexObjIso _ H ≪≫
    homotopyCofiber.mapArrowIso _ _ hc
      (Arrow.isoMk (Iso.refl _) ((H.mapHomologicalComplex c).mapBiprod F F) (by
        apply biprod.hom_ext <;> simp [← Functor.map_comp]))

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `map_ι₀_mapHomologicalComplexObjIso_hom` / 引理 `map_ι₀_mapHomologicalComplexObjIso_hom`

English:
lemma map_ι₀_mapHomologicalComplexObjIso_hom
  proof: by
  dsimp [mapHomologicalComplexObjIso, ι₀, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp]; rw [assoc]; rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc]; rw [homotopyCofiber.inr_desc]; rw [← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

中文:
引理 map_ι₀_mapHomologicalComplexObjIso_hom
  证明: by
  dsimp [mapHomologicalComplexObjIso, ι₀, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp]; rw [assoc]; rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc]; rw [homotopyCofiber.inr_desc]; rw [← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, _neg, biprod, biprod.hom_ext, hom_ext, homotopyCofiber, homotopyCofiber.inr_desc, homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc, homotopyCofiber.mapArrowHom, inr_desc, inr_mapHomologicalComplexObjIso_hom_assoc, leftHomologyMap, mapArrowHom, mapHomologicalComplexObjIso, map_comp
-/
lemma map_ι₀_mapHomologicalComplexObjIso_hom :
    (H.mapHomologicalComplex c).map (cylinder.ι₀ F) ≫ (mapHomologicalComplexObjIso F H hc).hom =
      cylinder.ι₀ _ := by
  dsimp [mapHomologicalComplexObjIso, ι₀, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp]; rw [assoc]; rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc]; rw [homotopyCofiber.inr_desc]; rw [← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `map_ι₁_mapHomologicalComplexObjIso_hom` / 引理 `map_ι₁_mapHomologicalComplexObjIso_hom`

English:
lemma map_ι₁_mapHomologicalComplexObjIso_hom
  proof: by
  dsimp [mapHomologicalComplexObjIso, ι₁, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp]; rw [assoc]; rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc]; rw [homotopyCofiber.inr_desc]; rw [← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

中文:
引理 map_ι₁_mapHomologicalComplexObjIso_hom
  证明: by
  dsimp [mapHomologicalComplexObjIso, ι₁, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp]; rw [assoc]; rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc]; rw [homotopyCofiber.inr_desc]; rw [← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, _add, biprod, biprod.hom_ext, hom_ext, homotopyCofiber, homotopyCofiber.inr_desc, homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc, homotopyCofiber.mapArrowHom, inr_desc, inr_mapHomologicalComplexObjIso_hom_assoc, leftHomologyMap, mapArrowHom, mapHomologicalComplexObjIso, map_comp
-/
lemma map_ι₁_mapHomologicalComplexObjIso_hom :
    (H.mapHomologicalComplex c).map (cylinder.ι₁ F) ≫ (mapHomologicalComplexObjIso F H hc).hom =
      cylinder.ι₁ _ := by
  dsimp [mapHomologicalComplexObjIso, ι₁, homotopyCofiber.mapArrowHom]
  rw [Functor.map_comp]; rw [assoc]; rw [homotopyCofiber.inr_mapHomologicalComplexObjIso_hom_assoc]; rw [homotopyCofiber.inr_desc]; rw [← Category.assoc]
  congr 1
  apply biprod.hom_ext <;> simp [← Functor.map_comp]

end

end cylinder

omit [DecidableRel c.Rel] in
/--
lemma `_root_.Homotopy.map_eq_of_inverts_homotopyEquivalences` / 引理 `_root_.Homotopy.map_eq_of_inverts_homotopyEquivalences`

English:
lemma _root_.Homotopy.map_eq_of_inverts_homotopyEquivalences
  proof: by
  classical
  simp only [← cylinder.ι₀_desc _ _ h, ← cylinder.ι₁_desc _ _ h, H.map_comp,
    cylinder.map_ι₀_eq_map_ι₁ _ hc _ hH]

中文:
引理 _root_.同伦.map_eq_of_inverts_homotopyEquivalences
  证明: by
  classical
  simp only [← cylinder.ι₀_desc _ _ h, ← cylinder.ι₁_desc _ _ h, H.map_comp,
    cylinder.map_ι₀_eq_map_ι₁ _ hc _ hH]

Depends on / 依赖: H.map_comp, _sub, classical, cylinder, cylinder.map_, leftHomologyMap, map_comp
-/
lemma _root_.Homotopy.map_eq_of_inverts_homotopyEquivalences
    {φ₀ φ₁ : F ⟶ G} (h : Homotopy φ₀ φ₁) (hc : forall j, exists i, c.Rel i j)
    [forall i, HasBinaryBiproduct (F.X i) (F.X i)]
    [HasHomotopyCofiber (biprod.lift (𝟙 F) (-𝟙 F))]
    {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map φ₀ = H.map φ₁ := by
  classical
  simp only [← cylinder.ι₀_desc _ _ h, ← cylinder.ι₁_desc _ _ h, H.map_comp,
    cylinder.map_ι₀_eq_map_ι₁ _ hc _ hH]

end

end HomologicalComplex
