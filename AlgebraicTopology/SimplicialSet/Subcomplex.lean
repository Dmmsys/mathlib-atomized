/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Subfunctor.OfSection

/-!
# Subcomplexes of a simplicial set

Given a simplicial set `X`, this file defines the type `X.Subcomplex`
of subcomplexes of `X` as an abbreviation for `Subfunctor X`.
It also introduces a coercion from `X.Subcomplex` to `SSet`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits

namespace SSet

-- Note: this could be obtained as `inferInstanceAs (Balanced (_ ⥤ _))`
-- by importing `Mathlib.CategoryTheory.Adhesive.Basic`, but we give a
-- different proof so as to reduce imports
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Balanced SSet.{u}
  body: by
    rw [NatTrans.isIso_iff_isIso_app]
    intro
    rw [isIso_iff_bijective]
    constructor
    · rw [← mono_iff_injective]
      infer_instance
    · rw [← epi_iff_surjective]
      infer_instance

中文:
实例 :
  签名: Balanced SSet.{u}
  定义体: by
    rw [NatTrans.isIso_iff_isIso_app]
    intro
    rw [isIso_iff_bijective]
    constructor
    · rw [← mono_iff_injective]
      infer_instance
    · rw [← epi_iff_surjective]
      infer_instance

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, epi_iff_surjective, infer_instance, isIso_iff_bijective, isIso_iff_isIso_app, mono_iff_injective
-/
instance : Balanced SSet.{u} where
  isIso_of_mono_of_epi f _ _ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro
    rw [isIso_iff_bijective]
    constructor
    · rw [← mono_iff_injective]
      infer_instance
    · rw [← epi_iff_surjective]
      infer_instance

variable (X Y : SSet.{u})

/--
Definition of `Subcomplex` / `Subcomplex` 的定义

English:
abbreviation Subcomplex
  body: Subfunctor X

中文:
缩写 Subcomplex
  定义体: Subfunctor X

Depends on / 依赖: Subfunctor
-/
abbrev Subcomplex := Subfunctor X

variable {X Y}

namespace Subcomplex

/--
Definition of `toSSet` / `toSSet` 的定义

English:
abbreviation toSSet
  signature: (A : X.Subcomplex)
  body: A.toFunctor

中文:
缩写 toSSet
  签名: (A : X.Subcomplex)
  定义体: A.toFunctor

Depends on / 依赖: A.toFunctor, toFunctor
-/
abbrev toSSet (A : X.Subcomplex) : SSet.{u} := A.toFunctor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut X.Subcomplex SSet.{u}
  body: fun S => S.toSSet

中文:
实例 :
  签名: CoeOut X.Subcomplex SSet.{u}
  定义体: fun S => S.toSSet

Depends on / 依赖: S.toSSet, toSSet
-/
instance : CoeOut X.Subcomplex SSet.{u} where
  coe := fun S => S.toSSet

instance {X : SSet.{u}} (n : SimplexCategoryᵒᵖ) (A : X.Subcomplex)
    [DecidableEq (X.obj n)] :
    DecidableEq ((A : SSet).obj n) :=
  inferInstanceAs (DecidableEq (A.obj n))

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: (A : Subcomplex X)
  body: Subfunctor.ι A

中文:
缩写 ι
  签名: (A : Subcomplex X)
  定义体: Subfunctor.ι A

Depends on / 依赖: Subfunctor
-/
abbrev ι (A : Subcomplex X) : Quiver.Hom (V := SSet) A X := Subfunctor.ι A

instance (A : X.Subcomplex) : Mono A.ι :=
  inferInstanceAs (Mono (Subfunctor.ι A))

section

variable {S₁ S₂ : X.Subcomplex} (h : S₁ <= S₂)

/--
Definition of `homOfLE` / `homOfLE` 的定义

English:
abbreviation homOfLE
  signature: : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u})
  body: Subfunctor.homOfLe h

@[reassoc]

中文:
缩写 homOfLE
  签名: : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u})
  定义体: Subfunctor.homOfLe h

@[reassoc]

Depends on / 依赖: Subfunctor, Subfunctor.homOfLe, homOfLe
-/
abbrev homOfLE : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u}) := Subfunctor.homOfLe h

@[reassoc]
/--
lemma `homOfLE_comp` / 引理 `homOfLE_comp`

English:
lemma homOfLE_comp
  given: {S₃ : X.Subcomplex} (h' : S₂ <= S₃)
  proof: rfl

中文:
引理 homOfLE_comp
  条件: {S₃ : X.Subcomplex} (h' : S₂ <= S₃)
  证明: rfl
-/
lemma homOfLE_comp {S₃ : X.Subcomplex} (h' : S₂ <= S₃) :
    homOfLE h ≫ homOfLE h' = homOfLE (h.trans h') := rfl

variable (S₁) in
@[simp]
/--
lemma `homOfLE_refl` / 引理 `homOfLE_refl`

English:
lemma homOfLE_refl
  statement: homOfLE (by rfl : S₁ <= S₁) = 𝟙 _
  proof: rfl

@[simp]

中文:
引理 homOfLE_refl
  结论: homOfLE (by rfl : S₁ <= S₁) = 𝟙 _
  证明: rfl

@[simp]
-/
lemma homOfLE_refl : homOfLE (by rfl : S₁ <= S₁) = 𝟙 _ := rfl

@[simp]
/--
lemma `homOfLE_app_val` / 引理 `homOfLE_app_val`

English:
lemma homOfLE_app_val
  given: (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ)
  proof: rfl

@[simp, reassoc]

中文:
引理 homOfLE_app_val
  条件: (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ)
  证明: rfl

@[simp, reassoc]
-/
lemma homOfLE_app_val (Δ : SimplexCategoryᵒᵖ) (x : S₁.obj Δ) :
    dsimp% ((homOfLE h).app Δ x).val = x.val := rfl

@[simp, reassoc]
/--
lemma `homOfLE_ι` / 引理 `homOfLE_ι`

English:
lemma homOfLE_ι
  statement: homOfLE h ≫ S₂.ι = S₁.ι
  proof: rfl

中文:
引理 homOfLE_ι
  结论: homOfLE h ≫ S₂.ι = S₁.ι
  证明: rfl
-/
lemma homOfLE_ι : homOfLE h ≫ S₂.ι = S₁.ι := rfl

/--
Instance `mono_homOfLE` / 实例 `mono_homOfLE`

English:
instance mono_homOfLE
  signature: : Mono (homOfLE h)
  body: mono_of_mono_fac (homOfLE_ι h)

中文:
实例 mono_homOfLE
  签名: : Mono (homOfLE h)
  定义体: mono_of_mono_fac (homOfLE_ι h)

Depends on / 依赖: mono_of_mono_fac
-/
instance mono_homOfLE : Mono (homOfLE h) := mono_of_mono_fac (homOfLE_ι h)

/-- This is the isomorphism of simplicial sets corresponding to
an equality of subcomplexes. -/
@[simps]
/--
Definition of `eqToIso` / `eqToIso` 的定义

English:
definition eqToIso
  signature: (h : S₁ = S₂)
  body: homOfLE h.le
  inv := homOfLE h.symm.le

中文:
定义 eqToIso
  签名: (h : S₁ = S₂)
  定义体: homOfLE h.le
  inv := homOfLE h.symm.le
-/
protected def eqToIso (h : S₁ = S₂) : (S₁ : SSet.{u}) ≅ S₂ where
  hom := homOfLE h.le
  inv := homOfLE h.symm.le

end

/-- The functor which sends `A : X.Subcomplex` to `A.toSSet`. -/
@[simps]
/--
Definition of `toSSetFunctor` / `toSSetFunctor` 的定义

English:
definition toSSetFunctor
  signature: : X.Subcomplex ⥤ SSet.{u} where
  body: A
  map h := homOfLE (leOfHom h)

中文:
定义 toSSetFunctor
  签名: : X.Subcomplex ⥤ SSet.{u} where
  定义体: A
  map h := homOfLE (leOfHom h)
-/
def toSSetFunctor : X.Subcomplex ⥤ SSet.{u} where
  obj A := A
  map h := homOfLE (leOfHom h)

section

variable (X)

/-- If `X : SSet`, this is the isomorphism of simplicial sets
from `⊤ : X.Subcomplex` to `X`. -/
@[simps! inv_app_hom_apply]
/--
Definition of `topIso` / `topIso` 的定义

English:
definition topIso
  signature: : ((⊤ : X.Subcomplex) : SSet) ≅ X
  body: NatIso.ofComponents (fun n => (Equiv.Set.univ (X.obj n)).toIso)

@[simp]

中文:
定义 topIso
  签名: : ((⊤ : X.Subcomplex) : SSet) ≅ X
  定义体: NatIso.ofComponents (fun n => (Equiv.Set.univ (X.obj n)).toIso)

@[simp]

Depends on / 依赖: Equiv.Set.univ, NatIso, NatIso.ofComponents, X.obj, ofComponents
-/
def topIso : ((⊤ : X.Subcomplex) : SSet) ≅ X :=
  NatIso.ofComponents (fun n => (Equiv.Set.univ (X.obj n)).toIso)

@[simp]
/--
lemma `topIso_hom` / 引理 `topIso_hom`

English:
lemma topIso_hom
  statement: (topIso X).hom = Subcomplex.ι _
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 topIso_hom
  结论: (topIso X).hom = Subcomplex.ι _
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma topIso_hom : (topIso X).hom = Subcomplex.ι _ := rfl

@[reassoc (attr := simp)]
/--
lemma `topIso_inv_ι` / 引理 `topIso_inv_ι`

English:
lemma topIso_inv_ι
  statement: (topIso X).inv ≫ Subfunctor.ι _ = 𝟙 _
  proof: rfl

中文:
引理 topIso_inv_ι
  结论: (topIso X).inv ≫ Subfunctor.ι _ = 𝟙 _
  证明: rfl
-/
lemma topIso_inv_ι : (topIso X).inv ≫ Subfunctor.ι _ = 𝟙 _ := rfl

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y)
  body: by ext _ ⟨_, h⟩; tauto

中文:
实例 :
  签名: Subsingleton (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y)
  定义体: by ext _ ⟨_, h⟩; tauto
-/
instance : Subsingleton (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y) where
  allEq _ _ := by ext _ ⟨_, h⟩; tauto

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y)
  body: { app _ := ↾fun ⟨_, h⟩ => by tauto
      naturality _ _ _ := by ext ⟨_, h⟩; tauto }
  uniq := by subsingleton

中文:
实例 :
  签名: Unique (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y)
  定义体: { app _ := ↾fun ⟨_, h⟩ => by tauto
      naturality _ _ _ := by ext ⟨_, h⟩; tauto }
  uniq := by subsingleton

Depends on / 依赖: naturality, subsingleton
-/
instance : Unique (((⊥ : X.Subcomplex) : SSet.{u}) ⟶ Y) where
  default :=
    { app _ := ↾fun ⟨_, h⟩ => by tauto
      naturality _ _ _ := by ext ⟨_, h⟩; tauto }
  uniq := by subsingleton

/--
Definition of `isInitialBot` / `isInitialBot` 的定义

English:
definition isInitialBot
  signature: : IsInitial ((⊥ : X.Subcomplex) : SSet.{u})
  body: IsInitial.ofUnique _

中文:
定义 isInitialBot
  签名: : IsInitial ((⊥ : X.Subcomplex) : SSet.{u})
  定义体: IsInitial.ofUnique _

Depends on / 依赖: IsInitial, IsInitial.ofUnique, ofUnique
-/
def isInitialBot : IsInitial ((⊥ : X.Subcomplex) : SSet.{u}) :=
  IsInitial.ofUnique _

/--
Definition of `ofSimplex` / `ofSimplex` 的定义

English:
abbreviation ofSimplex
  signature: {n : Nat} (x : X _⦋n⦌)
  body: Subfunctor.ofSection x

@[simp]

中文:
缩写 ofSimplex
  签名: {n : 自然数} (x : X _⦋n⦌)
  定义体: Subfunctor.ofSection x

@[simp]

Depends on / 依赖: Subfunctor, Subfunctor.ofSection, ofSection
-/
abbrev ofSimplex {n : Nat} (x : X _⦋n⦌) : X.Subcomplex := Subfunctor.ofSection x

@[simp]
/--
lemma `ofSimplex_ι` / 引理 `ofSimplex_ι`

English:
lemma ofSimplex_ι
  given: (x : X _⦋0⦌)
  statement: (ofSimplex x).ι = SSet.const x
  proof: by
  ext n ⟨_, ⟨u⟩, rfl⟩
  obtain rfl := Subsingleton.elim u (SimplexCategory.const _ _ 0)
  rfl

中文:
引理 ofSimplex_ι
  条件: (x : X _⦋0⦌)
  结论: (ofSimplex x).ι = SSet.const x
  证明: by
  ext n ⟨_, ⟨u⟩, rfl⟩
  obtain rfl := Subsingleton.elim u (SimplexCategory.const _ _ 0)
  rfl

Depends on / 依赖: SimplexCategory, SimplexCategory.const, Subsingleton, Subsingleton.elim
-/
lemma ofSimplex_ι (x : X _⦋0⦌) : (ofSimplex x).ι = SSet.const x := by
  ext n ⟨_, ⟨u⟩, rfl⟩
  obtain rfl := Subsingleton.elim u (SimplexCategory.const _ _ 0)
  rfl

/--
lemma `mem_ofSimplex_obj` / 引理 `mem_ofSimplex_obj`

English:
lemma mem_ofSimplex_obj
  given: {n : Nat} (x : X _⦋n⦌)
  proof: Subfunctor.mem_ofSection_obj x

中文:
引理 mem_ofSimplex_obj
  条件: {n : 自然数} (x : X _⦋n⦌)
  证明: Subfunctor.mem_ofSection_obj x

Depends on / 依赖: Subfunctor, Subfunctor.mem_ofSection_obj, mem_ofSection_obj
-/
lemma mem_ofSimplex_obj {n : Nat} (x : X _⦋n⦌) :
    x in (ofSimplex x).obj _ :=
  Subfunctor.mem_ofSection_obj x

/--
lemma `ofSimplex_le_iff` / 引理 `ofSimplex_le_iff`

English:
lemma ofSimplex_le_iff
  given: {n : Nat} (x : X _⦋n⦌) (A : X.Subcomplex)
  proof: Subfunctor.ofSection_le_iff _ _

中文:
引理 ofSimplex_le_iff
  条件: {n : 自然数} (x : X _⦋n⦌) (A : X.Subcomplex)
  证明: Subfunctor.ofSection_le_iff _ _

Depends on / 依赖: Subfunctor, Subfunctor.ofSection_le_iff, ofSection_le_iff
-/
lemma ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌) (A : X.Subcomplex) :
    ofSimplex x <= A ↔ x in A.obj _ :=
  Subfunctor.ofSection_le_iff _ _

/--
lemma `mem_ofSimplex_obj_iff` / 引理 `mem_ofSimplex_obj_iff`

English:
lemma mem_ofSimplex_obj_iff
  given: {n : Nat} (x : X _⦋n⦌) {m : SimplexCategoryᵒᵖ} (y : X.obj m)
  proof: by
  dsimp [ofSimplex, Subfunctor.ofSection]
  aesop

中文:
引理 mem_ofSimplex_obj_iff
  条件: {n : 自然数} (x : X _⦋n⦌) {m : SimplexCategoryᵒᵖ} (y : X.obj m)
  证明: by
  dsimp [ofSimplex, Subfunctor.ofSection]
  aesop

Depends on / 依赖: Subfunctor, Subfunctor.ofSection, ofSection, ofSimplex
-/
lemma mem_ofSimplex_obj_iff {n : Nat} (x : X _⦋n⦌) {m : SimplexCategoryᵒᵖ} (y : X.obj m) :
    y in (ofSimplex x).obj m ↔ exists (f : m.unop ⟶ ⦋n⦌), X.map f.op x = y := by
  dsimp [ofSimplex, Subfunctor.ofSection]
  aesop

/--
lemma `ofSimplex_map_le` / 引理 `ofSimplex_map_le`

English:
lemma ofSimplex_map_le
  statement: {X : SSet.{u}} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌)
  proof: by
  simp only [Subfunctor.ofSection_le_iff]
  exact ⟨f.op, by simp⟩

@[simp]

中文:
引理 ofSimplex_map_le
  结论: {X : SSet.{u}} {n m : 自然数} (f : ⦋n⦌ ⟶ ⦋m⦌)
  证明: by
  simp only [Subfunctor.ofSection_le_iff]
  exact ⟨f.op, by simp⟩

@[simp]

Depends on / 依赖: Subfunctor, Subfunctor.ofSection_le_iff, f.op, ofSection_le_iff
-/
lemma ofSimplex_map_le {X : SSet.{u}} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) <= ofSimplex x := by
  simp only [Subfunctor.ofSection_le_iff]
  exact ⟨f.op, by simp⟩

@[simp]
/--
lemma `ofSimplex_map_of_epi` / 引理 `ofSimplex_map_of_epi`

English:
lemma ofSimplex_map_of_epi
  statement: {X : SSet.{u}} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
  proof: by
  refine le_antisymm (ofSimplex_map_le f x) ?_
  simp only [Subfunctor.ofSection_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← Functor.map_comp_apply, ← op_comp]⟩

中文:
引理 ofSimplex_map_of_epi
  结论: {X : SSet.{u}} {n m : 自然数} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
  证明: by
  refine le_antisymm (ofSimplex_map_le f x) ?_
  simp only [Subfunctor.ofSection_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← Functor.map_comp_apply, ← op_comp]⟩

Depends on / 依赖: Functor, Functor.map_comp_apply, Subfunctor, Subfunctor.ofSection_le_iff, isSplitEpi_of_epi, le_antisymm, map_comp_apply, ofSection_le_iff, ofSimplex_map_le, op_comp, section_
-/
lemma ofSimplex_map_of_epi {X : SSet.{u}} {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) = ofSimplex x := by
  refine le_antisymm (ofSimplex_map_le f x) ?_
  simp only [Subfunctor.ofSection_le_iff]
  have := isSplitEpi_of_epi f
  exact ⟨(section_ f).op, by simp [← Functor.map_comp_apply, ← op_comp]⟩

section

variable (f : X ⟶ Y)

/--
Definition of `range` / `range` 的定义

English:
abbreviation range
  signature: : Y.Subcomplex
  body: Subfunctor.range f

中文:
缩写 range
  签名: : Y.Subcomplex
  定义体: Subfunctor.range f

Depends on / 依赖: Subfunctor, Subfunctor.range
-/
abbrev range : Y.Subcomplex := Subfunctor.range f

/--
Definition of `toRange` / `toRange` 的定义

English:
abbreviation toRange
  signature: : X ⟶ Subcomplex.range f
  body: Subfunctor.toRange f

@[simp, reassoc]

中文:
缩写 toRange
  签名: : X ⟶ Subcomplex.range f
  定义体: Subfunctor.toRange f

@[simp, reassoc]

Depends on / 依赖: Subfunctor, Subfunctor.toRange, toRange
-/
abbrev toRange : X ⟶ Subcomplex.range f := Subfunctor.toRange f

@[simp, reassoc]
/--
lemma `toRange_ι` / 引理 `toRange_ι`

English:
lemma toRange_ι
  statement: toRange f ≫ (Subcomplex.range f).ι = f
  proof: rfl

@[simp]

中文:
引理 toRange_ι
  结论: toRange f ≫ (Subcomplex.range f).ι = f
  证明: rfl

@[simp]
-/
lemma toRange_ι : toRange f ≫ (Subcomplex.range f).ι = f := rfl

@[simp]
/--
lemma `toRange_app_val` / 引理 `toRange_app_val`

English:
lemma toRange_app_val
  given: {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ)
  proof: rfl

中文:
引理 toRange_app_val
  条件: {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ)
  证明: rfl
-/
lemma toRange_app_val {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    dsimp% ((toRange f).app Δ x).val = f.app Δ x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (toRange f)
  body: inferInstanceAs (Epi (Subfunctor.toRange f))

中文:
实例 :
  签名: Epi (toRange f)
  定义体: inferInstanceAs (Epi (Subfunctor.toRange f))

Depends on / 依赖: Subfunctor, Subfunctor.toRange, toRange
-/
instance : Epi (toRange f) :=
  inferInstanceAs (Epi (Subfunctor.toRange f))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Mono (toRange f)
  body: mono_of_mono_fac (toRange_ι f)

中文:
实例 [Mono
  签名: f] : Mono (toRange f)
  定义体: mono_of_mono_fac (toRange_ι f)

Depends on / 依赖: mono_of_mono_fac
-/
instance [Mono f] : Mono (toRange f) :=
  mono_of_mono_fac (toRange_ι f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : IsIso (toRange f)
  body: isIso_of_mono_of_epi _

中文:
实例 [Mono
  签名: f] : IsIso (toRange f)
  定义体: isIso_of_mono_of_epi _

Depends on / 依赖: isIso_of_mono_of_epi
-/
instance [Mono f] : IsIso (toRange f) :=
  isIso_of_mono_of_epi _

/--
lemma `range_eq_top_iff` / 引理 `range_eq_top_iff`

English:
lemma range_eq_top_iff
  statement: Subcomplex.range f = ⊤ ↔ Epi f
  proof: by
  rw [NatTrans.epi_iff_epi_app]; rw [Subfunctor.ext_iff]; rw [funext_iff]
  simp only [epi_iff_surjective, Subfunctor.range_obj, Subfunctor.top_obj,
    Set.top_eq_univ, Set.range_eq_univ]

中文:
引理 range_eq_top_iff
  结论: Subcomplex.range f = ⊤ ↔ Epi f
  证明: by
  rw [NatTrans.epi_iff_epi_app]; rw [Subfunctor.ext_iff]; rw [funext_iff]
  simp only [epi_iff_surjective, Subfunctor.range_obj, Subfunctor.top_obj,
    Set.top_eq_univ, Set.range_eq_univ]

Depends on / 依赖: NatTrans, NatTrans.epi_iff_epi_app, Set.range_eq_univ, Set.top_eq_univ, Subfunctor, Subfunctor.ext_iff, Subfunctor.range_obj, Subfunctor.top_obj, epi_iff_epi_app, epi_iff_surjective, ext_iff, funext_iff, range_eq_univ, range_obj, top_eq_univ, top_obj
-/
lemma range_eq_top_iff : Subcomplex.range f = ⊤ ↔ Epi f := by
  rw [NatTrans.epi_iff_epi_app]; rw [Subfunctor.ext_iff]; rw [funext_iff]
  simp only [epi_iff_surjective, Subfunctor.range_obj, Subfunctor.top_obj,
    Set.top_eq_univ, Set.range_eq_univ]

/--
lemma `range_eq_top` / 引理 `range_eq_top`

English:
lemma range_eq_top
  given: [Epi f]
  statement: Subcomplex.range f = ⊤
  proof: by
  rwa [range_eq_top_iff]

中文:
引理 range_eq_top
  条件: [Epi f]
  结论: Subcomplex.range f = ⊤
  证明: by
  rwa [range_eq_top_iff]

Depends on / 依赖: range_eq_top_iff
-/
lemma range_eq_top [Epi f] : Subcomplex.range f = ⊤ := by
  rwa [range_eq_top_iff]

end

section

variable (f : X ⟶ Y) {B : Y.Subcomplex} (hf : range f <= B)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : X ⟶ B
  body: Subfunctor.lift f hf

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: : X ⟶ B
  定义体: Subfunctor.lift f hf

@[reassoc (attr := simp)]

Depends on / 依赖: Subfunctor, Subfunctor.lift
-/
def lift : X ⟶ B := Subfunctor.lift f hf

@[reassoc (attr := simp)]
/--
lemma `lift_ι` / 引理 `lift_ι`

English:
lemma lift_ι
  statement: lift f hf ≫ B.ι = f
  proof: rfl

@[simp]

中文:
引理 lift_ι
  结论: lift f hf ≫ B.ι = f
  证明: rfl

@[simp]
-/
lemma lift_ι : lift f hf ≫ B.ι = f := rfl

@[simp]
/--
lemma `lift_app_coe` / 引理 `lift_app_coe`

English:
lemma lift_app_coe
  given: {n : SimplexCategoryᵒᵖ} (x : X.obj n)
  proof: rfl

中文:
引理 lift_app_coe
  条件: {n : SimplexCategoryᵒᵖ} (x : X.obj n)
  证明: rfl
-/
lemma lift_app_coe {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    dsimp% ((lift f hf).app _ x).1 = f.app _ x := rfl

end

section

/-- The preimage of a subcomplex by a morphism of simplicial sets. -/
@[simps]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (A : X.Subcomplex) (p : Y ⟶ X)
  body: p.app n ⁻¹' (A.obj n)
  map f := (Set.preimage_mono (A.map f)).trans (by simp [Set.preimage_preimage])

@[simp]

中文:
定义 preimage
  签名: (A : X.Subcomplex) (p : Y ⟶ X)
  定义体: p.app n ⁻¹' (A.obj n)
  map f := (Set.preimage_mono (A.map f)).trans (by simp [Set.preimage_preimage])

@[simp]

Depends on / 依赖: A.obj, p.app
-/
def preimage (A : X.Subcomplex) (p : Y ⟶ X) : Y.Subcomplex where
  obj n := p.app n ⁻¹' (A.obj n)
  map f := (Set.preimage_mono (A.map f)).trans (by simp [Set.preimage_preimage])

@[simp]
/--
lemma `preimage_max` / 引理 `preimage_max`

English:
lemma preimage_max
  given: (A B : X.Subcomplex) (p : Y ⟶ X)
  proof: rfl

@[simp]

中文:
引理 preimage_max
  条件: (A B : X.Subcomplex) (p : Y ⟶ X)
  证明: rfl

@[simp]
-/
lemma preimage_max (A B : X.Subcomplex) (p : Y ⟶ X) :
    (A ⊔ B).preimage p = A.preimage p ⊔ B.preimage p := rfl

@[simp]
/--
lemma `preimage_min` / 引理 `preimage_min`

English:
lemma preimage_min
  given: (A B : X.Subcomplex) (p : Y ⟶ X)
  proof: rfl

@[simp]

中文:
引理 preimage_min
  条件: (A B : X.Subcomplex) (p : Y ⟶ X)
  证明: rfl

@[simp]
-/
lemma preimage_min (A B : X.Subcomplex) (p : Y ⟶ X) :
    (A ⊓ B).preimage p = A.preimage p ⊓ B.preimage p := rfl

@[simp]
/--
lemma `preimage_iSup` / 引理 `preimage_iSup`

English:
lemma preimage_iSup
  given: {ι : Type*} (A : ι -> X.Subcomplex) (p : Y ⟶ X)
  proof: by aesop

@[simp]

中文:
引理 preimage_iSup
  条件: {ι : 类型} (A : ι -> X.Subcomplex) (p : Y ⟶ X)
  证明: by aesop

@[simp]
-/
lemma preimage_iSup {ι : Type*} (A : ι -> X.Subcomplex) (p : Y ⟶ X) :
    (⨆ i, A i).preimage p = ⨆ i, (A i).preimage p := by aesop

@[simp]
/--
lemma `preimage_iInf` / 引理 `preimage_iInf`

English:
lemma preimage_iInf
  given: {ι : Type*} (A : ι -> X.Subcomplex) (p : Y ⟶ X)
  proof: by aesop

@[simp]

中文:
引理 preimage_iInf
  条件: {ι : 类型} (A : ι -> X.Subcomplex) (p : Y ⟶ X)
  证明: by aesop

@[simp]
-/
lemma preimage_iInf {ι : Type*} (A : ι -> X.Subcomplex) (p : Y ⟶ X) :
    (⨅ i, A i).preimage p = ⨅ i, (A i).preimage p := by aesop

@[simp]
/--
lemma `preimage_id` / 引理 `preimage_id`

English:
lemma preimage_id
  given: (A : X.Subcomplex)
  statement: A.preimage (𝟙 X) = A
  proof: rfl

中文:
引理 preimage_id
  条件: (A : X.Subcomplex)
  结论: A.preimage (𝟙 X) = A
  证明: rfl
-/
lemma preimage_id (A : X.Subcomplex) : A.preimage (𝟙 X) = A := rfl

/--
lemma `preimage_comp` / 引理 `preimage_comp`

English:
lemma preimage_comp
  given: {Z : SSet.{u}} (A : Z.Subcomplex) (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 preimage_comp
  条件: {Z : SSet.{u}} (A : Z.Subcomplex) (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma preimage_comp {Z : SSet.{u}} (A : Z.Subcomplex) (f : X ⟶ Y) (g : Y ⟶ Z) :
    A.preimage (f ≫ g) = (A.preimage g).preimage f := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `preimage_ι` / 引理 `preimage_ι`

English:
lemma preimage_ι
  given: (A : X.Subcomplex)
  statement: A.preimage A.ι = ⊤
  proof: by aesop

中文:
引理 preimage_ι
  条件: (A : X.Subcomplex)
  结论: A.preimage A.ι = ⊤
  证明: by aesop
-/
lemma preimage_ι (A : X.Subcomplex) : A.preimage A.ι = ⊤ := by aesop

end

section

variable (A : X.Subcomplex) (f : X ⟶ Y)

/-- The image of a subcomplex by a morphism of simplicial sets. -/
@[simps!]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : Y.Subcomplex
  body: Subfunctor.image A f

中文:
定义 image
  签名: : Y.Subcomplex
  定义体: Subfunctor.image A f

Depends on / 依赖: Subfunctor, Subfunctor.image
-/
def image : Y.Subcomplex := Subfunctor.image A f

/--
lemma `image_le_iff` / 引理 `image_le_iff`

English:
lemma image_le_iff
  given: (Z : Y.Subcomplex)
  proof: by
  simp [Subfunctor.le_def]

中文:
引理 image_le_iff
  条件: (Z : Y.Subcomplex)
  证明: by
  simp [Subfunctor.le_def]

Depends on / 依赖: Subfunctor, Subfunctor.le_def, le_def
-/
lemma image_le_iff (Z : Y.Subcomplex) :
    A.image f <= Z ↔ A <= Z.preimage f := by
  simp [Subfunctor.le_def]

/--
lemma `image_top` / 引理 `image_top`

English:
lemma image_top
  statement: (⊤ : X.Subcomplex).image f = range f
  proof: by aesop

@[simp]

中文:
引理 image_top
  结论: (⊤ : X.Subcomplex).image f = range f
  证明: by aesop

@[simp]
-/
lemma image_top : (⊤ : X.Subcomplex).image f = range f := by aesop

@[simp]
/--
lemma `image_id` / 引理 `image_id`

English:
lemma image_id
  statement: A.image (𝟙 _) = A
  proof: by aesop

中文:
引理 image_id
  结论: A.image (𝟙 _) = A
  证明: by aesop
-/
lemma image_id : A.image (𝟙 _) = A := by aesop

/--
lemma `image_comp` / 引理 `image_comp`

English:
lemma image_comp
  given: {Z : SSet.{u}} (g : Y ⟶ Z)
  proof: by aesop

中文:
引理 image_comp
  条件: {Z : SSet.{u}} (g : Y ⟶ Z)
  证明: by aesop
-/
lemma image_comp {Z : SSet.{u}} (g : Y ⟶ Z) :
    A.image (f ≫ g) = (A.image f).image g := by aesop

/--
lemma `range_comp` / 引理 `range_comp`

English:
lemma range_comp
  given: {Z : SSet.{u}} (g : Y ⟶ Z)
  proof: by aesop

中文:
引理 range_comp
  条件: {Z : SSet.{u}} (g : Y ⟶ Z)
  证明: by aesop
-/
lemma range_comp {Z : SSet.{u}} (g : Y ⟶ Z) :
    Subcomplex.range (f ≫ g) = (Subcomplex.range f).image g := by aesop

set_option backward.defeqAttrib.useBackward true in
/--
lemma `image_eq_range` / 引理 `image_eq_range`

English:
lemma image_eq_range
  statement: A.image f = range (A.ι ≫ f)
  proof: by aesop

中文:
引理 image_eq_range
  结论: A.image f = range (A.ι ≫ f)
  证明: by aesop
-/
lemma image_eq_range : A.image f = range (A.ι ≫ f) := by aesop

/--
lemma `image_iSup` / 引理 `image_iSup`

English:
lemma image_iSup
  given: {ι : Type*} (S : ι -> X.Subcomplex) (f : X ⟶ Y)
  proof: by
  aesop

@[simp]

中文:
引理 image_iSup
  条件: {ι : 类型} (S : ι -> X.Subcomplex) (f : X ⟶ Y)
  证明: by
  aesop

@[simp]
-/
lemma image_iSup {ι : Type*} (S : ι -> X.Subcomplex) (f : X ⟶ Y) :
    image (⨆ i, S i) f = ⨆ i, (S i).image f := by
  aesop

@[simp]
/--
lemma `preimage_range` / 引理 `preimage_range`

English:
lemma preimage_range
  statement: (range f).preimage f = ⊤
  proof: le_antisymm (by simp) (by rw [← image_le_iff, image_top])

@[simp]

中文:
引理 preimage_range
  结论: (range f).preimage f = ⊤
  证明: le_antisymm (by simp) (by rw [← image_le_iff, image_top])

@[simp]

Depends on / 依赖: image_le_iff, image_top, le_antisymm
-/
lemma preimage_range : (range f).preimage f = ⊤ :=
  le_antisymm (by simp) (by rw [← image_le_iff, image_top])

@[simp]
/--
lemma `image_le_range` / 引理 `image_le_range`

English:
lemma image_le_range
  statement: A.image f <= range f
  proof: by
  simp [image_le_iff, preimage_range, le_top]

@[simp]

中文:
引理 image_le_range
  结论: A.image f <= range f
  证明: by
  simp [image_le_iff, preimage_range, le_top]

@[simp]

Depends on / 依赖: image_le_iff, le_top, preimage_range
-/
lemma image_le_range : A.image f <= range f := by
  simp [image_le_iff, preimage_range, le_top]

@[simp]
/--
lemma `image_ofSimplex` / 引理 `image_ofSimplex`

English:
lemma image_ofSimplex
  given: {n : Nat} (x : X _⦋n⦌) (f : X ⟶ Y)
  proof: by
  apply le_antisymm
  · rw [image_le_iff, ofSimplex_le_iff, preimage_obj, Set.mem_preimage]
    apply mem_ofSimplex_obj
  · rw [ofSimplex_le_iff]
    exact ⟨x, mem_ofSimplex_obj _, rfl⟩

中文:
引理 image_ofSimplex
  条件: {n : 自然数} (x : X _⦋n⦌) (f : X ⟶ Y)
  证明: by
  apply le_antisymm
  · rw [image_le_iff, ofSimplex_le_iff, preimage_obj, Set.mem_preimage]
    apply mem_ofSimplex_obj
  · rw [ofSimplex_le_iff]
    exact ⟨x, mem_ofSimplex_obj _, rfl⟩

Depends on / 依赖: Set.mem_preimage, image_le_iff, le_antisymm, mem_ofSimplex_obj, mem_preimage, ofSimplex_le_iff, preimage_obj
-/
lemma image_ofSimplex {n : Nat} (x : X _⦋n⦌) (f : X ⟶ Y) :
    (ofSimplex x).image f = ofSimplex (f.app _ x) := by
  apply le_antisymm
  · rw [image_le_iff, ofSimplex_le_iff, preimage_obj, Set.mem_preimage]
    apply mem_ofSimplex_obj
  · rw [ofSimplex_le_iff]
    exact ⟨x, mem_ofSimplex_obj _, rfl⟩

/-- Given a morphism of simplicial sets `f : X ⟶ Y` and a subcomplex `A` of `X`,
this is the induced morphism from `A` to `A.image f`. -/
@[simps! +dsimpLhs]
/--
Definition of `toImage` / `toImage` 的定义

English:
definition toImage
  signature: : (A : SSet) ⟶ (A.image f : SSet)
  body: (A.image f).lift (A.ι ≫ f) (by rw [image_eq_range])

@[reassoc (attr := simp)]

中文:
定义 toImage
  签名: : (A : SSet) ⟶ (A.image f : SSet)
  定义体: (A.image f).lift (A.ι ≫ f) (by rw [image_eq_range])

@[reassoc (attr := simp)]

Depends on / 依赖: A.image, image_eq_range
-/
def toImage : (A : SSet) ⟶ (A.image f : SSet) :=
  (A.image f).lift (A.ι ≫ f) (by rw [image_eq_range])

@[reassoc (attr := simp)]
/--
lemma `toImage_ι` / 引理 `toImage_ι`

English:
lemma toImage_ι
  statement: A.toImage f ≫ (A.image f).ι = A.ι ≫ f
  proof: rfl

中文:
引理 toImage_ι
  结论: A.toImage f ≫ (A.image f).ι = A.ι ≫ f
  证明: rfl
-/
lemma toImage_ι : A.toImage f ≫ (A.image f).ι = A.ι ≫ f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (A.toImage f)
  body: by
  rw [← range_eq_top_iff]
  apply le_antisymm (by simp)
  rintro m ⟨_, ⟨y, hy, rfl⟩⟩ _
  exact ⟨⟨y, hy⟩, rfl⟩

中文:
实例 :
  签名: Epi (A.toImage f)
  定义体: by
  rw [← range_eq_top_iff]
  apply le_antisymm (by simp)
  rintro m ⟨_, ⟨y, hy, rfl⟩⟩ _
  exact ⟨⟨y, hy⟩, rfl⟩

Depends on / 依赖: le_antisymm, range_eq_top_iff
-/
instance : Epi (A.toImage f) := by
  rw [← range_eq_top_iff]
  apply le_antisymm (by simp)
  rintro m ⟨_, ⟨y, hy, rfl⟩⟩ _
  exact ⟨⟨y, hy⟩, rfl⟩

/--
lemma `image_monotone` / 引理 `image_monotone`

English:
lemma image_monotone
  statement: Monotone (fun (S : X.Subcomplex) => S.image f)
  proof: by
  intro S T h
  rw [image_le_iff]
  exact h.trans (by rw [← image_le_iff])

中文:
引理 image_monotone
  结论: Monotone (fun (S : X.Subcomplex) => S.image f)
  证明: by
  intro S T h
  rw [image_le_iff]
  exact h.trans (by rw [← image_le_iff])

Depends on / 依赖: h.trans, image_le_iff
-/
lemma image_monotone : Monotone (fun (S : X.Subcomplex) => S.image f) := by
  intro S T h
  rw [image_le_iff]
  exact h.trans (by rw [← image_le_iff])

end

/--
lemma `preimage_eq_top_iff` / 引理 `preimage_eq_top_iff`

English:
lemma preimage_eq_top_iff
  given: (B : X.Subcomplex) (f : Y ⟶ X)
  proof: by
  rw [← image_top]; rw [image_le_iff]; rw [top_le_iff]

@[simp]

中文:
引理 preimage_eq_top_iff
  条件: (B : X.Subcomplex) (f : Y ⟶ X)
  证明: by
  rw [← image_top]; rw [image_le_iff]; rw [top_le_iff]

@[simp]

Depends on / 依赖: image_le_iff, image_top, top_le_iff
-/
lemma preimage_eq_top_iff (B : X.Subcomplex) (f : Y ⟶ X) :
    B.preimage f = ⊤ ↔ range f <= B := by
  rw [← image_top]; rw [image_le_iff]; rw [top_le_iff]

@[simp]
/--
lemma `image_preimage_le` / 引理 `image_preimage_le`

English:
lemma image_preimage_le
  given: (B : X.Subcomplex) (f : Y ⟶ X)
  proof: by
  rw [image_le_iff]

@[simp]

中文:
引理 image_preimage_le
  条件: (B : X.Subcomplex) (f : Y ⟶ X)
  证明: by
  rw [image_le_iff]

@[simp]

Depends on / 依赖: image_le_iff
-/
lemma image_preimage_le (B : X.Subcomplex) (f : Y ⟶ X) :
    (B.preimage f).image f <= B := by
  rw [image_le_iff]

@[simp]
/--
lemma `preimage_image_of_isIso` / 引理 `preimage_image_of_isIso`

English:
lemma preimage_image_of_isIso
  given: (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f]
  proof: by
  apply le_antisymm (B.image_preimage_le f)
  · intro n y hy
    exact ⟨(inv f).app _ y, by simpa [← NatIso.isIso_inv_app, ← NatTrans.comp_app_apply]⟩

中文:
引理 preimage_image_of_isIso
  条件: (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f]
  证明: by
  apply le_antisymm (B.image_preimage_le f)
  · intro n y hy
    exact ⟨(inv f).app _ y, by simpa [← NatIso.isIso_inv_app, ← NatTrans.comp_app_apply]⟩

Depends on / 依赖: B.image_preimage_le, NatIso, NatIso.isIso_inv_app, NatTrans, NatTrans.comp_app_apply, comp_app_apply, image_preimage_le, isIso_inv_app, le_antisymm
-/
lemma preimage_image_of_isIso (f : X ⟶ Y) (B : Y.Subcomplex) [IsIso f] :
    (B.preimage f).image f = B := by
  apply le_antisymm (B.image_preimage_le f)
  · intro n y hy
    exact ⟨(inv f).app _ y, by simpa [← NatIso.isIso_inv_app, ← NatTrans.comp_app_apply]⟩

/--
lemma `preimage_inv` / 引理 `preimage_inv`

English:
lemma preimage_inv
  given: {X Y : SSet.{u}} (A : Subcomplex X) (f : X ⟶ Y) [IsIso f]
  proof: by
  ext _ x
  simp only [preimage_obj, NatIso.isIso_inv_app, Set.mem_preimage, image_obj, Set.mem_image]
  exact ⟨fun hx => ⟨(inv f).app _ x, by simpa⟩, by rintro ⟨x, hx, rfl⟩; simpa⟩

中文:
引理 preimage_inv
  条件: {X Y : SSet.{u}} (A : Subcomplex X) (f : X ⟶ Y) [IsIso f]
  证明: by
  ext _ x
  simp only [preimage_obj, NatIso.isIso_inv_app, Set.mem_preimage, image_obj, Set.mem_image]
  exact ⟨fun hx => ⟨(inv f).app _ x, by simpa⟩, by rintro ⟨x, hx, rfl⟩; simpa⟩

Depends on / 依赖: NatIso, NatIso.isIso_inv_app, Set.mem_image, Set.mem_preimage, image_obj, isIso_inv_app, mem_image, mem_preimage, preimage_obj
-/
lemma preimage_inv {X Y : SSet.{u}} (A : Subcomplex X) (f : X ⟶ Y) [IsIso f] :
    A.preimage (inv f) = A.image f := by
  ext _ x
  simp only [preimage_obj, NatIso.isIso_inv_app, Set.mem_preimage, image_obj, Set.mem_image]
  exact ⟨fun hx => ⟨(inv f).app _ x, by simpa⟩, by rintro ⟨x, hx, rfl⟩; simpa⟩

/--
lemma `image_inv` / 引理 `image_inv`

English:
lemma image_inv
  given: {X Y : SSet.{u}} (A : Subcomplex Y) (f : X ⟶ Y) [IsIso f]
  proof: by
  simp [← preimage_inv]

中文:
引理 image_inv
  条件: {X Y : SSet.{u}} (A : Subcomplex Y) (f : X ⟶ Y) [IsIso f]
  证明: by
  simp [← preimage_inv]

Depends on / 依赖: preimage_inv
-/
lemma image_inv {X Y : SSet.{u}} (A : Subcomplex Y) (f : X ⟶ Y) [IsIso f] :
    A.image (inv f) = A.preimage f := by
  simp [← preimage_inv]

/-- Given a morphism of simplicial sets `p : Y ⟶ X` and
`A : X.Subcomplex`, this is the induced morphism
`(A.preimage p : SSet) ⟶ (A : SSet)`. -/
@[simps! +dsimpLhs]
/--
Definition of `fromPreimage` / `fromPreimage` 的定义

English:
definition fromPreimage
  signature: (A : X.Subcomplex) (p : Y ⟶ X)
  body: lift (Subcomplex.ι _ ≫ p) (by simp [range_comp])

@[reassoc (attr := simp)]

中文:
定义 fromPreimage
  签名: (A : X.Subcomplex) (p : Y ⟶ X)
  定义体: lift (Subcomplex.ι _ ≫ p) (by simp [range_comp])

@[reassoc (attr := simp)]

Depends on / 依赖: Subcomplex, range_comp
-/
def fromPreimage (A : X.Subcomplex) (p : Y ⟶ X) :
    (A.preimage p : SSet) ⟶ (A : SSet) :=
  lift (Subcomplex.ι _ ≫ p) (by simp [range_comp])

@[reassoc (attr := simp)]
/--
lemma `fromPreimage_ι` / 引理 `fromPreimage_ι`

English:
lemma fromPreimage_ι
  given: (A : X.Subcomplex) (p : Y ⟶ X)
  proof: rfl

中文:
引理 fromPreimage_ι
  条件: (A : X.Subcomplex) (p : Y ⟶ X)
  证明: rfl
-/
lemma fromPreimage_ι (A : X.Subcomplex) (p : Y ⟶ X) :
    A.fromPreimage p ≫ A.ι = (A.preimage p).ι ≫ p := rfl

end Subcomplex

end SSet
