/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The colimit type of a functor to types

Given a category `J` (with `J : Type u` and `[Category.{v} J]`) and
a functor `F : J ⥤ Type w₀`, we introduce a type `F.ColimitType : Type (max u w₀)`,
which satisfies a certain universal property of the colimit: it is defined
as a suitable quotient of `Σ j, F.obj j`. This universal property is not
expressed in a categorical way (as in general `Type (max u w₀)`
is not the same as `Type u`).

We also introduce a notion of cocone of `F : J ⥤ Type w₀`, this is `F.CoconeTypes`,
or more precisely `Functor.CoconeTypes.{w₁} F`, which consists of a candidate
colimit type for `F` which is in `Type w₁` (in case `w₁ = w₀`, we shall show
this is the same as the data of `c : Cocone F` in the categorical sense).
Given `c : F.CoconeTypes`, we also introduce a property `c.IsColimit` which says
that the canonical map `F.ColimitType → c.pt` is a bijection, and we shall show (TODO)
that when `w₁ = w₀`, it is equivalent to saying that the corresponding cocone
in a categorical sense is a colimit.

## TODO
* refactor `DirectedSystem` and the construction of colimits in `Type`
  by using `Functor.ColimitType`.
* add a similar API for limits in `Type`?

-/

@[expose] public section

universe w₃ w₂ w₁ w₀ w₀' v u

assert_not_exists CategoryTheory.Limits.Cocone

namespace CategoryTheory

variable {J : Type u} [Category.{v} J]

namespace Functor

variable (F : J ⥤ Type w₀)

/--
Definition of `CoconeTypes` / `CoconeTypes` 的定义

English:
structure CoconeTypes
  parameters: where
  axioms and operations (3):
    - pt : Type w₁
    - ι((j : J)) : F.obj j -> pt
    - ι_naturality({j j' : J} (f : j ⟶ j')) : (ι j').comp (F.map f) = ι j  [default: by aesop]

中文:
结构 CoconeTypes
  参数: where
  公理与运算 (3 个):
    - pt : Type w₁
    - ι((j : J)) : F.obj j -> pt
    - ι_naturality({j j' : J} (f : j ⟶ j')) : (ι j').comp (F.map f) = ι j  [默认: by aesop]
-/
structure CoconeTypes where
  /-- the point of the cocone -/
  pt : Type w₁
  /-- a family of maps to `pt` -/
  ι (j : J) : F.obj j -> pt
  ι_naturality {j j' : J} (f : j ⟶ j') :
      (ι j').comp (F.map f) = ι j := by aesop

namespace CoconeTypes

attribute [simp] ι_naturality

variable {F}

@[simp]
/--
lemma `ι_naturality_apply` / 引理 `ι_naturality_apply`

English:
lemma ι_naturality_apply
  given: (c : CoconeTypes.{w₁} F) {j j' : J} (f : j ⟶ j') (x : F.obj j)
  proof: congr_fun (c.ι_naturality f) x

中文:
引理 ι_naturality_apply
  条件: (c : CoconeTypes.{w₁} F) {j j' : J} (f : j ⟶ j') (x : F.obj j)
  证明: congr_fun (c.ι_naturality f) x

Depends on / 依赖: congr_fun
-/
lemma ι_naturality_apply (c : CoconeTypes.{w₁} F) {j j' : J} (f : j ⟶ j') (x : F.obj j) :
    c.ι j' (F.map f x) = c.ι j x :=
  congr_fun (c.ι_naturality f) x

/-- Given `c : F.CoconeTypes` and a map `φ : c.pt → T`, this is
the cocone for `F` obtained by postcomposition with `φ`. -/
@[simps -fullyApplied]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: (c : CoconeTypes.{w₁} F) {T : Type w₂} (φ : c.pt -> T)
  body: T
  ι j := φ.comp (c.ι j)

中文:
定义 postcomp
  签名: (c : CoconeTypes.{w₁} F) {T : Type w₂} (φ : c.pt -> T)
  定义体: T
  ι j := φ.comp (c.ι j)
-/
def postcomp (c : CoconeTypes.{w₁} F) {T : Type w₂} (φ : c.pt -> T) :
    F.CoconeTypes where
  pt := T
  ι j := φ.comp (c.ι j)

/-- The cocone for `G : J ⥤ Type w₀'` that is deduced from a cocone for `F : J ⥤ Type w₀`
and a natural map `G.obj j → F.obj j` for all `j : J`. -/
@[simps -fullyApplied]
/--
Definition of `precompose` / `precompose` 的定义

English:
definition precompose
  signature: (c : CoconeTypes.{w₁} F) {G : J ⥤ Type w₀'} (app : forall j, G.obj j -> F.obj j)
  body: c.pt
  ι j := c.ι j ∘ app j
  ι_naturality f := by
    rw [Function.comp_assoc]; rw [naturality]; rw [← Function.comp_assoc]; rw [ι_naturality]

中文:
定义 precompose
  签名: (c : CoconeTypes.{w₁} F) {G : J ⥤ Type w₀'} (app : 对任意 j, G.obj j -> F.obj j)
  定义体: c.pt
  ι j := c.ι j ∘ app j
  ι_naturality f := by
    rw [Function.comp_assoc]; rw [naturality]; rw [← Function.comp_assoc]; rw [ι_naturality]

Depends on / 依赖: c.pt
-/
def precompose (c : CoconeTypes.{w₁} F) {G : J ⥤ Type w₀'} (app : forall j, G.obj j -> F.obj j)
    (naturality : forall {j j'} (f : j ⟶ j'), app j' ∘ G.map f = F.map f ∘ app j) :
    CoconeTypes.{w₁} G where
  pt := c.pt
  ι j := c.ι j ∘ app j
  ι_naturality f := by
    rw [Function.comp_assoc]; rw [naturality]; rw [← Function.comp_assoc]; rw [ι_naturality]

set_option backward.defeqAttrib.useBackward true in
/-- Given `F : J ⥤ w₀`, `c : F.CoconeTypes` and `G : J' ⥤ J`, this is
the induced cocone in `(G ⋙ F).CoconeTypes`. -/
@[simps]
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: (c : CoconeTypes.{w₁} F) {J' : Type*} [Category* J'] (G : J' ⥤ J)
  body: c.pt
  ι _ := c.ι _

中文:
定义 precomp
  签名: (c : CoconeTypes.{w₁} F) {J' : 类型} [Category* J'] (G : J' ⥤ J)
  定义体: c.pt
  ι _ := c.ι _

Depends on / 依赖: c.pt
-/
def precomp (c : CoconeTypes.{w₁} F) {J' : Type*} [Category* J'] (G : J' ⥤ J) :
    CoconeTypes.{w₁} (G ⋙ F) where
  pt := c.pt
  ι _ := c.ι _

end CoconeTypes

/--
Definition of `ColimitTypeRel` / `ColimitTypeRel` 的定义

English:
definition ColimitTypeRel
  signature: : (Σ j, F.obj j) -> (Σ j, F.obj j) -> Prop
  body: fun p p' => exists f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

中文:
定义 ColimitTypeRel
  签名: : (Σ j, F.obj j) -> (Σ j, F.obj j) -> 命题
  定义体: fun p p' => exists f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

Depends on / 依赖: F.map
-/
def ColimitTypeRel : (Σ j, F.obj j) -> (Σ j, F.obj j) -> Prop :=
  fun p p' => exists f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

/--
Definition of `ColimitType` / `ColimitType` 的定义

English:
definition ColimitType
  signature: : Type (max u w₀)
  body: Quot F.ColimitTypeRel

中文:
定义 ColimitType
  签名: : Type (max u w₀)
  定义体: Quot F.ColimitTypeRel

Depends on / 依赖: ColimitTypeRel, F.ColimitTypeRel
-/
def ColimitType : Type (max u w₀) := Quot F.ColimitTypeRel

/--
Definition of `ιColimitType` / `ιColimitType` 的定义

English:
definition ιColimitType
  signature: (j : J) (x : F.obj j)
  body: Quot.mk _ ⟨j, x⟩

中文:
定义 ιColimitType
  签名: (j : J) (x : F.obj j)
  定义体: Quot.mk _ ⟨j, x⟩

Depends on / 依赖: Quot.mk
-/
def ιColimitType (j : J) (x : F.obj j) : F.ColimitType :=
  Quot.mk _ ⟨j, x⟩

/--
lemma `ιColimitType_eq_iff` / 引理 `ιColimitType_eq_iff`

English:
lemma ιColimitType_eq_iff
  given: {j j' : J} (x : F.obj j) (y : F.obj j')
  proof: Quot.eq

中文:
引理 ιColimitType_eq_iff
  条件: {j j' : J} (x : F.obj j) (y : F.obj j')
  证明: Quot.eq

Depends on / 依赖: Quot.eq, add_comm
-/
lemma ιColimitType_eq_iff {j j' : J} (x : F.obj j) (y : F.obj j') :
    F.ιColimitType j x = F.ιColimitType j' y ↔
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', y⟩ :=
  Quot.eq

/--
lemma `ιColimitType_eq_of_map_eq_map` / 引理 `ιColimitType_eq_of_map_eq_map`

English:
lemma ιColimitType_eq_of_map_eq_map
  statement: {j j' : J} (x : F.obj j) (y : F.obj j')
  proof: (ιColimitType_eq_iff ..).mpr (.trans _ _ _ (.rel _ ⟨k, F.map f x⟩ ⟨f, rfl⟩)
    (.symm _ _ (.rel _ _ ⟨f', H⟩)))

中文:
引理 ιColimitType_eq_of_map_eq_map
  结论: {j j' : J} (x : F.obj j) (y : F.obj j')
  证明: (ιColimitType_eq_iff ..).mpr (.trans _ _ _ (.rel _ ⟨k, F.map f x⟩ ⟨f, rfl⟩)
    (.symm _ _ (.rel _ _ ⟨f', H⟩)))

Depends on / 依赖: F.map
-/
lemma ιColimitType_eq_of_map_eq_map {j j' : J} (x : F.obj j) (y : F.obj j')
    {k : J} (f : j ⟶ k) (f' : j' ⟶ k) (H : F.map f x = F.map f' y) :
    F.ιColimitType j x = F.ιColimitType j' y :=
  (ιColimitType_eq_iff ..).mpr (.trans _ _ _ (.rel _ ⟨k, F.map f x⟩ ⟨f, rfl⟩)
    (.symm _ _ (.rel _ _ ⟨f', H⟩)))

/--
lemma `ιColimitType_jointly_surjective` / 引理 `ιColimitType_jointly_surjective`

English:
lemma ιColimitType_jointly_surjective
  given: (t : F.ColimitType)
  proof: by
  obtain ⟨_, _⟩ := t
  exact ⟨_, _, rfl⟩

@[simp]

中文:
引理 ιColimitType_jointly_surjective
  条件: (t : F.ColimitType)
  证明: by
  obtain ⟨_, _⟩ := t
  exact ⟨_, _, rfl⟩

@[simp]
-/
lemma ιColimitType_jointly_surjective (t : F.ColimitType) :
    exists j x, F.ιColimitType j x = t := by
  obtain ⟨_, _⟩ := t
  exact ⟨_, _, rfl⟩

@[simp]
/--
lemma `ιColimitType_map` / 引理 `ιColimitType_map`

English:
lemma ιColimitType_map
  given: {j j' : J} (f : j ⟶ j') (x : F.obj j)
  proof: (Quot.sound ⟨f, rfl⟩).symm

中文:
引理 ιColimitType_map
  条件: {j j' : J} (f : j ⟶ j') (x : F.obj j)
  证明: (Quot.sound ⟨f, rfl⟩).symm

Depends on / 依赖: Quot.sound
-/
lemma ιColimitType_map {j j' : J} (f : j ⟶ j') (x : F.obj j) :
    F.ιColimitType j' (F.map f x) = F.ιColimitType j x :=
  (Quot.sound ⟨f, rfl⟩).symm

/-- The cocone corresponding to `F.ColimitType`. -/
@[simps -fullyApplied]
/--
Definition of `coconeTypes` / `coconeTypes` 的定义

English:
definition coconeTypes
  signature: : F.CoconeTypes where
  body: F.ColimitType
  ι j := F.ιColimitType j

中文:
定义 coconeTypes
  签名: : F.CoconeTypes where
  定义体: F.ColimitType
  ι j := F.ιColimitType j

Depends on / 依赖: ColimitType, F.ColimitType
-/
def coconeTypes : F.CoconeTypes where
  pt := F.ColimitType
  ι j := F.ιColimitType j

/--
Definition of `descColimitType` / `descColimitType` 的定义

English:
definition descColimitType
  signature: (c : F.CoconeTypes)
  body: Quot.lift (fun ⟨j, x⟩ => c.ι j x) (by rintro _ _ ⟨_, _⟩; aesop)

@[simp]

中文:
定义 descColimitType
  签名: (c : F.CoconeTypes)
  定义体: Quot.lift (fun ⟨j, x⟩ => c.ι j x) (by rintro _ _ ⟨_, _⟩; aesop)

@[simp]

Depends on / 依赖: Quot.lift
-/
def descColimitType (c : F.CoconeTypes) : F.ColimitType -> c.pt :=
  Quot.lift (fun ⟨j, x⟩ => c.ι j x) (by rintro _ _ ⟨_, _⟩; aesop)

@[simp]
/--
lemma `descColimitType_comp_ι` / 引理 `descColimitType_comp_ι`

English:
lemma descColimitType_comp_ι
  given: (c : F.CoconeTypes) (j : J)
  proof: rfl

@[simp]

中文:
引理 descColimitType_comp_ι
  条件: (c : F.CoconeTypes) (j : J)
  证明: rfl

@[simp]
-/
lemma descColimitType_comp_ι (c : F.CoconeTypes) (j : J) :
    (F.descColimitType c).comp (F.ιColimitType j) = c.ι j := rfl

@[simp]
/--
lemma `descColimitType_ιColimitType_apply` / 引理 `descColimitType_ιColimitType_apply`

English:
lemma descColimitType_ιColimitType_apply
  given: (c : F.CoconeTypes) (j : J) (x : F.obj j)
  proof: rfl

中文:
引理 descColimitType_ιColimitType_apply
  条件: (c : F.CoconeTypes) (j : J) (x : F.obj j)
  证明: rfl
-/
lemma descColimitType_ιColimitType_apply (c : F.CoconeTypes) (j : J) (x : F.obj j) :
    F.descColimitType c (F.ιColimitType j x) = c.ι j x := rfl

namespace CoconeTypes

variable {F} (c : CoconeTypes.{w₁} F)

/--
lemma `descColimitType_surjective_iff` / 引理 `descColimitType_surjective_iff`

English:
lemma descColimitType_surjective_iff
  proof: by
  constructor
  · intro h z
    obtain ⟨⟨i, x⟩, rfl⟩ := h z
    exact ⟨i, x, rfl⟩
  · intro h z
    obtain ⟨i, x, rfl⟩ := h z
    exact ⟨F.ιColimitType i x, rfl⟩

中文:
引理 descColimitType_surjective_iff
  证明: by
  constructor
  · intro h z
    obtain ⟨⟨i, x⟩, rfl⟩ := h z
    exact ⟨i, x, rfl⟩
  · intro h z
    obtain ⟨i, x, rfl⟩ := h z
    exact ⟨F.ιColimitType i x, rfl⟩
-/
lemma descColimitType_surjective_iff :
    Function.Surjective (F.descColimitType c) ↔
      forall (z : c.pt), exists (i : J) (x : F.obj i), c.ι i x = z := by
  constructor
  · intro h z
    obtain ⟨⟨i, x⟩, rfl⟩ := h z
    exact ⟨i, x, rfl⟩
  · intro h z
    obtain ⟨i, x, rfl⟩ := h z
    exact ⟨F.ιColimitType i x, rfl⟩

/--
Definition of `IsColimit` / `IsColimit` 的定义

English:
structure IsColimit
  parameters: : Prop where
  axioms and operations (1):
    - bijective : Function.Bijective (F.descColimitType c)

中文:
结构 IsColimit
  参数: : 命题 where
  公理与运算 (1 个):
    - bijective : Function.Bijective (F.descColimitType c)
-/
structure IsColimit : Prop where
  bijective : Function.Bijective (F.descColimitType c)

namespace IsColimit

variable {c} (hc : c.IsColimit)

include hc

/-- Given `F : J ⥤ Type w₀`, and `c : F.CoconeTypes` a cocone that is a colimit,
this is the equivalence `F.ColimitType ≃ c.pt`. -/
@[simps! apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : F.ColimitType ≃ c.pt
  body: Equiv.ofBijective _ hc.bijective

@[simp]

中文:
定义 equiv
  签名: : F.ColimitType ≃ c.pt
  定义体: Equiv.ofBijective _ hc.bijective

@[simp]

Depends on / 依赖: Equiv.ofBijective, bijective, hc.bijective, ofBijective
-/
noncomputable def equiv : F.ColimitType ≃ c.pt :=
  Equiv.ofBijective _ hc.bijective

@[simp]
/--
lemma `equiv_symm_ι_apply` / 引理 `equiv_symm_ι_apply`

English:
lemma equiv_symm_ι_apply
  given: (j : J) (x : F.obj j)
  proof: hc.equiv.injective (by simp)

中文:
引理 equiv_symm_ι_apply
  条件: (j : J) (x : F.obj j)
  证明: hc.equiv.injective (by simp)

Depends on / 依赖: hc.equiv.injective, injective
-/
lemma equiv_symm_ι_apply (j : J) (x : F.obj j) :
    hc.equiv.symm (c.ι j x) = F.ιColimitType j x :=
  hc.equiv.injective (by simp)

/--
lemma `ι_jointly_surjective` / 引理 `ι_jointly_surjective`

English:
lemma ι_jointly_surjective
  given: (y : c.pt)
  proof: by
  obtain ⟨z, rfl⟩ := hc.equiv.surjective y
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective z
  exact ⟨j, x, rfl⟩

中文:
引理 ι_jointly_surjective
  条件: (y : c.pt)
  证明: by
  obtain ⟨z, rfl⟩ := hc.equiv.surjective y
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective z
  exact ⟨j, x, rfl⟩

Depends on / 依赖: hc.equiv.surjective, surjective
-/
lemma ι_jointly_surjective (y : c.pt) :
    exists j x, c.ι j x = y := by
  obtain ⟨z, rfl⟩ := hc.equiv.surjective y
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective z
  exact ⟨j, x, rfl⟩

/--
lemma `funext` / 引理 `funext`

English:
lemma funext
  statement: {T : Type w₂} {f g : c.pt -> T}
  proof: by
  funext y
  obtain ⟨j, x, rfl⟩ := hc.ι_jointly_surjective y
  exact congr_fun (h j) x

中文:
引理 funext
  结论: {T : Type w₂} {f g : c.pt -> T}
  证明: by
  funext y
  obtain ⟨j, x, rfl⟩ := hc.ι_jointly_surjective y
  exact congr_fun (h j) x

Depends on / 依赖: congr_fun
-/
lemma funext {T : Type w₂} {f g : c.pt -> T}
    (h : forall j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g := by
  funext y
  obtain ⟨j, x, rfl⟩ := hc.ι_jointly_surjective y
  exact congr_fun (h j) x

/--
lemma `exists_desc` / 引理 `exists_desc`

English:
lemma exists_desc
  given: (c' : CoconeTypes.{w₂} F)
  proof: ⟨(F.descColimitType c').comp hc.equiv.symm, by aesop⟩

中文:
引理 exists_desc
  条件: (c' : CoconeTypes.{w₂} F)
  证明: ⟨(F.descColimitType c').comp hc.equiv.symm, by aesop⟩

Depends on / 依赖: F.descColimitType, descColimitType, hc.equiv.symm
-/
lemma exists_desc (c' : CoconeTypes.{w₂} F) :
    exists (f : c.pt -> c'.pt), forall (j : J), f.comp (c.ι j) = c'.ι j :=
  ⟨(F.descColimitType c').comp hc.equiv.symm, by aesop⟩

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (c' : CoconeTypes.{w₂} F)
  body: (hc.exists_desc c').choose

@[simp]

中文:
定义 desc
  签名: (c' : CoconeTypes.{w₂} F)
  定义体: (hc.exists_desc c').choose

@[simp]

Depends on / 依赖: exists_desc, hc.exists_desc
-/
noncomputable def desc (c' : CoconeTypes.{w₂} F) : c.pt -> c'.pt :=
  (hc.exists_desc c').choose

@[simp]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  given: (c' : CoconeTypes.{w₂} F) (j : J)
  proof: (hc.exists_desc c').choose_spec j

@[simp]

中文:
引理 fac
  条件: (c' : CoconeTypes.{w₂} F) (j : J)
  证明: (hc.exists_desc c').choose_spec j

@[simp]

Depends on / 依赖: choose_spec, exists_desc, hc.exists_desc
-/
lemma fac (c' : CoconeTypes.{w₂} F) (j : J) :
    (hc.desc c').comp (c.ι j) = c'.ι j :=
  (hc.exists_desc c').choose_spec j

@[simp]
/--
lemma `fac_apply` / 引理 `fac_apply`

English:
lemma fac_apply
  given: (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j)
  proof: congr_fun (hc.fac c' j) x

中文:
引理 fac_apply
  条件: (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j)
  证明: congr_fun (hc.fac c' j) x

Depends on / 依赖: congr_fun, hc.fac
-/
lemma fac_apply (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) :
    hc.desc c' (c.ι j x) = c'.ι j x :=
  congr_fun (hc.fac c' j) x

/--
lemma `of_equiv` / 引理 `of_equiv`

English:
lemma of_equiv
  statement: {c' : CoconeTypes.{w₂} F} (e : c.pt ≃ c'.pt)
  proof: by
    convert! Function.Bijective.comp e.bijective hc.bijective
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    simp_all

中文:
引理 of_equiv
  结论: {c' : CoconeTypes.{w₂} F} (e : c.pt ≃ c'.pt)
  证明: by
    convert! Function.Bijective.comp e.bijective hc.bijective
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    simp_all

Depends on / 依赖: Bijective, Function, Function.Bijective.comp, bijective, convert, e.bijective, hc.bijective
-/
lemma of_equiv {c' : CoconeTypes.{w₂} F} (e : c.pt ≃ c'.pt)
    (he : forall j x, c'.ι j x = e (c.ι j x)) : c'.IsColimit where
  bijective := by
    convert! Function.Bijective.comp e.bijective hc.bijective
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    simp_all

/--
lemma `iff_bijective` / 引理 `iff_bijective`

English:
lemma iff_bijective
  statement: {c' : CoconeTypes.{w₂} F}
  proof: by
  refine ⟨fun hc' => ?_, fun h => hc.of_equiv (Equiv.ofBijective _ h) hf⟩
  have h₁ := hc.bijective
  rw [← Function.Bijective.of_comp_iff _ hc.bijective]
  convert! hc'.bijective
  ext x
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective x
  simp [hf]

中文:
引理 iff_bijective
  结论: {c' : CoconeTypes.{w₂} F}
  证明: by
  refine ⟨fun hc' => ?_, fun h => hc.of_equiv (Equiv.ofBijective _ h) hf⟩
  have h₁ := hc.bijective
  rw [← Function.Bijective.of_comp_iff _ hc.bijective]
  convert! hc'.bijective
  ext x
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective x
  simp [hf]

Depends on / 依赖: Bijective, Equiv.ofBijective, Function, Function.Bijective.of_comp_iff, bijective, convert, hc.bijective, hc.of_equiv, ofBijective, of_comp_iff, of_equiv
-/
lemma iff_bijective {c' : CoconeTypes.{w₂} F}
    (f : c.pt -> c'.pt) (hf : forall j x, c'.ι j x = f (c.ι j x)) :
    c'.IsColimit ↔ Function.Bijective f := by
  refine ⟨fun hc' => ?_, fun h => hc.of_equiv (Equiv.ofBijective _ h) hf⟩
  have h₁ := hc.bijective
  rw [← Function.Bijective.of_comp_iff _ hc.bijective]
  convert! hc'.bijective
  ext x
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective x
  simp [hf]

end IsColimit

/--
Definition of `IsColimitCore` / `IsColimitCore` 的定义

English:
structure IsColimitCore
  parameters: where
  axioms and operations (3):
    - desc((c' : CoconeTypes.{w₂} F)) : c.pt -> c'.pt
    - fac((c' : CoconeTypes.{w₂} F) (j : J)) : (desc c').comp (c.ι j) = c'.ι j  [default: by aesop]
    - funext({T : Type w₂} {f g : c.pt -> T} (h : forall j, f.comp (c.ι j) = g.comp (c.ι j))) : f = g

中文:
结构 IsColimitCore
  参数: where
  公理与运算 (3 个):
    - desc((c' : CoconeTypes.{w₂} F)) : c.pt -> c'.pt
    - fac((c' : CoconeTypes.{w₂} F) (j : J)) : (desc c').comp (c.ι j) = c'.ι j  [默认: by aesop]
    - funext({T : Type w₂} {f g : c.pt -> T} (h : 对任意 j, f.comp (c.ι j) = g.comp (c.ι j))) : f = g

Depends on / 依赖: c.pt, f.comp, g.comp
-/
structure IsColimitCore where
  /-- any cocone descends (in a unique way) as a map -/
  desc (c' : CoconeTypes.{w₂} F) : c.pt -> c'.pt
  fac (c' : CoconeTypes.{w₂} F) (j : J) :
    (desc c').comp (c.ι j) = c'.ι j := by aesop
  funext {T : Type w₂} {f g : c.pt -> T}
    (h : forall j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g

namespace IsColimitCore

attribute [simp] fac

variable {c}

@[simp]
/--
lemma `fac_apply` / 引理 `fac_apply`

English:
lemma fac_apply
  statement: (hc : IsColimitCore.{w₂} c)
  proof: congr_fun (hc.fac c' j) x

中文:
引理 fac_apply
  结论: (hc : IsColimitCore.{w₂} c)
  证明: congr_fun (hc.fac c' j) x

Depends on / 依赖: congr_fun, hc.fac
-/
lemma fac_apply (hc : IsColimitCore.{w₂} c)
    (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) :
    hc.desc c' (c.ι j x) = c'.ι j x :=
  congr_fun (hc.fac c' j) x

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `down` / `down` 的定义

English:
definition down
  signature: (hc : IsColimitCore.{max w₂ w₃} c)
  body: Equiv.ulift.toFun.comp
    (hc.desc (c'.postcomp Equiv.ulift.{w₃}.symm))
  fac c' j := by
    rw [Function.comp_assoc]; rw [hc.fac]
    rfl
  funext {T f g} h := by
    suffices Equiv.ulift.{w₃}.invFun.comp f =
        Equiv.ulift.invFun.comp g by
      ext x
      simpa using congr_fun this x
    e

中文:
定义 down
  签名: (hc : IsColimitCore.{max w₂ w₃} c)
  定义体: Equiv.ulift.toFun.comp
    (hc.desc (c'.postcomp Equiv.ulift.{w₃}.symm))
  fac c' j := by
    rw [Function.comp_assoc]; rw [hc.fac]
    rfl
  funext {T f g} h := by
    suffices Equiv.ulift.{w₃}.invFun.comp f =
        Equiv.ulift.invFun.comp g by
      ext x
      simpa using congr_fun this x
    e

Depends on / 依赖: Equiv.ulift.toFun.comp
-/
def down (hc : IsColimitCore.{max w₂ w₃} c) :
    IsColimitCore.{w₂} c where
  desc c' := Equiv.ulift.toFun.comp
    (hc.desc (c'.postcomp Equiv.ulift.{w₃}.symm))
  fac c' j := by
    rw [Function.comp_assoc]; rw [hc.fac]
    rfl
  funext {T f g} h := by
    suffices Equiv.ulift.{w₃}.invFun.comp f =
        Equiv.ulift.invFun.comp g by
      ext x
      simpa using congr_fun this x
    exact hc.funext (fun j => by simp [Function.comp_assoc, h])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `precompose` / `precompose` 的定义

English:
definition precompose
  signature: (hc : IsColimitCore.{w₂} c)
  body: hc.desc (c'.precompose _ (FunctorToTypes.naturality_symm e naturality))
  fac c' j := by
    rw [precompose_ι]; rw [← Function.comp_assoc]; rw [hc.fac]; rw [precompose_ι]; rw [Function.comp_assoc]; rw [Equiv.symm_comp_self]; rw [Function.comp_id]
  funext {T f g} h := hc.funext (fun j => by
    ext 

中文:
定义 precompose
  签名: (hc : IsColimitCore.{w₂} c)
  定义体: hc.desc (c'.precompose _ (FunctorToTypes.naturality_symm e naturality))
  fac c' j := by
    rw [precompose_ι]; rw [← Function.comp_assoc]; rw [hc.fac]; rw [precompose_ι]; rw [Function.comp_assoc]; rw [Equiv.symm_comp_self]; rw [Function.comp_id]
  funext {T f g} h := hc.funext (fun j => by
    ext 

Depends on / 依赖: FunctorToTypes, FunctorToTypes.naturality_symm, hc.desc, naturality, naturality_symm, precompose
-/
def precompose (hc : IsColimitCore.{w₂} c)
    {G : J ⥤ Type w₀'} (e : forall j, G.obj j ≃ F.obj j)
    (naturality : forall {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    IsColimitCore.{w₂} (c.precompose _ naturality) where
  desc c' := hc.desc (c'.precompose _ (FunctorToTypes.naturality_symm e naturality))
  fac c' j := by
    rw [precompose_ι]; rw [← Function.comp_assoc]; rw [hc.fac]; rw [precompose_ι]; rw [Function.comp_assoc]; rw [Equiv.symm_comp_self]; rw [Function.comp_id]
  funext {T f g} h := hc.funext (fun j => by
    ext x
    obtain ⟨y, rfl⟩ := (e j).surjective x
    exact congr_fun (h j) y)

end IsColimitCore

variable {c} in
/-- When `c : F.CoconeTypes` satisfies the property
`c.IsColimit`, this is a term in `IsColimitCore.{w₂} c`
for any universe `w₂`. -/
@[simps]
/--
Definition of `IsColimit.isColimitCore` / `IsColimit.isColimitCore` 的定义

English:
definition IsColimit.isColimitCore
  signature: (hc : c.IsColimit)
  body: hc.desc
  funext := hc.funext

中文:
定义 IsColimit.isColimitCore
  签名: (hc : c.IsColimit)
  定义体: hc.desc
  funext := hc.funext

Depends on / 依赖: hc.desc
-/
noncomputable def IsColimit.isColimitCore (hc : c.IsColimit) :
    IsColimitCore.{w₂} c where
  desc := hc.desc
  funext := hc.funext

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsColimitCore.isColimit` / 引理 `IsColimitCore.isColimit`

English:
lemma IsColimitCore.isColimit
  given: (hc : IsColimitCore.{max u w₀ w₁} c)
  proof: by
    let e : F.ColimitType ≃ c.pt :=
      { toFun := F.descColimitType c
        invFun := (down.{max u w₁} hc).desc F.coconeTypes
        left_inv y := by
          obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
          simp
        right_inv := by
          have : (F.descColimitTyp

中文:
引理 IsColimitCore.isColimit
  条件: (hc : IsColimitCore.{max u w₀ w₁} c)
  证明: by
    let e : F.ColimitType ≃ c.pt :=
      { toFun := F.descColimitType c
        invFun := (down.{max u w₁} hc).desc F.coconeTypes
        left_inv y := by
          obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
          simp
        right_inv := by
          have : (F.descColimitTyp

Depends on / 依赖: ColimitType, F.ColimitType, F.coconeTypes, F.descColimitType, Function, Function.comp_assoc, Function.id_comp, bijective, c.pt, coconeTypes, comp_assoc, congr_fun, descColimitType, e.bijective, id_comp, invFun, left_inv, right_inv
-/
lemma IsColimitCore.isColimit (hc : IsColimitCore.{max u w₀ w₁} c) :
    c.IsColimit where
  bijective := by
    let e : F.ColimitType ≃ c.pt :=
      { toFun := F.descColimitType c
        invFun := (down.{max u w₁} hc).desc F.coconeTypes
        left_inv y := by
          obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
          simp
        right_inv := by
          have : (F.descColimitType c).comp
              ((down.{max u w₁} hc).desc F.coconeTypes) = id :=
            (down.{max u w₀} hc).funext (fun j => by
              rw [Function.id_comp]; rw [Function.comp_assoc]; rw [fac]; rw [coconeTypes_ι]; rw [descColimitType_comp_ι])
          exact congr_fun this }
    exact e.bijective

variable {c} in
/--
lemma `IsColimit.precompose` / 引理 `IsColimit.precompose`

English:
lemma IsColimit.precompose
  statement: (hc : c.IsColimit) {G : J ⥤ Type w₀'} (e : forall j, G.obj j ≃ F.obj j)
  proof: (hc.isColimitCore.precompose e naturality).isColimit

中文:
引理 IsColimit.precompose
  结论: (hc : c.IsColimit) {G : J ⥤ Type w₀'} (e : 对任意 j, G.obj j ≃ F.obj j)
  证明: (hc.isColimitCore.precompose e naturality).isColimit

Depends on / 依赖: hc.isColimitCore.precompose, isColimit, isColimitCore, naturality, precompose
-/
lemma IsColimit.precompose (hc : c.IsColimit) {G : J ⥤ Type w₀'} (e : forall j, G.obj j ≃ F.obj j)
    (naturality : forall {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    (c.precompose _ naturality).IsColimit :=
  (hc.isColimitCore.precompose e naturality).isColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isColimit_precompose_iff` / 引理 `isColimit_precompose_iff`

English:
lemma isColimit_precompose_iff
  statement: {G : J ⥤ Type w₀'} (e : forall j, G.obj j ≃ F.obj j)
  proof: ⟨fun hc => (hc.precompose (fun j => (e j).symm)
      (FunctorToTypes.naturality_symm e naturality)).of_equiv (Equiv.refl _) (by simp),
    fun hc => hc.precompose e naturality⟩

中文:
引理 isColimit_precompose_iff
  结论: {G : J ⥤ Type w₀'} (e : 对任意 j, G.obj j ≃ F.obj j)
  证明: ⟨fun hc => (hc.precompose (fun j => (e j).symm)
      (FunctorToTypes.naturality_symm e naturality)).of_equiv (Equiv.refl _) (by simp),
    fun hc => hc.precompose e naturality⟩

Depends on / 依赖: Equiv.refl, FunctorToTypes, FunctorToTypes.naturality_symm, hc.precompose, naturality, naturality_symm, of_equiv, precompose
-/
lemma isColimit_precompose_iff {G : J ⥤ Type w₀'} (e : forall j, G.obj j ≃ F.obj j)
    (naturality : forall {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    (c.precompose _ naturality).IsColimit ↔ c.IsColimit :=
  ⟨fun hc => (hc.precompose (fun j => (e j).symm)
      (FunctorToTypes.naturality_symm e naturality)).of_equiv (Equiv.refl _) (by simp),
    fun hc => hc.precompose e naturality⟩

end CoconeTypes

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isColimit_coconeTypes` / 引理 `isColimit_coconeTypes`

English:
lemma isColimit_coconeTypes
  statement: F.coconeTypes.IsColimit where
  proof: by
    convert! Function.bijective_id
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    rfl

中文:
引理 isColimit_coconeTypes
  结论: F.coconeTypes.IsColimit where
  证明: by
    convert! Function.bijective_id
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    rfl

Depends on / 依赖: Function, Function.bijective_id, bijective_id, convert
-/
lemma isColimit_coconeTypes : F.coconeTypes.IsColimit where
  bijective := by
    convert! Function.bijective_id
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    rfl

end Functor

end CategoryTheory
