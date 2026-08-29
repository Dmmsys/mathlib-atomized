/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Andrew Yang, Joël Riou
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# Shift

A `Shift` on a category `C` indexed by a monoid `A` is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexes the terms, so the degree `i` term of `Shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `HasShift`: A typeclass asserting the existence of a shift functor.
* `shiftEquiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  a self-equivalence of `C`.
* `shiftComm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

`[HasShift C A]` is implemented using monoidal functors from `Discrete A` to `C ⥤ C`.
However, the API of monoidal functors is used only internally: one should use the API of
shift functors which includes `shiftFunctor C a : C ⥤ C` for `a : A`,
`shiftFunctorZero C A : shiftFunctor C (0 : A) ≅ 𝟭 C` and
`shiftFunctorAdd C i j : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j`
(and its variant `shiftFunctorAdd'`). These isomorphisms satisfy some coherence properties
which are stated in lemmas like `shiftFunctorAdd'_assoc`, `shiftFunctorAdd'_zero_add` and
`shiftFunctorAdd'_add_zero`.

-/

@[expose] public section


namespace CategoryTheory

open CategoryTheory.Functor

noncomputable section

universe v u

variable (C : Type u) (A : Type*) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

variable {A C}

section Defs

variable (A C) [AddMonoid A]

/--
Definition of `HasShift` / `HasShift` 的定义

English:
class HasShift
  parameters: (C : Type u) (A : Type*) [Category.{v} C] [AddMonoid A]
  axioms and operations (2):
    - shift : Discrete A ⥤ C ⥤ C
    - shiftMonoidal : shift.Monoidal  [default: by infer_instance]

中文:
类 HasShift
  参数: (C : 类型u) (A : 类型) [Category.{v} C] [AddMonoid A]
  公理与运算 (2 个):
    - shift : Discrete A ⥤ C ⥤ C
    - shiftMonoidal : shift.Monoidal  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasShift (C : Type u) (A : Type*) [Category.{v} C] [AddMonoid A] where
  /-- a shift is a monoidal functor from `A` to `C ⥤ C` -/
  shift : Discrete A ⥤ C ⥤ C
  /-- `shift` is monoidal -/
  shiftMonoidal : shift.Monoidal := by infer_instance

/--
Definition of `ShiftMkCore` / `ShiftMkCore` 的定义

English:
structure ShiftMkCore
  parameters: where
  axioms and operations (6):
    - F : A -> C ⥤ C
    - zero : F 0 ≅ 𝟭 C
    - add : forall n m : A, F (n + m) ≅ F n ⋙ F m
    - assoc_hom_app : forall (m₁ m₂ m₃ : A) (X : C), (add (m₁ + m₂) m₃).hom.app X ≫ (F m₃).map ((add m₁ m₂).hom.app X) = eqToHom (by rw [add_assoc]) ≫ (add m₁ (m₂ + m₃)).hom.app X ≫ (add m₂ m₃).hom.app ((F m₁).obj X)  [default: by cat_disch]
    - zero_add_hom_app : forall (n : A) (X : C), (add 0 n).hom.app X = eqToHom (by dsimp; rw [zero_add]) ≫ (F n).map (zero.inv.app X)  [default: by cat_disch]
    - add_zero_hom_app : forall (n : A) (X : C), (add n 0).hom.app X = eqToHom (by dsimp; rw [add_zero]) ≫ zero.inv.app ((F n).obj X)  [default: by cat_disch]

中文:
结构 ShiftMkCore
  参数: where
  公理与运算 (6 个):
    - F : A -> C ⥤ C
    - zero : F 0 ≅ 𝟭 C
    - add : 对任意 n m : A, F (n + m) ≅ F n ⋙ F m
    - assoc_hom_app : 对任意 (m₁ m₂ m₃ : A) (X : C), (add (m₁ + m₂) m₃).hom.app X ≫ (F m₃).map ((add m₁ m₂).hom.app X) = eqToHom (by rw [add_assoc]) ≫ (add m₁ (m₂ + m₃)).hom.app X ≫ (add m₂ m₃).hom.app ((F m₁).obj X)  [默认: by cat_disch]
    - zero_add_hom_app : 对任意 (n : A) (X : C), (add 0 n).hom.app X = eqToHom (by dsimp; rw [zero_add]) ≫ (F n).map (zero.inv.app X)  [默认: by cat_disch]
    - add_zero_hom_app : 对任意 (n : A) (X : C), (add n 0).hom.app X = eqToHom (by dsimp; rw [add_zero]) ≫ zero.inv.app ((F n).obj X)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure ShiftMkCore where
  /-- the family of shift functors -/
  F : A -> C ⥤ C
  /-- the shift by 0 identifies to the identity functor -/
  zero : F 0 ≅ 𝟭 C
  /-- the composition of shift functors identifies to the shift by the sum -/
  add : forall n m : A, F (n + m) ≅ F n ⋙ F m
  /-- compatibility with the associativity -/
  assoc_hom_app : forall (m₁ m₂ m₃ : A) (X : C),
    (add (m₁ + m₂) m₃).hom.app X ≫ (F m₃).map ((add m₁ m₂).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (add m₁ (m₂ + m₃)).hom.app X ≫
        (add m₂ m₃).hom.app ((F m₁).obj X) := by cat_disch
  /-- compatibility with the left addition with 0 -/
  zero_add_hom_app : forall (n : A) (X : C), (add 0 n).hom.app X =
    eqToHom (by dsimp; rw [zero_add]) ≫ (F n).map (zero.inv.app X) := by cat_disch
  /-- compatibility with the right addition with 0 -/
  add_zero_hom_app : forall (n : A) (X : C), (add n 0).hom.app X =
    eqToHom (by dsimp; rw [add_zero]) ≫ zero.inv.app ((F n).obj X) := by cat_disch

namespace ShiftMkCore

variable {C A}

attribute [reassoc] assoc_hom_app

@[reassoc]
/--
lemma `assoc_inv_app` / 引理 `assoc_inv_app`

English:
lemma assoc_inv_app
  given: (h : ShiftMkCore C A) (m₁ m₂ m₃ : A) (X : C)
  proof: by
  rw [← cancel_mono ((h.add (m₁ + m₂) m₃).hom.app X ≫ (h.F m₃).map ((h.add m₁ m₂).hom.app X))]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [h.assoc_hom_app]; rw [eqToHom_tr

中文:
引理 assoc_inv_app
  条件: (h : ShiftMkCore C A) (m₁ m₂ m₃ : A) (X : C)
  证明: by
  rw [← cancel_mono ((h.add (m₁ + m₂) m₃).hom.app X ≫ (h.F m₃).map ((h.add m₁ m₂).hom.app X))]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [h.assoc_hom_app]; rw [eqToHom_tr

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Functor, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, assoc_hom_app, cancel_mono, eqToHom_refl, eqToHom_trans_assoc, h.add, h.assoc_hom_app, hom.app, id_comp, inv_hom_id_app, inv_hom_id_app_assoc, map_comp, map_id
-/
lemma assoc_inv_app (h : ShiftMkCore C A) (m₁ m₂ m₃ : A) (X : C) :
    (h.F m₃).map ((h.add m₁ m₂).inv.app X) ≫ (h.add (m₁ + m₂) m₃).inv.app X =
    (h.add m₂ m₃).inv.app ((h.F m₁).obj X) ≫ (h.add m₁ (m₂ + m₃)).inv.app X ≫
      eqToHom (by rw [add_assoc]) := by
  rw [← cancel_mono ((h.add (m₁ + m₂) m₃).hom.app X ≫ (h.F m₃).map ((h.add m₁ m₂).hom.app X))]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [h.assoc_hom_app]; rw [eqToHom_trans_assoc]; rw [eqToHom_refl]; rw [Category.id_comp]; rw [Iso.inv_hom_id_app_assoc]; rw [Iso.inv_hom_id_app]
  rfl

/--
lemma `zero_add_inv_app` / 引理 `zero_add_inv_app`

English:
lemma zero_add_inv_app
  given: (h : ShiftMkCore C A) (n : A) (X : C)
  proof: by
  rw [← cancel_epi ((h.add 0 n).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [h.zero_add_hom_app]; rw [Category.assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [eqToHom_trans]; rw [eqToHom_refl]

中文:
引理 zero_add_inv_app
  条件: (h : ShiftMkCore C A) (n : A) (X : C)
  证明: by
  rw [← cancel_epi ((h.add 0 n).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [h.zero_add_hom_app]; rw [Category.assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [eqToHom_trans]; rw [eqToHom_refl]

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Functor, Functor.map_comp_assoc, Functor.map_id, Iso.hom_inv_id_app, Iso.inv_hom_id_app, cancel_epi, eqToHom_refl, eqToHom_trans, h.add, h.zero_add_hom_app, hom.app, hom_inv_id_app, id_comp, inv_hom_id_app, map_comp_assoc, map_id, zero_add_hom_app
-/
lemma zero_add_inv_app (h : ShiftMkCore C A) (n : A) (X : C) :
    (h.add 0 n).inv.app X = (h.F n).map (h.zero.hom.app X) ≫
      eqToHom (by dsimp; rw [zero_add]) := by
  rw [← cancel_epi ((h.add 0 n).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [h.zero_add_hom_app]; rw [Category.assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [eqToHom_trans]; rw [eqToHom_refl]

/--
lemma `add_zero_inv_app` / 引理 `add_zero_inv_app`

English:
lemma add_zero_inv_app
  given: (h : ShiftMkCore C A) (n : A) (X : C)
  proof: by
  rw [← cancel_epi ((h.add n 0).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [h.add_zero_hom_app]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]

中文:
引理 add_zero_inv_app
  条件: (h : ShiftMkCore C A) (n : A) (X : C)
  证明: by
  rw [← cancel_epi ((h.add n 0).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [h.add_zero_hom_app]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]

Depends on / 依赖: Category, Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, add_zero_hom_app, cancel_epi, eqToHom_refl, eqToHom_trans, h.add, h.add_zero_hom_app, hom.app, hom_inv_id_app, inv_hom_id_app_assoc
-/
lemma add_zero_inv_app (h : ShiftMkCore C A) (n : A) (X : C) :
    (h.add n 0).inv.app X = h.zero.hom.app ((h.F n).obj X) ≫
      eqToHom (by dsimp; rw [add_zero]) := by
  rw [← cancel_epi ((h.add n 0).hom.app X)]; rw [Iso.hom_inv_id_app]; rw [h.add_zero_hom_app]; rw [Category.assoc]; rw [Iso.inv_hom_id_app_assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]

end ShiftMkCore

section

attribute [local simp] eqToHom_map

instance (h : ShiftMkCore C A) : (Discrete.functor h.F).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := h.zero.symm
      μIso := fun m n => (h.add m.as n.as).symm
      μIso_hom_natural_left := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨X'⟩
        ext
        simp
      μIso_hom_natural_right := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨⟨⟨rfl⟩⟩⟩
        ext
        simp
      associativity := by
        rintro ⟨m₁⟩ ⟨m₂⟩ ⟨m₃⟩
        ext X
        simp [h.assoc_inv_app_assoc]
      left_unitality := by
        rintro ⟨n⟩
        ext X
        simp [h.zero_add_inv_app, ← Functor.map_comp]
      right_unitality := by
        rintro ⟨n⟩
        ext X
        simp [h.add_zero_inv_app] }

/-- Constructs a `HasShift C A` instance from `ShiftMkCore`. -/
@[instance_reducible]
/--
Definition of `hasShiftMk` / `hasShiftMk` 的定义

English:
definition hasShiftMk
  signature: (h : ShiftMkCore C A)
  body: Discrete.functor h.F

中文:
定义 hasShiftMk
  签名: (h : ShiftMkCore C A)
  定义体: Discrete.functor h.F

Depends on / 依赖: Discrete, Discrete.functor, functor
-/
def hasShiftMk (h : ShiftMkCore C A) : HasShift C A where
  shift := Discrete.functor h.F

end

section
variable [HasShift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `HasShift` instance. -/
@[implicit_reducible]
/--
Definition of `shiftMonoidalFunctor` / `shiftMonoidalFunctor` 的定义

English:
definition shiftMonoidalFunctor
  signature: : Discrete A ⥤ C ⥤ C
  body: HasShift.shift

中文:
定义 shiftMonoidalFunctor
  签名: : Discrete A ⥤ C ⥤ C
  定义体: HasShift.shift

Depends on / 依赖: HasShift, HasShift.shift
-/
def shiftMonoidalFunctor : Discrete A ⥤ C ⥤ C :=
  HasShift.shift

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (shiftMonoidalFunctor C A).Monoidal
  body: HasShift.shiftMonoidal

中文:
实例 :
  签名: (shiftMonoidalFunctor C A).Monoidal
  定义体: HasShift.shiftMonoidal

Depends on / 依赖: HasShift, HasShift.shiftMonoidal, shiftMonoidal
-/
instance : (shiftMonoidalFunctor C A).Monoidal := HasShift.shiftMonoidal

variable {A}

open Functor.Monoidal

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
@[implicit_reducible]
/--
Definition of `shiftFunctor` / `shiftFunctor` 的定义

English:
definition shiftFunctor
  signature: (i : A)
  body: (shiftMonoidalFunctor C A).obj ⟨i⟩

中文:
定义 shiftFunctor
  签名: (i : A)
  定义体: (shiftMonoidalFunctor C A).obj ⟨i⟩

Depends on / 依赖: shiftMonoidalFunctor
-/
def shiftFunctor (i : A) : C ⥤ C :=
  (shiftMonoidalFunctor C A).obj ⟨i⟩

/--
Definition of `shiftFunctorAdd` / `shiftFunctorAdd` 的定义

English:
definition shiftFunctorAdd
  signature: (i j : A)
  body: (μIso (shiftMonoidalFunctor C A) ⟨i⟩ ⟨j⟩).symm

中文:
定义 shiftFunctorAdd
  签名: (i j : A)
  定义体: (μIso (shiftMonoidalFunctor C A) ⟨i⟩ ⟨j⟩).symm

Depends on / 依赖: shiftMonoidalFunctor
-/
def shiftFunctorAdd (i j : A) : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  (μIso (shiftMonoidalFunctor C A) ⟨i⟩ ⟨j⟩).symm

/--
Definition of `shiftFunctorAdd'` / `shiftFunctorAdd'` 的定义

English:
definition shiftFunctorAdd'
  signature: (i j k : A) (h : i + j = k)
  body: eqToIso (by rw [h]) ≪≫ shiftFunctorAdd C i j

中文:
定义 shiftFunctorAdd'
  签名: (i j k : A) (h : i + j = k)
  定义体: eqToIso (by rw [h]) ≪≫ shiftFunctorAdd C i j

Depends on / 依赖: eqToIso, shiftFunctorAdd
-/
def shiftFunctorAdd' (i j k : A) (h : i + j = k) :
    shiftFunctor C k ≅ shiftFunctor C i ⋙ shiftFunctor C j :=
  eqToIso (by rw [h]) ≪≫ shiftFunctorAdd C i j

/--
lemma `shiftFunctorAdd'_eq_shiftFunctorAdd` / 引理 `shiftFunctorAdd'_eq_shiftFunctorAdd`

English:
lemma shiftFunctorAdd'_eq_shiftFunctorAdd
  given: (i j : A)
  proof: by
  ext1
  apply Category.id_comp

中文:
引理 shiftFunctorAdd'_eq_shiftFunctorAdd
  条件: (i j : A)
  证明: by
  ext1
  apply Category.id_comp
-/
lemma shiftFunctorAdd'_eq_shiftFunctorAdd (i j : A) :
    shiftFunctorAdd' C i j (i + j) rfl = shiftFunctorAdd C i j := by
  ext1
  apply Category.id_comp

variable (A) in
/--
Definition of `shiftFunctorZero` / `shiftFunctorZero` 的定义

English:
definition shiftFunctorZero
  signature: : shiftFunctor C (0 : A) ≅ 𝟭 C
  body: (εIso (shiftMonoidalFunctor C A)).symm

中文:
定义 shiftFunctorZero
  签名: : shiftFunctor C (0 : A) ≅ 𝟭 C
  定义体: (εIso (shiftMonoidalFunctor C A)).symm

Depends on / 依赖: shiftMonoidalFunctor
-/
def shiftFunctorZero : shiftFunctor C (0 : A) ≅ 𝟭 C :=
  (εIso (shiftMonoidalFunctor C A)).symm

/--
Definition of `shiftFunctorZero'` / `shiftFunctorZero'` 的定义

English:
definition shiftFunctorZero'
  signature: (a : A) (ha : a = 0)
  body: eqToIso (by rw [ha]) ≪≫ shiftFunctorZero C A

中文:
定义 shiftFunctorZero'
  签名: (a : A) (ha : a = 0)
  定义体: eqToIso (by rw [ha]) ≪≫ shiftFunctorZero C A

Depends on / 依赖: eqToIso, shiftFunctorZero
-/
def shiftFunctorZero' (a : A) (ha : a = 0) : shiftFunctor C a ≅ 𝟭 C :=
  eqToIso (by rw [ha]) ≪≫ shiftFunctorZero C A

end

variable {C A}

/--
lemma `ShiftMkCore.shiftFunctor_eq` / 引理 `ShiftMkCore.shiftFunctor_eq`

English:
lemma ShiftMkCore.shiftFunctor_eq
  given: (h : ShiftMkCore C A) (a : A)
  proof: hasShiftMk C A h
    shiftFunctor C a = h.F a := rfl

中文:
引理 ShiftMkCore.shiftFunctor_eq
  条件: (h : ShiftMkCore C A) (a : A)
  证明: hasShiftMk C A h
    shiftFunctor C a = h.F a := rfl

Depends on / 依赖: hasShiftMk
-/
lemma ShiftMkCore.shiftFunctor_eq (h : ShiftMkCore C A) (a : A) :
    letI := hasShiftMk C A h
    shiftFunctor C a = h.F a := rfl

/--
lemma `ShiftMkCore.shiftFunctorZero_eq` / 引理 `ShiftMkCore.shiftFunctorZero_eq`

English:
lemma ShiftMkCore.shiftFunctorZero_eq
  given: (h : ShiftMkCore C A)
  proof: hasShiftMk C A h
    shiftFunctorZero C A = h.zero := rfl

中文:
引理 ShiftMkCore.shiftFunctorZero_eq
  条件: (h : ShiftMkCore C A)
  证明: hasShiftMk C A h
    shiftFunctorZero C A = h.zero := rfl

Depends on / 依赖: hasShiftMk
-/
lemma ShiftMkCore.shiftFunctorZero_eq (h : ShiftMkCore C A) :
    letI := hasShiftMk C A h
    shiftFunctorZero C A = h.zero := rfl

/--
lemma `ShiftMkCore.shiftFunctorAdd_eq` / 引理 `ShiftMkCore.shiftFunctorAdd_eq`

English:
lemma ShiftMkCore.shiftFunctorAdd_eq
  given: (h : ShiftMkCore C A) (a b : A)
  proof: hasShiftMk C A h
    shiftFunctorAdd C a b = h.add a b := rfl

中文:
引理 ShiftMkCore.shiftFunctorAdd_eq
  条件: (h : ShiftMkCore C A) (a b : A)
  证明: hasShiftMk C A h
    shiftFunctorAdd C a b = h.add a b := rfl

Depends on / 依赖: hasShiftMk
-/
lemma ShiftMkCore.shiftFunctorAdd_eq (h : ShiftMkCore C A) (a b : A) :
    letI := hasShiftMk C A h
    shiftFunctorAdd C a b = h.add a b := rfl

set_option quotPrecheck false in
/-- shifting an object `X` by `n` is obtained by the notation `X⟦n⟧` -/
notation -- Any better notational suggestions?
X "⟦" n "⟧" => (shiftFunctor _ n).obj X

set_option quotPrecheck false in
/-- shifting a morphism `f` by `n` is obtained by the notation `f⟦n⟧'` -/
notation f "⟦" n "⟧'" => (shiftFunctor _ n).map f

variable (C)
variable [HasShift C A]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_zero_add` / 引理 `shiftFunctorAdd'_zero_add`

English:
lemma shiftFunctorAdd'_zero_add
  given: (a : A)
  proof: by
  ext X
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, obj_ε_app, Discrete.addMonoidal_leftUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

中文:
引理 shiftFunctorAdd'_zero_add
  条件: (a : A)
  证明: by
  ext X
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, obj_ε_app, Discrete.addMonoidal_leftUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl
-/
lemma shiftFunctorAdd'_zero_add (a : A) :
    shiftFunctorAdd' C 0 a a (zero_add a) = (leftUnitor _).symm ≪≫
    isoWhiskerRight (shiftFunctorZero C A).symm (shiftFunctor C a) := by
  ext X
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, obj_ε_app, Discrete.addMonoidal_leftUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_add_zero` / 引理 `shiftFunctorAdd'_add_zero`

English:
lemma shiftFunctorAdd'_add_zero
  given: (a : A)
  proof: by
  ext
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, ε_app_obj, Discrete.addMonoidal_rightUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

中文:
引理 shiftFunctorAdd'_add_zero
  条件: (a : A)
  证明: by
  ext
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, ε_app_obj, Discrete.addMonoidal_rightUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl
-/
lemma shiftFunctorAdd'_add_zero (a : A) :
    shiftFunctorAdd' C a 0 a (add_zero a) = (rightUnitor _).symm ≪≫
    isoWhiskerLeft (shiftFunctor C a) (shiftFunctorZero C A).symm := by
  ext
  dsimp [shiftFunctorAdd', shiftFunctorZero, shiftFunctor]
  simp only [eqToHom_app, ε_app_obj, Discrete.addMonoidal_rightUnitor, eqToIso.inv,
    eqToHom_map, Category.id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_assoc` / 引理 `shiftFunctorAdd'_assoc`

English:
lemma shiftFunctorAdd'_assoc
  statement: (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  proof: by
  subst h₁₂ h₂₃ h₁₂₃
  ext X
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.comp_id]
  dsimp [shiftFunctorAdd']
  simp only [eqToHom_app]
  dsimp [shiftFunctorAdd, shiftFunctor]
  simp only [obj_μ_inv_app, Discrete.addMonoidal_associator, eqToIso.hom, eqToHom_map,
    eqToHom_

中文:
引理 shiftFunctorAdd'_assoc
  结论: (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  证明: by
  subst h₁₂ h₂₃ h₁₂₃
  ext X
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.comp_id]
  dsimp [shiftFunctorAdd']
  simp only [eqToHom_app]
  dsimp [shiftFunctorAdd, shiftFunctor]
  simp only [obj_μ_inv_app, Discrete.addMonoidal_associator, eqToIso.hom, eqToHom_map,
    eqToHom_
-/
lemma shiftFunctorAdd'_assoc (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) :
    shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃]) ≪≫
      isoWhiskerRight (shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂) _ ≪≫ associator _ _ _ =
    shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃]) ≪≫
      isoWhiskerLeft _ (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃) := by
  subst h₁₂ h₂₃ h₁₂₃
  ext X
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.comp_id]
  dsimp [shiftFunctorAdd']
  simp only [eqToHom_app]
  dsimp [shiftFunctorAdd, shiftFunctor]
  simp only [obj_μ_inv_app, Discrete.addMonoidal_associator, eqToIso.hom, eqToHom_map,
    eqToHom_app]
  erw [δ_μ_app_assoc, Category.assoc]
  rfl

/--
lemma `shiftFunctorAdd_assoc` / 引理 `shiftFunctorAdd_assoc`

English:
lemma shiftFunctorAdd_assoc
  given: (a₁ a₂ a₃ : A)
  proof: by
  ext X
  simpa [shiftFunctorAdd'_eq_shiftFunctorAdd]
    using NatTrans.congr_app (congr_arg Iso.hom
      (shiftFunctorAdd'_assoc C a₁ a₂ a₃ _ _ _ rfl rfl rfl)) X

中文:
引理 shiftFunctorAdd_assoc
  条件: (a₁ a₂ a₃ : A)
  证明: by
  ext X
  simpa [shiftFunctorAdd'_eq_shiftFunctorAdd]
    using NatTrans.congr_app (congr_arg Iso.hom
      (shiftFunctorAdd'_assoc C a₁ a₂ a₃ _ _ _ rfl rfl rfl)) X

Depends on / 依赖: Iso.hom, NatTrans, NatTrans.congr_app, _assoc, _eq_shiftFunctorAdd, congr_app, congr_arg, shiftFunctorAdd
-/
lemma shiftFunctorAdd_assoc (a₁ a₂ a₃ : A) :
    shiftFunctorAdd C (a₁ + a₂) a₃ ≪≫
      isoWhiskerRight (shiftFunctorAdd C a₁ a₂) _ ≪≫ associator _ _ _ =
    shiftFunctorAdd' C a₁ (a₂ + a₃) _ (add_assoc a₁ a₂ a₃).symm ≪≫
      isoWhiskerLeft _ (shiftFunctorAdd C a₂ a₃) := by
  ext X
  simpa [shiftFunctorAdd'_eq_shiftFunctorAdd]
    using NatTrans.congr_app (congr_arg Iso.hom
      (shiftFunctorAdd'_assoc C a₁ a₂ a₃ _ _ _ rfl rfl rfl)) X

variable {C}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_zero_add_hom_app` / 引理 `shiftFunctorAdd'_zero_add_hom_app`

English:
lemma shiftFunctorAdd'_zero_add_hom_app
  given: (a : A) (X : C)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_zero_add C a)) X

中文:
引理 shiftFunctorAdd'_zero_add_hom_app
  条件: (a : A) (X : C)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_zero_add C a)) X
-/
lemma shiftFunctorAdd'_zero_add_hom_app (a : A) (X : C) :
    (shiftFunctorAdd' C 0 a a (zero_add a)).hom.app X =
    ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_zero_add C a)) X

/--
lemma `shiftFunctorAdd_zero_add_hom_app` / 引理 `shiftFunctorAdd_zero_add_hom_app`

English:
lemma shiftFunctorAdd_zero_add_hom_app
  given: (a : A) (X : C)
  proof: by
  simp [← shiftFunctorAdd'_zero_add_hom_app, shiftFunctorAdd']

中文:
引理 shiftFunctorAdd_zero_add_hom_app
  条件: (a : A) (X : C)
  证明: by
  simp [← shiftFunctorAdd'_zero_add_hom_app, shiftFunctorAdd']

Depends on / 依赖: _zero_add_hom_app, shiftFunctorAdd
-/
lemma shiftFunctorAdd_zero_add_hom_app (a : A) (X : C) :
    (shiftFunctorAdd C 0 a).hom.app X =
    eqToHom (by dsimp; rw [zero_add]) ≫ ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simp [← shiftFunctorAdd'_zero_add_hom_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_zero_add_inv_app` / 引理 `shiftFunctorAdd'_zero_add_inv_app`

English:
lemma shiftFunctorAdd'_zero_add_inv_app
  given: (a : A) (X : C)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_zero_add C a)) X

中文:
引理 shiftFunctorAdd'_zero_add_inv_app
  条件: (a : A) (X : C)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_zero_add C a)) X
-/
lemma shiftFunctorAdd'_zero_add_inv_app (a : A) (X : C) :
    (shiftFunctorAdd' C 0 a a (zero_add a)).inv.app X =
    ((shiftFunctorZero C A).hom.app X)⟦a⟧' := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_zero_add C a)) X

/--
lemma `shiftFunctorAdd_zero_add_inv_app` / 引理 `shiftFunctorAdd_zero_add_inv_app`

English:
lemma shiftFunctorAdd_zero_add_inv_app
  given: (a : A) (X : C)
  statement: (shiftFunctorAdd C 0 a).inv.app X =
  proof: by
  simp [← shiftFunctorAdd'_zero_add_inv_app, shiftFunctorAdd']

中文:
引理 shiftFunctorAdd_zero_add_inv_app
  条件: (a : A) (X : C)
  结论: (shiftFunctorAdd C 0 a).inv.app X =
  证明: by
  simp [← shiftFunctorAdd'_zero_add_inv_app, shiftFunctorAdd']

Depends on / 依赖: _zero_add_inv_app, shiftFunctorAdd
-/
lemma shiftFunctorAdd_zero_add_inv_app (a : A) (X : C) : (shiftFunctorAdd C 0 a).inv.app X =
    ((shiftFunctorZero C A).hom.app X)⟦a⟧' ≫ eqToHom (by dsimp; rw [zero_add]) := by
  simp [← shiftFunctorAdd'_zero_add_inv_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_add_zero_hom_app` / 引理 `shiftFunctorAdd'_add_zero_hom_app`

English:
lemma shiftFunctorAdd'_add_zero_hom_app
  given: (a : A) (X : C)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_add_zero C a)) X

中文:
引理 shiftFunctorAdd'_add_zero_hom_app
  条件: (a : A) (X : C)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_add_zero C a)) X
-/
lemma shiftFunctorAdd'_add_zero_hom_app (a : A) (X : C) :
    (shiftFunctorAdd' C a 0 a (add_zero a)).hom.app X =
    (shiftFunctorZero C A).inv.app (X⟦a⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd'_add_zero C a)) X

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd_add_zero_hom_app` / 引理 `shiftFunctorAdd_add_zero_hom_app`

English:
lemma shiftFunctorAdd_add_zero_hom_app
  given: (a : A) (X : C)
  statement: (shiftFunctorAdd C a 0).hom.app X =
  proof: by
  simp [← shiftFunctorAdd'_add_zero_hom_app, shiftFunctorAdd']

中文:
引理 shiftFunctorAdd_add_zero_hom_app
  条件: (a : A) (X : C)
  结论: (shiftFunctorAdd C a 0).hom.app X =
  证明: by
  simp [← shiftFunctorAdd'_add_zero_hom_app, shiftFunctorAdd']

Depends on / 依赖: _add_zero_hom_app, shiftFunctorAdd
-/
lemma shiftFunctorAdd_add_zero_hom_app (a : A) (X : C) : (shiftFunctorAdd C a 0).hom.app X =
    eqToHom (by dsimp; rw [add_zero]) ≫ (shiftFunctorZero C A).inv.app (X⟦a⟧) := by
  simp [← shiftFunctorAdd'_add_zero_hom_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd'_add_zero_inv_app` / 引理 `shiftFunctorAdd'_add_zero_inv_app`

English:
lemma shiftFunctorAdd'_add_zero_inv_app
  given: (a : A) (X : C)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_add_zero C a)) X

中文:
引理 shiftFunctorAdd'_add_zero_inv_app
  条件: (a : A) (X : C)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_add_zero C a)) X
-/
lemma shiftFunctorAdd'_add_zero_inv_app (a : A) (X : C) :
    (shiftFunctorAdd' C a 0 a (add_zero a)).inv.app X =
    (shiftFunctorZero C A).hom.app (X⟦a⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd'_add_zero C a)) X

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorAdd_add_zero_inv_app` / 引理 `shiftFunctorAdd_add_zero_inv_app`

English:
lemma shiftFunctorAdd_add_zero_inv_app
  given: (a : A) (X : C)
  statement: (shiftFunctorAdd C a 0).inv.app X =
  proof: by
  simp [← shiftFunctorAdd'_add_zero_inv_app, shiftFunctorAdd']

中文:
引理 shiftFunctorAdd_add_zero_inv_app
  条件: (a : A) (X : C)
  结论: (shiftFunctorAdd C a 0).inv.app X =
  证明: by
  simp [← shiftFunctorAdd'_add_zero_inv_app, shiftFunctorAdd']

Depends on / 依赖: _add_zero_inv_app, shiftFunctorAdd
-/
lemma shiftFunctorAdd_add_zero_inv_app (a : A) (X : C) : (shiftFunctorAdd C a 0).inv.app X =
    (shiftFunctorZero C A).hom.app (X⟦a⟧) ≫ eqToHom (by dsimp; rw [add_zero]) := by
  simp [← shiftFunctorAdd'_add_zero_inv_app, shiftFunctorAdd']

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shiftFunctorAdd'_assoc_hom_app` / 引理 `shiftFunctorAdd'_assoc_hom_app`

English:
lemma shiftFunctorAdd'_assoc_hom_app
  statement: (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

中文:
引理 shiftFunctorAdd'_assoc_hom_app
  结论: (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X
-/
lemma shiftFunctorAdd'_assoc_hom_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).hom.app X ≫
      ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).hom.app X)⟦a₃⟧' =
    (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).hom.app X ≫
      (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).hom.app (X⟦a₁⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shiftFunctorAdd'_assoc_inv_app` / 引理 `shiftFunctorAdd'_assoc_inv_app`

English:
lemma shiftFunctorAdd'_assoc_inv_app
  statement: (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

中文:
引理 shiftFunctorAdd'_assoc_inv_app
  结论: (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X
-/
lemma shiftFunctorAdd'_assoc_inv_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
    ((shiftFunctorAdd' C a₁ a₂ a₁₂ h₁₂).inv.app X)⟦a₃⟧' ≫
      (shiftFunctorAdd' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).inv.app X =
    (shiftFunctorAdd' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
      (shiftFunctorAdd' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).inv.app X := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv
    (shiftFunctorAdd'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shiftFunctorAdd_assoc_hom_app` / 引理 `shiftFunctorAdd_assoc_hom_app`

English:
lemma shiftFunctorAdd_assoc_hom_app
  given: (a₁ a₂ a₃ : A) (X : C)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

中文:
引理 shiftFunctorAdd_assoc_hom_app
  条件: (a₁ a₂ a₃ : A) (X : C)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

Depends on / 依赖: Iso.hom, NatTrans, NatTrans.congr_app, congr_app, congr_arg, shiftFunctorAdd_assoc
-/
lemma shiftFunctorAdd_assoc_hom_app (a₁ a₂ a₃ : A) (X : C) :
    (shiftFunctorAdd C (a₁ + a₂) a₃).hom.app X ≫
      ((shiftFunctorAdd C a₁ a₂).hom.app X)⟦a₃⟧' =
    (shiftFunctorAdd' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).hom.app X ≫
      (shiftFunctorAdd C a₂ a₃).hom.app (X⟦a₁⟧) := by
  simpa using NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shiftFunctorAdd_assoc_inv_app` / 引理 `shiftFunctorAdd_assoc_inv_app`

English:
lemma shiftFunctorAdd_assoc_inv_app
  given: (a₁ a₂ a₃ : A) (X : C)
  proof: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

中文:
引理 shiftFunctorAdd_assoc_inv_app
  条件: (a₁ a₂ a₃ : A) (X : C)
  证明: by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

Depends on / 依赖: Iso.inv, NatTrans, NatTrans.congr_app, congr_app, congr_arg, shiftFunctorAdd_assoc
-/
lemma shiftFunctorAdd_assoc_inv_app (a₁ a₂ a₃ : A) (X : C) :
    ((shiftFunctorAdd C a₁ a₂).inv.app X)⟦a₃⟧' ≫
      (shiftFunctorAdd C (a₁ + a₂) a₃).inv.app X =
    (shiftFunctorAdd C a₂ a₃).inv.app (X⟦a₁⟧) ≫
      (shiftFunctorAdd' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).inv.app X := by
  simpa using NatTrans.congr_app (congr_arg Iso.inv (shiftFunctorAdd_assoc C a₁ a₂ a₃)) X

end Defs

section AddMonoid

variable [AddMonoid A] [HasShift C A] (X Y : C) (f : X ⟶ Y)

--@[simp]
--theorem HasShift.shift_obj_obj (n : A) (X : C) : (HasShift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
-- rfl

/--
Definition of `shiftAdd` / `shiftAdd` 的定义

English:
abbreviation shiftAdd
  signature: (i j : A)
  body: (shiftFunctorAdd C i j).app _

中文:
缩写 shiftAdd
  签名: (i j : A)
  定义体: (shiftFunctorAdd C i j).app _

Depends on / 依赖: shiftFunctorAdd
-/
abbrev shiftAdd (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ :=
  (shiftFunctorAdd C i j).app _

/--
theorem `shift_shift'` / 定理 `shift_shift'`

English:
theorem shift_shift'
  given: (i j : A)
  proof: by
  simp

中文:
定理 shift_shift'
  条件: (i j : A)
  证明: by
  simp
-/
theorem shift_shift' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftAdd X i j).inv ≫ f⟦i + j⟧' ≫ (shiftAdd Y i j).hom := by
  simp

variable (A)

/--
Definition of `shiftZero` / `shiftZero` 的定义

English:
abbreviation shiftZero
  signature: : X⟦(0 : A)⟧ ≅ X
  body: (shiftFunctorZero C A).app _

中文:
缩写 shiftZero
  签名: : X⟦(0 : A)⟧ ≅ X
  定义体: (shiftFunctorZero C A).app _

Depends on / 依赖: shiftFunctorZero
-/
abbrev shiftZero : X⟦(0 : A)⟧ ≅ X :=
  (shiftFunctorZero C A).app _

/--
theorem `shiftZero'` / 定理 `shiftZero'`

English:
theorem shiftZero'
  statement: f⟦(0 : A)⟧' = (shiftZero A X).hom ≫ f ≫ (shiftZero A Y).inv
  proof: by
  symm
  rw [Iso.app_inv]; rw [Iso.app_hom]
  apply NatIso.naturality_2

中文:
定理 shiftZero'
  结论: f⟦(0 : A)⟧' = (shiftZero A X).hom ≫ f ≫ (shiftZero A Y).inv
  证明: by
  symm
  rw [Iso.app_inv]; rw [Iso.app_hom]
  apply NatIso.naturality_2

Depends on / 依赖: Iso.app_hom, Iso.app_inv, NatIso, NatIso.naturality_2, app_hom, app_inv, naturality_2
-/
theorem shiftZero' : f⟦(0 : A)⟧' = (shiftZero A X).hom ≫ f ≫ (shiftZero A Y).inv := by
  symm
  rw [Iso.app_inv]; rw [Iso.app_hom]
  apply NatIso.naturality_2

variable (C) {A}

/--
Definition of `shiftFunctorCompIsoId` / `shiftFunctorCompIsoId` 的定义

English:
definition shiftFunctorCompIsoId
  signature: (i j : A) (h : i + j = 0)
  body: (shiftFunctorAdd' C i j 0 h).symm ≪≫ shiftFunctorZero C A

中文:
定义 shiftFunctorCompIsoId
  签名: (i j : A) (h : i + j = 0)
  定义体: (shiftFunctorAdd' C i j 0 h).symm ≪≫ shiftFunctorZero C A

Depends on / 依赖: shiftFunctorAdd, shiftFunctorZero
-/
def shiftFunctorCompIsoId (i j : A) (h : i + j = 0) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅ 𝟭 C :=
  (shiftFunctorAdd' C i j 0 h).symm ≪≫ shiftFunctorZero C A

end AddMonoid

section AddGroup

variable (C)
variable [AddGroup A] [HasShift C A]

set_option backward.defeqAttrib.useBackward true in
/-- Shifting by `i` and shifting by `j` forms an equivalence when `i + j = 0`. -/
@[simps]
/--
Definition of `shiftEquiv'` / `shiftEquiv'` 的定义

English:
definition shiftEquiv'
  signature: (i j : A) (h : i + j = 0)
  body: shiftFunctor C i
  inverse := shiftFunctor C j
  unitIso := (shiftFunctorCompIsoId C i j h).symm
  counitIso := shiftFunctorCompIsoId C j i
    (by rw [← add_left_inj j, add_assoc, h, zero_add, add_zero])
  functor_unitIso_comp X := by
    convert!
      (equivOfTensorIsoUnit (shiftMonoidalFunctor C

中文:
定义 shiftEquiv'
  签名: (i j : A) (h : i + j = 0)
  定义体: shiftFunctor C i
  inverse := shiftFunctor C j
  unitIso := (shiftFunctorCompIsoId C i j h).symm
  counitIso := shiftFunctorCompIsoId C j i
    (by rw [← add_left_inj j, add_assoc, h, zero_add, add_zero])
  functor_unitIso_comp X := by
    convert!
      (equivOfTensorIsoUnit (shiftMonoidalFunctor C

Depends on / 依赖: shiftFunctor
-/
def shiftEquiv' (i j : A) (h : i + j = 0) : C ≌ C where
  functor := shiftFunctor C i
  inverse := shiftFunctor C j
  unitIso := (shiftFunctorCompIsoId C i j h).symm
  counitIso := shiftFunctorCompIsoId C j i
    (by rw [← add_left_inj j, add_assoc, h, zero_add, add_zero])
  functor_unitIso_comp X := by
    convert!
      (equivOfTensorIsoUnit (shiftMonoidalFunctor C A) ⟨i⟩ ⟨j⟩ (Discrete.eqToIso h)
            (Discrete.eqToIso (by dsimp; rw [← add_left_inj j, add_assoc, h, zero_add, add_zero]))
            (Subsingleton.elim _ _)).functor_unitIso_comp
        X
    all_goals
      ext X
      dsimp [shiftFunctorCompIsoId, unitOfTensorIsoUnit,
        shiftFunctorAdd']
      simp only [Category.assoc, eqToHom_map]
      rfl

/--
Definition of `shiftEquiv` / `shiftEquiv` 的定义

English:
abbreviation shiftEquiv
  signature: (n : A)
  body: shiftEquiv' C n (-n) (add_neg_cancel n)

中文:
缩写 shiftEquiv
  签名: (n : A)
  定义体: shiftEquiv' C n (-n) (add_neg_cancel n)

Depends on / 依赖: add_neg_cancel, shiftEquiv
-/
abbrev shiftEquiv (n : A) : C ≌ C := shiftEquiv' C n (-n) (add_neg_cancel n)

variable (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : (shiftFunctor C i).IsEquivalence := by
  change (shiftEquiv C i).functor.IsEquivalence
  infer_instance

variable {C}

/--
Definition of `shiftShiftNeg` / `shiftShiftNeg` 的定义

English:
abbreviation shiftShiftNeg
  signature: (i : A)
  body: (shiftEquiv C i).unitIso.symm.app X

中文:
缩写 shiftShiftNeg
  签名: (i : A)
  定义体: (shiftEquiv C i).unitIso.symm.app X

Depends on / 依赖: shiftEquiv, unitIso, unitIso.symm.app
-/
abbrev shiftShiftNeg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
  (shiftEquiv C i).unitIso.symm.app X

/--
Definition of `shiftNegShift` / `shiftNegShift` 的定义

English:
abbreviation shiftNegShift
  signature: (i : A)
  body: (shiftEquiv C i).counitIso.app X

中文:
缩写 shiftNegShift
  签名: (i : A)
  定义体: (shiftEquiv C i).counitIso.app X

Depends on / 依赖: counitIso, counitIso.app, shiftEquiv
-/
abbrev shiftNegShift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
  (shiftEquiv C i).counitIso.app X

variable {X Y}

@[reassoc (attr := simp)]
/--
lemma `shiftFunctorCompIsoId_naturality_1` / 引理 `shiftFunctorCompIsoId_naturality_1`

English:
lemma shiftFunctorCompIsoId_naturality_1
  given: (i j : A) (hij : i + j = 0)
  proof: NatIso.naturality_1 (shiftFunctorCompIsoId C i j hij) f

中文:
引理 shiftFunctorCompIsoId_naturality_1
  条件: (i j : A) (hij : i + j = 0)
  证明: NatIso.naturality_1 (shiftFunctorCompIsoId C i j hij) f

Depends on / 依赖: NatIso, NatIso.naturality_1, naturality_1, shiftFunctorCompIsoId
-/
lemma shiftFunctorCompIsoId_naturality_1 (i j : A) (hij : i + j = 0) :
    (shiftFunctorCompIsoId C i j hij).inv.app X ≫ f⟦i⟧'⟦j⟧' ≫
    (shiftFunctorCompIsoId C i j hij).hom.app Y = f :=
  NatIso.naturality_1 (shiftFunctorCompIsoId C i j hij) f

/--
theorem `shift_shift_neg'` / 定理 `shift_shift_neg'`

English:
theorem shift_shift_neg'
  given: (i : A)
  proof: (NatIso.naturality_2 (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)) f).symm

中文:
定理 shift_shift_neg'
  条件: (i : A)
  证明: (NatIso.naturality_2 (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)) f).symm

Depends on / 依赖: NatIso, NatIso.naturality_2, add_neg_cancel, closure_eq_closure, closure_inter_ground, h.isBasis_inter_ground.closure_eq_closure, isBasis_inter_ground, naturality_2, shiftFunctorCompIsoId
-/
theorem shift_shift_neg' (i : A) :
    f⟦i⟧'⟦-i⟧' = (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)).hom.app X ≫
      f ≫ (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompIsoId C i (-i) (add_neg_cancel i)) f).symm

/--
theorem `shift_neg_shift'` / 定理 `shift_neg_shift'`

English:
theorem shift_neg_shift'
  given: (i : A)
  proof: (NatIso.naturality_2 (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)) f).symm

中文:
定理 shift_neg_shift'
  条件: (i : A)
  证明: (NatIso.naturality_2 (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)) f).symm

Depends on / 依赖: NatIso, NatIso.naturality_2, naturality_2, neg_add_cancel, shiftFunctorCompIsoId
-/
theorem shift_neg_shift' (i : A) :
    f⟦-i⟧'⟦i⟧' = (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)).hom.app X ≫ f ≫
      (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)).inv.app Y :=
  (NatIso.naturality_2 (shiftFunctorCompIsoId C (-i) i (neg_add_cancel i)) f).symm

/--
theorem `shift_equiv_triangle` / 定理 `shift_equiv_triangle`

English:
theorem shift_equiv_triangle
  given: (n : A) (X : C)
  proof: (shiftEquiv C n).functor_unitIso_comp X

中文:
定理 shift_equiv_triangle
  条件: (n : A) (X : C)
  证明: (shiftEquiv C n).functor_unitIso_comp X

Depends on / 依赖: closure_eq_closure, functor_unitIso_comp, h.closure_eq_closure, h.indep.isBasis_closure, isBasis_closure, shiftEquiv
-/
theorem shift_equiv_triangle (n : A) (X : C) :
    (shiftShiftNeg X n).inv⟦n⟧' ≫ (shiftNegShift (X⟦n⟧) n).hom = 𝟙 (X⟦n⟧) :=
  (shiftEquiv C n).functor_unitIso_comp X

section

set_option backward.defeqAttrib.useBackward true in
/--
theorem `shift_shiftFunctorCompIsoId_hom_app` / 定理 `shift_shiftFunctorCompIsoId_hom_app`

English:
theorem shift_shiftFunctorCompIsoId_hom_app
  given: (n m : A) (h : n + m = 0) (X : C)
  proof: by
  dsimp [shiftFunctorCompIsoId]
  simpa only [Functor.map_comp, ← shiftFunctorAdd'_zero_add_inv_app n X,
    ← shiftFunctorAdd'_add_zero_inv_app n X]
    using shiftFunctorAdd'_assoc_inv_app n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel]) (by rw [h, zero_add]) X

中文:
定理 shift_shiftFunctorCompIsoId_hom_app
  条件: (n m : A) (h : n + m = 0) (X : C)
  证明: by
  dsimp [shiftFunctorCompIsoId]
  simpa only [Functor.map_comp, ← shiftFunctorAdd'_zero_add_inv_app n X,
    ← shiftFunctorAdd'_add_zero_inv_app n X]
    using shiftFunctorAdd'_assoc_inv_app n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel]) (by rw [h, zero_add]) X

Depends on / 依赖: Functor, Functor.map_comp, _add_zero_inv_app, _assoc_inv_app, _zero_add_inv_app, add_neg_cancel, map_comp, neg_eq_of_add_eq_zero_left, shiftFunctorAdd, shiftFunctorCompIsoId, zero_add
-/
theorem shift_shiftFunctorCompIsoId_hom_app (n m : A) (h : n + m = 0) (X : C) :
    ((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧' =
    (shiftFunctorCompIsoId C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel])).hom.app (X⟦n⟧) := by
  dsimp [shiftFunctorCompIsoId]
  simpa only [Functor.map_comp, ← shiftFunctorAdd'_zero_add_inv_app n X,
    ← shiftFunctorAdd'_add_zero_inv_app n X]
    using shiftFunctorAdd'_assoc_inv_app n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel]) (by rw [h, zero_add]) X

/--
theorem `shift_shiftFunctorCompIsoId_inv_app` / 定理 `shift_shiftFunctorCompIsoId_inv_app`

English:
theorem shift_shiftFunctorCompIsoId_inv_app
  given: (n m : A) (h : n + m = 0) (X : C)
  proof: by
  rw [← cancel_mono (((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧')]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [shift_shiftFunctorCompIsoId_hom_app]; rw [Iso.inv_hom_id_app]
  rfl

中文:
定理 shift_shiftFunctorCompIsoId_inv_app
  条件: (n m : A) (h : n + m = 0) (X : C)
  证明: by
  rw [← cancel_mono (((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧')]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [shift_shiftFunctorCompIsoId_hom_app]; rw [Iso.inv_hom_id_app]
  rfl

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app, cancel_mono, hom.app, inv_hom_id_app, map_comp, map_id, shiftFunctorCompIsoId, shift_shiftFunctorCompIsoId_hom_app
-/
theorem shift_shiftFunctorCompIsoId_inv_app (n m : A) (h : n + m = 0) (X : C) :
    ((shiftFunctorCompIsoId C n m h).inv.app X)⟦n⟧' =
    ((shiftFunctorCompIsoId C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_neg_cancel])).inv.app (X⟦n⟧)) := by
  rw [← cancel_mono (((shiftFunctorCompIsoId C n m h).hom.app X)⟦n⟧')]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [shift_shiftFunctorCompIsoId_hom_app]; rw [Iso.inv_hom_id_app]
  rfl

/--
theorem `shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app` / 定理 `shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app`

English:
theorem shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app
  given: (n : A) (X : C)
  proof: by
  apply shift_shiftFunctorCompIsoId_hom_app

中文:
定理 shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app
  条件: (n : A) (X : C)
  证明: by
  apply shift_shiftFunctorCompIsoId_hom_app

Depends on / 依赖: shift_shiftFunctorCompIsoId_hom_app
-/
theorem shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app X)⟦n⟧' =
    (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app (X⟦n⟧) := by
  apply shift_shiftFunctorCompIsoId_hom_app

/--
theorem `shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app` / 定理 `shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app`

English:
theorem shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app
  given: (n : A) (X : C)
  proof: by
  apply shift_shiftFunctorCompIsoId_inv_app

中文:
定理 shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app
  条件: (n : A) (X : C)
  证明: by
  apply shift_shiftFunctorCompIsoId_inv_app

Depends on / 依赖: shift_shiftFunctorCompIsoId_inv_app
-/
theorem shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X)⟦n⟧' =
    (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).inv.app (X⟦n⟧) := by
  apply shift_shiftFunctorCompIsoId_inv_app

/--
theorem `shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app` / 定理 `shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app`

English:
theorem shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app
  given: (n : A) (X : C)
  proof: by
  apply shift_shiftFunctorCompIsoId_hom_app

中文:
定理 shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app
  条件: (n : A) (X : C)
  证明: by
  apply shift_shiftFunctorCompIsoId_hom_app

Depends on / 依赖: shift_shiftFunctorCompIsoId_hom_app
-/
theorem shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app X)⟦-n⟧' =
    (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app (X⟦-n⟧) := by
  apply shift_shiftFunctorCompIsoId_hom_app

/--
theorem `shift_shiftFunctorCompIsoId_neg_add_cancel_inv_app` / 定理 `shift_shiftFunctorCompIsoId_neg_add_cancel_inv_app`

English:
theorem shift_shiftFunctorCompIsoId_neg_add_cancel_inv_app
  given: (n : A) (X : C)
  proof: by
  apply shift_shiftFunctorCompIsoId_inv_app

中文:
定理 shift_shiftFunctorCompIsoId_neg_add_cancel_inv_app
  条件: (n : A) (X : C)
  证明: by
  apply shift_shiftFunctorCompIsoId_inv_app

Depends on / 依赖: shift_shiftFunctorCompIsoId_inv_app
-/
theorem shift_shiftFunctorCompIsoId_neg_add_cancel_inv_app (n : A) (X : C) :
    ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).inv.app X)⟦-n⟧' =
    (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app (X⟦-n⟧) := by
  apply shift_shiftFunctorCompIsoId_inv_app

end

section

variable (A)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorCompIsoId_zero_zero_hom_app` / 引理 `shiftFunctorCompIsoId_zero_zero_hom_app`

English:
lemma shiftFunctorCompIsoId_zero_zero_hom_app
  given: (X : C)
  proof: by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_inv_app]

中文:
引理 shiftFunctorCompIsoId_zero_zero_hom_app
  条件: (X : C)
  证明: by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_inv_app]

Depends on / 依赖: _zero_add_inv_app, shiftFunctorAdd, shiftFunctorCompIsoId
-/
lemma shiftFunctorCompIsoId_zero_zero_hom_app (X : C) :
    (shiftFunctorCompIsoId C 0 0 (add_zero 0)).hom.app X =
      ((shiftFunctorZero C A).hom.app X)⟦0⟧' ≫ (shiftFunctorZero C A).hom.app X := by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_inv_app]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorCompIsoId_zero_zero_inv_app` / 引理 `shiftFunctorCompIsoId_zero_zero_inv_app`

English:
lemma shiftFunctorCompIsoId_zero_zero_inv_app
  given: (X : C)
  proof: by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_hom_app]

中文:
引理 shiftFunctorCompIsoId_zero_zero_inv_app
  条件: (X : C)
  证明: by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_hom_app]

Depends on / 依赖: _zero_add_hom_app, shiftFunctorAdd, shiftFunctorCompIsoId
-/
lemma shiftFunctorCompIsoId_zero_zero_inv_app (X : C) :
    (shiftFunctorCompIsoId C 0 0 (add_zero 0)).inv.app X =
      (shiftFunctorZero C A).inv.app X ≫ ((shiftFunctorZero C A).inv.app X)⟦0⟧' := by
  simp [shiftFunctorCompIsoId, shiftFunctorAdd'_zero_add_hom_app]

end

section

variable (m n p m' n' p' : A) (hm : m' + m = 0) (hn : n' + n = 0) (hp : p' + p = 0)
  (h : m + n = p)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorCompIsoId_add'_inv_app` / 引理 `shiftFunctorCompIsoId_add'_inv_app`

English:
lemma shiftFunctorCompIsoId_add'_inv_app
  proof: by
  dsimp [shiftFunctorCompIsoId]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← NatTrans.naturality]
  dsimp
  rw [← cancel_mono ((shiftFunctorAdd' C p' p 0 hp).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc

中文:
引理 shiftFunctorCompIsoId_add'_inv_app
  证明: by
  dsimp [shiftFunctorCompIsoId]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← NatTrans.naturality]
  dsimp
  rw [← cancel_mono ((shiftFunctorAdd' C p' p 0 hp).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.map_comp_assoc, Iso.hom_inv_id_app, NatTrans, NatTrans.naturality, _assoc_inv_app, add_assoc, add_left_inj, cancel_mono, hom_inv_id_app, inv.app, map_comp, map_comp_assoc, naturality, shiftFunctorAdd, shiftFunctorCompIsoId
-/
lemma shiftFunctorCompIsoId_add'_inv_app :
    (shiftFunctorCompIsoId C p' p hp).inv.app X =
      (shiftFunctorCompIsoId C n' n hn).inv.app X ≫
      (shiftFunctorCompIsoId C m' m hm).inv.app (X⟦n'⟧)⟦n⟧' ≫
      (shiftFunctorAdd' C m n p h).inv.app (X⟦n'⟧⟦m'⟧) ≫
      ((shiftFunctorAdd' C n' m' p'
        (by rw [← add_left_inj p, hp, ← h, add_assoc,
          ← add_assoc m', hm, zero_add, hn])).inv.app X)⟦p⟧' := by
  dsimp [shiftFunctorCompIsoId]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← NatTrans.naturality]
  dsimp
  rw [← cancel_mono ((shiftFunctorAdd' C p' p 0 hp).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← shiftFunctorAdd'_assoc_inv_app p' m n n' p 0
      (by rw [← add_left_inj n]; rw [hn]; rw [add_assoc]; rw [h]; rw [hp]) h (by rw [add_assoc, h, hp]),
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, Category.assoc,
    shiftFunctorAdd'_assoc_inv_app n' m' m p' 0 n' _ hm
      (by rw [add_assoc, hm, add_zero]), Iso.hom_inv_id_app_assoc,
    ← shiftFunctorAdd'_add_zero_hom_app, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorCompIsoId_add'_hom_app` / 引理 `shiftFunctorCompIsoId_add'_hom_app`

English:
lemma shiftFunctorCompIsoId_add'_hom_app
  proof: by
  rw [← cancel_mono ((shiftFunctorCompIsoId C p' p hp).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorCompIsoId_add'_inv_app m n p m' n' p' hm hn hp h]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_

中文:
引理 shiftFunctorCompIsoId_add'_hom_app
  证明: by
  rw [← cancel_mono ((shiftFunctorCompIsoId C p' p hp).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorCompIsoId_add'_inv_app m n p m' n' p' hm hn hp h]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_
-/
lemma shiftFunctorCompIsoId_add'_hom_app :
    (shiftFunctorCompIsoId C p' p hp).hom.app X =
      ((shiftFunctorAdd' C n' m' p'
          (by rw [← add_left_inj p, hp, ← h, add_assoc,
            ← add_assoc m', hm, zero_add, hn])).hom.app X)⟦p⟧' ≫
      (shiftFunctorAdd' C m n p h).hom.app (X⟦n'⟧⟦m'⟧) ≫
      (shiftFunctorCompIsoId C m' m hm).hom.app (X⟦n'⟧)⟦n⟧' ≫
      (shiftFunctorCompIsoId C n' n hn).hom.app X := by
  rw [← cancel_mono ((shiftFunctorCompIsoId C p' p hp).inv.app X)]; rw [Iso.hom_inv_id_app]; rw [shiftFunctorCompIsoId_add'_inv_app m n p m' n' p' hm hn hp h]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp_assoc]; rw [Iso.hom_inv_id_app]
  dsimp
  rw [Functor.map_id]; rw [Category.id_comp]; rw [Iso.hom_inv_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]

end

open CategoryTheory.Limits

variable [HasZeroMorphisms C]

/--
theorem `shift_zero_eq_zero` / 定理 `shift_zero_eq_zero`

English:
theorem shift_zero_eq_zero
  given: (X Y : C) (n : A)
  statement: (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧)
  proof: CategoryTheory.Functor.map_zero _ _ _

中文:
定理 shift_zero_eq_zero
  条件: (X Y : C) (n : A)
  结论: (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧)
  证明: CategoryTheory.Functor.map_zero _ _ _

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_zero, Functor, map_zero
-/
theorem shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
  CategoryTheory.Functor.map_zero _ _ _

end AddGroup

section AddCommMonoid

variable [AddCommMonoid A] [HasShift C A]
variable (C)

/--
Definition of `shiftFunctorComm` / `shiftFunctorComm` 的定义

English:
definition shiftFunctorComm
  signature: (i j : A)
  body: (shiftFunctorAdd C i j).symm ≪≫ shiftFunctorAdd' C j i (i + j) (add_comm j i)

中文:
定义 shiftFunctorComm
  签名: (i j : A)
  定义体: (shiftFunctorAdd C i j).symm ≪≫ shiftFunctorAdd' C j i (i + j) (add_comm j i)

Depends on / 依赖: add_comm, shiftFunctorAdd
-/
def shiftFunctorComm (i j : A) :
    shiftFunctor C i ⋙ shiftFunctor C j ≅
      shiftFunctor C j ⋙ shiftFunctor C i :=
  (shiftFunctorAdd C i j).symm ≪≫ shiftFunctorAdd' C j i (i + j) (add_comm j i)

/--
lemma `shiftFunctorComm_eq` / 引理 `shiftFunctorComm_eq`

English:
lemma shiftFunctorComm_eq
  given: (i j k : A) (h : i + j = k)
  proof: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

@[simp]

中文:
引理 shiftFunctorComm_eq
  条件: (i j k : A) (h : i + j = k)
  证明: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

@[simp]

Depends on / 依赖: _eq_shiftFunctorAdd, shiftFunctorAdd
-/
lemma shiftFunctorComm_eq (i j k : A) (h : i + j = k) :
    shiftFunctorComm C i j = (shiftFunctorAdd' C i j k h).symm ≪≫
      shiftFunctorAdd' C j i k (by rw [add_comm j i, h]) := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]
  rfl

@[simp]
/--
lemma `shiftFunctorComm_eq_refl` / 引理 `shiftFunctorComm_eq_refl`

English:
lemma shiftFunctorComm_eq_refl
  given: (i : A)
  proof: by
  rw [shiftFunctorComm_eq C i i (i + i) rfl]; rw [Iso.symm_self_id]

中文:
引理 shiftFunctorComm_eq_refl
  条件: (i : A)
  证明: by
  rw [shiftFunctorComm_eq C i i (i + i) rfl]; rw [Iso.symm_self_id]

Depends on / 依赖: Iso.symm_self_id, shiftFunctorComm_eq, symm_self_id
-/
lemma shiftFunctorComm_eq_refl (i : A) :
    shiftFunctorComm C i i = Iso.refl _ := by
  rw [shiftFunctorComm_eq C i i (i + i) rfl]; rw [Iso.symm_self_id]

/--
lemma `shiftFunctorComm_symm` / 引理 `shiftFunctorComm_symm`

English:
lemma shiftFunctorComm_symm
  given: (i j : A)
  proof: by
  ext1
  dsimp
  rw [shiftFunctorComm_eq C i j (i + j) rfl]; rw [shiftFunctorComm_eq C j i (i + j) (add_comm j i)]
  rfl

中文:
引理 shiftFunctorComm_symm
  条件: (i j : A)
  证明: by
  ext1
  dsimp
  rw [shiftFunctorComm_eq C i j (i + j) rfl]; rw [shiftFunctorComm_eq C j i (i + j) (add_comm j i)]
  rfl

Depends on / 依赖: add_comm, shiftFunctorComm_eq
-/
lemma shiftFunctorComm_symm (i j : A) :
    (shiftFunctorComm C i j).symm = shiftFunctorComm C j i := by
  ext1
  dsimp
  rw [shiftFunctorComm_eq C i j (i + j) rfl]; rw [shiftFunctorComm_eq C j i (i + j) (add_comm j i)]
  rfl

variable {C}
variable (X Y : C) (f : X ⟶ Y)

/--
Definition of `shiftComm` / `shiftComm` 的定义

English:
abbreviation shiftComm
  signature: (i j : A)
  body: (shiftFunctorComm C i j).app X

@[simp]

中文:
缩写 shiftComm
  签名: (i j : A)
  定义体: (shiftFunctorComm C i j).app X

@[simp]

Depends on / 依赖: shiftFunctorComm
-/
abbrev shiftComm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shiftFunctorComm C i j).app X

@[simp]
/--
theorem `shiftComm_symm` / 定理 `shiftComm_symm`

English:
theorem shiftComm_symm
  given: (i j : A)
  statement: (shiftComm X i j).symm = shiftComm X j i
  proof: by
  ext
  exact NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorComm_symm C i j)) X

中文:
定理 shiftComm_symm
  条件: (i j : A)
  结论: (shiftComm X i j).symm = shiftComm X j i
  证明: by
  ext
  exact NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorComm_symm C i j)) X

Depends on / 依赖: Iso.hom, NatTrans, NatTrans.congr_app, congr_app, congr_arg, shiftFunctorComm_symm
-/
theorem shiftComm_symm (i j : A) : (shiftComm X i j).symm = shiftComm X j i := by
  ext
  exact NatTrans.congr_app (congr_arg Iso.hom (shiftFunctorComm_symm C i j)) X

variable {X Y}

set_option backward.defeqAttrib.useBackward true in
/--
theorem `shiftComm'` / 定理 `shiftComm'`

English:
theorem shiftComm'
  given: (i j : A)
  proof: by
  erw [← shiftComm_symm Y i j, ← ((shiftFunctorComm C i j).hom.naturality_assoc f)]
  dsimp
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

@[reassoc]

中文:
定理 shiftComm'
  条件: (i j : A)
  证明: by
  erw [← shiftComm_symm Y i j, ← ((shiftFunctorComm C i j).hom.naturality_assoc f)]
  dsimp
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

@[reassoc]

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.comp_obj, Iso.hom_inv_id_app, comp_id, comp_obj, hom.naturality_assoc, hom_inv_id_app, naturality_assoc, shiftComm_symm, shiftFunctorComm
-/
theorem shiftComm' (i j : A) :
    f⟦i⟧'⟦j⟧' = (shiftComm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shiftComm _ _ _).hom := by
  erw [← shiftComm_symm Y i j, ← ((shiftFunctorComm C i j).hom.naturality_assoc f)]
  dsimp
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]

@[reassoc]
/--
theorem `shiftComm_hom_comp` / 定理 `shiftComm_hom_comp`

English:
theorem shiftComm_hom_comp
  given: (i j : A)
  proof: by
  rw [shiftComm']; rw [← shiftComm_symm]; rw [Iso.symm_hom]; rw [Iso.inv_hom_id_assoc]

中文:
定理 shiftComm_hom_comp
  条件: (i j : A)
  证明: by
  rw [shiftComm']; rw [← shiftComm_symm]; rw [Iso.symm_hom]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, Iso.symm_hom, inv_hom_id_assoc, shiftComm, shiftComm_symm, symm_hom
-/
theorem shiftComm_hom_comp (i j : A) :
    (shiftComm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shiftComm Y i j).hom := by
  rw [shiftComm']; rw [← shiftComm_symm]; rw [Iso.symm_hom]; rw [Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorZero_hom_app_shift` / 引理 `shiftFunctorZero_hom_app_shift`

English:
lemma shiftFunctorZero_hom_app_shift
  given: (n : A)
  proof: by
  rw [← shiftFunctorAdd'_zero_add_inv_app n X]; rw [shiftFunctorComm_eq C n 0 n (add_zero n)]
  dsimp
  rw [Category.assoc]; rw [Iso.hom_inv_id_app]; rw [Category.comp_id]; rw [shiftFunctorAdd'_add_zero_inv_app]

中文:
引理 shiftFunctorZero_hom_app_shift
  条件: (n : A)
  证明: by
  rw [← shiftFunctorAdd'_zero_add_inv_app n X]; rw [shiftFunctorComm_eq C n 0 n (add_zero n)]
  dsimp
  rw [Category.assoc]; rw [Iso.hom_inv_id_app]; rw [Category.comp_id]; rw [shiftFunctorAdd'_add_zero_inv_app]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Iso.hom_inv_id_app, _add_zero_inv_app, _zero_add_inv_app, add_zero, comp_id, hom_inv_id_app, shiftFunctorAdd, shiftFunctorComm_eq
-/
lemma shiftFunctorZero_hom_app_shift (n : A) :
    (shiftFunctorZero C A).hom.app (X⟦n⟧) =
    (shiftFunctorComm C n 0).hom.app X ≫ ((shiftFunctorZero C A).hom.app X)⟦n⟧' := by
  rw [← shiftFunctorAdd'_zero_add_inv_app n X]; rw [shiftFunctorComm_eq C n 0 n (add_zero n)]
  dsimp
  rw [Category.assoc]; rw [Iso.hom_inv_id_app]; rw [Category.comp_id]; rw [shiftFunctorAdd'_add_zero_inv_app]

/--
lemma `shiftFunctorZero_inv_app_shift` / 引理 `shiftFunctorZero_inv_app_shift`

English:
lemma shiftFunctorZero_inv_app_shift
  given: (n : A)
  proof: by
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app (X⟦n⟧))]; rw [Category.assoc]; rw [Iso.inv_hom_id_app]; rw [shiftFunctorZero_hom_app_shift]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id]

中文:
引理 shiftFunctorZero_inv_app_shift
  条件: (n : A)
  证明: by
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app (X⟦n⟧))]; rw [Category.assoc]; rw [Iso.inv_hom_id_app]; rw [shiftFunctorZero_hom_app_shift]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.map_id, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, cancel_mono, hom.app, inv_hom_id_app, inv_hom_id_app_assoc, map_comp, map_id, shiftFunctorZero, shiftFunctorZero_hom_app_shift
-/
lemma shiftFunctorZero_inv_app_shift (n : A) :
    (shiftFunctorZero C A).inv.app (X⟦n⟧) =
      ((shiftFunctorZero C A).inv.app X)⟦n⟧' ≫ (shiftFunctorComm C n 0).inv.app X := by
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app (X⟦n⟧))]; rw [Category.assoc]; rw [Iso.inv_hom_id_app]; rw [shiftFunctorZero_hom_app_shift]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id_app]
  dsimp
  rw [Functor.map_id]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorComm_zero_hom_app` / 引理 `shiftFunctorComm_zero_hom_app`

English:
lemma shiftFunctorComm_zero_hom_app
  given: (a : A)
  proof: by
  simp only [shiftFunctorZero_hom_app_shift, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.map_id, Functor.comp_obj, Category.comp_id]

中文:
引理 shiftFunctorComm_zero_hom_app
  条件: (a : A)
  证明: by
  simp only [shiftFunctorZero_hom_app_shift, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.map_id, Functor.comp_obj, Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Functor, Functor.comp_obj, Functor.map_comp, Functor.map_id, Iso.hom_inv_id_app, comp_id, comp_obj, hom_inv_id_app, map_comp, map_id, shiftFunctorZero_hom_app_shift
-/
lemma shiftFunctorComm_zero_hom_app (a : A) :
    (shiftFunctorComm C a 0).hom.app X =
      (shiftFunctorZero C A).hom.app (X⟦a⟧) ≫ ((shiftFunctorZero C A).inv.app X)⟦a⟧' := by
  simp only [shiftFunctorZero_hom_app_shift, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.map_id, Functor.comp_obj, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app` / 引理 `shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app`

English:
lemma shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app
  given: (m₁ m₂ m₃ : A) (X : C)
  proof: by
  rw [← cancel_mono ((shiftFunctorComm C m₁ m₃).inv.app (X⟦m₂⟧))]; rw [← cancel_mono (((shiftFunctorComm C m₁ m₂).inv.app X)⟦m₃⟧')]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp
  simp only [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  dsimp
  simp only [Functor.map_id, 

中文:
引理 shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app
  条件: (m₁ m₂ m₃ : A) (X : C)
  证明: by
  rw [← cancel_mono ((shiftFunctorComm C m₁ m₃).inv.app (X⟦m₂⟧))]; rw [← cancel_mono (((shiftFunctorComm C m₁ m₂).inv.app X)⟦m₃⟧')]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp
  simp only [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  dsimp
  simp only [Functor.map_id, 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Functor, Functor.map_comp, Functor.map_id, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc, _eq_shiftFunctorAdd, cancel_mono, comp_id, hom_inv_id_app, hom_inv_id_app_assoc, id_comp, inv.app, inv_hom_id_app_assoc, map_comp, map_id
-/
lemma shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app (m₁ m₂ m₃ : A) (X : C) :
    (shiftFunctorComm C m₁ (m₂ + m₃)).hom.app X ≫
    ((shiftFunctorAdd C m₂ m₃).hom.app X)⟦m₁⟧' =
      (shiftFunctorAdd C m₂ m₃).hom.app (X⟦m₁⟧) ≫
        ((shiftFunctorComm C m₁ m₂).hom.app X)⟦m₃⟧' ≫
        (shiftFunctorComm C m₁ m₃).hom.app (X⟦m₂⟧) := by
  rw [← cancel_mono ((shiftFunctorComm C m₁ m₃).inv.app (X⟦m₂⟧))]; rw [← cancel_mono (((shiftFunctorComm C m₁ m₂).inv.app X)⟦m₃⟧')]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp
  simp only [Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  dsimp
  simp only [Functor.map_id, Category.comp_id,
    shiftFunctorComm_eq C _ _ _ rfl, ← shiftFunctorAdd'_eq_shiftFunctorAdd]
  dsimp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp,
    shiftFunctorAdd'_assoc_hom_app_assoc m₂ m₃ m₁ (m₂ + m₃) (m₁ + m₃) (m₁ + (m₂ + m₃)) rfl
      (add_comm m₃ m₁) (add_comm _ m₁) X,
    ← shiftFunctorAdd'_assoc_hom_app_assoc m₂ m₁ m₃ (m₁ + m₂) (m₁ + m₃)
      (m₁ + (m₂ + m₃)) (add_comm _ _) rfl (by rw [add_comm m₂ m₁, add_assoc]) X,
    shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃
      (m₁ + m₂) (m₂ + m₃) (m₁ + (m₂ + m₃)) rfl rfl (add_assoc _ _ _) X]

@[reassoc]
/--
lemma `shiftFunctorComm_hom_app_of_add_eq_zero` / 引理 `shiftFunctorComm_hom_app_of_add_eq_zero`

English:
lemma shiftFunctorComm_hom_app_of_add_eq_zero
  given: (m n : A) (hmn : m + n = 0) (X : C)
  proof: by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

@[reassoc]

中文:
引理 shiftFunctorComm_hom_app_of_add_eq_zero
  条件: (m n : A) (hmn : m + n = 0) (X : C)
  证明: by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

@[reassoc]

Depends on / 依赖: shiftFunctorComm_eq, shiftFunctorCompIsoId
-/
lemma shiftFunctorComm_hom_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) :
    (shiftFunctorComm C m n).hom.app X =
      (shiftFunctorCompIsoId C m n hmn).hom.app X ≫
        (shiftFunctorCompIsoId C n m (by rw [add_comm, hmn])).inv.app X := by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

@[reassoc]
/--
lemma `shiftFunctorComm_inv_app_of_add_eq_zero` / 引理 `shiftFunctorComm_inv_app_of_add_eq_zero`

English:
lemma shiftFunctorComm_inv_app_of_add_eq_zero
  given: (m n : A) (hmn : m + n = 0) (X : C)
  proof: by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

中文:
引理 shiftFunctorComm_inv_app_of_add_eq_zero
  条件: (m n : A) (hmn : m + n = 0) (X : C)
  证明: by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

Depends on / 依赖: shiftFunctorComm_eq, shiftFunctorCompIsoId
-/
lemma shiftFunctorComm_inv_app_of_add_eq_zero (m n : A) (hmn : m + n = 0) (X : C) :
    (shiftFunctorComm C m n).inv.app X =
      (shiftFunctorCompIsoId C n m (by rw [add_comm, hmn])).hom.app X ≫
        (shiftFunctorCompIsoId C m n hmn).inv.app X := by
  simp [shiftFunctorCompIsoId, shiftFunctorComm_eq C m n 0 hmn]

end AddCommMonoid

namespace Functor.FullyFaithful

variable {D : Type*} [Category* D] [AddMonoid A] [HasShift D A]
variable {F : C ⥤ D} (hF : F.FullyFaithful)
variable (s : A -> C ⥤ C) (i : forall i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace hasShift

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: : s 0 ≅ 𝟭 C
  body: (hF.whiskeringRight C).preimageIso ((i 0) ≪≫ isoWhiskerLeft F (shiftFunctorZero D A) ≪≫
    rightUnitor _ ≪≫ (leftUnitor _).symm)

中文:
定义 zero
  签名: : s 0 ≅ 𝟭 C
  定义体: (hF.whiskeringRight C).preimageIso ((i 0) ≪≫ isoWhiskerLeft F (shiftFunctorZero D A) ≪≫
    rightUnitor _ ≪≫ (leftUnitor _).symm)

Depends on / 依赖: hF.whiskeringRight, isoWhiskerLeft, leftUnitor, preimageIso, rightUnitor, shiftFunctorZero, whiskeringRight
-/
def zero : s 0 ≅ 𝟭 C :=
  (hF.whiskeringRight C).preimageIso ((i 0) ≪≫ isoWhiskerLeft F (shiftFunctorZero D A) ≪≫
    rightUnitor _ ≪≫ (leftUnitor _).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `map_zero_hom_app` / 引理 `map_zero_hom_app`

English:
lemma map_zero_hom_app
  given: (X : C)
  proof: by
  simp [zero]

中文:
引理 map_zero_hom_app
  条件: (X : C)
  证明: by
  simp [zero]
-/
lemma map_zero_hom_app (X : C) :
    F.map ((zero hF s i).hom.app X) =
      (i 0).hom.app X ≫ (shiftFunctorZero D A).hom.app (F.obj X) := by
  simp [zero]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `map_zero_inv_app` / 引理 `map_zero_inv_app`

English:
lemma map_zero_inv_app
  given: (X : C)
  proof: by
  simp [zero]

中文:
引理 map_zero_inv_app
  条件: (X : C)
  证明: by
  simp [zero]
-/
lemma map_zero_inv_app (X : C) :
    F.map ((zero hF s i).inv.app X) =
      (shiftFunctorZero D A).inv.app (F.obj X) ≫ (i 0).inv.app X := by
  simp [zero]

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (a b : A)
  body: (hF.whiskeringRight C).preimageIso (i (a + b) ≪≫ isoWhiskerLeft _ (shiftFunctorAdd D a b) ≪≫
      (associator _ _ _).symm ≪≫ (isoWhiskerRight (i a).symm _) ≪≫
      associator _ _ _ ≪≫ (isoWhiskerLeft _ (i b).symm) ≪≫
      (associator _ _ _).symm)

中文:
定义 add
  签名: (a b : A)
  定义体: (hF.whiskeringRight C).preimageIso (i (a + b) ≪≫ isoWhiskerLeft _ (shiftFunctorAdd D a b) ≪≫
      (associator _ _ _).symm ≪≫ (isoWhiskerRight (i a).symm _) ≪≫
      associator _ _ _ ≪≫ (isoWhiskerLeft _ (i b).symm) ≪≫
      (associator _ _ _).symm)

Depends on / 依赖: associator, hF.whiskeringRight, isoWhiskerLeft, isoWhiskerRight, preimageIso, shiftFunctorAdd, whiskeringRight
-/
def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  (hF.whiskeringRight C).preimageIso (i (a + b) ≪≫ isoWhiskerLeft _ (shiftFunctorAdd D a b) ≪≫
      (associator _ _ _).symm ≪≫ (isoWhiskerRight (i a).symm _) ≪≫
      associator _ _ _ ≪≫ (isoWhiskerLeft _ (i b).symm) ≪≫
      (associator _ _ _).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `map_add_hom_app` / 引理 `map_add_hom_app`

English:
lemma map_add_hom_app
  given: (a b : A) (X : C)
  proof: by
  dsimp [add]
  simp

中文:
引理 map_add_hom_app
  条件: (a b : A) (X : C)
  证明: by
  dsimp [add]
  simp
-/
lemma map_add_hom_app (a b : A) (X : C) :
    F.map ((add hF s i a b).hom.app X) =
      (i (a + b)).hom.app X ≫ (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        ((i a).inv.app X)⟦b⟧' ≫ (i b).inv.app ((s a).obj X) := by
  dsimp [add]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `map_add_inv_app` / 引理 `map_add_inv_app`

English:
lemma map_add_inv_app
  given: (a b : A) (X : C)
  proof: by
  dsimp [add]
  simp

中文:
引理 map_add_inv_app
  条件: (a b : A) (X : C)
  证明: by
  dsimp [add]
  simp
-/
lemma map_add_inv_app (a b : A) (X : C) :
    F.map ((add hF s i a b).inv.app X) =
      (i b).hom.app ((s a).obj X) ≫ ((i a).hom.app X)⟦b⟧' ≫
        (shiftFunctorAdd D a b).inv.app (F.obj X) ≫ (i (a + b)).inv.app X := by
  dsimp [add]
  simp

end hasShift

set_option backward.defeqAttrib.useBackward true in
open hasShift in
/-- Given a family of endomorphisms of `C` which are intertwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
@[instance_reducible]
/--
Definition of `hasShift` / `hasShift` 的定义

English:
definition hasShift
  signature: :
  body: hasShiftMk C A
    { F := s
      zero := zero hF s i
      add := add hF s i
      assoc_hom_app := fun m₁ m₂ m₃ X => hF.map_injective (by
        have h := shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃ _ _ (m₁ + m₂ + m₃) rfl rfl rfl (F.obj X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at h


中文:
定义 hasShift
  签名: :
  定义体: hasShiftMk C A
    { F := s
      zero := zero hF s i
      add := add hF s i
      assoc_hom_app := fun m₁ m₂ m₃ X => hF.map_injective (by
        have h := shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃ _ _ (m₁ + m₂ + m₃) rfl rfl rfl (F.obj X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at h


Depends on / 依赖: Category, Category.assoc, F.obj, Functor, Functor.comp_map, Functor.comp_obj, Functor.map_comp, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, M.subset_closure, NatTrans, NatTrans.naturality_assoc, _assoc_hom_app, _eq_shiftFunctorAdd, _iff_isBasis_inter_ground, assoc_hom_app, cancel_mono, closure_inter_ground, comp_map, comp_obj
-/
def hasShift :
    HasShift C A :=
  hasShiftMk C A
    { F := s
      zero := zero hF s i
      add := add hF s i
      assoc_hom_app := fun m₁ m₂ m₃ X => hF.map_injective (by
        have h := shiftFunctorAdd'_assoc_hom_app m₁ m₂ m₃ _ _ (m₁ + m₂ + m₃) rfl rfl rfl (F.obj X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at h
        rw [← cancel_mono ((i m₃).hom.app ((s m₂).obj ((s m₁).obj X)))]
        simp only [Functor.comp_obj, Functor.map_comp, map_add_hom_app,
          Category.assoc, Iso.inv_hom_id_app_assoc, NatTrans.naturality_assoc, Functor.comp_map,
          Iso.inv_hom_id_app, Category.comp_id]
        erw [(i m₃).hom.naturality]
        rw [Functor.comp_map]; rw [map_add_hom_app]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Iso.inv_hom_id_app_assoc]; rw [← Functor.map_comp_assoc _ ((i (m₁ + m₂)).inv.app X)]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [Category.id_comp]; rw [reassoc_of% h]; rw [dcongr_arg (fun a => (i a).hom.app X) (add_assoc m₁ m₂ m₃)]
        simp [shiftFunctorAdd', eqToHom_map])
      zero_add_hom_app := fun n X => hF.map_injective (by
        have := dcongr_arg (fun a => (i a).hom.app X) (zero_add n)
        rw [← cancel_mono ((i n).hom.app ((s 0).obj X))]
        simp only [comp_obj, map_add_hom_app, this, shiftFunctorAdd_zero_add_hom_app, id_obj,
          Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_app,
          Category.comp_id, map_comp, eqToHom_map]
        congr 1
        erw [(i n).hom.naturality]
        simp)
      add_zero_hom_app := fun n X => hF.map_injective (by
        have := dcongr_arg (fun a => (i a).hom.app X) (add_zero n)
        simp [this, ← NatTrans.naturality_assoc, eqToHom_map,
          shiftFunctorAdd_add_zero_hom_app]) }

end Functor.FullyFaithful

end

end CategoryTheory
