/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# Homotopies in the arrow category

We define left and right homotopies between morphisms of `Arrow V`, where `V` is
a preadditive category.

TODO: Define the preadditive categories `LeftFreyd V` (resp. `RightFreyd V`) obtained by
taking the quotient of `Arrow V` by the left (resp. right) homotopy relation. If `V`
has binary biproducts, this will have all kernels (resp. cokernels) and will be the
category obtained by freely adjoining kernels (resp. cokernels) to `V`.

-/

@[expose] public section

noncomputable section

open CategoryTheory Category

variable {V : Type*} [Category* V] [Preadditive V]

namespace CategoryTheory.Arrow

variable {u v w : Arrow V} (f g : u ⟶ v)

/-- A left homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
/--
Definition of `LeftHomotopy` / `LeftHomotopy` 的定义

English:
structure LeftHomotopy
  parameters: where
  (no additional axioms)

中文:
结构 LeftHomotopy
  参数: where
  (无附加公理)

Depends on / 依赖: cat_disch
-/
structure LeftHomotopy where
/-- A "diagonal" morphism from the right object of `u` to the left object of `v`. -/
  hom : u.right ⟶ v.left
/-- The difference of the left morphisms factors through `hom`. -/
  comm : f.left - g.left = u.hom ≫ hom := by cat_disch

/-- A right homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
/--
Definition of `RightHomotopy` / `RightHomotopy` 的定义

English:
structure RightHomotopy
  parameters: where
  axioms and operations (2):
    - hom : u.right ⟶ v.left
    - comm : f.right - g.right = hom ≫ v.hom  [default: by cat_disch]

中文:
结构 RightHomotopy
  参数: where
  公理与运算 (2 个):
    - hom : u.right ⟶ v.left
    - comm : f.right - g.right = hom ≫ v.hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure RightHomotopy where
  /-- A "diagonal" morphism from the right object of `u` to the left object of `v`. -/
  hom : u.right ⟶ v.left
  /-- The difference of the right morphisms factors through `hom`. -/
  comm : f.right - g.right = hom ≫ v.hom := by cat_disch

variable {f g}

namespace LeftHomotopy

/--
Definition of `equivSubZero` / `equivSubZero` 的定义

English:
definition equivSubZero
  signature: : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where
  body: { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 equivSubZero
  签名: : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where
  定义体: { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: cat_disch, h.comm, h.hom, invFun, left_inv, right_inv
-/
def equivSubZero : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal maps of arrows are left homotopic. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : f = g)
  body: 0

中文:
定义 ofEq
  签名: (h : f = g)
  定义体: 0
-/
def ofEq (h : f = g) : LeftHomotopy f g where
  hom := 0

/-- Every map of arrows is left homotopic to itself. -/
@[simps!, refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : u ⟶ v)
  body: ofEq (rfl : f = f)

中文:
定义 refl
  签名: (f : u ⟶ v)
  定义体: ofEq (rfl : f = f)

Depends on / 依赖: Composition, Composition.ones
-/
def refl (f : u ⟶ v) : LeftHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is left homotopic to `g` iff `g` is left homotopic to `f`. -/
@[simps!, symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f g : u ⟶ v} (h : LeftHomotopy f g)
  body: -h.hom
  comm := by simp [← h.comm]

中文:
定义 symm
  签名: {f g : u ⟶ v} (h : LeftHomotopy f g)
  定义体: -h.hom
  comm := by simp [← h.comm]

Depends on / 依赖: h.hom
-/
def symm {f g : u ⟶ v} (h : LeftHomotopy f g) : LeftHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- Left homotopy is a transitive relation. -/
@[simps!, trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g)
  body: h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

中文:
定义 trans
  签名: {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g)
  定义体: h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

Depends on / 依赖: h.hom, k.hom
-/
def trans {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g) : LeftHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- The sum of two left homotopies is a left homotopy between the sum of the respective
morphisms. -/
@[simps!]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂)
  body: h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

中文:
定义 add
  签名: {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂)
  定义体: h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]
-/
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) :
    LeftHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- Left homotopy is closed under composition (on the right). -/
@[simps]
/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w)
  body: h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

中文:
定义 compRight
  签名: {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w)
  定义体: h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

Depends on / 依赖: g.left, h.hom
-/
def compRight {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w) :
    LeftHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- Left homotopy is closed under composition (on the left). -/
@[simps]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v)
  body: e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

中文:
定义 compLeft
  签名: {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v)
  定义体: e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

Depends on / 依赖: e.right, h.hom
-/
def compLeft {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v) :
    LeftHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

/-- Left homotopy is closed under composition. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
  body: (h₁.compRight _).trans (h₂.compLeft _)

中文:
定义 comp
  签名: {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
  定义体: (h₁.compRight _).trans (h₂.compLeft _)

Depends on / 依赖: compLeft, compRight
-/
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) : LeftHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- A variant of `LeftHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
/--
Definition of `compRightId` / `compRightId` 的定义

English:
definition compRightId
  signature: {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v)
  body: (h.compRight g).trans (ofEq <| id_comp _)

中文:
定义 compRightId
  签名: {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v)
  定义体: (h.compRight g).trans (ofEq <| id_comp _)

Depends on / 依赖: compRight, h.compRight, id_comp
-/
def compRightId {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v) : LeftHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- A variant of `LeftHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
/--
Definition of `compLeftId` / `compLeftId` 的定义

English:
definition compLeftId
  signature: {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v)
  body: (h.compLeft g).trans (ofEq <| comp_id _)

中文:
定义 compLeftId
  签名: {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v)
  定义体: (h.compLeft g).trans (ofEq <| comp_id _)

Depends on / 依赖: compLeft, comp_id, h.compLeft
-/
def compLeftId {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v) : LeftHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end LeftHomotopy

namespace RightHomotopy

/--
Definition of `equivSubZero` / `equivSubZero` 的定义

English:
definition equivSubZero
  signature: : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  body: { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 equivSubZero
  签名: : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  定义体: { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: cat_disch, h.comm, h.hom, invFun, left_inv, right_inv
-/
def equivSubZero : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal maps of arrows are right homotopic. -/
@[simps]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : f = g)
  body: 0

中文:
定义 ofEq
  签名: (h : f = g)
  定义体: 0
-/
def ofEq (h : f = g) : RightHomotopy f g where
  hom := 0

/-- Every map of arrows is right homotopic to itself. -/
@[simps!, refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : u ⟶ v)
  body: ofEq (rfl : f = f)

中文:
定义 refl
  签名: (f : u ⟶ v)
  定义体: ofEq (rfl : f = f)
-/
def refl (f : u ⟶ v) : RightHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is right homotopic to `g` iff `g` is right homotopic to `f`. -/
@[simps!, symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f g : u ⟶ v} (h : RightHomotopy f g)
  body: -h.hom
  comm := by simp [← h.comm]

中文:
定义 symm
  签名: {f g : u ⟶ v} (h : RightHomotopy f g)
  定义体: -h.hom
  comm := by simp [← h.comm]

Depends on / 依赖: h.hom
-/
def symm {f g : u ⟶ v} (h : RightHomotopy f g) : RightHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- Right homotopy is a transitive relation. -/
@[simps!, trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g)
  body: h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

中文:
定义 trans
  签名: {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g)
  定义体: h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

Depends on / 依赖: h.hom, k.hom
-/
def trans {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g) : RightHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- The sum of two right homotopies is a right homotopy between the sum of the respective
morphisms. -/
@[simps!]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂)
  body: h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

中文:
定义 add
  签名: {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂)
  定义体: h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]
-/
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) :
    RightHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- Right homotopy is closed under composition (on the right). -/
@[simps]
/--
Definition of `compRight` / `compRight` 的定义

English:
definition compRight
  signature: {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w)
  body: h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

中文:
定义 compRight
  签名: {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w)
  定义体: h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

Depends on / 依赖: g.left, h.hom
-/
def compRight {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w) :
    RightHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- Right homotopy is closed under composition (on the left). -/
@[simps]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v)
  body: e.right ≫ h.hom
  comm := by simp [← h.comm]

中文:
定义 compLeft
  签名: {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v)
  定义体: e.right ≫ h.hom
  comm := by simp [← h.comm]

Depends on / 依赖: e.right, h.hom
-/
def compLeft {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v) :
    RightHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← h.comm]

/-- Right homotopy is closed under composition. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
  body: (h₁.compRight _).trans (h₂.compLeft _)

中文:
定义 comp
  签名: {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
  定义体: (h₁.compRight _).trans (h₂.compLeft _)

Depends on / 依赖: compLeft, compRight
-/
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) : RightHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- A variant of `RightHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
/--
Definition of `compRightId` / `compRightId` 的定义

English:
definition compRightId
  signature: {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v)
  body: (h.compRight g).trans (ofEq <| id_comp _)

中文:
定义 compRightId
  签名: {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v)
  定义体: (h.compRight g).trans (ofEq <| id_comp _)

Depends on / 依赖: compRight, h.compRight, id_comp
-/
def compRightId {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v) : RightHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- A variant of `RightHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
/--
Definition of `compLeftId` / `compLeftId` 的定义

English:
definition compLeftId
  signature: {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v)
  body: (h.compLeft g).trans (ofEq <| comp_id _)

中文:
定义 compLeftId
  签名: {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v)
  定义体: (h.compLeft g).trans (ofEq <| comp_id _)

Depends on / 依赖: compLeft, comp_id, h.compLeft
-/
def compLeftId {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v) : RightHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end RightHomotopy

variable (V)

/--
Definition of `leftHomotopic` / `leftHomotopic` 的定义

English:
definition leftHomotopic
  signature: : HomRel (Arrow V)
  body: fun _ _ f g => Nonempty (LeftHomotopy f g)

中文:
定义 leftHomotopic
  签名: : HomRel (Arrow V)
  定义体: fun _ _ f g => Nonempty (LeftHomotopy f g)

Depends on / 依赖: LeftHomotopy, Nonempty
-/
def leftHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (LeftHomotopy f g)

/--
Instance `leftHomotopy_congruence` / 实例 `leftHomotopy_congruence`

English:
instance leftHomotopy_congruence
  signature: : Congruence (leftHomotopic V) where
  body: { refl := fun C => ⟨LeftHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

中文:
实例 leftHomotopy_congruence
  签名: : Congruence (leftHomotopic V) where
  定义体: { refl := fun C => ⟨LeftHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

Depends on / 依赖: LeftHomotopy, LeftHomotopy.refl, compLeft, compRight, comp_left, comp_right, i.compLeft, i.compRight, w.symm
-/
instance leftHomotopy_congruence : Congruence (leftHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨LeftHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/--
Definition of `rightHomotopic` / `rightHomotopic` 的定义

English:
definition rightHomotopic
  signature: : HomRel (Arrow V)
  body: fun _ _ f g => Nonempty (RightHomotopy f g)

中文:
定义 rightHomotopic
  签名: : HomRel (Arrow V)
  定义体: fun _ _ f g => Nonempty (RightHomotopy f g)

Depends on / 依赖: Nonempty, RightHomotopy
-/
def rightHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (RightHomotopy f g)

/--
Instance `rightHomotopy_congruence` / 实例 `rightHomotopy_congruence`

English:
instance rightHomotopy_congruence
  signature: : Congruence (rightHomotopic V) where
  body: { refl := fun C => ⟨RightHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

中文:
实例 rightHomotopy_congruence
  签名: : Congruence (rightHomotopic V) where
  定义体: { refl := fun C => ⟨RightHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

Depends on / 依赖: RightHomotopy, RightHomotopy.refl, compLeft, compRight, comp_left, comp_right, i.compLeft, i.compRight, w.symm
-/
instance rightHomotopy_congruence : Congruence (rightHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨RightHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

end CategoryTheory.Arrow
