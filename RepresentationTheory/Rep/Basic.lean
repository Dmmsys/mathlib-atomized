/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.RepresentationTheory.Action
public import Mathlib.RepresentationTheory.Equiv

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

Given a `G`-representation `ρ` on a module `V`, you can construct the bundled representation as
`Rep.of ρ`. Conversely, given a bundled representation `A : Rep k G`, you can get the underlying
module as `A.V` and the representation on it as `A.ρ`.

-/

@[expose] public section

universe w w' u u' v v'

open CategoryTheory
open scoped MonoidAlgebra

/--
Definition of `Rep` / `Rep` 的定义

English:
structure Rep
  parameters: (k : Type u) (G : Type v) [Semiring k] [Monoid G]
  axioms and operations (5):
    - private(mk) : :
    - V : Type w
    - [hV1 : AddCommGroup V]
    - [hV2 : Module k V]
    - ρ : Representation k G V

中文:
结构 Rep
  参数: (k : 类型u) (G : 类型v) [半环 k] [幺半群 G]
  公理与运算 (5 个):
    - private(mk) : :
    - V : 类型 w
    - [hV1 : 加法交换群 V]
    - [hV2 : 模 k V]
    - ρ : Representation k G V
-/
structure Rep (k : Type u) (G : Type v) [Semiring k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `Rep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  /-- the underlying representation of an object in `Rep k G` -/
  ρ : Representation k G V

namespace Rep

noncomputable section

section semiring

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G] {X Y : Type w} [AddCommGroup X]
  [AddCommGroup Y] [Module k X] [Module k Y] {ρ : Representation k G X} {σ : Representation k G Y}
  (A B C : Rep.{w} k G)

attribute [instance] hV1 hV2

initialize_simps_projections Rep (-hV1, -hV2)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (Rep k G) (Type w)
  body: ⟨Rep.V⟩

中文:
实例 :
  签名: CoeSort (Rep k G) (类型 w)
  定义体: ⟨Rep.V⟩

Depends on / 依赖: Rep.V
-/
instance : CoeSort (Rep k G) (Type w) := ⟨Rep.V⟩

attribute [coe] V

variable (ρ) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : Rep.{w} k G
  body: ⟨X, ρ⟩

中文:
缩写 of
  签名: : Rep.{w} k G
  定义体: ⟨X, ρ⟩
-/
abbrev of : Rep.{w} k G := ⟨X, ρ⟩

variable (X ρ) in
/--
lemma `of_V` / 引理 `of_V`

English:
lemma of_V
  statement: (of ρ).V = X
  proof: by with_reducible rfl

中文:
引理 of_V
  结论: (of ρ).V = X
  证明: by with_reducible rfl

Depends on / 依赖: with_reducible
-/
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
/--
lemma `of_ρ` / 引理 `of_ρ`

English:
lemma of_ρ
  statement: (of ρ).ρ = ρ
  proof: by with_reducible rfl

中文:
引理 of_ρ
  结论: (of ρ).ρ = ρ
  证明: by with_reducible rfl

Depends on / 依赖: with_reducible
-/
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

/-- The type of morphisms in `Rep.{w} k G`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (2):
    - private(mk) : :
    - hom' : A.ρ.IntertwiningMap B.ρ

中文:
结构 态射
  参数: where
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A.ρ.整数ertwining映射 B.ρ
-/
structure Hom where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ.IntertwiningMap B.ρ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Rep.{w} k G)
  body: Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 (Rep.{w} k G)
  定义体: Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category (Rep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (Rep.{w} k G) (fun A B => A.ρ.IntertwiningMap B.ρ)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 (Rep.{w} k G) (fun A B => A.ρ.整数ertwining映射 B.ρ)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (Rep.{w} k G) (fun A B => A.ρ.IntertwiningMap B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {A B} in
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: (f : Hom A B)
  body: ConcreteCategory.hom (C := Rep k G) f

中文:
缩写 态射.hom
  签名: (f : 态射 A B)
  定义体: ConcreteCategory.hom (C := Rep k G) f
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := Rep k G) f

variable {A B} in
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: (f : ρ.IntertwiningMap σ)
  body: ConcreteCategory.ofHom (C := Rep.{w} k G) f

中文:
缩写 ofHom
  签名: (f : ρ.整数ertwining映射 σ)
  定义体: ConcreteCategory.ofHom (C := Rep.{w} k G) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom (f : ρ.IntertwiningMap σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := Rep.{w} k G) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (f : Hom A B)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (f : 态射 A B)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' -> hom)

/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  statement: (𝟙 A : A ⟶ A).hom = .id A.ρ
  proof: rfl

中文:
引理 hom_id
  结论: (𝟙 A : A ⟶ A).hom = .id A.ρ
  证明: rfl
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id A.ρ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (a : A)
  statement: (𝟙 A : A ⟶ A) a = a
  proof: by
  simp [Representation.IntertwiningMap.id]

中文:
引理 id_apply
  条件: (a : A)
  结论: (𝟙 A : A ⟶ A) a = a
  证明: by
  simp [Representation.IntertwiningMap.id]

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.id
-/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by
  simp [Representation.IntertwiningMap.id]

/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: (f : A ⟶ B) (g : B ⟶ C)
  statement: (f ≫ g).hom = g.hom.comp f.hom
  proof: rfl

中文:
引理 hom_comp
  条件: (f : A ⟶ B) (g : B ⟶ C)
  结论: (f ≫ g).hom = g.hom.comp f.hom
  证明: rfl
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  statement: (f ≫ g) a = g (f a)
  proof: by simp

中文:
引理 comp_apply
  条件: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  结论: (f ≫ g) a = g (f a)
  证明: by simp
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

variable {A B} in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : A ⟶ B} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {f g : A ⟶ B} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
/--
lemma `hom_comm_apply` / 引理 `hom_comm_apply`

English:
lemma hom_comm_apply
  given: (f : A ⟶ B) (g : G) (a : A)
  statement: f.hom (A.ρ g a) = B.ρ g (f.hom a)
  proof: by
  simpa using congr($(f.hom.2 g) a)

中文:
引理 hom_comm_apply
  条件: (f : A ⟶ B) (g : G) (a : A)
  结论: f.hom (A.ρ g a) = B.ρ g (f.hom a)
  证明: by
  simpa using congr($(f.hom.2 g) a)

Depends on / 依赖: f.hom
-/
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

variable {Z : Type w} [AddCommGroup Z] [Module k Z] {τ : Representation k G Z}

/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: (f : ρ.IntertwiningMap σ)
  statement: (ofHom f).hom = f
  proof: rfl

中文:
引理 hom_ofHom
  条件: (f : ρ.整数ertwining映射 σ)
  结论: (ofHom f).hom = f
  证明: rfl
-/
@[simp] lemma hom_ofHom (f : ρ.IntertwiningMap σ) : (ofHom f).hom = f := rfl
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: (f : A ⟶ B)
  statement: ofHom f.hom = f
  proof: rfl

中文:
引理 ofHom_hom
  条件: (f : A ⟶ B)
  结论: ofHom f.hom = f
  证明: rfl
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  statement: ofHom (.id σ) = 𝟙 (of σ)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  结论: ofHom (.id σ) = 𝟙 (of σ)
  证明: rfl

@[simp]
-/
@[simp] lemma ofHom_id : ofHom (.id σ) = 𝟙 (of σ) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  given: (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ)
  proof: rfl

中文:
引理 ofHom_comp
  条件: (f : ρ.整数ertwining映射 σ) (g : σ.整数ertwining映射 τ)
  证明: rfl
-/
lemma ofHom_comp (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
  ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: (f : ρ.IntertwiningMap σ) (x : X)
  statement: ofHom f x = f x
  proof: rfl

中文:
引理 ofHom_apply
  条件: (f : ρ.整数ertwining映射 σ) (x : X)
  结论: ofHom f x = f x
  证明: rfl
-/
lemma ofHom_apply (f : ρ.IntertwiningMap σ) (x : X) : ofHom f x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: (e : A ≅ B) (x : A)
  statement: e.inv.hom (e.hom.hom x) = x
  proof: by simp

中文:
引理 inv_hom_apply
  条件: (e : A ≅ B) (x : A)
  结论: e.inv.hom (e.hom.hom x) = x
  证明: by simp
-/
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: (e : A ≅ B) (x : B)
  statement: e.hom.hom (e.inv.hom x) = x
  proof: by simp

中文:
引理 hom_inv_apply
  条件: (e : A ≅ B) (x : B)
  结论: e.hom.hom (e.inv.hom x) = x
  证明: by simp
-/
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Rep.{u} k G)
  body: ⟨of (Representation.trivial k G PUnit)⟩

中文:
实例 :
  签名: 可居 (Rep.{u} k G)
  定义体: ⟨of (Representation.trivial k G PUnit)⟩

Depends on / 依赖: Representation, Representation.trivial
-/
instance : Inhabited (Rep.{u} k G) := ⟨of (Representation.trivial k G PUnit)⟩

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  statement: (forget (Rep.{w} k G)).obj A = A
  proof: rfl

中文:
引理 forget_obj
  结论: (forget (Rep.{w} k G)).obj A = A
  证明: rfl
-/
lemma forget_obj : (forget (Rep.{w} k G)).obj A = A := rfl

/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: (f : A ⟶ B)
  statement: (forget (Rep.{w} k G)).map f = (f : _ -> _)
  proof: rfl

中文:
引理 forget_map
  条件: (f : A ⟶ B)
  结论: (forget (Rep.{w} k G)).map f = (f : _ -> _)
  证明: rfl
-/
lemma forget_map (f : A ⟶ B) : (forget (Rep.{w} k G)).map f = (f : _ -> _) := rfl

/-- An equiv between the underlying representations induce isomorphism between objects in
  `Rep k G`. -/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: (e : ρ.Equiv σ)
  body: ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]

中文:
定义 mkIso
  签名: (e : ρ.等价 σ)
  定义体: ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]

Depends on / 依赖: e.toIntertwiningMap, toIntertwiningMap
-/
def mkIso (e : ρ.Equiv σ) : of ρ ≅ of σ where
  hom := ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]
/--
lemma `mkIso_hom_hom_apply` / 引理 `mkIso_hom_hom_apply`

English:
lemma mkIso_hom_hom_apply
  given: (e : ρ.Equiv σ) (x : X)
  proof: rfl

@[simp]

中文:
引理 mkIso_hom_hom_apply
  条件: (e : ρ.等价 σ) (x : X)
  证明: rfl

@[simp]
-/
lemma mkIso_hom_hom_apply (e : ρ.Equiv σ) (x : X) :
    (mkIso e).hom.hom x = e.toLinearMap x := rfl

@[simp]
/--
lemma `mkIso_hom_hom_toLinearMap` / 引理 `mkIso_hom_hom_toLinearMap`

English:
lemma mkIso_hom_hom_toLinearMap
  given: (e : ρ.Equiv σ)
  proof: rfl

@[simp]

中文:
引理 mkIso_hom_hom_toLinearMap
  条件: (e : ρ.等价 σ)
  证明: rfl

@[simp]
-/
lemma mkIso_hom_hom_toLinearMap (e : ρ.Equiv σ) :
    (mkIso e).hom.hom.toLinearMap = e.toLinearMap := rfl

@[simp]
/--
lemma `mkIso_inv_hom_toLinearMap` / 引理 `mkIso_inv_hom_toLinearMap`

English:
lemma mkIso_inv_hom_toLinearMap
  given: (e : ρ.Equiv σ)
  proof: rfl

@[simp]

中文:
引理 mkIso_inv_hom_toLinearMap
  条件: (e : ρ.等价 σ)
  证明: rfl

@[simp]
-/
lemma mkIso_inv_hom_toLinearMap (e : ρ.Equiv σ) :
    (mkIso e).inv.hom.toLinearMap = e.symm.toIntertwiningMap.toLinearMap := rfl

@[simp]
/--
lemma `mkIso_inv_hom_apply` / 引理 `mkIso_inv_hom_apply`

English:
lemma mkIso_inv_hom_apply
  given: (e : ρ.Equiv σ) (y : Y)
  proof: rfl

@[simp]

中文:
引理 mkIso_inv_hom_apply
  条件: (e : ρ.等价 σ) (y : Y)
  证明: rfl

@[simp]
-/
lemma mkIso_inv_hom_apply (e : ρ.Equiv σ) (y : Y) :
    (mkIso e).inv.hom y = e.symm y := rfl

@[simp]
/--
lemma `mkIso_hom_hom` / 引理 `mkIso_hom_hom`

English:
lemma mkIso_hom_hom
  given: (e : ρ.Equiv σ)
  proof: rfl

中文:
引理 mkIso_hom_hom
  条件: (e : ρ.等价 σ)
  证明: rfl
-/
lemma mkIso_hom_hom (e : ρ.Equiv σ) :
    (mkIso e).hom.hom = e.toIntertwiningMap := rfl

variable {A B C}

/-- The equivalence between representations induced from iso between objects in `Rep k G`. -/
@[simps]
/--
Definition of `_root_.Representation.equivOfIso` / `_root_.Representation.equivOfIso` 的定义

English:
definition _root_.Representation.equivOfIso
  signature: (i : A ≅ B)
  body: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

中文:
定义 _root_.Representation.equivOfIso
  签名: (i : A ≅ B)
  定义体: i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

Depends on / 依赖: i.hom.hom
-/
def _root_.Representation.equivOfIso (i : A ≅ B) : A.ρ.Equiv B.ρ where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/--
Instance `reflectsIsomorphisms_forget` / 实例 `reflectsIsomorphisms_forget`

English:
instance reflectsIsomorphisms_forget
  signature: : (forget (Rep.{w} k G)).ReflectsIsomorphisms where
  body: by
    let i := asIso ((forget (Rep.{w} k G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom

中文:
实例 reflectsIsomorphisms_forget
  签名: : (forget (Rep.{w} k G)).反映同构 where
  定义体: by
    let i := asIso ((forget (Rep.{w} k G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom

Depends on / 依赖: f.hom, forget, i.toEquiv, isIso_hom, toEquiv
-/
instance reflectsIsomorphisms_forget : (forget (Rep.{w} k G)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (Rep.{w} k G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom

/--
lemma `hom_bijective` / 引理 `hom_bijective`

English:
lemma hom_bijective
  proof: Rep.hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

中文:
引理 hom_bijective
  证明: Rep.hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

Depends on / 依赖: Rep.hom_ext, hom_ext
-/
lemma hom_bijective :
    Function.Bijective (Rep.Hom.hom : (A ⟶ B) -> (A.ρ.IntertwiningMap B.ρ)) where
  left _ _ h := Rep.hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

/--
lemma `hom_injective` / 引理 `hom_injective`

English:
lemma hom_injective
  proof: hom_bijective.injective

中文:
引理 hom_injective
  证明: hom_bijective.injective

Depends on / 依赖: hom_bijective, hom_bijective.injective, injective
-/
lemma hom_injective :
    Function.Injective (Hom.hom : (A ⟶ B) -> (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.injective

/--
lemma `hom_surjective` / 引理 `hom_surjective`

English:
lemma hom_surjective
  proof: hom_bijective.surjective

中文:
引理 hom_surjective
  证明: hom_bijective.surjective

Depends on / 依赖: hom_bijective, hom_bijective.surjective, surjective
-/
lemma hom_surjective :
    Function.Surjective (Hom.hom : (A ⟶ B) -> (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.surjective

/-- The morphisms between two objects in `Rep k G` has an equivalence to the intertwining maps
  between their underlying representations. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (A ⟶ B) ≃ (A.ρ.IntertwiningMap B.ρ) where
  body: Hom.hom
  invFun := ofHom

中文:
定义 homEquiv
  签名: : (A ⟶ B) ≃ (A.ρ.整数ertwining映射 B.ρ) where
  定义体: Hom.hom
  invFun := ofHom

Depends on / 依赖: Hom.hom
-/
def homEquiv : (A ⟶ B) ≃ (A.ρ.IntertwiningMap B.ρ) where
  toFun := Hom.hom
  invFun := ofHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (A ⟶ B)
  body: ofHom (f.hom + g.hom)

中文:
实例 :
  签名: 加法 (A ⟶ B)
  定义体: ofHom (f.hom + g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Add (A ⟶ B) where add f g := ofHom (f.hom + g.hom)

/--
lemma `ofHom_add` / 引理 `ofHom_add`

English:
lemma ofHom_add
  given: (f g : ρ.IntertwiningMap σ)
  proof: rfl

中文:
引理 ofHom_add
  条件: (f g : ρ.整数ertwining映射 σ)
  证明: rfl
-/
lemma ofHom_add (f g : ρ.IntertwiningMap σ) :
    ofHom (f + g) = ofHom f + ofHom g := rfl

/--
lemma `add_hom` / 引理 `add_hom`

English:
lemma add_hom
  given: (f g : A ⟶ B)
  statement: (f + g).hom = f.hom + g.hom
  proof: rfl

中文:
引理 add_hom
  条件: (f g : A ⟶ B)
  结论: (f + g).hom = f.hom + g.hom
  证明: rfl
-/
lemma add_hom (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl

/--
lemma `hom_comp_toLinearMap` / 引理 `hom_comp_toLinearMap`

English:
lemma hom_comp_toLinearMap
  given: (f : A ⟶ B) (g : B ⟶ C)
  proof: rfl

中文:
引理 hom_comp_toLinearMap
  条件: (f : A ⟶ B) (g : B ⟶ C)
  证明: rfl
-/
lemma hom_comp_toLinearMap (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl

/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  given: (f₁ f₂ : A ⟶ B) (g : B ⟶ C)
  proof: by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

中文:
引理 add_comp
  条件: (f₁ f₂ : A ⟶ B) (g : B ⟶ C)
  证明: by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.add_comp, add_comp, add_hom
-/
lemma add_comp (f₁ f₂ : A ⟶ B) (g : B ⟶ C) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]

/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  given: (f : A ⟶ B) (g₁ g₂ : B ⟶ C)
  proof: by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

中文:
引理 comp_add
  条件: (f : A ⟶ B) (g₁ g₂ : B ⟶ C)
  证明: by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.comp_add, add_hom, comp_add
-/
lemma comp_add (f : A ⟶ B) (g₁ g₂ : B ⟶ C) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (A ⟶ B)
  body: ofHom (0 : A.ρ.IntertwiningMap B.ρ)

@[simp]

中文:
实例 :
  签名: 零 (A ⟶ B)
  定义体: ofHom (0 : A.ρ.IntertwiningMap B.ρ)

@[simp]

Depends on / 依赖: IntertwiningMap
-/
instance : Zero (A ⟶ B) where
  zero := ofHom (0 : A.ρ.IntertwiningMap B.ρ)

@[simp]
/--
lemma `ofHom_zero` / 引理 `ofHom_zero`

English:
lemma ofHom_zero
  statement: ofHom (0 : ρ.IntertwiningMap σ) = 0
  proof: rfl

@[simp]

中文:
引理 ofHom_zero
  结论: ofHom (0 : ρ.整数ertwining映射 σ) = 0
  证明: rfl

@[simp]
-/
lemma ofHom_zero : ofHom (0 : ρ.IntertwiningMap σ) = 0 := rfl

@[simp]
/--
lemma `zero_hom` / 引理 `zero_hom`

English:
lemma zero_hom
  statement: (0 : A ⟶ B).hom = 0
  proof: rfl

中文:
引理 zero_hom
  结论: (0 : A ⟶ B).hom = 0
  证明: rfl
-/
lemma zero_hom : (0 : A ⟶ B).hom = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (A ⟶ B)
  body: ofHom (n • f.hom)

中文:
实例 :
  签名: 标量乘法 自然数 (A ⟶ B)
  定义体: ofHom (n • f.hom)

Depends on / 依赖: f.hom
-/
instance : SMul Nat (A ⟶ B) where smul n f := ofHom (n • f.hom)

/--
lemma `ofHom_nsmul` / 引理 `ofHom_nsmul`

English:
lemma ofHom_nsmul
  given: (f : ρ.IntertwiningMap σ) (n : Nat)
  proof: rfl

中文:
引理 ofHom_nsmul
  条件: (f : ρ.整数ertwining映射 σ) (n : 自然数)
  证明: rfl
-/
lemma ofHom_nsmul (f : ρ.IntertwiningMap σ) (n : Nat) :
    ofHom (n • f) = n • ofHom f := rfl

/--
lemma `nsmul_hom` / 引理 `nsmul_hom`

English:
lemma nsmul_hom
  given: (f : A ⟶ B) (n : Nat)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 nsmul_hom
  条件: (f : A ⟶ B) (n : 自然数)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
lemma nsmul_hom (f : A ⟶ B) (n : Nat) : (n • f).hom = n • f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (A ⟶ B)
  body: ofHom (-f.hom)

中文:
实例 :
  签名: 取负 (A ⟶ B)
  定义体: ofHom (-f.hom)

Depends on / 依赖: f.hom
-/
instance : Neg (A ⟶ B) where neg f := ofHom (-f.hom)

/--
lemma `ofHom_neg` / 引理 `ofHom_neg`

English:
lemma ofHom_neg
  given: (f : ρ.IntertwiningMap σ)
  statement: ofHom (-f) = -ofHom f
  proof: rfl

中文:
引理 ofHom_neg
  条件: (f : ρ.整数ertwining映射 σ)
  结论: ofHom (-f) = -ofHom f
  证明: rfl
-/
lemma ofHom_neg (f : ρ.IntertwiningMap σ) : ofHom (-f) = -ofHom f := rfl

/--
lemma `neg_hom` / 引理 `neg_hom`

English:
lemma neg_hom
  given: (f : A ⟶ B)
  statement: (-f).hom = -f.hom
  proof: rfl

中文:
引理 neg_hom
  条件: (f : A ⟶ B)
  结论: (-f).hom = -f.hom
  证明: rfl
-/
lemma neg_hom (f : A ⟶ B) : (-f).hom = -f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (A ⟶ B)
  body: ofHom (f.hom - g.hom)

中文:
实例 :
  签名: 减法 (A ⟶ B)
  定义体: ofHom (f.hom - g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Sub (A ⟶ B) where sub f g := ofHom (f.hom - g.hom)

/--
lemma `ofHom_sub` / 引理 `ofHom_sub`

English:
lemma ofHom_sub
  given: (f g : ρ.IntertwiningMap σ)
  statement: ofHom (f - g) = ofHom f - ofHom g
  proof: rfl

中文:
引理 ofHom_sub
  条件: (f g : ρ.整数ertwining映射 σ)
  结论: ofHom (f - g) = ofHom f - ofHom g
  证明: rfl
-/
lemma ofHom_sub (f g : ρ.IntertwiningMap σ) : ofHom (f - g) = ofHom f - ofHom g := rfl

/--
lemma `sub_hom` / 引理 `sub_hom`

English:
lemma sub_hom
  given: (f g : A ⟶ B)
  statement: (f - g).hom = f.hom - g.hom
  proof: rfl

中文:
引理 sub_hom
  条件: (f g : A ⟶ B)
  结论: (f - g).hom = f.hom - g.hom
  证明: rfl
-/
lemma sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (A ⟶ B)
  body: ofHom (n • f.hom)

中文:
实例 :
  签名: 标量乘法 整数 (A ⟶ B)
  定义体: ofHom (n • f.hom)

Depends on / 依赖: f.hom
-/
instance : SMul Int (A ⟶ B) where smul n f := ofHom (n • f.hom)

/--
lemma `ofHom_zsmul` / 引理 `ofHom_zsmul`

English:
lemma ofHom_zsmul
  given: (f : ρ.IntertwiningMap σ) (n : Int)
  statement: ofHom (n • f) = n • ofHom f
  proof: rfl

中文:
引理 ofHom_zsmul
  条件: (f : ρ.整数ertwining映射 σ) (n : 整数)
  结论: ofHom (n • f) = n • ofHom f
  证明: rfl
-/
lemma ofHom_zsmul (f : ρ.IntertwiningMap σ) (n : Int) : ofHom (n • f) = n • ofHom f := rfl

/--
lemma `zsmul_hom` / 引理 `zsmul_hom`

English:
lemma zsmul_hom
  given: (f : A ⟶ B) (n : Int)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 zsmul_hom
  条件: (f : A ⟶ B) (n : 整数)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
lemma zsmul_hom (f : A ⟶ B) (n : Int) : (n • f).hom = n • f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (A ⟶ B)
  body: fast_instance% hom_injective.addCommGroup
    Rep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom

中文:
实例 :
  签名: 加法交换群 (A ⟶ B)
  定义体: fast_instance% hom_injective.addCommGroup
    Rep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom

Depends on / 依赖: addCommGroup, fast_instance, hom_injective, hom_injective.addCommGroup
-/
instance : AddCommGroup (A ⟶ B) := fast_instance% hom_injective.addCommGroup
    Rep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Rep.{w} k G)
  body: add_comp
  comp_add _ _ _ := comp_add

中文:
实例 :
  签名: 预加性 (Rep.{w} k G)
  定义体: add_comp
  comp_add _ _ _ := comp_add

Depends on / 依赖: add_comp
-/
instance : Preadditive (Rep.{w} k G) where
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add

/--
lemma `sum_hom` / 引理 `sum_hom`

English:
lemma sum_hom
  given: {ι : Type u'} (f : ι -> (A ⟶ B)) (s : Finset ι)
  proof: by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

中文:
引理 sum_hom
  条件: {ι : 类型u'} (f : ι -> (A ⟶ B)) (s : 有限集 ι)
  证明: by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, add_hom, classical, insert, sum_insert
-/
lemma sum_hom {ι : Type u'} (f : ι -> (A ⟶ B)) (s : Finset ι) :
    (∑ i in s, f i).hom = ∑ i in s, (f i).hom := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]

/--
lemma `ofHom_sum` / 引理 `ofHom_sum`

English:
lemma ofHom_sum
  statement: {ι : Type u'} {M N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module k M]
  proof: by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ofHom_add, h]

中文:
引理 ofHom_sum
  结论: {ι : 类型u'} {M N : 类型v'} [加法交换群 M] [加法交换群 N] [模 k M]
  证明: by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ofHom_add, h]

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, classical, insert, ofHom_add, sum_insert
-/
lemma ofHom_sum {ι : Type u'} {M N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module k M]
    [Module k N] {σ : Representation k G M} {ρ : Representation k G N} (f : ι -> σ.IntertwiningMap ρ)
    (s : Finset ι) :
    ofHom (∑ i in s, f i) = ∑ i in s, ofHom (f i) := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ofHom_add, h]

variable (k G) in
/--
Definition of `trivial` / `trivial` 的定义

English:
abbreviation trivial
  signature: (V : Type w) [AddCommGroup V] [Module k V]
  body: Rep.of (Representation.trivial k G V)

中文:
缩写 trivial
  签名: (V : 类型 w) [加法交换群 V] [模 k V]
  定义体: Rep.of (Representation.trivial k G V)

Depends on / 依赖: Rep.of, Representation, Representation.trivial
-/
abbrev trivial (V : Type w) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (Representation.trivial k G V)

/--
lemma `trivial_V` / 引理 `trivial_V`

English:
lemma trivial_V
  given: {V : Type w} [AddCommGroup V] [Module k V]
  statement: (trivial k G V).V = V
  proof: rfl

中文:
引理 trivial_V
  条件: {V : 类型 w} [加法交换群 V] [模 k V]
  结论: (trivial k G V).V = V
  证明: rfl
-/
lemma trivial_V {V : Type w} [AddCommGroup V] [Module k V] : (trivial k G V).V = V := rfl

/--
lemma `trivial_ρ` / 引理 `trivial_ρ`

English:
lemma trivial_ρ
  given: {V : Type w} [AddCommGroup V] [Module k V] (g : G)
  proof: rfl

@[simp]

中文:
引理 trivial_ρ
  条件: {V : 类型 w} [加法交换群 V] [模 k V] (g : G)
  证明: rfl

@[simp]
-/
lemma trivial_ρ {V : Type w} [AddCommGroup V] [Module k V] (g : G) :
    (trivial k G V).ρ g = LinearMap.id := rfl

@[simp]
/--
lemma `trivial_ρ_apply` / 引理 `trivial_ρ_apply`

English:
lemma trivial_ρ_apply
  given: {V : Type w} [AddCommGroup V] [Module k V] (g : G) (v : V)
  proof: rfl

中文:
引理 trivial_ρ_apply
  条件: {V : 类型 w} [加法交换群 V] [模 k V] (g : G) (v : V)
  证明: rfl
-/
lemma trivial_ρ_apply {V : Type w} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v := rfl

/--
lemma `ρ_mul` / 引理 `ρ_mul`

English:
lemma ρ_mul
  given: (g1 g2 : G)
  statement: A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2
  proof: by ext; simp

中文:
引理 ρ_mul
  条件: (g1 g2 : G)
  结论: A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2
  证明: by ext; simp
-/
lemma ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2 := by ext; simp

section Commutative

variable {G : Type v} [CommMonoid G]
variable (A : Rep k G)

/--
Definition of `applyAsHom` / `applyAsHom` 的定义

English:
definition applyAsHom
  signature: (g : G)
  body: Rep.ofHom ⟨A.ρ g, by simp [← ρ_mul, mul_comm]⟩

@[simp]

中文:
定义 applyAsHom
  签名: (g : G)
  定义体: Rep.ofHom ⟨A.ρ g, by simp [← ρ_mul, mul_comm]⟩

@[simp]

Depends on / 依赖: Rep.ofHom, mul_comm
-/
def applyAsHom (g : G) : A ⟶ A := Rep.ofHom ⟨A.ρ g, by simp [← ρ_mul, mul_comm]⟩

@[simp]
/--
lemma `applyAsHom_apply` / 引理 `applyAsHom_apply`

English:
lemma applyAsHom_apply
  given: {A : Rep k G} (g : G) (x : A)
  statement: (A.applyAsHom g).hom x = A.ρ g x
  proof: rfl

@[reassoc, elementwise]

中文:
引理 applyAsHom_apply
  条件: {A : Rep k G} (g : G) (x : A)
  结论: (A.applyAsHom g).hom x = A.ρ g x
  证明: rfl

@[reassoc, elementwise]
-/
lemma applyAsHom_apply {A : Rep k G} (g : G) (x : A) : (A.applyAsHom g).hom x = A.ρ g x := rfl

@[reassoc, elementwise]
/--
lemma `applyAsHom_comm` / 引理 `applyAsHom_comm`

English:
lemma applyAsHom_comm
  given: {A B : Rep k G} (f : A ⟶ B) (g : G)
  proof: by
  ext; simp [hom_comm_apply]

中文:
引理 applyAsHom_comm
  条件: {A B : Rep k G} (f : A ⟶ B) (g : G)
  证明: by
  ext; simp [hom_comm_apply]

Depends on / 依赖: hom_comm_apply
-/
lemma applyAsHom_comm {A B : Rep k G} (f : A ⟶ B) (g : G) :
    A.applyAsHom g ≫ f = f ≫ B.applyAsHom g := by
  ext; simp [hom_comm_apply]

end Commutative

end semiring

section ring

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section setup

variable (k G)

/--
Definition of `ofMulAction` / `ofMulAction` 的定义

English:
abbreviation ofMulAction
  signature: (H : Type w') [MulAction G H]
  body: of Representation.ofMulAction k G H

中文:
缩写 ofMulAction
  签名: (H : 类型 w') [乘法作用 G H]
  定义体: of Representation.ofMulAction k G H

Depends on / 依赖: Representation, Representation.ofMulAction, ofMulAction
-/
abbrev ofMulAction (H : Type w') [MulAction G H] : Rep k G :=
of Representation.ofMulAction k G H

/--
Definition of `leftRegular` / `leftRegular` 的定义

English:
abbreviation leftRegular
  signature: : Rep k G
  body: ofMulAction k G G

中文:
缩写 leftRegular
  签名: : Rep k G
  定义体: ofMulAction k G G

Depends on / 依赖: ofMulAction
-/
abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/--
Definition of `diagonal` / `diagonal` 的定义

English:
abbreviation diagonal
  signature: (n : Nat)
  body: ofMulAction k G (Fin n -> G)

中文:
缩写 diagonal
  签名: (n : 自然数)
  定义体: ofMulAction k G (Fin n -> G)

Depends on / 依赖: ofMulAction
-/
abbrev diagonal (n : Nat) : Rep k G :=
  ofMulAction k G (Fin n -> G)

/--
Definition of `diagonalOneIsoLeftRegular` / `diagonalOneIsoLeftRegular` 的定义

English:
abbreviation diagonalOneIsoLeftRegular
  signature: :
  body: Rep.mkIso (Representation.diagonalOneEquivLeftRegular k G)

中文:
缩写 diagonalOneIsoLeftRegular
  签名: :
  定义体: Rep.mkIso (Representation.diagonalOneEquivLeftRegular k G)

Depends on / 依赖: Rep.mkIso, Representation, Representation.diagonalOneEquivLeftRegular, diagonalOneEquivLeftRegular
-/
abbrev diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G := Rep.mkIso (Representation.diagonalOneEquivLeftRegular k G)

/--
Definition of `ofMulActionSubsingletonIsoTrivial` / `ofMulActionSubsingletonIsoTrivial` 的定义

English:
abbreviation ofMulActionSubsingletonIsoTrivial
  body: mkIso Representation.ofMulActionSubsingletonEquivTrivial k G H

中文:
缩写 ofMulActionSubsingletonIsoTrivial
  定义体: mkIso Representation.ofMulActionSubsingletonEquivTrivial k G H

Depends on / 依赖: Representation, Representation.ofMulActionSubsingletonEquivTrivial, ofMulActionSubsingletonEquivTrivial
-/
abbrev ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
mkIso Representation.ofMulActionSubsingletonEquivTrivial k G H

section

variable (A : Type w') [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]

/--
Definition of `ofDistribMulAction` / `ofDistribMulAction` 的定义

English:
definition ofDistribMulAction
  signature: : Rep k G
  body: Rep.of (Representation.ofDistribMulAction k G A)

中文:
定义 ofDistribMulAction
  签名: : Rep k G
  定义体: Rep.of (Representation.ofDistribMulAction k G A)

Depends on / 依赖: Rep.of, Representation, Representation.ofDistribMulAction, ofDistribMulAction
-/
def ofDistribMulAction : Rep k G := Rep.of (Representation.ofDistribMulAction k G A)

/--
theorem `ofDistribMulAction_ρ_apply_apply` / 定理 `ofDistribMulAction_ρ_apply_apply`

English:
theorem ofDistribMulAction_ρ_apply_apply
  given: (g : G) (a : A)
  proof: rfl

中文:
定理 ofDistribMulAction_ρ_apply_apply
  条件: (g : G) (a : A)
  证明: rfl
-/
@[simp] theorem ofDistribMulAction_ρ_apply_apply (g : G) (a : A) :
    (ofDistribMulAction k G A).ρ g a = g • a := rfl

/--
Definition of `ofAlgebraAut` / `ofAlgebraAut` 的定义

English:
definition ofAlgebraAut
  signature: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  body: ofDistribMulAction Int (S ≃ₐ[R] S) S

中文:
定义 ofAlgebraAut
  签名: (R S : 类型) [交换环 R] [交换环 S] [代数 R S]
  定义体: ofDistribMulAction Int (S ≃ₐ[R] S) S
-/
@[simp] def ofAlgebraAut (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep Int (S ≃ₐ[R] S) := ofDistribMulAction Int (S ≃ₐ[R] S) S

end

section
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/--
Definition of `ofMulDistribMulAction` / `ofMulDistribMulAction` 的定义

English:
definition ofMulDistribMulAction
  signature: : Rep Int M
  body: Rep.of (Representation.ofMulDistribMulAction M G)

中文:
定义 ofMulDistribMulAction
  签名: : Rep 整数 M
  定义体: Rep.of (Representation.ofMulDistribMulAction M G)

Depends on / 依赖: Rep.of, Representation, Representation.ofMulDistribMulAction, ofMulDistribMulAction
-/
def ofMulDistribMulAction : Rep Int M := Rep.of (Representation.ofMulDistribMulAction M G)

variable {G M}

/-- Unfolds `ofMulDistribMulAction`; useful to keep track of additivity. -/
@[simps!]
/--
Definition of `toAdditive` / `toAdditive` 的定义

English:
definition toAdditive
  signature: : ofMulDistribMulAction M G ≃+ Additive G
  body: AddEquiv.refl _

中文:
定义 toAdditive
  签名: : ofMulDistribMulAction M G ≃+ 加性 G
  定义体: AddEquiv.refl _

Depends on / 依赖: AddEquiv, AddEquiv.refl
-/
def toAdditive : ofMulDistribMulAction M G ≃+ Additive G := AddEquiv.refl _

/--
theorem `ofMulDistribMulAction_ρ_apply_apply` / 定理 `ofMulDistribMulAction_ρ_apply_apply`

English:
theorem ofMulDistribMulAction_ρ_apply_apply
  given: (g : M) (a : Additive G)
  proof: rfl

中文:
定理 ofMulDistribMulAction_ρ_apply_apply
  条件: (g : M) (a : 加性 G)
  证明: rfl
-/
@[simp] theorem ofMulDistribMulAction_ρ_apply_apply (g : M) (a : Additive G) :
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • a.toMul) := rfl

/--
Definition of `ofAlgebraAutOnUnits` / `ofAlgebraAutOnUnits` 的定义

English:
definition ofAlgebraAutOnUnits
  signature: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  body: Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

中文:
定义 ofAlgebraAutOnUnits
  签名: (R S : 类型) [交换环 R] [交换环 S] [代数 R S]
  定义体: Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ
-/
@[simp] def ofAlgebraAutOnUnits (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep Int (S ≃ₐ[R] S) := Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

end

variable {k G}

/--
Definition of `leftRegularHom` / `leftRegularHom` 的定义

English:
abbreviation leftRegularHom
  signature: (A : Rep k G) (x : A)
  body: Rep.ofHom ⟨Finsupp.lift A k G (fun g => A.ρ g x) ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g => by ext; simp⟩

中文:
缩写 leftRegularHom
  签名: (A : Rep k G) (x : A)
  定义体: Rep.ofHom ⟨Finsupp.lift A k G (fun g => A.ρ g x) ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g => by ext; simp⟩

Depends on / 依赖: Finsupp, Finsupp.lift, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, Rep.ofHom, coeffLinearEquiv, toLinearMap
-/
abbrev leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A :=
  Rep.ofHom ⟨Finsupp.lift A k G (fun g => A.ρ g x) ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g => by ext; simp⟩

/--
theorem `leftRegularHom_hom_single` / 定理 `leftRegularHom_hom_single`

English:
theorem leftRegularHom_hom_single
  given: {A : Rep k G} (g : G) (x : A) (r : k)
  proof: by
  simp [leftRegularHom]

中文:
定理 leftRegularHom_hom_single
  条件: {A : Rep k G} (g : G) (x : A) (r : k)
  证明: by
  simp [leftRegularHom]

Depends on / 依赖: leftRegularHom
-/
theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (.single g r) = r • A.ρ g x := by
  simp [leftRegularHom]

variable (A : Rep k G)

/--
Definition of `subrepresentation` / `subrepresentation` 的定义

English:
abbreviation subrepresentation
  signature: (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g))
  body: Rep.of (A.ρ.subrepresentation W le_comap)

中文:
缩写 subrepresentation
  签名: (W : 子模 k A) (le_comap : 对任意 g, W <= W.comap (A.ρ g))
  定义体: Rep.of (A.ρ.subrepresentation W le_comap)

Depends on / 依赖: Rep.of, le_comap, subrepresentation
-/
abbrev subrepresentation (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps!]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g))
  body: Rep.ofHom ⟨W.subtype, fun _ => rfl⟩

中文:
定义 subtype
  签名: (W : 子模 k A) (le_comap : 对任意 g, W <= W.comap (A.ρ g))
  定义体: Rep.ofHom ⟨W.subtype, fun _ => rfl⟩

Depends on / 依赖: Rep.ofHom, W.subtype, subtype
-/
def subtype (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A := Rep.ofHom ⟨W.subtype, fun _ => rfl⟩

/--
Definition of `quotient` / `quotient` 的定义

English:
abbreviation quotient
  signature: (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g))
  body: Rep.of (A.ρ.quotient W le_comap)

中文:
缩写 quotient
  签名: (W : 子模 k A) (le_comap : 对任意 g, W <= W.comap (A.ρ g))
  定义体: Rep.of (A.ρ.quotient W le_comap)

Depends on / 依赖: Rep.of, le_comap, quotient
-/
abbrev quotient (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps!]
/--
Definition of `mkQ` / `mkQ` 的定义

English:
definition mkQ
  signature: (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g))
  body: Rep.ofHom ⟨W.mkQ, fun _ => rfl⟩

中文:
定义 mkQ
  签名: (W : 子模 k A) (le_comap : 对任意 g, W <= W.comap (A.ρ g))
  定义体: Rep.ofHom ⟨W.mkQ, fun _ => rfl⟩

Depends on / 依赖: Rep.ofHom, W.mkQ
-/
def mkQ (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap := Rep.ofHom ⟨W.mkQ, fun _ => rfl⟩

end setup

variable (k G) in
/-- The functor equipping a module with the trivial representation. -/
@[implicit_reducible, simps! obj_V map_hom]
/--
Definition of `trivialFunctor` / `trivialFunctor` 的定义

English:
definition trivialFunctor
  signature: : ModuleCat.{w} k ⥤ Rep.{w} k G where
  body: trivial k G V
  map f := ofHom ⟨f.hom, fun _ => rfl⟩

中文:
定义 trivialFunctor
  签名: : 模范畴.{w} k ⥤ Rep.{w} k G where
  定义体: trivial k G V
  map f := ofHom ⟨f.hom, fun _ => rfl⟩
-/
def trivialFunctor : ModuleCat.{w} k ⥤ Rep.{w} k G where
  obj V := trivial k G V
  map f := ofHom ⟨f.hom, fun _ => rfl⟩

/--
Definition of `IsTrivial` / `IsTrivial` 的定义

English:
abbreviation IsTrivial
  signature: (A : Rep k G)
  body: A.ρ.IsTrivial

中文:
缩写 是平凡
  签名: (A : Rep k G)
  定义体: A.ρ.IsTrivial

Depends on / 依赖: IsTrivial
-/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial

instance (X : ModuleCat k) : ((trivialFunctor k G).obj X).IsTrivial where

instance {V : Type w} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where

instance {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where
  out := Representation.isTrivial_def ρ

instance {H : Type u'} {V : Type w} [Group H] [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (f : G ->* H) [Representation.IsTrivial (ρ.comp f)] :
    Representation.IsTrivial ((Rep.of ρ).ρ.comp f) := ‹_›

variable {A B C : Rep.{w} k G}

/--
Instance `hasForgetToModuleCat` / 实例 `hasForgetToModuleCat`

English:
instance hasForgetToModuleCat
  signature: :
  body: .of k A
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

中文:
实例 hasForgetToModuleCat
  签名: :
  定义体: .of k A
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap
-/
instance hasForgetToModuleCat :
    HasForget₂ (Rep.{w} k G) (ModuleCat.{w} k) where
  forget₂.obj A := .of k A
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

/--
Definition of `Hom.toModuleCatHom` / `Hom.toModuleCatHom` 的定义

English:
abbreviation Hom.toModuleCatHom
  signature: (f : A ⟶ B)
  body: ModuleCat.ofHom f.hom.toLinearMap

中文:
缩写 态射.toModuleCatHom
  签名: (f : A ⟶ B)
  定义体: ModuleCat.ofHom f.hom.toLinearMap

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, f.hom.toLinearMap, toLinearMap
-/
abbrev Hom.toModuleCatHom (f : A ⟶ B) : ModuleCat.of k A.V ⟶ ModuleCat.of k B.V :=
  ModuleCat.ofHom f.hom.toLinearMap

/--
lemma `forget₂_moduleCat_obj` / 引理 `forget₂_moduleCat_obj`

English:
lemma forget₂_moduleCat_obj
  given: (A : Rep.{w} k G)
  proof: rfl

中文:
引理 forget₂_moduleCat_obj
  条件: (A : Rep.{w} k G)
  证明: rfl
-/
@[simp] lemma forget₂_moduleCat_obj (A : Rep.{w} k G) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).obj A = .of k A := rfl

/--
lemma `forget₂_moduleCat_map` / 引理 `forget₂_moduleCat_map`

English:
lemma forget₂_moduleCat_map
  given: (f : A ⟶ B)
  proof: rfl

中文:
引理 forget₂_moduleCat_map
  条件: (f : A ⟶ B)
  证明: rfl
-/
@[simp] lemma forget₂_moduleCat_map (f : A ⟶ B) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Faithful
  body: inferInstance

中文:
实例 :
  签名: (forget₂ (Rep.{w} k G) (模范畴.{w} k)).忠实
  定义体: inferInstance
-/
instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Faithful := inferInstance

section Action

variable (k G)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every object in `Rep k G` naturally correspond to an object in `Action`. -/
@[simps]
/--
Definition of `RepToAction` / `RepToAction` 的定义

English:
definition RepToAction
  signature: : Rep.{w} k G ⥤ Action (ModuleCat.{w} k) G where
  body: ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
map f := ⟨f.toModuleCatHom, fun g => ModuleCat.hom_ext by
    simp [ModuleCat.endRingEquiv, f.hom.2]⟩

中文:
定义 RepToAction
  签名: : Rep.{w} k G ⥤ 作用 (模范畴.{w} k) G where
  定义体: ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
map f := ⟨f.toModuleCatHom, fun g => ModuleCat.hom_ext by
    simp [ModuleCat.endRingEquiv, f.hom.2]⟩

Depends on / 依赖: ModuleCat, ModuleCat.endRingEquiv, endRingEquiv, symm.toMonoidHom.comp, toMonoidHom
-/
def RepToAction : Rep.{w} k G ⥤ Action (ModuleCat.{w} k) G where
  obj X := ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
map f := ⟨f.toModuleCatHom, fun g => ModuleCat.hom_ext by
    simp [ModuleCat.endRingEquiv, f.hom.2]⟩

/--
lemma `RepToAction_obj` / 引理 `RepToAction_obj`

English:
lemma RepToAction_obj
  given: (X : Rep.{w} k G)
  statement: (RepToAction k G).obj X =
  proof: rfl

中文:
引理 RepToAction_obj
  条件: (X : Rep.{w} k G)
  结论: (RepToAction k G).obj X =
  证明: rfl
-/
lemma RepToAction_obj (X : Rep.{w} k G) : (RepToAction k G).obj X =
  ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩ := rfl

/-- Every object in `ModuleCat k` that `G` acts on is an object in `Rep k G`. -/
@[simps]
/--
Definition of `ActionToRep` / `ActionToRep` 的定义

English:
definition ActionToRep
  signature: : Action (ModuleCat.{w} k) G ⥤ Rep.{w} k G where
  body: of (ModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map f := ofHom ⟨f.hom.hom, fun g => by simpa using ModuleCat.hom_ext_iff.1 (f.comm g)⟩

中文:
定义 ActionToRep
  签名: : 作用 (模范畴.{w} k) G ⥤ Rep.{w} k G where
  定义体: of (ModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map f := ofHom ⟨f.hom.hom, fun g => by simpa using ModuleCat.hom_ext_iff.1 (f.comm g)⟩

Depends on / 依赖: ModuleCat, ModuleCat.endRingEquiv, endRingEquiv, toMonoidHom, toMonoidHom.comp
-/
def ActionToRep : Action (ModuleCat.{w} k) G ⥤ Rep.{w} k G where
obj X := of (ModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map f := ofHom ⟨f.hom.hom, fun g => by simpa using ModuleCat.hom_ext_iff.1 (f.comm g)⟩

/--
Definition of `RepToAction_ActionToRep` / `RepToAction_ActionToRep` 的定义

English:
definition RepToAction_ActionToRep
  signature: (A : Action (ModuleCat.{w} k) G)
  body: ⟨𝟙 _, fun g => by rfl⟩
  inv := ⟨𝟙 _, fun g => by rfl⟩

中文:
定义 RepToAction_ActionToRep
  签名: (A : 作用 (模范畴.{w} k) G)
  定义体: ⟨𝟙 _, fun g => by rfl⟩
  inv := ⟨𝟙 _, fun g => by rfl⟩
-/
def RepToAction_ActionToRep (A : Action (ModuleCat.{w} k) G) :
    (RepToAction k G).obj ((ActionToRep k G).obj A) ≅ A where
  hom := ⟨𝟙 _, fun g => by rfl⟩
  inv := ⟨𝟙 _, fun g => by rfl⟩

/--
Definition of `ActionToRep_RepToAction` / `ActionToRep_RepToAction` 的定义

English:
definition ActionToRep_RepToAction
  signature: (X : Rep.{w} k G)
  body: ofHom ⟨LinearMap.id, fun g => show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩
  inv := ofHom ⟨LinearMap.id, fun g => show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩

中文:
定义 ActionToRep_RepToAction
  签名: (X : Rep.{w} k G)
  定义体: ofHom ⟨LinearMap.id, fun g => show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩
  inv := ofHom ⟨LinearMap.id, fun g => show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩

Depends on / 依赖: LinearMap, LinearMap.id
-/
def ActionToRep_RepToAction (X : Rep.{w} k G) :
    (ActionToRep k G).obj ((RepToAction k G).obj X) ≅ X where
  hom := ofHom ⟨LinearMap.id, fun g => show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩
  inv := ofHom ⟨LinearMap.id, fun g => show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩

/--
Definition of `repIsoAction` / `repIsoAction` 的定义

English:
definition repIsoAction
  signature: : Rep.{w} k G ≌ Action (ModuleCat.{w} k) G where
  body: RepToAction k G
  inverse := ActionToRep k G
  unitIso := NatIso.ofComponents (ActionToRep_RepToAction k G)
  counitIso := NatIso.ofComponents (RepToAction_ActionToRep k G)

中文:
定义 repIsoAction
  签名: : Rep.{w} k G ≌ 作用 (模范畴.{w} k) G where
  定义体: RepToAction k G
  inverse := ActionToRep k G
  unitIso := NatIso.ofComponents (ActionToRep_RepToAction k G)
  counitIso := NatIso.ofComponents (RepToAction_ActionToRep k G)

Depends on / 依赖: RepToAction
-/
def repIsoAction : Rep.{w} k G ≌ Action (ModuleCat.{w} k) G where
  functor := RepToAction k G
  inverse := ActionToRep k G
  unitIso := NatIso.ofComponents (ActionToRep_RepToAction k G)
  counitIso := NatIso.ofComponents (RepToAction_ActionToRep k G)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (RepToAction k G).IsEquivalence
  body: .isEquivalence_functor repIsoAction k G

中文:
实例 :
  签名: (RepToAction k G).是等价
  定义体: .isEquivalence_functor repIsoAction k G

Depends on / 依赖: isEquivalence_functor, repIsoAction
-/
instance : (RepToAction k G).IsEquivalence :=
.isEquivalence_functor repIsoAction k G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ActionToRep k G).IsEquivalence
  body: .isEquivalence_inverse repIsoAction k G

中文:
实例 :
  签名: (ActionToRep k G).是等价
  定义体: .isEquivalence_inverse repIsoAction k G

Depends on / 依赖: isEquivalence_inverse, repIsoAction
-/
instance : (ActionToRep k G).IsEquivalence :=
.isEquivalence_inverse repIsoAction k G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Additive
  body: by ext1; simp [add_hom]

中文:
实例 :
  签名: (forget₂ (Rep.{w} k G) (模范畴.{w} k)).加性
  定义体: by ext1; simp [add_hom]

Depends on / 依赖: add_hom
-/
instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Additive where
  map_add {X Y} f g := by ext1; simp [add_hom]

/--
Definition of `forgetNatIsoActionForget` / `forgetNatIsoActionForget` 的定义

English:
abbreviation forgetNatIsoActionForget
  signature: : forget₂ (Rep.{w} k G) (ModuleCat k) ≅ (RepToAction k G) ⋙
  body: .refl _

中文:
缩写 forget自然数IsoActionForget
  签名: : forget₂ (Rep.{w} k G) (模范畴 k) ≅ (RepToAction k G) ⋙
  定义体: .refl _
-/
abbrev forgetNatIsoActionForget : forget₂ (Rep.{w} k G) (ModuleCat k) ≅ (RepToAction k G) ⋙
    Action.forget (ModuleCat k) G := .refl _

/--
Instance `preservesLimits_forget` / 实例 `preservesLimits_forget`

English:
instance preservesLimits_forget
  signature: :
  body: Limits.preservesLimits_of_natIso (forgetNatIsoActionForget k G).symm

中文:
实例 preservesLimits_forget
  签名: :
  定义体: Limits.preservesLimits_of_natIso (forgetNatIsoActionForget k G).symm

Depends on / 依赖: Limits, Limits.preservesLimits_of_natIso, forgetNatIsoActionForget, preservesLimits_of_natIso
-/
instance preservesLimits_forget :
    Limits.PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesLimits_of_natIso (forgetNatIsoActionForget k G).symm

/--
Instance `preservesColimits_forget` / 实例 `preservesColimits_forget`

English:
instance preservesColimits_forget
  signature: :
  body: Limits.preservesColimits_of_natIso (forgetNatIsoActionForget k G).symm

中文:
实例 preservesColimits_forget
  签名: :
  定义体: Limits.preservesColimits_of_natIso (forgetNatIsoActionForget k G).symm

Depends on / 依赖: Limits, Limits.preservesColimits_of_natIso, forgetNatIsoActionForget, preservesColimits_of_natIso
-/
instance preservesColimits_forget :
    Limits.PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesColimits_of_natIso (forgetNatIsoActionForget k G).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasBinaryBiproducts (Rep.{w} k G)
  body: Limits.hasBinaryBiproduct_of_total
    ⟨Rep.of (X := A.V × B.V) (A.ρ.prod B.ρ), Rep.ofHom (.fst k A.ρ B.ρ), Rep.ofHom (.snd k A.ρ B.ρ),
      Rep.ofHom (.inl k A.ρ B.ρ), Rep.ofHom (.inr k A.ρ B.ρ), by ext1; simp,
by ext1; simp [zero_hom], by ext1; simp [zero_hom], by ext1; simp⟩ by
    ext1; simp [R

中文:
实例 :
  签名: Limits.有BinaryBiproducts (Rep.{w} k G)
  定义体: Limits.hasBinaryBiproduct_of_total
    ⟨Rep.of (X := A.V × B.V) (A.ρ.prod B.ρ), Rep.ofHom (.fst k A.ρ B.ρ), Rep.ofHom (.snd k A.ρ B.ρ),
      Rep.ofHom (.inl k A.ρ B.ρ), Rep.ofHom (.inr k A.ρ B.ρ), by ext1; simp,
by ext1; simp [zero_hom], by ext1; simp [zero_hom], by ext1; simp⟩ by
    ext1; simp [R

Depends on / 依赖: Limits, Limits.hasBinaryBiproduct_of_total, hasBinaryBiproduct_of_total
-/
instance : Limits.HasBinaryBiproducts (Rep.{w} k G) where
  has_binary_biproduct A B := Limits.hasBinaryBiproduct_of_total
    ⟨Rep.of (X := A.V × B.V) (A.ρ.prod B.ρ), Rep.ofHom (.fst k A.ρ B.ρ), Rep.ofHom (.snd k A.ρ B.ρ),
      Rep.ofHom (.inl k A.ρ B.ρ), Rep.ofHom (.inr k A.ρ B.ρ), by ext1; simp,
by ext1; simp [zero_hom], by ext1; simp [zero_hom], by ext1; simp⟩ by
    ext1; simp [Rep.add_hom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasZeroObject (Rep.{w} k G)
  body: ⟨Rep.trivial k G PUnit, {
    unique_to X := Nonempty.intro ⟨⟨0⟩, fun f => by
      ext x; have : x = 0 := Subsingleton.elim _ _; subst this; simp⟩
    unique_from X := Nonempty.intro ⟨⟨0⟩, fun f => by ext⟩
  }⟩

中文:
实例 :
  签名: Limits.有ZeroObject (Rep.{w} k G)
  定义体: ⟨Rep.trivial k G PUnit, {
    unique_to X := Nonempty.intro ⟨⟨0⟩, fun f => by
      ext x; have : x = 0 := Subsingleton.elim _ _; subst this; simp⟩
    unique_from X := Nonempty.intro ⟨⟨0⟩, fun f => by ext⟩
  }⟩

Depends on / 依赖: Rep.trivial
-/
instance : Limits.HasZeroObject (Rep.{w} k G) where
  zero := ⟨Rep.trivial k G PUnit, {
    unique_to X := Nonempty.intro ⟨⟨0⟩, fun f => by
      ext x; have : x = 0 := Subsingleton.elim _ _; subst this; simp⟩
    unique_from X := Nonempty.intro ⟨⟨0⟩, fun f => by ext⟩
  }⟩

/--
lemma `isZero_iff` / 引理 `isZero_iff`

English:
lemma isZero_iff
  given: (M : Rep k G)
  statement: Limits.IsZero M ↔ Subsingleton M.V
  proof: by
  simp [Limits.IsZero.iff_id_eq_zero, Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff,
    ← ModuleCat.isZero_of_iff_subsingleton (R := k), ModuleCat.hom_ext_iff]

中文:
引理 isZero_iff
  条件: (M : Rep k G)
  结论: Limits.是零 M ↔ 子单例 M.V
  证明: by
  simp [Limits.IsZero.iff_id_eq_zero, Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff,
    ← ModuleCat.isZero_of_iff_subsingleton (R := k), ModuleCat.hom_ext_iff]

Depends on / 依赖: IntertwiningMap, IsZero, Limits, Limits.IsZero.iff_id_eq_zero, ModuleCat, ModuleCat.hom_ext_iff, ModuleCat.isZero_of_iff_subsingleton, Rep.hom_ext_iff, Representation, Representation.IntertwiningMap.ext_iff, ext_iff, hom_ext_iff, iff_id_eq_zero, isZero_of_iff_subsingleton
-/
lemma isZero_iff (M : Rep k G) : Limits.IsZero M ↔ Subsingleton M.V := by
  simp [Limits.IsZero.iff_id_eq_zero, Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff,
    ← ModuleCat.isZero_of_iff_subsingleton (R := k), ModuleCat.hom_ext_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasLimits (Rep.{w} k G)
  body: Adjunction.has_limits_of_equivalence (repIsoAction k G).functor

中文:
实例 :
  签名: Limits.有极限 (Rep.{w} k G)
  定义体: Adjunction.has_limits_of_equivalence (repIsoAction k G).functor

Depends on / 依赖: Adjunction, Adjunction.has_limits_of_equivalence, functor, has_limits_of_equivalence, repIsoAction
-/
instance : Limits.HasLimits (Rep.{w} k G) :=
  Adjunction.has_limits_of_equivalence (repIsoAction k G).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasColimits (Rep.{w} k G)
  body: Adjunction.has_colimits_of_equivalence (repIsoAction k G).functor

中文:
实例 :
  签名: Limits.有余极限 (Rep.{w} k G)
  定义体: Adjunction.has_colimits_of_equivalence (repIsoAction k G).functor

Depends on / 依赖: Adjunction, Adjunction.has_colimits_of_equivalence, functor, has_colimits_of_equivalence, repIsoAction
-/
instance : Limits.HasColimits (Rep.{w} k G) :=
  Adjunction.has_colimits_of_equivalence (repIsoAction k G).functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.ReflectsLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k))
  body: Limits.reflectsLimits_of_reflectsIsomorphisms

中文:
实例 :
  签名: Limits.ReflectsLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (模范畴 k))
  定义体: Limits.reflectsLimits_of_reflectsIsomorphisms

Depends on / 依赖: Limits, Limits.reflectsLimits_of_reflectsIsomorphisms, reflectsLimits_of_reflectsIsomorphisms
-/
instance : Limits.ReflectsLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.reflectsLimits_of_reflectsIsomorphisms

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.ReflectsColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k))
  body: Limits.reflectsColimits_of_reflectsIsomorphisms

中文:
实例 :
  签名: Limits.ReflectsColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (模范畴 k))
  定义体: Limits.reflectsColimits_of_reflectsIsomorphisms

Depends on / 依赖: Limits, Limits.reflectsColimits_of_reflectsIsomorphisms, reflectsColimits_of_reflectsIsomorphisms
-/
instance : Limits.ReflectsColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.reflectsColimits_of_reflectsIsomorphisms

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (Rep.{w} k G)
  body: abelianOfEquivalence (RepToAction k G)

中文:
实例 :
  签名: 交换 (Rep.{w} k G)
  定义体: abelianOfEquivalence (RepToAction k G)

Depends on / 依赖: RepToAction, abelianOfEquivalence
-/
instance : Abelian (Rep.{w} k G) := abelianOfEquivalence (RepToAction k G)

variable {k G} in
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: (f : A ⟶ B)
  statement: Epi f ↔ Function.Surjective f.hom
  proof: ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

中文:
定理 epi_iff_surjective
  条件: (f : A ⟶ B)
  结论: 满态射 f ↔ 函数.满射 f.hom
  证明: ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, epi_iff_surjective, epi_of_epi_map
-/
theorem epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

variable {k G} in
/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  given: (f : A ⟶ B)
  statement: Mono f ↔ Function.Injective f.hom
  proof: ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

中文:
定理 mono_iff_injective
  条件: (f : A ⟶ B)
  结论: 单态射 f ↔ 函数.单射 f.hom
  证明: ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, mono_iff_injective, mono_of_mono_map
-/
theorem mono_iff_injective (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩

instance (f : A ⟶ B) [Mono f] : Mono f.toModuleCatHom :=
inferInstanceAs Mono ((forget₂ _ _).map f)

instance (f : A ⟶ B) [Epi f] : Epi f.toModuleCatHom :=
inferInstanceAs Epi ((forget₂ _ _).map f)

end Action

end ring

section CommSemiring

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G]

instance {M N : Rep k G} : SMul k (M ⟶ N) where
  smul r f := ofHom (r • f.hom)

/--
lemma `ofHom_smul` / 引理 `ofHom_smul`

English:
lemma ofHom_smul
  statement: {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  proof: rfl

中文:
引理 ofHom_smul
  结论: {M N : 类型 w} [加法交换群 M] [加法交换群 N] [模 k M] [模 k N]
  证明: rfl
-/
lemma ofHom_smul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (r : k) :
    ofHom (r • f) = r • ofHom f := rfl

/--
lemma `smul_hom` / 引理 `smul_hom`

English:
lemma smul_hom
  given: {M N : Rep k G} (f : M ⟶ N) (r : k)
  statement: (r • f).hom = r • f.hom
  proof: rfl

中文:
引理 smul_hom
  条件: {M N : Rep k G} (f : M ⟶ N) (r : k)
  结论: (r • f).hom = r • f.hom
  证明: rfl
-/
lemma smul_hom {M N : Rep k G} (f : M ⟶ N) (r : k) : (r • f).hom = r • f.hom := rfl

/--
lemma `smul_comp` / 引理 `smul_comp`

English:
lemma smul_comp
  given: {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O)
  proof: by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]

中文:
引理 smul_comp
  条件: {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O)
  证明: by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.comp_smul, comp_smul, smul_hom
-/
lemma smul_comp {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O) :
    (r • f) ≫ g = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]

/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  given: {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O)
  proof: by
  ext
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

中文:
引理 comp_smul
  条件: {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O)
  证明: by
  ext
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

Depends on / 依赖: IntertwiningMap, Representation, Representation.IntertwiningMap.smul_comp, smul_comp, smul_hom
-/
lemma comp_smul {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O) :
    f ≫ (r • g) = r • (f ≫ g) := by
  ext
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]

instance {M N : Rep k G} : Module k (M ⟶ N) := fast_instance% hom_injective.module
_ ⟨⟨_, zero_hom⟩, add_hom⟩ by simp [smul_hom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear k (Rep k G)
  body: smul_comp
  comp_smul _ _ _ := comp_smul

中文:
实例 :
  签名: 线性 k (Rep k G)
  定义体: smul_comp
  comp_smul _ _ _ := comp_smul

Depends on / 依赖: smul_comp
-/
instance : Linear k (Rep k G) where
  smul_comp _ _ _ := smul_comp
  comp_smul _ _ _ := comp_smul

end CommSemiring

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Linear k (forget₂ (Rep.{w} k G) (ModuleCat.{w} k))
  body: by
    ext
    simp [smul_hom]

中文:
实例 :
  签名: 函子.线性 k (forget₂ (Rep.{w} k G) (模范畴.{w} k))
  定义体: by
    ext
    simp [smul_hom]

Depends on / 依赖: smul_hom
-/
instance : Functor.Linear k (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)) where
  map_smul {X Y} f r := by
    ext
    simp [smul_hom]

/--
Definition of `homLinearEquiv` / `homLinearEquiv` 的定义

English:
abbreviation homLinearEquiv
  signature: (X Y : Rep k G)
  body: homEquiv
  map_add' := add_hom
  map_smul' _ _ := smul_hom _ _

中文:
缩写 homLinearEquiv
  签名: (X Y : Rep k G)
  定义体: homEquiv
  map_add' := add_hom
  map_smul' _ _ := smul_hom _ _

Depends on / 依赖: homEquiv
-/
abbrev homLinearEquiv (X Y : Rep k G) : (X ⟶ Y) ≃ₗ[k] (X.ρ.IntertwiningMap Y.ρ) where
  __ := homEquiv
  map_add' := add_hom
  map_smul' _ _ := smul_hom _ _

section monoidal

open MonoidalCategory CategoryTheory Representation.IntertwiningMap
  Representation.TensorProduct

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (Rep.{u} k G)
  body: of (X.ρ.tprod Y.ρ)
  whiskerLeft X _ _ f := ofHom (lTensor X.ρ f.hom)
  whiskerRight f Z := ofHom (rTensor Z.ρ f.hom)
  tensorUnit := Rep.trivial k G k
  tensorHom f g := ofHom (f.hom.tensor g.hom)
  associator X Y Z := Rep.mkIso (assoc X.ρ Y.ρ Z.ρ)
  leftUnitor X := Rep.mkIso (lid k X.ρ)
  rightUni

中文:
实例 :
  签名: 幺半群范畴 (Rep.{u} k G)
  定义体: of (X.ρ.tprod Y.ρ)
  whiskerLeft X _ _ f := ofHom (lTensor X.ρ f.hom)
  whiskerRight f Z := ofHom (rTensor Z.ρ f.hom)
  tensorUnit := Rep.trivial k G k
  tensorHom f g := ofHom (f.hom.tensor g.hom)
  associator X Y Z := Rep.mkIso (assoc X.ρ Y.ρ Z.ρ)
  leftUnitor X := Rep.mkIso (lid k X.ρ)
  rightUni
-/
instance : MonoidalCategory (Rep.{u} k G) where
  tensorObj X Y := of (X.ρ.tprod Y.ρ)
  whiskerLeft X _ _ f := ofHom (lTensor X.ρ f.hom)
  whiskerRight f Z := ofHom (rTensor Z.ρ f.hom)
  tensorUnit := Rep.trivial k G k
  tensorHom f g := ofHom (f.hom.tensor g.hom)
  associator X Y Z := Rep.mkIso (assoc X.ρ Y.ρ Z.ρ)
  leftUnitor X := Rep.mkIso (lid k X.ρ)
  rightUnitor X := Rep.mkIso (rid k X.ρ)
  associator_naturality _ _ _ := by ext; simp
  leftUnitor_naturality _ := by ext; simp [trivial_V]
  rightUnitor_naturality _ := by ext; simp [trivial_V]
  pentagon _ _ _ _ := by ext; simp
  triangle X Y := by ext; simp

@[simp]
/--
lemma `tensorUnit_V` / 引理 `tensorUnit_V`

English:
lemma tensorUnit_V
  statement: (𝟙_ (Rep.{u} k G)).V = k
  proof: rfl

@[simp]

中文:
引理 tensorUnit_V
  结论: (𝟙_ (Rep.{u} k G)).V = k
  证明: rfl

@[simp]
-/
lemma tensorUnit_V : (𝟙_ (Rep.{u} k G)).V = k := rfl

@[simp]
/--
lemma `tensorUnit_ρ` / 引理 `tensorUnit_ρ`

English:
lemma tensorUnit_ρ
  statement: (𝟙_ (Rep.{u} k G)).ρ = Representation.trivial k G k
  proof: rfl

@[simp]

中文:
引理 tensorUnit_ρ
  结论: (𝟙_ (Rep.{u} k G)).ρ = Representation.trivial k G k
  证明: rfl

@[simp]

Depends on / 依赖: FractionRing, FractionRing.frobenius, LinearEquiv, LinearEquiv.smulOfNeZero, WittVector, WittVector.FractionRing.p_nonzero, frobenius, p_nonzero, smulOfNeZero, toSemilinearEquiv, toSemilinearEquiv.trans, zpow_ne_zero
-/
lemma tensorUnit_ρ : (𝟙_ (Rep.{u} k G)).ρ = Representation.trivial k G k := rfl

@[simp]
/--
lemma `tensor_V` / 引理 `tensor_V`

English:
lemma tensor_V
  given: {X Y : Rep k G}
  statement: (X otimes Y).V = TensorProduct k X.V Y.V
  proof: rfl

@[simp]

中文:
引理 tensor_V
  条件: {X Y : Rep k G}
  结论: (X otimes Y).V = 张量积 k X.V Y.V
  证明: rfl

@[simp]
-/
lemma tensor_V {X Y : Rep k G} : (X otimes Y).V = TensorProduct k X.V Y.V := rfl

@[simp]
/--
lemma `tensor_ρ` / 引理 `tensor_ρ`

English:
lemma tensor_ρ
  given: {X Y : Rep k G}
  statement: (X otimes Y).ρ = X.ρ.tprod Y.ρ
  proof: rfl

@[simp]

中文:
引理 tensor_ρ
  条件: {X Y : Rep k G}
  结论: (X otimes Y).ρ = X.ρ.tprod Y.ρ
  证明: rfl

@[simp]
-/
lemma tensor_ρ {X Y : Rep k G} : (X otimes Y).ρ = X.ρ.tprod Y.ρ := rfl

@[simp]
/--
lemma `hom_whiskerRight` / 引理 `hom_whiskerRight`

English:
lemma hom_whiskerRight
  given: {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂)
  proof: rfl

@[simp]

中文:
引理 hom_whiskerRight
  条件: {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂)
  证明: rfl

@[simp]
-/
lemma hom_whiskerRight {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂) :
    (f ▷ Y).hom = .rTensor _ f.hom := rfl

@[simp]
/--
lemma `hom_whiskerLeft` / 引理 `hom_whiskerLeft`

English:
lemma hom_whiskerLeft
  given: {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂)
  proof: rfl

@[simp]

中文:
引理 hom_whiskerLeft
  条件: {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂)
  证明: rfl

@[simp]
-/
lemma hom_whiskerLeft {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).hom = .lTensor _ f.hom := rfl

@[simp]
/--
lemma `hom_tensorHom` / 引理 `hom_tensorHom`

English:
lemma hom_tensorHom
  given: {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  proof: rfl

@[simp]

中文:
引理 hom_tensorHom
  条件: {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  证明: rfl

@[simp]
-/
lemma hom_tensorHom {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f otimesₘ g).hom = f.hom.tensor g.hom := rfl

@[simp]
/--
lemma `of_tensor` / 引理 `of_tensor`

English:
lemma of_tensor
  statement: {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
  proof: rfl

@[simp]

中文:
引理 of_tensor
  结论: {X Y : 类型u} [加法交换群 X] [加法交换群 Y] [模 k X] [模 k Y]
  证明: rfl

@[simp]
-/
lemma of_tensor {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    (σ : Representation k G X) (ρ : Representation k G Y) :
    of (σ.tprod ρ) = of σ otimes of ρ := rfl

@[simp]
/--
lemma `hom_hom_associator` / 引理 `hom_hom_associator`

English:
lemma hom_hom_associator
  given: {X Y Z : Rep k G}
  statement: (α_ X Y Z).hom.hom =
  proof: by
  ext1
  refine TensorProduct.ext_threefold fun x y z => by rfl

@[simp]

中文:
引理 hom_hom_associator
  条件: {X Y Z : Rep k G}
  结论: (α_ X Y Z).hom.hom =
  证明: by
  ext1
  refine TensorProduct.ext_threefold fun x y z => by rfl

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.ext_threefold, ext_threefold
-/
lemma hom_hom_associator {X Y Z : Rep k G} : (α_ X Y Z).hom.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).toIntertwiningMap := by
  ext1
  refine TensorProduct.ext_threefold fun x y z => by rfl

@[simp]
/--
lemma `hom_inv_associator` / 引理 `hom_inv_associator`

English:
lemma hom_inv_associator
  given: {X Y Z : Rep k G}
  statement: (α_ X Y Z).inv.hom =
  proof: rfl

@[simp]

中文:
引理 hom_inv_associator
  条件: {X Y Z : Rep k G}
  结论: (α_ X Y Z).inv.hom =
  证明: rfl

@[simp]
-/
lemma hom_inv_associator {X Y Z : Rep k G} : (α_ X Y Z).inv.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).symm.toIntertwiningMap := rfl

@[simp]
/--
lemma `hom_hom_leftUnitor` / 引理 `hom_hom_leftUnitor`

English:
lemma hom_hom_leftUnitor
  given: {X : Rep k G}
  statement: (fun_ X).hom.hom =
  proof: rfl

@[simp]

中文:
引理 hom_hom_leftUnitor
  条件: {X : Rep k G}
  结论: (fun_ X).hom.hom =
  证明: rfl

@[simp]
-/
lemma hom_hom_leftUnitor {X : Rep k G} : (fun_ X).hom.hom =
    (Representation.TensorProduct.lid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
/--
lemma `hom_inv_leftUnitor` / 引理 `hom_inv_leftUnitor`

English:
lemma hom_inv_leftUnitor
  given: {X : Rep k G}
  statement: (fun_ X).inv.hom =
  proof: rfl

@[simp]

中文:
引理 hom_inv_leftUnitor
  条件: {X : Rep k G}
  结论: (fun_ X).inv.hom =
  证明: rfl

@[simp]
-/
lemma hom_inv_leftUnitor {X : Rep k G} : (fun_ X).inv.hom =
    (Representation.TensorProduct.lid k X.ρ).symm.toIntertwiningMap := rfl

@[simp]
/--
lemma `hom_hom_rightUnitor` / 引理 `hom_hom_rightUnitor`

English:
lemma hom_hom_rightUnitor
  given: {X : Rep k G}
  statement: (ρ_ X).hom.hom =
  proof: rfl

@[simp]

中文:
引理 hom_hom_rightUnitor
  条件: {X : Rep k G}
  结论: (ρ_ X).hom.hom =
  证明: rfl

@[simp]
-/
lemma hom_hom_rightUnitor {X : Rep k G} : (ρ_ X).hom.hom =
    (Representation.TensorProduct.rid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
/--
lemma `hom_inv_rightUnitor` / 引理 `hom_inv_rightUnitor`

English:
lemma hom_inv_rightUnitor
  given: {X : Rep k G}
  statement: (ρ_ X).inv.hom =
  proof: rfl

中文:
引理 hom_inv_rightUnitor
  条件: {X : Rep k G}
  结论: (ρ_ X).inv.hom =
  证明: rfl
-/
lemma hom_inv_rightUnitor {X : Rep k G} : (ρ_ X).inv.hom =
    (Representation.TensorProduct.rid k X.ρ).symm.toIntertwiningMap := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalPreadditive (Rep.{u} k G)
  body: by ext1; simp
  zero_whiskerRight {_ _ _} := by ext1; simp
  whiskerLeft_add _ _ := by ext1; simp [add_hom]
  add_whiskerRight _ _ := by ext1; simp [add_hom]

中文:
实例 :
  签名: 幺半群预加性 (Rep.{u} k G)
  定义体: by ext1; simp
  zero_whiskerRight {_ _ _} := by ext1; simp
  whiskerLeft_add _ _ := by ext1; simp [add_hom]
  add_whiskerRight _ _ := by ext1; simp [add_hom]

Depends on / 依赖: add_hom, add_whiskerRight, whiskerLeft_add, zero_whiskerRight
-/
instance : MonoidalPreadditive (Rep.{u} k G) where
  whiskerLeft_zero {_ _ _} := by ext1; simp
  zero_whiskerRight {_ _ _} := by ext1; simp
  whiskerLeft_add _ _ := by ext1; simp [add_hom]
  add_whiskerRight _ _ := by ext1; simp [add_hom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalLinear k (Rep.{u} k G)
  body: by ext1; simp [smul_hom]
  smul_whiskerRight _ _ _ _ _ := by ext1; simp [smul_hom]

中文:
实例 :
  签名: 幺半群线性 k (Rep.{u} k G)
  定义体: by ext1; simp [smul_hom]
  smul_whiskerRight _ _ _ _ _ := by ext1; simp [smul_hom]

Depends on / 依赖: smul_hom, smul_whiskerRight
-/
instance : MonoidalLinear k (Rep.{u} k G) where
  whiskerLeft_smul _ _ _ _ _ := by ext1; simp [smul_hom]
  smul_whiskerRight _ _ _ _ _ := by ext1; simp [smul_hom]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (Rep.{u} k G)
  body: Rep.mkIso (Representation.TensorProduct.comm X.ρ Y.ρ)
  braiding_naturality_right _ _ _ _ := by ext1; simp [comm_comp_lTensor]
  braiding_naturality_left _ _ := by ext1; simp [comm_comp_rTensor]
  hexagon_forward _ _ _ := by
    ext : 2
exact TensorProduct.ext_threefold fun _ _ _ => by simp
  hexago

中文:
实例 :
  签名: 辫范畴 (Rep.{u} k G)
  定义体: Rep.mkIso (Representation.TensorProduct.comm X.ρ Y.ρ)
  braiding_naturality_right _ _ _ _ := by ext1; simp [comm_comp_lTensor]
  braiding_naturality_left _ _ := by ext1; simp [comm_comp_rTensor]
  hexagon_forward _ _ _ := by
    ext : 2
exact TensorProduct.ext_threefold fun _ _ _ => by simp
  hexago

Depends on / 依赖: Rep.mkIso, Representation, Representation.TensorProduct.comm, TensorProduct
-/
instance : BraidedCategory (Rep.{u} k G) where
  braiding X Y := Rep.mkIso (Representation.TensorProduct.comm X.ρ Y.ρ)
  braiding_naturality_right _ _ _ _ := by ext1; simp [comm_comp_lTensor]
  braiding_naturality_left _ _ := by ext1; simp [comm_comp_rTensor]
  hexagon_forward _ _ _ := by
    ext : 2
exact TensorProduct.ext_threefold fun _ _ _ => by simp
  hexagon_reverse X Y Z := by
    ext : 2
    simp only [tensor_V, tensor_ρ, hom_comp, hom_inv_associator, mkIso_hom_hom, comp_toLinearMap,
      assoc_symm_toLinearMap, toLinearMap_comm, LinearEquiv.comp_coe, hom_whiskerRight,
      hom_whiskerLeft, toLinearMap_rTensor, toLinearMap_lTensor]
    ext; simp

@[simp]
/--
lemma `hom_braiding` / 引理 `hom_braiding`

English:
lemma hom_braiding
  given: {X Y : Rep k G}
  statement: (β_ X Y).hom.hom =
  proof: rfl

中文:
引理 hom_braiding
  条件: {X Y : Rep k G}
  结论: (β_ X Y).hom.hom =
  证明: rfl
-/
lemma hom_braiding {X Y : Rep k G} : (β_ X Y).hom.hom =
    (Representation.TensorProduct.comm X.ρ Y.ρ).toIntertwiningMap := rfl

open Representation.Equiv in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SymmetricCategory (Rep.{u} k G)
  body: by ext1; simp [← comm_symm Y.ρ X.ρ, ← toIntertwiningMap_trans,
    trans_symm, toIntertwiningMap_refl]

中文:
实例 :
  签名: 对称范畴 (Rep.{u} k G)
  定义体: by ext1; simp [← comm_symm Y.ρ X.ρ, ← toIntertwiningMap_trans,
    trans_symm, toIntertwiningMap_refl]

Depends on / 依赖: comm_symm, toIntertwiningMap_refl, toIntertwiningMap_trans, trans_symm
-/
instance : SymmetricCategory (Rep.{u} k G) where
  symmetry X Y := by ext1; simp [← comm_symm Y.ρ X.ρ, ← toIntertwiningMap_trans,
    trans_symm, toIntertwiningMap_refl]

end monoidal

section MonoidalClosed
open MonoidalCategory Action

variable {G : Type v} [Group G] (A B C : Rep.{w} k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def ihom
  body: Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g => by
    ext; simp [Representation.IntertwiningMap.toLinearMap_apply, ← hom_comm_apply]⟩
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

中文:
定义 noncomputable
  签名: def ihom
  定义体: Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g => by
    ext; simp [Representation.IntertwiningMap.toLinearMap_apply, ← hom_comm_apply]⟩
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl
-/
protected noncomputable def ihom : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g => by
    ext; simp [Representation.IntertwiningMap.toLinearMap_apply, ← hom_comm_apply]⟩
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl

/--
theorem `ihom_obj_ρ_apply` / 定理 `ihom_obj_ρ_apply`

English:
theorem ihom_obj_ρ_apply
  given: {A B : Rep k G} (g : G) (x : A ->ₗ[k] B)
  proof: rfl

中文:
定理 ihom_obj_ρ_apply
  条件: {A B : Rep k G} (g : G) (x : A ->ₗ[k] B)
  证明: rfl
-/
@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A ->ₗ[k] B) :
    -- Hint to put this lemma into `simp`-normal form.
    DFunLike.coe (F := (Representation k G (↑A.V ->ₗ[k] ↑B.V)))
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps]
/--
Definition of `tensorHomEquiv` / `tensorHomEquiv` 的定义

English:
definition tensorHomEquiv
  signature: (A B C : Rep.{u} k G)
  body: Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g => by
    ext x y
    simp only [tensor_V, tensor_ρ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.linHom_apply]
   

中文:
定义 tensorHomEquiv
  签名: (A B C : Rep.{u} k G)
  定义体: Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g => by
    ext x y
    simp only [tensor_V, tensor_ρ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.linHom_apply]
   

Depends on / 依赖: Function, Function.comp_apply, IntertwiningMap, LinearMap, LinearMap.coe_comp, LinearMap.flip_apply, Rep.ofHom, Representation, Representation.IntertwiningMap.toLinearMap_apply, Representation.linHom_apply, TensorProduct, TensorProduct.curry, TensorProduct.curry_apply, TensorProduct.ext, TensorProduct.uncurry, coe_comp, comp_apply, curry_apply, f.hom.toLinearMap, f.hom.toLinearMap.flip
-/
def tensorHomEquiv (A B C : Rep.{u} k G) : (A otimes B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g => by
    ext x y
    simp only [tensor_V, tensor_ρ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.linHom_apply]
    have := by simpa using (hom_comm_apply f g (A.ρ g⁻¹ y otimesₜ[k] x)).symm
    simp [this]⟩
  invFun f := Rep.ofHom ⟨TensorProduct.uncurry (.id k) _ _ _
    f.hom.toLinearMap.flip, fun g => TensorProduct.ext' fun x y => by
    simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x)⟩
left_inv _ := Rep.Hom.ext Representation.IntertwiningMap.ext
    TensorProduct.ext' fun _ _ => rfl

variable {A B C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalClosed (Rep k G)
  body: { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
homEquiv_naturality_left_symm := fun _ _ => Rep.hom_ext
Representation.IntertwiningMap.ext TensorProduct.ext' fun _ _ => rfl
homEquiv_naturality_right _ _ := Rep.hom_ext
Representation.Intertwin

中文:
实例 :
  签名: 幺半群闭 (Rep k G)
  定义体: { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
homEquiv_naturality_left_symm := fun _ _ => Rep.hom_ext
Representation.IntertwiningMap.ext TensorProduct.ext' fun _ _ => rfl
homEquiv_naturality_right _ _ := Rep.hom_ext
Representation.Intertwin

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, IntertwiningMap, LinearMap, LinearMap.ext, Rep.hom_ext, Rep.ihom, Rep.tensorHomEquiv, Representation, Representation.IntertwiningMap.ext, TensorProduct, TensorProduct.ext, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, hom_ext, mkOfHomEquiv, rightAdj, tensorHomEquiv
-/
noncomputable instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
homEquiv_naturality_left_symm := fun _ _ => Rep.hom_ext
Representation.IntertwiningMap.ext TensorProduct.ext' fun _ _ => rfl
homEquiv_naturality_right _ _ := Rep.hom_ext
Representation.IntertwiningMap.ext
            LinearMap.ext fun _ => LinearMap.ext fun _ => rfl }) }

@[simp]
/--
theorem `ihom_obj_ρ_def` / 定理 `ihom_obj_ρ_def`

English:
theorem ihom_obj_ρ_def
  given: (A B : Rep k G)
  statement: ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ
  proof: rfl

@[simp]

中文:
定理 ihom_obj_ρ_def
  条件: (A B : Rep k G)
  结论: ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ
  证明: rfl

@[simp]
-/
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
/--
theorem `homEquiv_def` / 定理 `homEquiv_def`

English:
theorem homEquiv_def
  given: (A B C : Rep k G)
  statement: (ihom.adjunction A).homEquiv B C =
  proof: congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]

中文:
定理 homEquiv_def
  条件: (A B C : Rep k G)
  结论: (ihom.adjunction A).homEquiv B C =
  证明: congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv_homEquiv, mkOfHomEquiv_homEquiv
-/
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C =
    Rep.tensorHomEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
/--
theorem `ihom_ev_app_hom` / 定理 `ihom_ev_app_hom`

English:
theorem ihom_ev_app_hom
  given: (A B : Rep k G)
  proof: by
  ext; rfl

中文:
定理 ihom_ev_app_hom
  条件: (A B : Rep k G)
  证明: by
  ext; rfl
-/
theorem ihom_ev_app_hom (A B : Rep k G) :
    ((ihom.ev A).app B).hom.toLinearMap = (TensorProduct.uncurry (.id k) A (A ->ₗ[k] B) B
      LinearMap.id.flip) := by
  ext; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ihom_coev_app_hom` / 定理 `ihom_coev_app_hom`

English:
theorem ihom_coev_app_hom
  given: (A B : Rep k G)
  proof: LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

中文:
定理 ihom_coev_app_hom
  条件: (A B : Rep k G)
  证明: LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
-/
@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom.toLinearMap = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/--
Definition of `MonoidalClosed.linearHomEquiv` / `MonoidalClosed.linearHomEquiv` 的定义

English:
definition MonoidalClosed.linearHomEquiv
  signature: (A B C : Rep.{u} k G)
  body: { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 幺半群闭.linearHomEquiv
  签名: (A B C : Rep.{u} k G)
  定义体: { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: adjunction, homEquiv, ihom.adjunction, map_add, map_smul
-/
def MonoidalClosed.linearHomEquiv (A B C : Rep.{u} k G) : (A otimes B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/--
Definition of `MonoidalClosed.linearHomEquivComm` / `MonoidalClosed.linearHomEquivComm` 的定义

English:
definition MonoidalClosed.linearHomEquivComm
  signature: (A B C : Rep.{u} k G)
  body: Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

@[simp]

中文:
定义 幺半群闭.linearHomEquivComm
  签名: (A B C : Rep.{u} k G)
  定义体: Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

@[simp]

Depends on / 依赖: Iso.refl, Linear, Linear.homCongr, MonoidalClosed, MonoidalClosed.linearHomEquiv, homCongr, linearHomEquiv
-/
def MonoidalClosed.linearHomEquivComm (A B C : Rep.{u} k G) : (A otimes B ⟶ C) ≃ₗ[k] A ⟶ B
    ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

@[simp]
/--
theorem `MonoidalClosed.linearHomEquiv_hom` / 定理 `MonoidalClosed.linearHomEquiv_hom`

English:
theorem MonoidalClosed.linearHomEquiv_hom
  given: (A B C : Rep.{u} k G) (f : A otimes B ⟶ C)
  proof: rfl

@[simp]

中文:
定理 幺半群闭.linearHomEquiv_hom
  条件: (A B C : Rep.{u} k G) (f : A otimes B ⟶ C)
  证明: rfl

@[simp]
-/
theorem MonoidalClosed.linearHomEquiv_hom (A B C : Rep.{u} k G) (f : A otimes B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom.toLinearMap =
    (TensorProduct.curry f.hom.toLinearMap).flip :=
  rfl

@[simp]
/--
theorem `MonoidalClosed.linearHomEquivComm_hom` / 定理 `MonoidalClosed.linearHomEquivComm_hom`

English:
theorem MonoidalClosed.linearHomEquivComm_hom
  given: (A B C : Rep.{u} k G) (f : A otimes B ⟶ C)
  proof: rfl

中文:
定理 幺半群闭.linearHomEquivComm_hom
  条件: (A B C : Rep.{u} k G) (f : A otimes B ⟶ C)
  证明: rfl
-/
theorem MonoidalClosed.linearHomEquivComm_hom (A B C : Rep.{u} k G) (f : A otimes B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom.toLinearMap =
    TensorProduct.curry f.hom.toLinearMap :=
  rfl

/--
theorem `MonoidalClosed.linearHomEquiv_symm_hom` / 定理 `MonoidalClosed.linearHomEquiv_symm_hom`

English:
theorem MonoidalClosed.linearHomEquiv_symm_hom
  given: (A B C : Rep.{u} k G) (f : B ⟶ A ⟶[Rep k G] C)
  proof: by
  simp [linearHomEquiv]
  rfl

中文:
定理 幺半群闭.linearHomEquiv_symm_hom
  条件: (A B C : Rep.{u} k G) (f : B ⟶ A ⟶[Rep k G] C)
  证明: by
  simp [linearHomEquiv]
  rfl

Depends on / 依赖: linearHomEquiv
-/
theorem MonoidalClosed.linearHomEquiv_symm_hom (A B C : Rep.{u} k G) (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap.flip := by
  simp [linearHomEquiv]
  rfl

/--
theorem `MonoidalClosed.linearHomEquivComm_symm_hom` / 定理 `MonoidalClosed.linearHomEquivComm_symm_hom`

English:
theorem MonoidalClosed.linearHomEquivComm_symm_hom
  given: (A B C : Rep.{u} k G) (f : A ⟶ B ⟶[Rep k G] C)
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 幺半群闭.linearHomEquivComm_symm_hom
  条件: (A B C : Rep.{u} k G) (f : A ⟶ B ⟶[Rep k G] C)
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem MonoidalClosed.linearHomEquivComm_symm_hom (A B C : Rep.{u} k G) (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed

section

variable {k : Type u} [Semiring k] {G : Type v} [Group G] [Fintype G] (A : Rep.{w} k G)

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : End A
  body: Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g => by ext; simp⟩

@[simp]

中文:
定义 norm
  签名: : End A
  定义体: Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g => by ext; simp⟩

@[simp]

Depends on / 依赖: Rep.ofHom, Representation, Representation.norm
-/
def norm : End A := Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g => by ext; simp⟩

@[simp]
/--
lemma `norm_apply` / 引理 `norm_apply`

English:
lemma norm_apply
  given: {x : A}
  statement: (norm A).hom x = A.ρ.norm x
  proof: rfl

@[reassoc, elementwise]

中文:
引理 norm_apply
  条件: {x : A}
  结论: (norm A).hom x = A.ρ.norm x
  证明: rfl

@[reassoc, elementwise]
-/
lemma norm_apply {x : A} : (norm A).hom x = A.ρ.norm x := rfl

@[reassoc, elementwise]
/--
lemma `norm_comm` / 引理 `norm_comm`

English:
lemma norm_comm
  given: {A B : Rep k G} (f : A ⟶ B)
  statement: f ≫ norm B = norm A ≫ f
  proof: by
  ext; simp [Representation.norm, hom_comm_apply]

中文:
引理 norm_comm
  条件: {A B : Rep k G} (f : A ⟶ B)
  结论: f ≫ norm B = norm A ≫ f
  证明: by
  ext; simp [Representation.norm, hom_comm_apply]

Depends on / 依赖: Representation, Representation.norm, hom_comm_apply
-/
lemma norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f := by
  ext; simp [Representation.norm, hom_comm_apply]

/-- Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined by
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity functor. -/
@[simps]
/--
Definition of `normNatTrans` / `normNatTrans` 的定义

English:
definition normNatTrans
  signature: : End (𝟭 (Rep k G)) where
  body: norm
  naturality _ _ := norm_comm

中文:
定义 norm自然数Trans
  签名: : End (𝟭 (Rep k G)) where
  定义体: norm
  naturality _ _ := norm_comm
-/
def normNatTrans : End (𝟭 (Rep k G)) where
  app := norm
  naturality _ _ := norm_comm

end

noncomputable section Linearization

variable (k G)

noncomputable section Finsupp

open Finsupp

variable (α : Type u') (A : Rep k G)

variable {k G} in
/--
Definition of `finsupp` / `finsupp` 的定义

English:
abbreviation finsupp
  signature: : Rep k G
  body: Rep.of (Representation.finsupp A.ρ α)

中文:
缩写 finsupp
  签名: : Rep k G
  定义体: Rep.of (Representation.finsupp A.ρ α)

Depends on / 依赖: Rep.of, Representation, Representation.finsupp, finsupp
-/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

/--
lemma `finsupp_V` / 引理 `finsupp_V`

English:
lemma finsupp_V
  statement: (finsupp α A).V = (α ->₀ A.V)
  proof: rfl

中文:
引理 finsupp_V
  结论: (finsupp α A).V = (α ->₀ A.V)
  证明: rfl
-/
@[simp] lemma finsupp_V : (finsupp α A).V = (α ->₀ A.V) := rfl

/--
Definition of `free` / `free` 的定义

English:
abbreviation free
  signature: : Rep k G
  body: Rep.of (Representation.free k G α)

中文:
缩写 free
  签名: : Rep k G
  定义体: Rep.of (Representation.free k G α)

Depends on / 依赖: Rep.of, Representation, Representation.free
-/
abbrev free : Rep k G := Rep.of (Representation.free k G α)

variable {α}

/--
Definition of `freeLift` / `freeLift` 的定义

English:
abbreviation freeLift
  signature: (f : α -> A)
  body: Rep.ofHom (Representation.freeLift A.ρ f)

中文:
缩写 freeLift
  签名: (f : α -> A)
  定义体: Rep.ofHom (Representation.freeLift A.ρ f)

Depends on / 依赖: Rep.ofHom, Representation, Representation.freeLift, freeLift
-/
abbrev freeLift (f : α -> A) :
    free k G α ⟶ A := Rep.ofHom (Representation.freeLift A.ρ f)

variable (α) in
/--
Definition of `freeLiftLEquiv` / `freeLiftLEquiv` 的定义

English:
abbreviation freeLiftLEquiv
  signature: :
  body: homLinearEquiv _ _ ≪≫ₗ Representation.freeLiftLEquiv A.ρ α

中文:
缩写 freeLiftLEquiv
  签名: :
  定义体: homLinearEquiv _ _ ≪≫ₗ Representation.freeLiftLEquiv A.ρ α

Depends on / 依赖: Representation, Representation.freeLiftLEquiv, freeLiftLEquiv, homLinearEquiv
-/
abbrev freeLiftLEquiv :
    (free k G α ⟶ A) ≃ₗ[k] (α -> A) :=
  homLinearEquiv _ _ ≪≫ₗ Representation.freeLiftLEquiv A.ρ α

/--
lemma `free_ext` / 引理 `free_ext`

English:
lemma free_ext
  statement: (f g : free k G α ⟶ A)
  proof: by
  exact (freeLiftLEquiv k G α A).injective (funext_iff.2 h)

中文:
引理 free_ext
  结论: (f g : free k G α ⟶ A)
  证明: by
  exact (freeLiftLEquiv k G α A).injective (funext_iff.2 h)

Depends on / 依赖: freeLiftLEquiv, funext_iff, injective
-/
lemma free_ext (f g : free k G α ⟶ A)
    (h : forall i : α, f.hom (single i (.single 1 1)) = g.hom (single i (.single 1 1))) : f = g := by
  exact (freeLiftLEquiv k G α A).injective (funext_iff.2 h)

variable {A}
section

open MonoidalCategory

variable (A B : Rep.{u} k G) (α : Type u) [DecidableEq α]

open TensorProduct in
/--
Definition of `finsuppTensorLeft` / `finsuppTensorLeft` 的定义

English:
abbreviation finsuppTensorLeft
  signature: : A.finsupp α otimes B ≅ (A otimes B).finsupp α
  body: mkIso (Representation.finsuppTensorLeft A.ρ B.ρ α)

中文:
缩写 finsuppTensorLeft
  签名: : A.finsupp α otimes B ≅ (A otimes B).finsupp α
  定义体: mkIso (Representation.finsuppTensorLeft A.ρ B.ρ α)

Depends on / 依赖: Representation, Representation.finsuppTensorLeft, finsuppTensorLeft
-/
abbrev finsuppTensorLeft : A.finsupp α otimes B ≅ (A otimes B).finsupp α :=
  mkIso (Representation.finsuppTensorLeft A.ρ B.ρ α)

/--
Definition of `finsuppTensorRight` / `finsuppTensorRight` 的定义

English:
abbreviation finsuppTensorRight
  signature: : A otimes B.finsupp α ≅ (A otimes B).finsupp α
  body: mkIso (Representation.finsuppTensorRight A.ρ B.ρ α)

中文:
缩写 finsuppTensorRight
  签名: : A otimes B.finsupp α ≅ (A otimes B).finsupp α
  定义体: mkIso (Representation.finsuppTensorRight A.ρ B.ρ α)

Depends on / 依赖: Representation, Representation.finsuppTensorRight, finsuppTensorRight
-/
abbrev finsuppTensorRight : A otimes B.finsupp α ≅ (A otimes B).finsupp α :=
  mkIso (Representation.finsuppTensorRight A.ρ B.ρ α)

section

variable (k G α : Type u) [DecidableEq α] [CommRing k] [Monoid G]

/--
Definition of `leftRegularTensorTrivialIsoFree` / `leftRegularTensorTrivialIsoFree` 的定义

English:
abbreviation leftRegularTensorTrivialIsoFree
  signature: : leftRegular k G otimes trivial k G k[α] ≅ free k G α
  body: mkIso (Representation.leftRegularTensorTrivialIsoFree α)

中文:
缩写 leftRegularTensorTrivialIsoFree
  签名: : leftRegular k G otimes trivial k G k[α] ≅ free k G α
  定义体: mkIso (Representation.leftRegularTensorTrivialIsoFree α)

Depends on / 依赖: Representation, Representation.leftRegularTensorTrivialIsoFree, leftRegularTensorTrivialIsoFree
-/
abbrev leftRegularTensorTrivialIsoFree : leftRegular k G otimes trivial k G k[α] ≅ free k G α :=
  mkIso (Representation.leftRegularTensorTrivialIsoFree α)

end
end
end Finsupp

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
@[simps]
/--
Definition of `linearization` / `linearization` 的定义

English:
abbreviation linearization
  signature: : Action (Type w) G ⥤ Rep.{max w u} k G where
  body: .of .linearize k G X
map f := Rep.ofHom Representation.linearizeMap f

中文:
缩写 linearization
  签名: : 作用 (类型 w) G ⥤ Rep.{最大值 w u} k G where
  定义体: .of .linearize k G X
map f := Rep.ofHom Representation.linearizeMap f

Depends on / 依赖: linearize
-/
abbrev linearization : Action (Type w) G ⥤ Rep.{max w u} k G where
obj X := .of .linearize k G X
map f := Rep.ofHom Representation.linearizeMap f

open MonoidalCategory Representation.LinearizeMonoidal in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (linearization k G).LaxMonoidal
  body: ofHom (ε k G)
  μ X Y := ofHom (μ X Y)
μ_natural_left f Z := hom_ext μ_comp_rTensor f Z
  μ_natural_right Z f := by ext1; simp [μ_comp_lTensor _]
  associativity X Y Z := by ext1; simp [μ_comp_assoc _]
left_unitality X := hom_ext μ_leftUnitor X
right_unitality X := hom_ext μ_rightUnitor X

中文:
实例 :
  签名: (linearization k G).松弛幺半群
  定义体: ofHom (ε k G)
  μ X Y := ofHom (μ X Y)
μ_natural_left f Z := hom_ext μ_comp_rTensor f Z
  μ_natural_right Z f := by ext1; simp [μ_comp_lTensor _]
  associativity X Y Z := by ext1; simp [μ_comp_assoc _]
left_unitality X := hom_ext μ_leftUnitor X
right_unitality X := hom_ext μ_rightUnitor X
-/
instance : (linearization k G).LaxMonoidal where
  ε := ofHom (ε k G)
  μ X Y := ofHom (μ X Y)
μ_natural_left f Z := hom_ext μ_comp_rTensor f Z
  μ_natural_right Z f := by ext1; simp [μ_comp_lTensor _]
  associativity X Y Z := by ext1; simp [μ_comp_assoc _]
left_unitality X := hom_ext μ_leftUnitor X
right_unitality X := hom_ext μ_rightUnitor X

open MonoidalCategory Representation.LinearizeMonoidal in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (linearization k G).OplaxMonoidal
  body: ofHom (η k G)
  δ X Y := ofHom (δ X Y)
δ_natural_left f Z := hom_ext rTensor_comp_δ Z f
δ_natural_right Z f := hom_ext lTensor_comp_δ Z f
oplax_associativity X Y Z := hom_ext by simpa using assoc_comp_δ X Y Z (k := k)
oplax_left_unitality X := hom_ext leftUnitor_δ X
oplax_right_unitality X := hom_ex

中文:
实例 :
  签名: (linearization k G).反松弛幺半群
  定义体: ofHom (η k G)
  δ X Y := ofHom (δ X Y)
δ_natural_left f Z := hom_ext rTensor_comp_δ Z f
δ_natural_right Z f := hom_ext lTensor_comp_δ Z f
oplax_associativity X Y Z := hom_ext by simpa using assoc_comp_δ X Y Z (k := k)
oplax_left_unitality X := hom_ext leftUnitor_δ X
oplax_right_unitality X := hom_ex
-/
instance : (linearization k G).OplaxMonoidal where
  η := ofHom (η k G)
  δ X Y := ofHom (δ X Y)
δ_natural_left f Z := hom_ext rTensor_comp_δ Z f
δ_natural_right Z f := hom_ext lTensor_comp_δ Z f
oplax_associativity X Y Z := hom_ext by simpa using assoc_comp_δ X Y Z (k := k)
oplax_left_unitality X := hom_ext leftUnitor_δ X
oplax_right_unitality X := hom_ext rightUnitor_δ X

open MonoidalCategory Representation.LinearizeMonoidal in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (linearization k G).Monoidal
  body: hom_ext η_ε k G
η_ε := hom_ext ε_η k G
μ_δ X Y := hom_ext δ_μ (k := k) X Y
δ_μ X Y := hom_ext μ_δ (k := k) X Y

中文:
实例 :
  签名: (linearization k G).幺半群
  定义体: hom_ext η_ε k G
η_ε := hom_ext ε_η k G
μ_δ X Y := hom_ext δ_μ (k := k) X Y
δ_μ X Y := hom_ext μ_δ (k := k) X Y

Depends on / 依赖: hom_ext
-/
instance : (linearization k G).Monoidal where
ε_η := hom_ext η_ε k G
η_ε := hom_ext ε_η k G
μ_δ X Y := hom_ext δ_μ (k := k) X Y
δ_μ X Y := hom_ext μ_δ (k := k) X Y

variable {k G}

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

open scoped MonoidalCategory

section

open MonoidalCategory Representation.LinearizeMonoidal

/--
lemma `μ_def` / 引理 `μ_def`

English:
lemma μ_def
  given: {X Y : Action (Type u) G}
  statement: Functor.LaxMonoidal.μ (linearization k G) X Y =
  proof: rfl

中文:
引理 μ_def
  条件: {X Y : 作用 (类型u) G}
  结论: 函子.松弛幺半群.μ (linearization k G) X Y =
  证明: rfl
-/
lemma μ_def {X Y : Action (Type u) G} : Functor.LaxMonoidal.μ (linearization k G) X Y =
    ofHom (μ X Y) := rfl

/--
lemma `μ_hom` / 引理 `μ_hom`

English:
lemma μ_hom
  given: {X Y : Action (Type u) G}
  statement: (Functor.LaxMonoidal.μ (linearization k G) X Y).hom
  proof: rfl

中文:
引理 μ_hom
  条件: {X Y : 作用 (类型u) G}
  结论: (函子.松弛幺半群.μ (linearization k G) X Y).hom
  证明: rfl
-/
lemma μ_hom {X Y : Action (Type u) G} : (Functor.LaxMonoidal.μ (linearization k G) X Y).hom
    = μ X Y := rfl

/--
lemma `ε_def` / 引理 `ε_def`

English:
lemma ε_def
  statement: Functor.LaxMonoidal.ε (linearization k G) = ofHom (ε k G)
  proof: rfl

中文:
引理 ε_def
  结论: 函子.松弛幺半群.ε (linearization k G) = ofHom (ε k G)
  证明: rfl
-/
lemma ε_def : Functor.LaxMonoidal.ε (linearization k G) = ofHom (ε k G) := rfl

/--
lemma `ε_hom` / 引理 `ε_hom`

English:
lemma ε_hom
  statement: (Functor.LaxMonoidal.ε (linearization k G)).hom = ε k G
  proof: rfl

中文:
引理 ε_hom
  结论: (函子.松弛幺半群.ε (linearization k G)).hom = ε k G
  证明: rfl
-/
lemma ε_hom : (Functor.LaxMonoidal.ε (linearization k G)).hom = ε k G := rfl

/--
lemma `δ_def` / 引理 `δ_def`

English:
lemma δ_def
  given: {X Y : Action (Type u) G}
  statement: Functor.OplaxMonoidal.δ (linearization k G) X Y =
  proof: rfl

中文:
引理 δ_def
  条件: {X Y : 作用 (类型u) G}
  结论: 函子.反松弛幺半群.δ (linearization k G) X Y =
  证明: rfl
-/
lemma δ_def {X Y : Action (Type u) G} : Functor.OplaxMonoidal.δ (linearization k G) X Y =
    ofHom (δ X Y) := rfl

/--
lemma `δ_hom` / 引理 `δ_hom`

English:
lemma δ_hom
  given: {X Y : Action (Type u) G}
  statement: (Functor.OplaxMonoidal.δ (linearization k G) X Y).hom
  proof: rfl

中文:
引理 δ_hom
  条件: {X Y : 作用 (类型u) G}
  结论: (函子.反松弛幺半群.δ (linearization k G) X Y).hom
  证明: rfl
-/
lemma δ_hom {X Y : Action (Type u) G} : (Functor.OplaxMonoidal.δ (linearization k G) X Y).hom
    = δ X Y := rfl

/--
lemma `η_def` / 引理 `η_def`

English:
lemma η_def
  statement: Functor.OplaxMonoidal.η (linearization k G) = ofHom (η k G)
  proof: rfl

中文:
引理 η_def
  结论: 函子.反松弛幺半群.η (linearization k G) = ofHom (η k G)
  证明: rfl
-/
lemma η_def : Functor.OplaxMonoidal.η (linearization k G) = ofHom (η k G) := rfl

/--
lemma `η_hom` / 引理 `η_hom`

English:
lemma η_hom
  statement: (Functor.OplaxMonoidal.η (linearization k G)).hom = η k G
  proof: rfl

中文:
引理 η_hom
  结论: (函子.反松弛幺半群.η (linearization k G)).hom = η k G
  证明: rfl
-/
lemma η_hom : (Functor.OplaxMonoidal.η (linearization k G)).hom = η k G := rfl

end

variable (k G) in
/--
Definition of `linearizationTrivialIso` / `linearizationTrivialIso` 的定义

English:
abbreviation linearizationTrivialIso
  signature: (X : Type u)
  body: Rep.mkIso (Representation.linearizeTrivialIso k G X)

中文:
缩写 linearizationTrivialIso
  签名: (X : 类型u)
  定义体: Rep.mkIso (Representation.linearizeTrivialIso k G X)

Depends on / 依赖: Rep.mkIso, Representation, Representation.linearizeTrivialIso, linearizeTrivialIso
-/
abbrev linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.trivial _ X) ≅ trivial k G k[X] :=
  Rep.mkIso (Representation.linearizeTrivialIso k G X)

variable (k G) in
/--
Definition of `linearizationOfMulActionIso` / `linearizationOfMulActionIso` 的定义

English:
abbreviation linearizationOfMulActionIso
  signature: (H : Type u) [MulAction G H]
  body: Rep.mkIso (Representation.linearizeOfMulActionIso k G H)

中文:
缩写 linearizationOfMulActionIso
  签名: (H : 类型u) [乘法作用 G H]
  定义体: Rep.mkIso (Representation.linearizeOfMulActionIso k G H)

Depends on / 依赖: Rep.mkIso, Representation, Representation.linearizeOfMulActionIso, linearizeOfMulActionIso
-/
abbrev linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Rep.mkIso (Representation.linearizeOfMulActionIso k G H)

/--
Definition of `leftRegularHomEquiv` / `leftRegularHomEquiv` 的定义

English:
abbreviation leftRegularHomEquiv
  signature: (A : Rep k G)
  body: homLinearEquiv _ _ ≪≫ₗ Representation.leftRegularMapEquiv A.ρ

中文:
缩写 leftRegularHomEquiv
  签名: (A : Rep k G)
  定义体: homLinearEquiv _ _ ≪≫ₗ Representation.leftRegularMapEquiv A.ρ

Depends on / 依赖: Representation, Representation.leftRegularMapEquiv, homLinearEquiv, leftRegularMapEquiv
-/
abbrev leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A :=
  homLinearEquiv _ _ ≪≫ₗ Representation.leftRegularMapEquiv A.ρ

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `leftRegularHomEquiv_symm_single` / 定理 `leftRegularHomEquiv_symm_single`

English:
theorem leftRegularHomEquiv_symm_single
  given: {A : Rep k G} (x : A) (g : G)
  proof: by
  simp [homEquiv]

中文:
定理 leftRegularHomEquiv_symm_single
  条件: {A : Rep k G} (x : A) (g : G)
  证明: by
  simp [homEquiv]

Depends on / 依赖: homEquiv
-/
theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (.single g 1) = A.ρ g x := by
  simp [homEquiv]

end Linearization

end

end Rep
