/-
Copyright (c) 2026 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar, Arnoud van der Leer
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveCodiscrete
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# The Coherent Isomorphism

We define the free walking isomorphism `WalkingIso`; the category with objects `zero` and
`one` and unique morphisms `zero ⟶ one` and `one ⟶ zero`. We construct an equivalence
`WalkingIso.equiv` between the type of functors from `WalkingIso` into any category `C` and the type
`Σ (X : C) (Y : C), (X ≅ Y)` of isomorphisms in that category.

The simplicial set `SSet.coherentIso` is defined as the nerve of `WalkingIso`, with
`coherentIso.x₀` and `coherentIso.x₁` the `0`-simplices corresponding to `WalkingIso.zero`
and `WalkingIso.one` respectively, and `coherentIso.hom : Edge x₀ x₁` and
`coherentIso.inv : Edge x₁ x₀` forward and backward edges corresponding to the morphisms in
`WalkingIso`. Given any simplicial set `X`, with a morphism `g : coherentIso ⟶ X`, `0`-simplices
`x₀ x₁: X _⦋0⦌` and an edge between them `f : Edge x₀ x₁`, such that `g` sends `coherentIso.hom` to
`f`, then `f` has an inverse (in the sense of `Edge.InvStruct`), see `invStructOfEqMapHom`.

-/

@[expose] public section

universe w u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as the codiscrete category on `Bool`. -/
/-
**CategoryTheory.WalkingIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：WalkingIso : Type w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the free-living isomorphism as the codiscrete category on `Bool`.
-/
abbrev WalkingIso : Type w := Codiscrete (ULift Bool)

namespace WalkingIso

/-- The underlying type of `WalkingIso` is equivalent to `Bool`, since they both have 2 elements. -/
/-
**CategoryTheory.WalkingIso.equivBool** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
WalkingIso`。
形式化陈述：equivBool : WalkingIso.{w} ≃ Bool
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The underlying type of `WalkingIso` is equivalent to `Bool`, since they both hav
e 2 elements.
-/
def equivBool : WalkingIso.{w} ≃ Bool := codiscreteEquiv.trans Equiv.ulift

section

variable {C : Type u} [Category.{v} C]

/-- The domain of the isomorphism -/
/-
**CategoryTheory.WalkingIso.zero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Walki
ngIso`。
形式化陈述：zero : WalkingIso.{w}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain of the isomorphism
-/
def zero : WalkingIso.{w} := .mk (.up false)

/-- The codomain of the isomorphism -/
/-
**CategoryTheory.WalkingIso.one** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Walkin
gIso`。
形式化陈述：one : WalkingIso.{w}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The codomain of the isomorphism
-/
def one : WalkingIso.{w} := .mk (.up true)

/-- The isomorphism between `zero` and `one` in `WalkingIso`. -/
/-
**CategoryTheory.WalkingIso.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Walkin
gIso`。
形式化陈述：iso : zero.{w} ≅ one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `zero` and `one` in `WalkingIso`.
-/
def iso : zero.{w} ≅ one := Codiscrete.iso zero one
/-
**CategoryTheory.WalkingIso.eq_iso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.WalkingIso`。
形式化陈述：eq_iso_hom (f : zero.{w} ⟶ one) : f = iso.{w}.hom
参数：f : zero.{w} ⟶ one。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Codiscrete.eq_iso_hom`：eq_iso_hom {A : Type u} {x y : Cod
iscrete A} (f : x ⟶ y) : f = (iso x y).hom
-/
lemma eq_iso_hom (f : zero.{w} ⟶ one) : f = iso.{w}.hom := Codiscrete.eq_iso_hom f
/-
**CategoryTheory.WalkingIso.eq_iso_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.WalkingIso`。
形式化陈述：eq_iso_inv (f : one.{w} ⟶ zero) : f = iso.{w}.inv
参数：f : one.{w} ⟶ zero。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Codiscrete.eq_iso_inv`：eq_iso_inv {A : Type u} {x y : Cod
iscrete A} (f : x ⟶ y) : f = (iso y x).inv
-/
lemma eq_iso_inv (f : one.{w} ⟶ zero) : f = iso.{w}.inv := Codiscrete.eq_iso_inv f

/-- Functors out of `WalkingIso` define isomorphisms in the target category. -/
@[simps!]
/-
**CategoryTheory.WalkingIso.toIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Walk
ingIso`。
形式化陈述：toIso (F : WalkingIso.{w} ⥤ C) : F.obj zero ≅ F.obj one
参数：F : WalkingIso.{w} ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functors out of `WalkingIso` define isomorphisms in the target category.
-/
def toIso (F : WalkingIso.{w} ⥤ C) : F.obj zero ≅ F.obj one := F.mapIso iso

section induction

variable {motive : WalkingIso.{u} → Sort*} (zero : motive zero) (one : motive one)

/-- The recursor for WalkingIso, which constructs a term of `∏ (x : WalkingIso), A x` from
a term of `A zero` and a term of `A one`. -/
@[elab_as_elim, induction_eliminator]
/-
**CategoryTheory.WalkingIso.rec** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Walkin
gIso`。
形式化陈述：{motive : CategoryTheory.WalkingIso → Sort u_1} →   motive CategoryTheory.
WalkingIso.zero →     motive CategoryTheory.WalkingIso.one → (a : CategoryTheory
.WalkingIso) → motive a
参数：a : CategoryTheory.WalkingIso。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The recursor for WalkingIso, which constructs a term of `∏ (x : WalkingIso), A x
` from
a term of `A zero` and a term of `A one`.
-/
protected def rec : ∀ a, motive a
  | .mk (.up false) => zero
  | .mk (.up true) => one
/-
**CategoryTheory.WalkingIso.rec_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.W
alkingIso`。
形式化陈述：∀ {motive : CategoryTheory.WalkingIso → Sort u_1} (zero : motive CategoryT
heory.WalkingIso.zero)   (one : motive CategoryTheory.WalkingIso.one),   Categor
yTheory.WalkingIso.rec zero one CategoryTheory.WalkingIso.zero = zero
参数：zero : motive CategoryTheory.WalkingIso.zero；one : motive CategoryTheory.Walk
ingIso.one。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rec_zero : WalkingIso.rec zero one .zero = zero := rfl
/-
**CategoryTheory.WalkingIso.rec_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Wa
lkingIso`。
形式化陈述：∀ {motive : CategoryTheory.WalkingIso → Sort u_1} (zero : motive CategoryT
heory.WalkingIso.zero)   (one : motive CategoryTheory.WalkingIso.one),   Categor
yTheory.WalkingIso.rec zero one CategoryTheory.WalkingIso.one = one
参数：zero : motive CategoryTheory.WalkingIso.zero；one : motive CategoryTheory.Walk
ingIso.one。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma rec_one : WalkingIso.rec zero one .one = one := rfl

end induction

set_option backward.isDefEq.respectTransparency false in
/-- From an isomorphism in a category, we can build a functor out of `WalkingIso` to
that category. -/
/-
**CategoryTheory.WalkingIso.fromIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Wa
lkingIso`。
形式化陈述：fromIso {X Y : C} (e : X ≅ Y) : WalkingIso.{w} ⥤ C where obj x
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From an isomorphism in a category, we can build a functor out of `WalkingIso` to
that category.
-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso.{w} ⥤ C where
  obj x := by induction x; exacts [X, Y]
  map {x y} _ := by induction x <;> induction y; exacts [𝟙 X, e.hom, e.inv, 𝟙 Y]
  map_comp {x y z} _ _ := by induction x <;> induction y <;> induction z <;> simp
  map_id {x} := by induction x <;> rfl

section

variable {X Y : C} (e : X ≅ Y)

@[simp]
/-
**CategoryTheory.WalkingIso.fromIso_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.WalkingIso`。
形式化陈述：fromIso_zero : (fromIso.{w} e).obj .zero = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromIso_zero : (fromIso.{w} e).obj .zero = X := rfl

@[simp]
/-
**CategoryTheory.WalkingIso.fromIso_one** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.WalkingIso`。
形式化陈述：fromIso_one : (fromIso.{w} e).obj .one = Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromIso_one : (fromIso.{w} e).obj .one = Y := rfl

@[simp]
/-
**CategoryTheory.WalkingIso.fromIso_map_zero_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.WalkingIso`。
形式化陈述：fromIso_map_zero_zero (f : zero ⟶ zero) : (fromIso.{w} e).map f = 𝟙 X
参数：f : zero ⟶ zero。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromIso_map_zero_zero (f : zero ⟶ zero) : (fromIso.{w} e).map f = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.WalkingIso.fromIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.WalkingIso`。
形式化陈述：fromIso_hom (f : zero ⟶ one) : (fromIso.{w} e).map f = e.hom
参数：f : zero ⟶ one。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromIso_hom (f : zero ⟶ one) : (fromIso.{w} e).map f = e.hom := rfl

@[simp]
/-
**CategoryTheory.WalkingIso.fromIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.WalkingIso`。
形式化陈述：fromIso_inv (f : one ⟶ zero) : (fromIso.{w} e).map f = e.inv
参数：f : one ⟶ zero。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromIso_inv (f : one ⟶ zero) : (fromIso.{w} e).map f = e.inv := rfl

@[simp]
/-
**CategoryTheory.WalkingIso.fromIso_map_one_one** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.WalkingIso`。
形式化陈述：fromIso_map_one_one (f : one ⟶ one) : (fromIso.{w} e).map f = 𝟙 Y
参数：f : one ⟶ one。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromIso_map_one_one (f : one ⟶ one) : (fromIso.{w} e).map f = 𝟙 Y := rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
@[simps]
/-
**CategoryTheory.WalkingIso.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Walk
ingIso`。
形式化陈述：equiv : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between the type of `WalkingIso`s in `C` and the type of isomorph
isms in `C`.
-/
def equiv : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := Functor.ext (by rintro (_ | _) <;> rfl) <| by
      intro X Y f
      induction X <;>
      induction Y <;>
      simp [Codiscrete.eq_id] <;>
      rfl

end

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge

/-- The simplicial set that encodes a single isomorphism.
Its n-simplices are formal compositions of arrows in WalkingIso. -/
/-
**SSet.coherentIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：coherentIso : SSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial set that encodes a single isomorphism.
Its n-simplices are formal compositions of arrows in WalkingIso.
-/
abbrev coherentIso : SSet := nerve WalkingIso.{u}

namespace coherentIso

/-- The source vertex of `coherentIso`. -/
/-
**SSet.coherentIso.x** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The source vertex of `coherentIso`.
-/
def x₀ : coherentIso.{u} _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero

/-- The target vertex of `coherentIso`. -/
/-
**SSet.coherentIso.x** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The target vertex of `coherentIso`.
-/
def x₁ : coherentIso.{u} _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one

/-- The forwards edge of `coherentIso`. -/
/-
**SSet.coherentIso.hom** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
形式化陈述：hom : Edge.{u} x₀ x₁ where edge
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forwards edge of `coherentIso`.
-/
def hom : Edge.{u} x₀ x₁ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.hom
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
/-
**SSet.coherentIso.inv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
形式化陈述：inv : Edge.{u} x₁ x₀ where edge
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The backwards edge of `coherentIso`.
-/
def inv : Edge.{u} x₁ x₀ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.inv
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
/-
**SSet.coherentIso.homInvId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
形式化陈述：homInvId : Edge.CompStruct.{u} hom inv (Edge.id x₀) where simplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forwards and backwards edge of `coherentIso` compose to the identity.
-/
def homInvId : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.hom WalkingIso.iso.inv
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
/-
**SSet.coherentIso.invHomId** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
形式化陈述：invHomId : Edge.CompStruct.{u} inv hom (Edge.id x₁) where simplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The backwards and forwards edge of `coherentIso` compose to the identity.
-/
def invHomId : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.inv WalkingIso.iso.hom
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` has an inverse. -/
@[simps]
/-
**SSet.coherentIso.invStructHom** 是 Mathlib 中的一个定义，位于命名空间 `SSet.coherentIso`。
形式化陈述：invStructHom : Edge.InvStruct.{u} coherentIso.hom where inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forwards edge of `coherentIso` has an inverse.
-/
def invStructHom : Edge.InvStruct.{u} coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- For a simplicial set `X`, if an edge in `X` is equal to the image of `hom`
under a morphism of simplicial sets, this edge has an inverse. -/
/-
**SSet.coherentIso.invStructOfEqMapHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.coheren
tIso`。
形式化陈述：invStructOfEqMapHom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {f : Edge x₀ x₁} {g : 
coherentIso ⟶ X} (hfg : f.edge = g.app _ hom.edge) : f.InvStruct
参数：hfg : f.edge = g.app _ hom.edge。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a simplicial set `X`, if an edge in `X` is equal to the image of `hom`
under a morphism of simplicial sets, this edge has an inverse.
-/
abbrev invStructOfEqMapHom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {f : Edge x₀ x₁}
    {g : coherentIso ⟶ X}
    (hfg : f.edge = g.app _ hom.edge) :
    f.InvStruct :=
  (invStructHom.map g).ofEq hfg.symm

end coherentIso

end SSet

