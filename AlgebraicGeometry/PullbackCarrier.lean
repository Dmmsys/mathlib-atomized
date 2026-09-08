/-
Copyright (c) 2024 Qi Ge, Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Ge, Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.LinearAlgebra
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Underlying topological space of fibre product of schemes

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes. In this file we describe the underlying
topological space of `pullback f g`, i.e. the fiber product `X ×[S] Y`.

## Main results

- `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: The bijective correspondence between the points
  of `X ×[S] Y` and pairs `(z, p)` of triples `z = (x, y, s)` with `f x = s = g y` and
  prime ideals `q` of `κ(x) ⊗[κ(s)] κ(y)`.
- `AlgebraicGeometry.Scheme.Pullback.exists_preimage`: For every triple `(x, y, s)` with
  `f x = s = g y`, there exists `z : X ×[S] Y` lying above `x` and `y`.

We also give the ranges of `pullback.fst`, `pullback.snd` and `pullback.map`.

-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace IsLocalRing TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- A `Triplet` over `f : X ⟶ S` and `g : Y ⟶ S` is a triple of points `x : X`, `y : Y`,
`s : S` such that `f x = s = f y`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：{X Y S : AlgebraicGeometry.Scheme} → (X ⟶ S) → (Y ⟶ S) → Type u
参数：X ⟶ S；Y ⟶ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Triplet` over `f : X ⟶ S` and `g : Y ⟶ S` is a triple of points `x : X`, `y :
 Y`,
`s : S` such that `f x = s = f y`.
-/
structure Triplet {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  /-- The point of `X`. -/
  x : X
  /-- The point of `Y`. -/
  y : Y
  /-- The point of `S` below `x` and `y`. -/
  s : S
  hx : f x = s
  hy : g y = s

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Triplet

@[ext]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.ext** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : Alge
braicGeometry.Scheme.Pullback.Triplet f g},   t₁.x = t₂.x → t₁.y = t₂.y → t₁ = t
₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.mk.injEq`：∀ {X Y S : Algebraic
Geometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (x : ↥X) (y : ↥Y) (s : ↥S) (hx : f x = 
s) (hy : g y = s)   (x_1 : ↥X) (y_1 : ↥Y…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma ext {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y) : t₁ = t₂ := by
  cases t₁; cases t₂; simp; aesop

/-- Make a triplet from `x : X` and `y : Y` such that `f x = g y`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：mk' (x : X) (y : Y) (h : f x = g y) : Triplet f g where x
参数：x : X；y : Y；h : f x = g y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a triplet from `x : X` and `y : Y` such that `f x = g y`.
-/
def mk' (x : X) (y : Y) (h : f x = g y) : Triplet f g where
  x := x
  y := y
  s := g y
  hx := h
  hy := rfl

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is `κ(x) ⊗[κ(s)] κ(y)`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensor** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensor (T : Triplet f g) : CommRingCat
参数：T : Triplet f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s

--- 原说明 ---
Given `x : X` and `y : Y` such that `f x = s = g y`, this is `κ(x) ⊗[κ(s)] κ(y)`
.
-/
def tensor (T : Triplet f g) : CommRingCat :=
  pushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.** 是 Mathlib 中的一个实例，位于命名空间 `Algebrai
cGeometry.Scheme.Pullback.Triplet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (T : Triplet f g) : Nontrivial T.tensor :=
  CommRingCat.nontrivial_of_isPushout_of_isField (Field.toIsField _)
    (IsPushout.of_hasPushout _ _)

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is the
canonical map `κ(x) ⟶ κ(x) ⊗[κ(s)] κ(y)`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorInl** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorInl (T : Triplet f g) : X.residueField T.x ⟶ T.tensor
参数：T : Triplet f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s

--- 原说明 ---
Given `x : X` and `y : Y` such that `f x = s = g y`, this is the
canonical map `κ(x) ⟶ κ(x) ⊗[κ(s)] κ(y)`.
-/
def tensorInl (T : Triplet f g) : X.residueField T.x ⟶ T.tensor := pushout.inl _ _

/-- Given `x : X` and `y : Y` such that `f x = s = g y`, this is the
canonical map `κ(y) ⟶ κ(x) ⊗[κ(s)] κ(y)`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorInr** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorInr (T : Triplet f g) : Y.residueField T.y ⟶ T.tensor
参数：T : Triplet f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s

--- 原说明 ---
Given `x : X` and `y : Y` such that `f x = s = g y`, this is the
canonical map `κ(y) ⟶ κ(x) ⊗[κ(s)] κ(y)`.
-/
def tensorInr (T : Triplet f g) : Y.residueField T.y ⟶ T.tensor := pushout.inr _ _
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.isPullback_SpecMap_tensor** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：isPullback_SpecMap_tensor (T : Triplet f g) : CategoryTheory.IsPullback (S
pec.map T.tensorInl) (Spec.map T.tensorInr) (Spec.map ((S.residueFieldCongr T.hx
).inv ≫ f.residueFieldMap T.x)) (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.re
sidueFieldMap T.y))
参数：T : Triplet f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.isPullback_SpecMap_pushout`：isPullback_SpecMap_pushout
 {A B C : CommRingCat} (f : A ⟶ B) (g : A ⟶ C) : IsPullback (Spec.map (pushout.i
nl f g)) (Spec.map (pushout.inr f …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s
-/
lemma isPullback_SpecMap_tensor (T : Triplet f g) : CategoryTheory.IsPullback
    (Spec.map T.tensorInl) (Spec.map T.tensorInr)
        (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
          (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
  isPullback_SpecMap_pushout _ _

section Congr

/-- Given propositionally equal triplets `T₁` and `T₂` over `f` and `g`, the corresponding
`T₁.tensor` and `T₂.tensor` are isomorphic. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorCongr {T₁ T₂ : Triplet f g} (e : T₁ = T₂) : T₁.tensor ≅ T₂.tensor
参数：e : T₁ = T₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given propositionally equal triplets `T₁` and `T₂` over `f` and `g`, the corresp
onding
`T₁.tensor` and `T₂.tensor` are isomorphic.
-/
def tensorCongr {T₁ T₂ : Triplet f g} (e : T₁ = T₂) :
    T₁.tensor ≅ T₂.tensor :=
  eqToIso (by subst e; rfl)

@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr_refl** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorCongr_refl {x : Triplet f g} : tensorCongr (refl x) = Iso.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
lemma tensorCongr_refl {x : Triplet f g} :
    tensorCongr (refl x) = Iso.refl _ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr_symm** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorCongr_symm {x y : Triplet f g} (e : x = y) : (tensorCongr e).symm = 
tensorCongr e.symm
参数：e : x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorCongr_symm {x y : Triplet f g} (e : x = y) :
    (tensorCongr e).symm = tensorCongr e.symm := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr_inv** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorCongr_inv {x y : Triplet f g} (e : x = y) : (tensorCongr e).inv = (t
ensorCongr e.symm).hom
参数：e : x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorCongr_inv {x y : Triplet f g} (e : x = y) :
    (tensorCongr e).inv = (tensorCongr e.symm).hom := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr_trans** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorCongr_trans {x y z : Triplet f g} (e : x = y) (e' : y = z) : tensorC
ongr e ≪≫ tensorCongr e' = tensorCongr (e.trans e')
参数：e : x = y；e' : y = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma tensorCongr_trans {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    tensorCongr e ≪≫ tensorCongr e' =
      tensorCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr_trans_hom** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：tensorCongr_trans_hom {x y z : Triplet f g} (e : x = y) (e' : y = z) : (te
nsorCongr e).hom ≫ (tensorCongr e').hom = (tensorCongr (e.trans e')).hom
参数：e : x = y；e' : y = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma tensorCongr_trans_hom {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    (tensorCongr e).hom ≫ (tensorCongr e').hom =
      (tensorCongr (e.trans e')).hom := by
  subst e e'
  rfl

end Congr

variable (T : Triplet f g)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.SpecMap_tensorInl_fromSpecResidueFie
ld** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：SpecMap_tensorInl_fromSpecResidueField : (Spec.map T.tensorInl ≫ X.fromSpe
cResidueField T.x) ≫ f = (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) ≫ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField`：residue
FieldCongr_fromSpecResidueField {x y : X} (h : x = y) : Spec.map (X.residueField
Congr h).hom ≫ X.fromSpecResidueField _ = X.fromSpecR…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SpecMap_tensorInl_fromSpecResidueField :
    (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x) ≫ f =
      (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) ≫ g := by
  simp only [residueFieldCongr_inv, Category.assoc, tensorInl, tensorInr,
    ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← residueFieldCongr_fromSpecResidueField T.hx.symm,
    ← residueFieldCongr_fromSpecResidueField T.hy.symm]
  simp only [← Category.assoc, ← Spec.map_comp, pushout.condition]

/-- Given `x : X`, `y : Y` and `s : S` such that `f x = s = g y`,
this is `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×ₛ Y`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.SpecTensorTo** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：SpecTensorTo : Spec T.tensor ⟶ pullback f g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecMap_tensorInl_fromSpecResi
dueField`：SpecMap_tensorInl_fromSpecResidueField : (Spec.map T.tensorInl ≫ X.fro
mSpecResidueField T.x) ≫ f = (Spec.map T.tensorInr ≫ Y.fromSpecResidue…

--- 原说明 ---
Given `x : X`, `y : Y` and `s : S` such that `f x = s = g y`,
this is `Spec (κ(x) ⊗[κ(s)] κ(y)) ⟶ X ×ₛ Y`.
-/
def SpecTensorTo : Spec T.tensor ⟶ pullback f g :=
  pullback.lift (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x)
    (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y)
    (SpecMap_tensorInl_fromSpecResidueField _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.fst_SpecTensorTo_apply** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：fst_SpecTensorTo_apply (p : Spec T.tensor) : pullback.fst f g (T.SpecTenso
rTo p) = T.x
参数：p : Spec T.tensor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecMap_tensorInl_fromSpecResi
dueField`：SpecMap_tensorInl_fromSpecResidueField : (Spec.map T.tensorInl ≫ X.fro
mSpecResidueField T.x) ≫ f = (Spec.map T.tensorInr ≫ Y.fromSpecResidue…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fst_SpecTensorTo_apply (p : Spec T.tensor) :
    pullback.fst f g (T.SpecTensorTo p) = T.x := by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.snd_SpecTensorTo_apply** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：snd_SpecTensorTo_apply (p : Spec T.tensor) : pullback.snd f g (T.SpecTenso
rTo p) = T.y
参数：p : Spec T.tensor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecMap_tensorInl_fromSpecResi
dueField`：SpecMap_tensorInl_fromSpecResidueField : (Spec.map T.tensorInl ≫ X.fro
mSpecResidueField T.x) ≫ f = (Spec.map T.tensorInr ≫ Y.fromSpecResidue…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_SpecTensorTo_apply (p : Spec T.tensor) :
    pullback.snd f g (T.SpecTensorTo p) = T.y := by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.specTensorTo_fst** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：specTensorTo_fst : T.SpecTensorTo ≫ pullback.fst f g = Spec.map T.tensorIn
l ≫ X.fromSpecResidueField T.x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecMap_tensorInl_fromSpecResi
dueField`：SpecMap_tensorInl_fromSpecResidueField : (Spec.map T.tensorInl ≫ X.fro
mSpecResidueField T.x) ≫ f = (Spec.map T.tensorInr ≫ Y.fromSpecResidue…
-/
lemma specTensorTo_fst :
    T.SpecTensorTo ≫ pullback.fst f g = Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.specTensorTo_snd** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：specTensorTo_snd : T.SpecTensorTo ≫ pullback.snd f g = Spec.map T.tensorIn
r ≫ Y.fromSpecResidueField T.y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecMap_tensorInl_fromSpecResi
dueField`：SpecMap_tensorInl_fromSpecResidueField : (Spec.map T.tensorInl ≫ X.fro
mSpecResidueField T.x) ≫ f = (Spec.map T.tensorInr ≫ Y.fromSpecResidue…
-/
lemma specTensorTo_snd :
    T.SpecTensorTo ≫ pullback.snd f g = Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y :=
  pullback.lift_snd _ _ _

/-- Given `t : X ×[S] Y`, it maps to `X` and `Y` with same image in `S`, yielding a
`Triplet f g`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：ofPoint (t : ↑(pullback f g)) : Triplet f g
参数：t : ↑(pullback f g)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g

--- 原说明 ---
Given `t : X ×[S] Y`, it maps to `X` and `Y` with same image in `S`, yielding a
`Triplet f g`.
-/
def ofPoint (t : ↑(pullback f g)) : Triplet f g :=
  ⟨pullback.fst f g t, pullback.snd f g t, _, rfl,
    congr($(pullback.condition (f := f) (g := g)) t).symm⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint_SpecTensorTo** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：ofPoint_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) : ofPoint (T.Sp
ecTensorTo p) = T
参数：T : Triplet f g；p : Spec T.tensor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.ext`：∀ {X Y S : AlgebraicGeome
try.Scheme} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : AlgebraicGeometry.Scheme.Pullback.T
riplet f g},   t₁.x = t₂.x → t₁.y =…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint_x`：∀ {X Y S : Algebrai
cGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (t : ↥(CategoryTheory.Limits.pullback 
f g)),   (AlgebraicGeometry.Scheme.Pullba…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.fst_SpecTensorTo_apply`：fst_Sp
ecTensorTo_apply (p : Spec T.tensor) : pullback.fst f g (T.SpecTensorTo p) = T.x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint_y`：∀ {X Y S : Algebrai
cGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (t : ↥(CategoryTheory.Limits.pullback 
f g)),   (AlgebraicGeometry.Scheme.Pullba…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.snd_SpecTensorTo_apply`：snd_Sp
ecTensorTo_apply (p : Spec T.tensor) : pullback.snd f g (T.SpecTensorTo p) = T.y
-/
lemma ofPoint_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    ofPoint (T.SpecTensorTo p) = T := by
  ext <;> simp

end Triplet

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoin
t** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：residueFieldCongr_inv_residueFieldMap_ofPoint (t : ↑(pullback f g)) : ((S.
residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ f.residueFieldMap (Triplet.ofPoi
nt t).x) ≫ (pullback.fst f g).residueFieldMap t = ((S.residueFieldCongr (Triplet
.ofPoint t).hy).inv ≫ g.residueFieldMap (Triplet.ofPoint t).y) ≫ (pullback.snd f
 g).residueFieldMap t
参数：t : ↑(pullback f g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr`：∀ {X Y : AlgebraicGe
ometry.Scheme} {f g : X ⟶ Y} (e : f = g) (x : ↥X),   AlgebraicGeometry.Scheme.Ho
m.residueFieldMap f x =     CategoryTheo…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma residueFieldCongr_inv_residueFieldMap_ofPoint (t : ↑(pullback f g)) :
    ((S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ f.residueFieldMap (Triplet.ofPoint t).x) ≫
      (pullback.fst f g).residueFieldMap t = ((S.residueFieldCongr (Triplet.ofPoint t).hy).inv ≫
          g.residueFieldMap (Triplet.ofPoint t).y) ≫ (pullback.snd f g).residueFieldMap t := by
  simp [← residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr pullback.condition]

/-- Given `t : X ×[S] Y` with projections to `X`, `Y` and `S` denoted by `x`, `y` and `s`
respectively, this is the canonical map `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.ofPointTensor** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.Pullback`。
形式化陈述：ofPointTensor (t : ↑(pullback f g)) : (Triplet.ofPoint t).tensor ⟶ (pullba
ck f g).residueField t
参数：t : ↑(pullback f g)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_
ofPoint`：residueFieldCongr_inv_residueFieldMap_ofPoint (t : ↑(pullback f g)) : (
(S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ f.residueFieldMap …

--- 原说明 ---
Given `t : X ×[S] Y` with projections to `X`, `Y` and `S` denoted by `x`, `y` an
d `s`
respectively, this is the canonical map `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)`.
-/
def ofPointTensor (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).tensor ⟶ (pullback f g).residueField t :=
  pushout.desc
    ((pullback.fst f g).residueFieldMap t)
    ((pullback.snd f g).residueFieldMap t)
    (residueFieldCongr_inv_residueFieldMap_ofPoint t)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Pullback.ofPointTensor_SpecTensorTo** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：ofPointTensor_SpecTensorTo (t : ↑(pullback f g)) : Spec.map (ofPointTensor
 t) ≫ (Triplet.ofPoint t).SpecTensorTo = (pullback f g).fromSpecResidueField t
参数：t : ↑(pullback f g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueFiel
d`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   CategoryTheory.Cat
egoryStruct.comp (AlgebraicGeometry.Spec.map (AlgebraicGeometry…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.specTensorTo_fst`：specTensorTo
_fst : T.SpecTensorTo ≫ pullback.fst f g = Spec.map T.tensorInl ≫ X.fromSpecResi
dueField T.x
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_
ofPoint`：residueFieldCongr_inv_residueFieldMap_ofPoint (t : ↑(pullback f g)) : (
(S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ f.residueFieldMap …
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.specTensorTo_snd`：specTensorTo
_snd : T.SpecTensorTo ≫ pullback.snd f g = Spec.map T.tensorInr ≫ Y.fromSpecResi
dueField T.y
· 使用定理 `CategoryTheory.Limits.pushout.inr_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
lemma ofPointTensor_SpecTensorTo (t : ↑(pullback f g)) :
    Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo =
      (pullback f g).fromSpecResidueField t := by
  apply pullback.hom_ext
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_fst]
    rw [← pushout.inl_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t), Spec.map_comp]
    rfl
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_snd]
    rw [← pushout.inr_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t), Spec.map_comp]
    rfl

/-- If `t` is a point in `X ×[S] Y` above `(x, y, s)`, then this is the image of the unique
point of `Spec κ(s)` in `Spec κ(x) ⊗[κ(s)] κ(y)`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.SpecOfPoint** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Pullback`。
形式化陈述：SpecOfPoint (t : ↑(pullback f g)) : Spec (Triplet.ofPoint t).tensor
参数：t : ↑(pullback f g)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g

--- 原说明 ---
If `t` is a point in `X ×[S] Y` above `(x, y, s)`, then this is the image of the
 unique
point of `Spec κ(s)` in `Spec κ(x) ⊗[κ(s)] κ(y)`.
-/
def SpecOfPoint (t : ↑(pullback f g)) : Spec (Triplet.ofPoint t).tensor :=
    Spec.map (ofPointTensor t) (⊥ : PrimeSpectrum _)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.SpecTensorTo_SpecOfPoint** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：SpecTensorTo_SpecOfPoint (t : ↑(pullback f g)) : (Triplet.ofPoint t).SpecT
ensorTo (SpecOfPoint t) = t
参数：t : ↑(pullback f g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.ofPointTensor_SpecTensorTo`：ofPointTen
sor_SpecTensorTo (t : ↑(pullback f g)) : Spec.map (ofPointTensor t) ≫ (Triplet.o
fPoint t).SpecTensorTo = (pullback f g).fromSpecRe…
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma SpecTensorTo_SpecOfPoint (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).SpecTensorTo (SpecOfPoint t) = t := by
  simp [SpecOfPoint, ← Scheme.Hom.comp_apply, ofPointTensor_SpecTensorTo]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Pullback.tensorCongr_SpecTensorTo** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：tensorCongr_SpecTensorTo {T T' : Triplet f g} (h : T = T') : Spec.map (Tri
plet.tensorCongr h).hom ≫ T.SpecTensorTo = T'.SpecTensorTo
参数：h : T = T'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorCongr_SpecTensorTo {T T' : Triplet f g} (h : T = T') :
    Spec.map (Triplet.tensorCongr h).hom ≫ T.SpecTensorTo = T'.SpecTensorTo := by
  subst h
  simp only [Triplet.tensorCongr_refl, Iso.refl_hom, Spec.map_id, Category.id_comp]
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.Spec_ofPointTensor_SpecTensorTo** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : Algebrai
cGeometry.Scheme.Pullback.Triplet f g)   (p : ↥(AlgebraicGeometry.Spec T.tensor)
),   CategoryTheory.CategoryStruct.comp       (AlgebraicGeometry.Spec.map (Algeb
raicGeometry.Scheme.Hom.residueFieldMap T.SpecTensorTo p))       (CategoryTheory
.CategoryStruct.comp         (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Sche
me.Pullback.ofPointTensor (T.SpecTensorTo p)))         (AlgebraicGeometry.Spec.m
ap (AlgebraicGeometry.Scheme.Pullback.Triplet.tensorCongr ⋯).hom)) =     (Algebr
aicGeometry.Spec T.tensor).fromSpecResidueField p
参数：T : AlgebraicGeometry.Scheme.Pullback.Triplet f g；p : ↥(AlgebraicGeometry.Spe
c T.tensor)；AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Hom.residueFiel
dMap T.SpecTensorTo p)；CategoryTheory.CategoryStruct.comp         (AlgebraicGeom
etry.Spec.map (AlgebraicGeometry.Scheme.Pullback.ofPointTensor (T.SpecTensorTo p
)))         (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Pullback.Tripl
et.tensorCongr ⋯).hom)；AlgebraicGeometry.Spec T.tensor。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hx`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   f self.x = self.s
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.hy`：∀ {X Y S : AlgebraicGeomet
ry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (self : AlgebraicGeometry.Scheme.Pullback.Tri
plet f g),   g self.y = self.s
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.isPullback_SpecMap_tensor`：isP
ullback_SpecMap_tensor (T : Triplet f g) : CategoryTheory.IsPullback (Spec.map T
.tensorInl) (Spec.map T.tensorInr) (Spec.map ((S.residueF…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint_SpecTensorTo`：ofPoint_
SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) : ofPoint (T.SpecTensorTo p) 
= T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.Scheme.instIsPreimmersionFromSpecResidueField`：∀ {X : 
AlgebraicGeometry.Scheme} (x : ↥X), AlgebraicGeometry.IsPreimmersion (X.fromSpec
ResidueField x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.specTensorTo_fst`：specTensorTo
_fst : T.SpecTensorTo ≫ pullback.fst f g = Spec.map T.tensorInl ≫ X.fromSpecResi
dueField T.x
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.tensorCongr_SpecTensorTo_assoc`：∀ {X Y
 S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} {T T' : AlgebraicGeometry
.Scheme.Pullback.Triplet f g}   (h : T = T') {Z : Alge…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueFiel
d_assoc`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X) {Z : AlgebraicG
eometry.Scheme} (h : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (Al…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.ofPointTensor_SpecTensorTo_assoc`：∀ {X
 Y S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (t : ↥(CategoryTheory.L
imits.pullback f g))   {Z : AlgebraicGeometry.Scheme} (h…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.specTensorTo_snd`：specTensorTo
_snd : T.SpecTensorTo ≫ pullback.snd f g = Spec.map T.tensorInr ≫ Y.fromSpecResi
dueField T.y
-/
lemma Triplet.Spec_ofPointTensor_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    Spec.map (Hom.residueFieldMap T.SpecTensorTo p) ≫
      Spec.map (ofPointTensor (T.SpecTensorTo p)) ≫
      Spec.map (tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom =
    (Spec T.tensor).fromSpecResidueField p := by
  apply T.isPullback_SpecMap_tensor.hom_ext
  · rw [← cancel_mono <| X.fromSpecResidueField T.x]
    simp_rw [Category.assoc, ← T.specTensorTo_fst, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, ofPointTensor_SpecTensorTo_assoc]
  · rw [← cancel_mono <| Y.fromSpecResidueField T.y]
    simp_rw [Category.assoc, ← T.specTensorTo_snd, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, ofPointTensor_SpecTensorTo_assoc]

/-- A helper lemma to work with `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.carrierEquiv_eq_iff** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：carrierEquiv_eq_iff {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor} : T₁ = T₂ ↔
 exists e : T₁.1 = T₂.1, Spec.map (Triplet.tensorCongr e).inv T₁.2 = T₂.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
A helper lemma to work with `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`.
-/
lemma carrierEquiv_eq_iff {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔ ∃ e : T₁.1 = T₂.1, Spec.map (Triplet.tensorCongr e).inv T₁.2 = T₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨T, _⟩ := T₁
    obtain ⟨T', _⟩ := T₂
    rintro ⟨rfl : T = T', e⟩
    simpa [e]

set_option backward.isDefEq.respectTransparency.types false in
/--
The points of the underlying topological space of `X ×[S] Y` bijectively correspond to
pairs of triples `x : X`, `y : Y`, `s : S` with `f x = s = f y` and prime ideals of
`κ(x) ⊗[κ(s)] κ(y)`.
-/
/-
**AlgebraicGeometry.Scheme.Pullback.carrierEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Pullback`。
形式化陈述：carrierEquiv : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where to
Fun t
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.SpecTensorTo_SpecOfPoint`：SpecTensorTo
_SpecOfPoint (t : ↑(pullback f g)) : (Triplet.ofPoint t).SpecTensorTo (SpecOfPoi
nt t) = t

--- 原说明 ---
The points of the underlying topological space of `X ×[S] Y` bijectively corresp
ond to
pairs of triples `x : X`, `y : Y`, `s : S` with `f x = s = f y` and prime ideals
 of
`κ(x) ⊗[κ(s)] κ(y)`.
-/
def carrierEquiv : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  toFun t := ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo T.2
  left_inv := SpecTensorTo_SpecOfPoint
  right_inv := by
    intro ⟨T, p⟩
    apply carrierEquiv_eq_iff.mpr
    use T.ofPoint_SpecTensorTo p
    have : Spec.map (Hom.residueFieldMap T.SpecTensorTo p) (⊥ : PrimeSpectrum _) =
        (⊥ : PrimeSpectrum _) :=
      (PrimeSpectrum.instUnique).uniq _
    simp only [SpecOfPoint, Triplet.tensorCongr_inv, ← this, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply]
    simp [Triplet.Spec_ofPointTensor_SpecTensorTo]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.carrierEquiv_symm_fst** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：carrierEquiv_symm_fst (T : Triplet f g) (p : Spec T.tensor) : pullback.fst
 f g (carrierEquiv.symm ⟨T, p⟩) = T.x
参数：T : Triplet f g；p : Spec T.tensor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.fst_SpecTensorTo_apply`：fst_Sp
ecTensorTo_apply (p : Spec T.tensor) : pullback.fst f g (T.SpecTensorTo p) = T.x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma carrierEquiv_symm_fst (T : Triplet f g) (p : Spec T.tensor) :
    pullback.fst f g (carrierEquiv.symm ⟨T, p⟩) = T.x := by
  simp [carrierEquiv]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Pullback.carrierEquiv_symm_snd** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：carrierEquiv_symm_snd (T : Triplet f g) (p : Spec T.tensor) : pullback.snd
 f g (carrierEquiv.symm ⟨T, p⟩) = T.y
参数：T : Triplet f g；p : Spec T.tensor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.Triplet.snd_SpecTensorTo_apply`：snd_Sp
ecTensorTo_apply (p : Spec T.tensor) : pullback.snd f g (T.SpecTensorTo p) = T.y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma carrierEquiv_symm_snd (T : Triplet f g) (p : Spec T.tensor) :
    pullback.snd f g (carrierEquiv.symm ⟨T, p⟩) = T.y := by
  simp [carrierEquiv]

/-- Given a triple `(x, y, s)` with `f x = s = f y` there exists `t : X ×[S] Y` above
`x` and `ỳ`. For the unpacked version without `Triplet`, see
`AlgebraicGeometry.Scheme.Pullback.exists_preimage`. -/
/-
**AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.Pullback.Triplet`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : Algebrai
cGeometry.Scheme.Pullback.Triplet f g),   ∃ t, (CategoryTheory.Limits.pullback.f
st f g) t = T.x ∧ (CategoryTheory.Limits.pullback.snd f g) t = T.y
参数：T : AlgebraicGeometry.Scheme.Pullback.Triplet f g；CategoryTheory.Limits.pullb
ack.fst f g；CategoryTheory.Limits.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgebraicGeometry.instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialC
arrier`：∀ {A : CommRingCat} [Nontrivial ↑A], Nonempty ↥(AlgebraicGeometry.Spec A
)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.instNontrivialCarrierTensor`：∀
 {X Y S : AlgebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : AlgebraicGeomet
ry.Scheme.Pullback.Triplet f g),   Nontrivial ↑T.tensor
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.carrierEquiv_symm_fst`：carrierEquiv_sy
mm_fst (T : Triplet f g) (p : Spec T.tensor) : pullback.fst f g (carrierEquiv.sy
mm ⟨T, p⟩) = T.x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.carrierEquiv_symm_snd`：carrierEquiv_sy
mm_snd (T : Triplet f g) (p : Spec T.tensor) : pullback.snd f g (carrierEquiv.sy
mm ⟨T, p⟩) = T.y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Given a triple `(x, y, s)` with `f x = s = f y` there exists `t : X ×[S] Y` abov
e
`x` and `ỳ`. For the unpacked version without `Triplet`, see
`AlgebraicGeometry.Scheme.Pullback.exists_preimage`.
-/
lemma Triplet.exists_preimage (T : Triplet f g) :
    ∃ t : ↑(pullback f g), pullback.fst f g t = T.x ∧ pullback.snd f g t = T.y :=
  ⟨carrierEquiv.symm ⟨T, Nonempty.some inferInstance⟩, by simp⟩

/--
If `f : X ⟶ S` and `g : Y ⟶ S` are morphisms of schemes and `x : X` and `y : Y` are points such
that `f x = g y`, then there exists `z : X ×[S] Y` lying above `x` and `y`.

In other words, the map from the underlying topological space of `X ×[S] Y` to the fiber product
of the underlying topological spaces of `X` and `Y` over `S` is surjective.
-/
/-
**AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：exists_preimage_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pu
llback f g), pullback.fst f g z = x ∧ pullback.snd f g z = y
参数：x : X；y : Y；h : f x = g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage`：∀ {X Y S : Al
gebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : AlgebraicGeometry.Scheme.Pu
llback.Triplet f g),   ∃ t, (CategoryTheory.Lim…

--- 原说明 ---
If `f : X ⟶ S` and `g : Y ⟶ S` are morphisms of schemes and `x : X` and `y : Y` 
are points such
that `f x = g y`, then there exists `z : X ×[S] Y` lying above `x` and `y`.

In other words, the map from the underlying topological space of `X ×[S] Y` to t
he fiber product
of the underlying topological spaces of `X` and `Y` over `S` is surjective.
-/
lemma exists_preimage_pullback (x : X) (y : Y) (h : f x = g y) :
    ∃ z : ↑(pullback f g), pullback.fst f g z = x ∧ pullback.snd f g z = y :=
  (Pullback.Triplet.mk' x y h).exists_preimage
/-
**AlgebraicGeometry.Scheme.Pullback._root_.AlgebraicGeometry.Scheme.isEmpty_pull
back_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.Scheme.isEmpty_pullback_iff {f : X ⟶ S} {g : Y ⟶ S} :
    IsEmpty ↑(Limits.pullback f g) ↔ Disjoint (Set.range f) (Set.range g) := by
  refine ⟨?_, Scheme.isEmpty_pullback f g⟩
  rw [Set.disjoint_iff_forall_ne]
  contrapose!
  rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, e⟩
  obtain ⟨z, -⟩ := exists_preimage_pullback x y e
  exact ⟨z⟩
/-
**AlgebraicGeometry.Scheme.Pullback.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.Scheme.Pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Nonempty X] [Nonempty Y] [Subsingleton S] :
    Nonempty ↑(pullback f g) := by
  have : Nonempty S := .map f ‹_›
  rw [← not_isEmpty_iff, AlgebraicGeometry.Scheme.isEmpty_pullback_iff, Set.not_disjoint_iff]
  exact ⟨Nonempty.some ‹_›, Function.surjective_to_subsingleton _ _,
    Function.surjective_to_subsingleton _ _⟩

variable (f g)
/-
**AlgebraicGeometry.Scheme.Pullback.range_fst** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：range_fst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage`：∀ {X Y S : Al
gebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : AlgebraicGeometry.Scheme.Pu
llback.Triplet f g),   ∃ t, (CategoryTheory.Lim…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma range_fst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g := by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' x y hy.symm)
    use a, ha.left
/-
**AlgebraicGeometry.Scheme.Pullback.range_snd** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：range_snd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage`：∀ {X Y S : Al
gebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : AlgebraicGeometry.Scheme.Pu
llback.Triplet f g),   ∃ t, (CategoryTheory.Lim…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma range_snd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f := by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, ← pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' y x hy)
    use a, ha.right
/-
**AlgebraicGeometry.Scheme.Pullback.range_fst_comp** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback`。
形式化陈述：range_fst_comp : Set.range (pullback.fst f g ≫ f) = Set.range f inter Set.
range g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.range_fst`：range_fst : Set.range (pull
back.fst f g) = f ⁻¹' Set.range g
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_fst_comp :
    Set.range (pullback.fst f g ≫ f) = Set.range f ∩ Set.range g := by
  simp [Set.range_comp, range_fst, Set.image_preimage_eq_range_inter]
/-
**AlgebraicGeometry.Scheme.Pullback.range_snd_comp** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Pullback`。
形式化陈述：range_snd_comp : Set.range (pullback.snd f g ≫ g) = Set.range f inter Set.
range g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.range_fst_comp`：range_fst_comp : Set.r
ange (pullback.fst f g ≫ f) = Set.range f inter Set.range g
-/
lemma range_snd_comp :
    Set.range (pullback.snd f g ≫ g) = Set.range f ∩ Set.range g := by
  rw [← pullback.condition, range_fst_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.range_map** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Pullback`。
形式化陈述：range_map {X' Y' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ 
X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') 
[Mono i₃] : Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) = pullback.fst f' 
g' ⁻¹' Set.range i₁ inter pullback.snd f' g' ⁻¹' Set.range i₂
参数：f' : X' ⟶ S'；g' : Y' ⟶ S'；i₁ : X ⟶ X'；i₂ : Y ⟶ Y'；i₃ : S ⟶ S'；e₁ : f ≫ i₃ = i
₁ ≫ f'；e₂ : g ≫ i₃ = i₂ ≫ g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage`：∀ {X Y S : Al
gebraicGeometry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (T : AlgebraicGeometry.Scheme.Pu
llback.Triplet f g),   ∃ t, (CategoryTheory.Lim…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.mk'_x`：∀ {X Y S : AlgebraicGeo
metry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (x : ↥X) (y : ↥Y) (h : f x = g y),   (Alge
braicGeometry.Scheme.Pullback.Triplet…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.pullback_map_eq_pullbackFstFstIso_inv`：pullback_ma
p_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X'
 ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y')…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.Triplet.mk'_y`：∀ {X Y S : AlgebraicGeo
metry.Scheme} {f : X ⟶ S} {g : Y ⟶ S} (x : ↥X) (y : ↥Y) (h : f x = g y),   (Alge
braicGeometry.Scheme.Pullback.Triplet…
-/
lemma range_map {X' Y' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) =
      pullback.fst f' g' ⁻¹' Set.range i₁ ∩ pullback.snd f' g' ⁻¹' Set.range i₂ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · use pullback.fst f g t
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      simp
    · use pullback.snd f g t
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      simp
  · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let T₁ : Triplet (pullback.fst f' g') i₁ := Triplet.mk' z x hx.symm
    obtain ⟨w₁, hw₁⟩ := T₁.exists_preimage
    let T₂ : Triplet (pullback.snd f' g') i₂ := Triplet.mk' z y hy.symm
    obtain ⟨w₂, hw₂⟩ := T₂.exists_preimage
    let T : Triplet (pullback.fst (pullback.fst f' g') i₁) (pullback.fst (pullback.snd f' g') i₂) :=
      Triplet.mk' w₁ w₂ <| by simp [hw₁.left, hw₂.left, T₁, T₂]
    obtain ⟨t, _, ht₂⟩ := T.exists_preimage
    use (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).hom t
    rw [pullback_map_eq_pullbackFstFstIso_inv, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    simp [ht₂, T, hw₂.left, T₂]

end Pullback

/-
**AlgebraicGeometry.Scheme.isJointlySurjectivePreserving** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme),   Algebr
aicGeometry.Scheme.IsJointlySurjectivePreserving P
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
-/
instance isJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) :
    IsJointlySurjectivePreserving P where
  exists_preimage_fst_triplet_of_prop {X Y S} f g _ hg x y hxy := by
    obtain ⟨a, b, h⟩ := Pullback.exists_preimage_pullback x y hxy
    use a

/-- The comparison map for pullbacks under the forgetful functor `Scheme ⥤ Type u` is surjective. -/
/-
**AlgebraicGeometry.Scheme.pullbackComparison_forget_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S),   Function.S
urjective     ⇑(CategoryTheory.ConcreteCategory.hom         (CategoryTheory.Limi
ts.pullbackComparison AlgebraicGeometry.Scheme.forget f g))
参数：f : X ⟶ S；g : Y ⟶ S；CategoryTheory.ConcreteCategory.hom         (CategoryTheo
ry.Limits.pullbackComparison AlgebraicGeometry.Scheme.forget f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp_left`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Injec
tive f → Function.Surj…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.pullbackIsoPullback_hom_fst`：∀ {X Y Z : Type
 u} (f : X ⟶ Z) (g : Y ⟶ Z) (p : CategoryTheory.Limits.pullback f g),   (↑((Cate
goryTheory.ConcreteCategory.hom (CategoryTheo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.types_comp_apply`：types_comp_apply {X Y Z : Type u} (f : 
X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_fst`：pullbackComparison_co
mp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
· 使用定理 `CategoryTheory.Limits.Types.pullbackIsoPullback_hom_snd`：∀ {X Y Z : Type
 u} (f : X ⟶ Z) (g : Y ⟶ Z) (p : CategoryTheory.Limits.pullback f g),   (↑((Cate
goryTheory.ConcreteCategory.hom (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_snd`：pullbackComparison_co
mp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
The comparison map for pullbacks under the forgetful functor `Scheme ⥤ Type u` i
s surjective.
-/
lemma pullbackComparison_forget_surjective {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Function.Surjective (pullbackComparison forget f g) := by
  refine .of_comp_left (fun x ↦ ?_) <|
    injective_of_mono (Types.pullbackIsoPullback (forget.map f) (forget.map g)).hom
  obtain ⟨z, h1, h2⟩ := Pullback.exists_preimage_pullback (f := f) (g := g) x.1.1 x.1.2 x.2
  use z
  ext
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_fst]
    rwa [← types_comp_apply (g := pullback.fst _ _), pullbackComparison_comp_fst]
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_snd]
    rwa [← types_comp_apply (g := pullback.snd _ _), pullbackComparison_comp_snd]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Epi (pullbackComparison Scheme.forgetToTop f g) := by
  refine (CategoryTheory.forget TopCat).epi_of_epi_map ?_
  rw [← CategoryTheory.epi_comp_iff_of_isIso _
    (pullbackComparison (CategoryTheory.forget TopCat) (forgetToTop.map f) (forgetToTop.map g)),
    ← _root_.CategoryTheory.Limits.pullbackComparison_comp, epi_iff_surjective]
  apply Scheme.pullbackComparison_forget_surjective _ _
/-
**AlgebraicGeometry.Scheme.exists_preimage_of_isPullback** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {P X Y Z : AlgebraicGeometry.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X 
⟶ Z} {g : Y ⟶ Z},   CategoryTheory.IsPullback fst snd f g → ∀ (x : ↥X) (y : ↥Y),
 f x = g y → ∃ p, fst p = x ∧ snd p = y
参数：x : ↥X；y : ↥Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst`：isoPullback_inv_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.f
st _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_snd`：isoPullback_inv_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.s
nd _ _
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma exists_preimage_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y)
    (hxy : f.base x = g.base y) :
    ∃ (p : P), fst.base p = x ∧ snd.base p = y := by
  let e := h.isoPullback
  obtain ⟨z, hzl, hzr⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x y hxy
  use h.isoPullback.inv.base z
  simp [← Scheme.Hom.comp_apply, hzl, hzr]
/-
**AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {P X Y Z : AlgebraicGeometry.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X 
⟶ Z} {g : Y ⟶ Z},   CategoryTheory.IsPullback fst snd f g → ∀ (s : Set ↥X), ⇑snd
 '' ⇑fst ⁻¹' s = ⇑g ⁻¹' ⇑f '' s
参数：s : Set ↥X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`：∀ {P X Y Z : Alg
ebraicGeometry.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},   Ca
tegoryTheory.IsPullback fst snd f g → ∀ (x :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma image_preimage_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (s : Set X) :
    snd.base '' fst.base ⁻¹' s = g.base ⁻¹' f.base '' s := by
  refine subset_antisymm ?_ (fun x hx ↦ ?_)
  · rw [Set.image_subset_iff, ← Set.preimage_comp, ← TopCat.coe_comp, ← Hom.comp_base, ← h.1.1]
    rw [Hom.comp_base, TopCat.coe_comp, ← Set.image_subset_iff, Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  · obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨o, hl, hr⟩ := exists_preimage_of_isPullback h y x heq
    use o
    simpa [hl, hr]

end Scheme

namespace Surjective

/-
**AlgebraicGeometry.Surjective.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sur
jective`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderBaseChange @Surjective := by
  refine .mk' ?_
  introv hg
  simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
  rw [hg, Set.preimage_univ]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Surjective.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sur
jective`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective g] :
    Surjective (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Surjective.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sur
jective`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f] :
    Surjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

end AlgebraicGeometry.Surjective

