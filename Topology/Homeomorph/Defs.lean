/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
module

public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

## Main definitions and results

* `Homeomorph X Y`: The type of homeomorphisms from `X` to `Y`.
  This type can be denoted using the following notation: `X ≃ₜ Y`.
* `HomeomorphClass`: `HomeomorphClass F A B` states that `F` is a type of homeomorphisms.

* `Homeomorph.symm`: the inverse of a homeomorphism
* `Homeomorph.trans`: composing two homeomorphisms
* Homeomorphisms are open and closed embeddings, inducing, quotient maps etc.
* `Homeomorph.homeomorphOfContinuousOpen`: A continuous bijection that is
  an open map is a homeomorphism.
* `Homeomorph.homeomorphOfUnique`: if both `X` and `Y` have a unique element, then `X ≃ₜ Y`.
* `Equiv.toHomeomorph`: an equivalence between topological spaces respecting openness
  is a homeomorphism.

* `IsHomeomorph`: the predicate that a function is a homeomorphism

-/

@[expose] public section

open Set Topology Filter

variable {X Y W Z : Type*}

/--
Definition of `Homeomorph` / `Homeomorph` 的定义

English:
structure Homeomorph
  parameters: (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
  extends: X ≃ Y
  axioms and operations (2):
    - continuous_toFun : Continuous toFun  [default: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]
    - continuous_invFun : Continuous invFun  [default: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]

中文:
结构 Homeomorph
  参数: (X : 类型) (Y : 类型) [TopologicalSpace X] [TopologicalSpace Y]
  继承: X ≃ Y
  公理与运算 (2 个):
    - continuous_toFun : Continuous toFun  [默认: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]
    - continuous_invFun : Continuous invFun  [默认: by first | fun_prop | eta_expand; dsimp; fun_prop | skip]

Depends on / 依赖: eta_expand, fun_prop
-/
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

@[inherit_doc]
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Function.Injective (toEquiv : X ≃ₜ Y -> X ≃ Y)

中文:
定理 toEquiv_injective
  结论: Function.Injective (toEquiv : X ≃ₜ Y -> X ≃ Y)
-/
theorem toEquiv_injective : Function.Injective (toEquiv : X ≃ₜ Y -> X ≃ Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (X ≃ₜ Y) X Y
  body: h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
coe_injective' _ _ H _ := toEquiv_injective DFunLike.ext' H

中文:
实例 :
  签名: EquivLike (X ≃ₜ Y) X Y
  定义体: h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
coe_injective' _ _ H _ := toEquiv_injective DFunLike.ext' H

Depends on / 依赖: h.toEquiv, toEquiv
-/
instance : EquivLike (X ≃ₜ Y) X Y where
  coe h := h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
coe_injective' _ _ H _ := toEquiv_injective DFunLike.ext' H

/--
theorem `homeomorph_mk_coe` / 定理 `homeomorph_mk_coe`

English:
theorem homeomorph_mk_coe
  given: (a : X ≃ Y) (b c)
  statement: (Homeomorph.mk a b c : X -> Y) = a
  proof: rfl

中文:
定理 homeomorph_mk_coe
  条件: (a : X ≃ Y) (b c)
  结论: (Homeomorph.mk a b c : X -> Y) = a
  证明: rfl
-/
@[simp] theorem homeomorph_mk_coe (a : X ≃ Y) (b c) : (Homeomorph.mk a b c : X -> Y) = a :=
  rfl

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: [IsEmpty X] [IsEmpty Y]
  body: Equiv.equivOfIsEmpty X Y

中文:
定义 empty
  签名: [IsEmpty X] [IsEmpty Y]
  定义体: Equiv.equivOfIsEmpty X Y
-/
protected def empty [IsEmpty X] [IsEmpty Y] : X ≃ₜ Y where
  __ := Equiv.equivOfIsEmpty X Y

/-- Inverse of a homeomorphism. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (h : X ≃ₜ Y)
  body: h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm

中文:
定义 symm
  签名: (h : X ≃ₜ Y)
  定义体: h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm
-/
protected def symm (h : X ≃ₜ Y) : Y ≃ₜ X where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm

/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (h : X ≃ₜ Y)
  statement: h.symm.symm = h
  proof: rfl

中文:
定理 symm_symm
  条件: (h : X ≃ₜ Y)
  结论: h.symm.symm = h
  证明: rfl
-/
@[simp] theorem symm_symm (h : X ≃ₜ Y) : h.symm.symm = h := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) -> Y ≃ₜ X)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) -> Y ≃ₜ X)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) -> Y ≃ₜ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : X ≃ₜ Y)
  body: h.symm

initialize_simps_projections Homeomorph (toFun -> apply, invFun -> symm_apply, as_prefix toEquiv)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (h : X ≃ₜ Y)
  定义体: h.symm

initialize_simps_projections Homeomorph (toFun -> apply, invFun -> symm_apply, as_prefix toEquiv)

@[simp]
-/
def Simps.symm_apply (h : X ≃ₜ Y) : Y -> X :=
  h.symm

initialize_simps_projections Homeomorph (toFun -> apply, invFun -> symm_apply, as_prefix toEquiv)

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (h : X ≃ₜ Y)
  statement: ⇑h.toEquiv = h
  proof: rfl

@[simp]

中文:
定理 coe_toEquiv
  条件: (h : X ≃ₜ Y)
  结论: ⇑h.toEquiv = h
  证明: rfl

@[simp]
-/
theorem coe_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv = h :=
  rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  given: (h : X ≃ₜ Y)
  statement: ⇑h.toEquiv.symm = h.symm
  proof: rfl

@[ext]

中文:
定理 coe_symm_toEquiv
  条件: (h : X ≃ₜ Y)
  结论: ⇑h.toEquiv.symm = h.symm
  证明: rfl

@[ext]
-/
theorem coe_symm_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv.symm = h.symm :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {h h' : X ≃ₜ Y} (H : forall x, h x = h' x)
  statement: h = h'
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: {h h' : X ≃ₜ Y} (H : 对任意 x, h x = h' x)
  结论: h = h'
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h' :=
  DFunLike.ext _ _ H

/-- Identity map as a homeomorphism. -/
@[simps! -fullyApplied apply]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (X : Type*) [TopologicalSpace X]
  body: Equiv.refl X

中文:
定义 refl
  签名: (X : 类型) [TopologicalSpace X]
  定义体: Equiv.refl X
-/
protected def refl (X : Type*) [TopologicalSpace X] : X ≃ₜ X where
  toEquiv := Equiv.refl X

/-- Composition of two homeomorphisms. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z)
  body: h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]

中文:
定义 trans
  签名: (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z)
  定义体: h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
-/
protected def trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) : X ≃ₜ Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X)
  statement: h₁.trans h₂ x = h₂ (h₁ x)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X)
  结论: h₁.trans h₂ x = h₂ (h₁ x)
  证明: rfl

@[simp]
-/
theorem trans_apply (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

@[simp]
/--
theorem `symm_trans_apply` / 定理 `symm_trans_apply`

English:
theorem symm_trans_apply
  given: (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z)
  proof: rfl

@[simp]

中文:
定理 symm_trans_apply
  条件: (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z)
  证明: rfl

@[simp]
-/
theorem symm_trans_apply (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z) :
    (f.trans g).symm z = f.symm (g.symm z) := rfl

@[simp]
/--
theorem `homeomorph_mk_coe_symm` / 定理 `homeomorph_mk_coe_symm`

English:
theorem homeomorph_mk_coe_symm
  given: (a : X ≃ Y) (b c)
  proof: rfl

@[simp]

中文:
定理 homeomorph_mk_coe_symm
  条件: (a : X ≃ Y) (b c)
  证明: rfl

@[simp]
-/
theorem homeomorph_mk_coe_symm (a : X ≃ Y) (b c) :
    ((Homeomorph.mk a b c).symm : Y -> X) = a.symm :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (Homeomorph.refl X).symm = Homeomorph.refl X
  proof: rfl

@[continuity, fun_prop]

中文:
定理 refl_symm
  结论: (Homeomorph.refl X).symm = Homeomorph.refl X
  证明: rfl

@[continuity, fun_prop]
-/
theorem refl_symm : (Homeomorph.refl X).symm = Homeomorph.refl X :=
  rfl

@[continuity, fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (h : X ≃ₜ Y)
  statement: Continuous h
  proof: h.continuous_toFun

中文:
定理 continuous
  条件: (h : X ≃ₜ Y)
  结论: Continuous h
  证明: h.continuous_toFun
-/
protected theorem continuous (h : X ≃ₜ Y) : Continuous h :=
  h.continuous_toFun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
/--
theorem `continuous_symm` / 定理 `continuous_symm`

English:
theorem continuous_symm
  given: (h : X ≃ₜ Y)
  statement: Continuous h.symm
  proof: h.continuous_invFun

@[simp]

中文:
定理 continuous_symm
  条件: (h : X ≃ₜ Y)
  结论: Continuous h.symm
  证明: h.continuous_invFun

@[simp]
-/
protected theorem continuous_symm (h : X ≃ₜ Y) : Continuous h.symm :=
  h.continuous_invFun

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (h : X ≃ₜ Y) (y : Y)
  statement: h (h.symm y) = y
  proof: h.toEquiv.apply_symm_apply y

@[simp]

中文:
定理 apply_symm_apply
  条件: (h : X ≃ₜ Y) (y : Y)
  结论: h (h.symm y) = y
  证明: h.toEquiv.apply_symm_apply y

@[simp]

Depends on / 依赖: apply_symm_apply, h.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (h : X ≃ₜ Y) (x : X)
  statement: h.symm (h x) = x
  proof: h.toEquiv.symm_apply_apply x

中文:
定理 symm_apply_apply
  条件: (h : X ≃ₜ Y) (x : X)
  结论: h.symm (h x) = x
  证明: h.toEquiv.symm_apply_apply x

Depends on / 依赖: h.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (h : X ≃ₜ Y) {x : X} {y : Y}
  statement: h.symm y = x ↔ y = h x
  proof: Equiv.symm_apply_eq _

中文:
定理 symm_apply_eq
  条件: (h : X ≃ₜ Y) {x : X} {y : Y}
  结论: h.symm y = x ↔ y = h x
  证明: Equiv.symm_apply_eq _

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem symm_apply_eq (h : X ≃ₜ Y) {x : X} {y : Y} : h.symm y = x ↔ y = h x :=
  Equiv.symm_apply_eq _

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (h : X ≃ₜ Y) {x : X} {y : Y}
  statement: x = h.symm y ↔ h x = y
  proof: Equiv.eq_symm_apply _

@[simp]

中文:
定理 eq_symm_apply
  条件: (h : X ≃ₜ Y) {x : X} {y : Y}
  结论: x = h.symm y ↔ h x = y
  证明: Equiv.eq_symm_apply _

@[simp]

Depends on / 依赖: Equiv.eq_symm_apply, eq_symm_apply
-/
theorem eq_symm_apply (h : X ≃ₜ Y) {x : X} {y : Y} : x = h.symm y ↔ h x = y :=
  Equiv.eq_symm_apply _

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (h : X ≃ₜ Y)
  statement: h.trans h.symm = Homeomorph.refl X
  proof: by
  ext
  apply symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  条件: (h : X ≃ₜ Y)
  结论: h.trans h.symm = Homeomorph.refl X
  证明: by
  ext
  apply symm_apply_apply

@[simp]

Depends on / 依赖: symm_apply_apply
-/
theorem self_trans_symm (h : X ≃ₜ Y) : h.trans h.symm = Homeomorph.refl X := by
  ext
  apply symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (h : X ≃ₜ Y)
  statement: h.symm.trans h = Homeomorph.refl Y
  proof: by
  ext
  apply apply_symm_apply

@[simps -isSimp]

中文:
定理 symm_trans_self
  条件: (h : X ≃ₜ Y)
  结论: h.symm.trans h = Homeomorph.refl Y
  证明: by
  ext
  apply apply_symm_apply

@[simps -isSimp]

Depends on / 依赖: apply_symm_apply
-/
theorem symm_trans_self (h : X ≃ₜ Y) : h.symm.trans h = Homeomorph.refl Y := by
  ext
  apply apply_symm_apply

@[simps -isSimp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (X ≃ₜ X)
  body: g.trans f
  mul_assoc f g h := rfl
  one := .refl X
  one_mul f := rfl
  mul_one f := rfl
  inv := .symm
  inv_mul_cancel := self_trans_symm

@[simp]

中文:
实例 :
  签名: Group (X ≃ₜ X)
  定义体: g.trans f
  mul_assoc f g h := rfl
  one := .refl X
  one_mul f := rfl
  mul_one f := rfl
  inv := .symm
  inv_mul_cancel := self_trans_symm

@[simp]

Depends on / 依赖: g.trans
-/
instance : Group (X ≃ₜ X) where
  mul f g := g.trans f
  mul_assoc f g h := rfl
  one := .refl X
  one_mul f := rfl
  mul_one f := rfl
  inv := .symm
  inv_mul_cancel := self_trans_symm

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : X)
  statement: (1 : X ≃ₜ X) x = x
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x : X)
  结论: (1 : X ≃ₜ X) x = x
  证明: rfl

@[simp]
-/
theorem one_apply (x : X) : (1 : X ≃ₜ X) x = x := rfl

@[simp]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: (f : X ≃ₜ X) (x : X)
  statement: f⁻¹ x = f.symm x
  proof: rfl

@[simp]

中文:
定理 inv_apply
  条件: (f : X ≃ₜ X) (x : X)
  结论: f⁻¹ x = f.symm x
  证明: rfl

@[simp]
-/
theorem inv_apply (f : X ≃ₜ X) (x : X) : f⁻¹ x = f.symm x := rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : X ≃ₜ X) (x : X)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : X ≃ₜ X) (x : X)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
theorem mul_apply (f g : X ≃ₜ X) (x : X) : (f * g) x = f (g x) := rfl

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (h : X ≃ₜ Y)
  statement: Function.Bijective h
  proof: h.toEquiv.bijective

中文:
定理 bijective
  条件: (h : X ≃ₜ Y)
  结论: Function.Bijective h
  证明: h.toEquiv.bijective
-/
protected theorem bijective (h : X ≃ₜ Y) : Function.Bijective h :=
  h.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (h : X ≃ₜ Y)
  statement: Function.Injective h
  proof: h.toEquiv.injective

中文:
定理 injective
  条件: (h : X ≃ₜ Y)
  结论: Function.Injective h
  证明: h.toEquiv.injective
-/
protected theorem injective (h : X ≃ₜ Y) : Function.Injective h :=
  h.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (h : X ≃ₜ Y)
  statement: Function.Surjective h
  proof: h.toEquiv.surjective

中文:
定理 surjective
  条件: (h : X ≃ₜ Y)
  结论: Function.Surjective h
  证明: h.toEquiv.surjective
-/
protected theorem surjective (h : X ≃ₜ Y) : Function.Surjective h :=
  h.toEquiv.surjective

/--
Definition of `changeInv` / `changeInv` 的定义

English:
definition changeInv
  signature: (f : X ≃ₜ Y) (g : Y -> X) (hg : Function.RightInverse g f)
  body: haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert! f.symm.continuous }

@[simp]

中文:
定义 changeInv
  签名: (f : X ≃ₜ Y) (g : Y -> X) (hg : Function.RightInverse g f)
  定义体: haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert! f.symm.continuous }

@[simp]

Depends on / 依赖: continuous, continuous_invFun, continuous_toFun, convert, eq_rightInverse, f.continuous, f.left_inv, f.left_inv.eq_rightInverse, f.right_inv, f.symm, f.symm.continuous, invFun, left_inv, right_inv
-/
def changeInv (f : X ≃ₜ Y) (g : Y -> X) (hg : Function.RightInverse g f) : X ≃ₜ Y :=
  haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert! f.symm.continuous }

@[simp]
/--
theorem `symm_comp_self` / 定理 `symm_comp_self`

English:
theorem symm_comp_self
  given: (h : X ≃ₜ Y)
  statement: h.symm ∘ h = id
  proof: funext h.symm_apply_apply

@[simp]

中文:
定理 symm_comp_self
  条件: (h : X ≃ₜ Y)
  结论: h.symm ∘ h = id
  证明: funext h.symm_apply_apply

@[simp]

Depends on / 依赖: h.symm_apply_apply, symm_apply_apply
-/
theorem symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
/--
theorem `self_comp_symm` / 定理 `self_comp_symm`

English:
theorem self_comp_symm
  given: (h : X ≃ₜ Y)
  statement: h ∘ h.symm = id
  proof: funext h.apply_symm_apply

中文:
定理 self_comp_symm
  条件: (h : X ≃ₜ Y)
  结论: h ∘ h.symm = id
  证明: funext h.apply_symm_apply

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply
-/
theorem self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id :=
  funext h.apply_symm_apply

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  given: (h : X ≃ₜ Y)
  statement: range h = univ
  proof: by simp

中文:
定理 range_coe
  条件: (h : X ≃ₜ Y)
  结论: range h = univ
  证明: by simp
-/
theorem range_coe (h : X ≃ₜ Y) : range h = univ := by simp

/--
theorem `image_symm` / 定理 `image_symm`

English:
theorem image_symm
  given: (h : X ≃ₜ Y)
  statement: image h.symm = preimage h
  proof: funext h.symm.toEquiv.image_eq_preimage_symm

中文:
定理 image_symm
  条件: (h : X ≃ₜ Y)
  结论: image h.symm = preimage h
  证明: funext h.symm.toEquiv.image_eq_preimage_symm

Depends on / 依赖: h.symm.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_symm (h : X ≃ₜ Y) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage_symm

/--
theorem `preimage_symm` / 定理 `preimage_symm`

English:
theorem preimage_symm
  given: (h : X ≃ₜ Y)
  statement: preimage h.symm = image h
  proof: (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]

中文:
定理 preimage_symm
  条件: (h : X ≃ₜ Y)
  结论: preimage h.symm = image h
  证明: (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]

Depends on / 依赖: h.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem preimage_symm (h : X ≃ₜ Y) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]
/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  given: (h : X ≃ₜ Y) (s : Set Y)
  statement: h '' h ⁻¹' s = s
  proof: h.toEquiv.image_preimage s

@[simp]

中文:
定理 image_preimage
  条件: (h : X ≃ₜ Y) (s : Set Y)
  结论: h '' h ⁻¹' s = s
  证明: h.toEquiv.image_preimage s

@[simp]

Depends on / 依赖: h.toEquiv.image_preimage, image_preimage, toEquiv
-/
theorem image_preimage (h : X ≃ₜ Y) (s : Set Y) : h '' h ⁻¹' s = s :=
  h.toEquiv.image_preimage s

@[simp]
/--
theorem `preimage_image` / 定理 `preimage_image`

English:
theorem preimage_image
  given: (h : X ≃ₜ Y) (s : Set X)
  statement: h ⁻¹' h '' s = s
  proof: h.toEquiv.preimage_image s

中文:
定理 preimage_image
  条件: (h : X ≃ₜ Y) (s : Set X)
  结论: h ⁻¹' h '' s = s
  证明: h.toEquiv.preimage_image s

Depends on / 依赖: h.toEquiv.preimage_image, preimage_image, toEquiv
-/
theorem preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻¹' h '' s = s :=
  h.toEquiv.preimage_image s

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (h : X ≃ₜ Y) (s : Set X)
  statement: h '' s = h.symm ⁻¹' s
  proof: h.toEquiv.image_eq_preimage_symm s

中文:
定理 image_eq_preimage_symm
  条件: (h : X ≃ₜ Y) (s : Set X)
  结论: h '' s = h.symm ⁻¹' s
  证明: h.toEquiv.image_eq_preimage_symm s

Depends on / 依赖: h.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_eq_preimage_symm (h : X ≃ₜ Y) (s : Set X) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage_symm s

/--
lemma `image_compl` / 引理 `image_compl`

English:
lemma image_compl
  given: (h : X ≃ₜ Y) (s : Set X)
  statement: h '' (sᶜ) = (h '' s)ᶜ
  proof: h.toEquiv.image_compl s

中文:
引理 image_compl
  条件: (h : X ≃ₜ Y) (s : Set X)
  结论: h '' (sᶜ) = (h '' s)ᶜ
  证明: h.toEquiv.image_compl s

Depends on / 依赖: h.toEquiv.image_compl, image_compl, toEquiv
-/
lemma image_compl (h : X ≃ₜ Y) (s : Set X) : h '' (sᶜ) = (h '' s)ᶜ :=
  h.toEquiv.image_compl s

/--
lemma `isInducing` / 引理 `isInducing`

English:
lemma isInducing
  given: (h : X ≃ₜ Y)
  statement: IsInducing h
  proof: .of_comp h.continuous h.symm.continuous by simp only [symm_comp_self, IsInducing.id]

中文:
引理 isInducing
  条件: (h : X ≃ₜ Y)
  结论: IsInducing h
  证明: .of_comp h.continuous h.symm.continuous by simp only [symm_comp_self, IsInducing.id]

Depends on / 依赖: IsInducing, IsInducing.id, continuous, h.continuous, h.symm.continuous, of_comp, symm_comp_self
-/
lemma isInducing (h : X ≃ₜ Y) : IsInducing h :=
.of_comp h.continuous h.symm.continuous by simp only [symm_comp_self, IsInducing.id]

/--
theorem `induced_eq` / 定理 `induced_eq`

English:
theorem induced_eq
  given: (h : X ≃ₜ Y)
  statement: TopologicalSpace.induced h ‹_› = ‹_›
  proof: h.isInducing.1.symm

中文:
定理 induced_eq
  条件: (h : X ≃ₜ Y)
  结论: TopologicalSpace.induced h ‹_› = ‹_›
  证明: h.isInducing.1.symm

Depends on / 依赖: h.isInducing, isInducing
-/
theorem induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induced h ‹_› = ‹_› := h.isInducing.1.symm

/--
theorem `isQuotientMap` / 定理 `isQuotientMap`

English:
theorem isQuotientMap
  given: (h : X ≃ₜ Y)
  statement: IsQuotientMap h
  proof: IsQuotientMap.of_comp h.symm.continuous h.continuous by
    simp only [self_comp_symm, IsQuotientMap.id]

中文:
定理 isQuotientMap
  条件: (h : X ≃ₜ Y)
  结论: IsQuotientMap h
  证明: IsQuotientMap.of_comp h.symm.continuous h.continuous by
    simp only [self_comp_symm, IsQuotientMap.id]

Depends on / 依赖: IsQuotientMap, IsQuotientMap.id, IsQuotientMap.of_comp, continuous, h.continuous, h.symm.continuous, of_comp, self_comp_symm
-/
theorem isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h :=
IsQuotientMap.of_comp h.symm.continuous h.continuous by
    simp only [self_comp_symm, IsQuotientMap.id]

/--
theorem `coinduced_eq` / 定理 `coinduced_eq`

English:
theorem coinduced_eq
  given: (h : X ≃ₜ Y)
  statement: TopologicalSpace.coinduced h ‹_› = ‹_›
  proof: h.isQuotientMap.isCoinducing.eq_coinduced.symm

中文:
定理 coinduced_eq
  条件: (h : X ≃ₜ Y)
  结论: TopologicalSpace.coinduced h ‹_› = ‹_›
  证明: h.isQuotientMap.isCoinducing.eq_coinduced.symm

Depends on / 依赖: eq_coinduced, h.isQuotientMap.isCoinducing.eq_coinduced.symm, isCoinducing, isQuotientMap
-/
theorem coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.isQuotientMap.isCoinducing.eq_coinduced.symm

/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: (h : X ≃ₜ Y)
  statement: IsEmbedding h
  proof: ⟨h.isInducing, h.injective⟩

中文:
定理 isEmbedding
  条件: (h : X ≃ₜ Y)
  结论: IsEmbedding h
  证明: ⟨h.isInducing, h.injective⟩

Depends on / 依赖: h.injective, h.isInducing, injective, isInducing
-/
theorem isEmbedding (h : X ≃ₜ Y) : IsEmbedding h := ⟨h.isInducing, h.injective⟩

/--
theorem `discreteTopology` / 定理 `discreteTopology`

English:
theorem discreteTopology
  given: [DiscreteTopology X] (h : X ≃ₜ Y)
  statement: DiscreteTopology Y
  proof: h.symm.isEmbedding.discreteTopology

中文:
定理 discreteTopology
  条件: [DiscreteTopology X] (h : X ≃ₜ Y)
  结论: DiscreteTopology Y
  证明: h.symm.isEmbedding.discreteTopology
-/
protected theorem discreteTopology [DiscreteTopology X] (h : X ≃ₜ Y) : DiscreteTopology Y :=
  h.symm.isEmbedding.discreteTopology

/--
theorem `discreteTopology_iff` / 定理 `discreteTopology_iff`

English:
theorem discreteTopology_iff
  given: (h : X ≃ₜ Y)
  statement: DiscreteTopology X ↔ DiscreteTopology Y
  proof: ⟨fun _ => h.discreteTopology, fun _ => h.symm.discreteTopology⟩

中文:
定理 discreteTopology_iff
  条件: (h : X ≃ₜ Y)
  结论: DiscreteTopology X ↔ DiscreteTopology Y
  证明: ⟨fun _ => h.discreteTopology, fun _ => h.symm.discreteTopology⟩

Depends on / 依赖: discreteTopology, h.discreteTopology, h.symm.discreteTopology
-/
theorem discreteTopology_iff (h : X ≃ₜ Y) : DiscreteTopology X ↔ DiscreteTopology Y :=
  ⟨fun _ => h.discreteTopology, fun _ => h.symm.discreteTopology⟩

/--
theorem `indiscreteTopology` / 定理 `indiscreteTopology`

English:
theorem indiscreteTopology
  given: [IndiscreteTopology X] (h : X ≃ₜ Y)
  proof: h.symm.isInducing.indiscreteTopology

中文:
定理 indiscreteTopology
  条件: [IndiscreteTopology X] (h : X ≃ₜ Y)
  证明: h.symm.isInducing.indiscreteTopology
-/
protected theorem indiscreteTopology [IndiscreteTopology X] (h : X ≃ₜ Y) :
    IndiscreteTopology Y :=
  h.symm.isInducing.indiscreteTopology

/--
theorem `indiscreteTopology_iff` / 定理 `indiscreteTopology_iff`

English:
theorem indiscreteTopology_iff
  given: (h : X ≃ₜ Y)
  statement: IndiscreteTopology X ↔ IndiscreteTopology Y
  proof: ⟨fun _ => h.indiscreteTopology, fun _ => h.symm.indiscreteTopology⟩

中文:
定理 indiscreteTopology_iff
  条件: (h : X ≃ₜ Y)
  结论: IndiscreteTopology X ↔ IndiscreteTopology Y
  证明: ⟨fun _ => h.indiscreteTopology, fun _ => h.symm.indiscreteTopology⟩

Depends on / 依赖: h.indiscreteTopology, h.symm.indiscreteTopology, indiscreteTopology
-/
theorem indiscreteTopology_iff (h : X ≃ₜ Y) : IndiscreteTopology X ↔ IndiscreteTopology Y :=
  ⟨fun _ => h.indiscreteTopology, fun _ => h.symm.indiscreteTopology⟩

/--
theorem `nontrivialTopology` / 定理 `nontrivialTopology`

English:
theorem nontrivialTopology
  given: [NontrivialTopology X] (h : X ≃ₜ Y)
  proof: h.isInducing.nontrivialTopology

中文:
定理 nontrivialTopology
  条件: [NontrivialTopology X] (h : X ≃ₜ Y)
  证明: h.isInducing.nontrivialTopology
-/
protected theorem nontrivialTopology [NontrivialTopology X] (h : X ≃ₜ Y) :
    NontrivialTopology Y :=
  h.isInducing.nontrivialTopology

/--
theorem `nontrivialTopology_iff` / 定理 `nontrivialTopology_iff`

English:
theorem nontrivialTopology_iff
  given: (h : X ≃ₜ Y)
  statement: NontrivialTopology X ↔ NontrivialTopology Y
  proof: ⟨fun _ => h.nontrivialTopology, fun _ => h.symm.nontrivialTopology⟩

@[simp]

中文:
定理 nontrivialTopology_iff
  条件: (h : X ≃ₜ Y)
  结论: NontrivialTopology X ↔ NontrivialTopology Y
  证明: ⟨fun _ => h.nontrivialTopology, fun _ => h.symm.nontrivialTopology⟩

@[simp]

Depends on / 依赖: h.nontrivialTopology, h.symm.nontrivialTopology, nontrivialTopology
-/
theorem nontrivialTopology_iff (h : X ≃ₜ Y) : NontrivialTopology X ↔ NontrivialTopology Y :=
  ⟨fun _ => h.nontrivialTopology, fun _ => h.symm.nontrivialTopology⟩

@[simp]
/--
theorem `isOpen_preimage` / 定理 `isOpen_preimage`

English:
theorem isOpen_preimage
  given: (h : X ≃ₜ Y) {s : Set Y}
  statement: IsOpen (h ⁻¹' s) ↔ IsOpen s
  proof: h.isQuotientMap.isOpen_preimage

@[simp]

中文:
定理 isOpen_preimage
  条件: (h : X ≃ₜ Y) {s : Set Y}
  结论: IsOpen (h ⁻¹' s) ↔ IsOpen s
  证明: h.isQuotientMap.isOpen_preimage

@[simp]

Depends on / 依赖: h.isQuotientMap.isOpen_preimage, isOpen_preimage, isQuotientMap
-/
theorem isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.isQuotientMap.isOpen_preimage

@[simp]
/--
theorem `isOpen_image` / 定理 `isOpen_image`

English:
theorem isOpen_image
  given: (h : X ≃ₜ Y) {s : Set X}
  statement: IsOpen (h '' s) ↔ IsOpen s
  proof: by
  rw [← preimage_symm]; rw [isOpen_preimage]

中文:
定理 isOpen_image
  条件: (h : X ≃ₜ Y) {s : Set X}
  结论: IsOpen (h '' s) ↔ IsOpen s
  证明: by
  rw [← preimage_symm]; rw [isOpen_preimage]

Depends on / 依赖: isOpen_preimage, preimage_symm
-/
theorem isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm]; rw [isOpen_preimage]

/--
theorem `isOpenMap` / 定理 `isOpenMap`

English:
theorem isOpenMap
  given: (h : X ≃ₜ Y)
  statement: IsOpenMap h
  proof: fun _ => h.isOpen_image.2

中文:
定理 isOpenMap
  条件: (h : X ≃ₜ Y)
  结论: IsOpenMap h
  证明: fun _ => h.isOpen_image.2
-/
protected theorem isOpenMap (h : X ≃ₜ Y) : IsOpenMap h := fun _ => h.isOpen_image.2

/--
theorem `isOpenQuotientMap` / 定理 `isOpenQuotientMap`

English:
theorem isOpenQuotientMap
  given: (h : X ≃ₜ Y)
  statement: IsOpenQuotientMap h
  proof: ⟨h.surjective, h.continuous, h.isOpenMap⟩

@[simp]

中文:
定理 isOpenQuotientMap
  条件: (h : X ≃ₜ Y)
  结论: IsOpenQuotientMap h
  证明: ⟨h.surjective, h.continuous, h.isOpenMap⟩

@[simp]
-/
protected theorem isOpenQuotientMap (h : X ≃ₜ Y) : IsOpenQuotientMap h :=
  ⟨h.surjective, h.continuous, h.isOpenMap⟩

@[simp]
/--
theorem `isClosed_preimage` / 定理 `isClosed_preimage`

English:
theorem isClosed_preimage
  given: (h : X ≃ₜ Y) {s : Set Y}
  statement: IsClosed (h ⁻¹' s) ↔ IsClosed s
  proof: by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]

@[simp]

中文:
定理 isClosed_preimage
  条件: (h : X ≃ₜ Y) {s : Set Y}
  结论: IsClosed (h ⁻¹' s) ↔ IsClosed s
  证明: by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]

@[simp]

Depends on / 依赖: isOpen_compl_iff, isOpen_preimage, preimage_compl
-/
theorem isClosed_preimage (h : X ≃ₜ Y) {s : Set Y} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]

@[simp]
/--
theorem `isClosed_image` / 定理 `isClosed_image`

English:
theorem isClosed_image
  given: (h : X ≃ₜ Y) {s : Set X}
  statement: IsClosed (h '' s) ↔ IsClosed s
  proof: by
  rw [← preimage_symm]; rw [isClosed_preimage]

中文:
定理 isClosed_image
  条件: (h : X ≃ₜ Y) {s : Set X}
  结论: IsClosed (h '' s) ↔ IsClosed s
  证明: by
  rw [← preimage_symm]; rw [isClosed_preimage]

Depends on / 依赖: isClosed_preimage, preimage_symm
-/
theorem isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm]; rw [isClosed_preimage]

/--
theorem `isClosedMap` / 定理 `isClosedMap`

English:
theorem isClosedMap
  given: (h : X ≃ₜ Y)
  statement: IsClosedMap h
  proof: fun _ => h.isClosed_image.2

中文:
定理 isClosedMap
  条件: (h : X ≃ₜ Y)
  结论: IsClosedMap h
  证明: fun _ => h.isClosed_image.2
-/
protected theorem isClosedMap (h : X ≃ₜ Y) : IsClosedMap h := fun _ => h.isClosed_image.2

/--
theorem `isOpenEmbedding` / 定理 `isOpenEmbedding`

English:
theorem isOpenEmbedding
  given: (h : X ≃ₜ Y)
  statement: IsOpenEmbedding h
  proof: .of_isEmbedding_isOpenMap h.isEmbedding h.isOpenMap

中文:
定理 isOpenEmbedding
  条件: (h : X ≃ₜ Y)
  结论: IsOpenEmbedding h
  证明: .of_isEmbedding_isOpenMap h.isEmbedding h.isOpenMap

Depends on / 依赖: h.isEmbedding, h.isOpenMap, isEmbedding, isOpenMap, of_isEmbedding_isOpenMap
-/
theorem isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbedding h :=
  .of_isEmbedding_isOpenMap h.isEmbedding h.isOpenMap

/--
theorem `isClosedEmbedding` / 定理 `isClosedEmbedding`

English:
theorem isClosedEmbedding
  given: (h : X ≃ₜ Y)
  statement: IsClosedEmbedding h
  proof: .of_isEmbedding_isClosedMap h.isEmbedding h.isClosedMap

中文:
定理 isClosedEmbedding
  条件: (h : X ≃ₜ Y)
  结论: IsClosedEmbedding h
  证明: .of_isEmbedding_isClosedMap h.isEmbedding h.isClosedMap

Depends on / 依赖: h.isClosedMap, h.isEmbedding, isClosedMap, isEmbedding, of_isEmbedding_isClosedMap
-/
theorem isClosedEmbedding (h : X ≃ₜ Y) : IsClosedEmbedding h :=
  .of_isEmbedding_isClosedMap h.isEmbedding h.isClosedMap

/--
theorem `preimage_closure` / 定理 `preimage_closure`

English:
theorem preimage_closure
  given: (h : X ≃ₜ Y) (s : Set Y)
  statement: h ⁻¹' closure s = closure (h ⁻¹' s)
  proof: h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _

中文:
定理 preimage_closure
  条件: (h : X ≃ₜ Y) (s : Set Y)
  结论: h ⁻¹' closure s = closure (h ⁻¹' s)
  证明: h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _

Depends on / 依赖: continuous, h.continuous, h.isOpenMap.preimage_closure_eq_closure_preimage, isOpenMap, preimage_closure_eq_closure_preimage
-/
theorem preimage_closure (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
  h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _

/--
theorem `image_closure` / 定理 `image_closure`

English:
theorem image_closure
  given: (h : X ≃ₜ Y) (s : Set X)
  statement: h '' closure s = closure (h '' s)
  proof: by
  rw [← preimage_symm]; rw [preimage_closure]

中文:
定理 image_closure
  条件: (h : X ≃ₜ Y) (s : Set X)
  结论: h '' closure s = closure (h '' s)
  证明: by
  rw [← preimage_symm]; rw [preimage_closure]

Depends on / 依赖: preimage_closure, preimage_symm
-/
theorem image_closure (h : X ≃ₜ Y) (s : Set X) : h '' closure s = closure (h '' s) := by
  rw [← preimage_symm]; rw [preimage_closure]

/--
theorem `preimage_interior` / 定理 `preimage_interior`

English:
theorem preimage_interior
  given: (h : X ≃ₜ Y) (s : Set Y)
  statement: h ⁻¹' interior s = interior (h ⁻¹' s)
  proof: h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _

中文:
定理 preimage_interior
  条件: (h : X ≃ₜ Y) (s : Set Y)
  结论: h ⁻¹' interior s = interior (h ⁻¹' s)
  证明: h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _

Depends on / 依赖: continuous, h.continuous, h.isOpenMap.preimage_interior_eq_interior_preimage, isOpenMap, preimage_interior_eq_interior_preimage
-/
theorem preimage_interior (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' interior s = interior (h ⁻¹' s) :=
  h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _

/--
theorem `image_interior` / 定理 `image_interior`

English:
theorem image_interior
  given: (h : X ≃ₜ Y) (s : Set X)
  statement: h '' interior s = interior (h '' s)
  proof: by
  rw [← preimage_symm]; rw [preimage_interior]

中文:
定理 image_interior
  条件: (h : X ≃ₜ Y) (s : Set X)
  结论: h '' interior s = interior (h '' s)
  证明: by
  rw [← preimage_symm]; rw [preimage_interior]

Depends on / 依赖: preimage_interior, preimage_symm
-/
theorem image_interior (h : X ≃ₜ Y) (s : Set X) : h '' interior s = interior (h '' s) := by
  rw [← preimage_symm]; rw [preimage_interior]

/--
theorem `preimage_frontier` / 定理 `preimage_frontier`

English:
theorem preimage_frontier
  given: (h : X ≃ₜ Y) (s : Set Y)
  statement: h ⁻¹' frontier s = frontier (h ⁻¹' s)
  proof: h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _

中文:
定理 preimage_frontier
  条件: (h : X ≃ₜ Y) (s : Set Y)
  结论: h ⁻¹' frontier s = frontier (h ⁻¹' s)
  证明: h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _

Depends on / 依赖: continuous, h.continuous, h.isOpenMap.preimage_frontier_eq_frontier_preimage, isOpenMap, preimage_frontier_eq_frontier_preimage
-/
theorem preimage_frontier (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' frontier s = frontier (h ⁻¹' s) :=
  h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _

/--
theorem `image_frontier` / 定理 `image_frontier`

English:
theorem image_frontier
  given: (h : X ≃ₜ Y) (s : Set X)
  statement: h '' frontier s = frontier (h '' s)
  proof: by
  rw [← preimage_symm]; rw [preimage_frontier]

@[simp]

中文:
定理 image_frontier
  条件: (h : X ≃ₜ Y) (s : Set X)
  结论: h '' frontier s = frontier (h '' s)
  证明: by
  rw [← preimage_symm]; rw [preimage_frontier]

@[simp]

Depends on / 依赖: preimage_frontier, preimage_symm
-/
theorem image_frontier (h : X ≃ₜ Y) (s : Set X) : h '' frontier s = frontier (h '' s) := by
  rw [← preimage_symm]; rw [preimage_frontier]

@[simp]
/--
theorem `comp_continuous_iff` / 定理 `comp_continuous_iff`

English:
theorem comp_continuous_iff
  given: (h : X ≃ₜ Y) {f : Z -> X}
  statement: Continuous (h ∘ f) ↔ Continuous f
  proof: h.isInducing.continuous_iff.symm

@[simp]

中文:
定理 comp_continuous_iff
  条件: (h : X ≃ₜ Y) {f : Z -> X}
  结论: Continuous (h ∘ f) ↔ Continuous f
  证明: h.isInducing.continuous_iff.symm

@[simp]

Depends on / 依赖: continuous_iff, h.isInducing.continuous_iff.symm, isInducing
-/
theorem comp_continuous_iff (h : X ≃ₜ Y) {f : Z -> X} : Continuous (h ∘ f) ↔ Continuous f :=
  h.isInducing.continuous_iff.symm

@[simp]
/--
theorem `comp_continuous_iff'` / 定理 `comp_continuous_iff'`

English:
theorem comp_continuous_iff'
  given: (h : X ≃ₜ Y) {f : Y -> Z}
  statement: Continuous (f ∘ h) ↔ Continuous f
  proof: h.isQuotientMap.continuous_iff.symm

中文:
定理 comp_continuous_iff'
  条件: (h : X ≃ₜ Y) {f : Y -> Z}
  结论: Continuous (f ∘ h) ↔ Continuous f
  证明: h.isQuotientMap.continuous_iff.symm

Depends on / 依赖: continuous_iff, h.isQuotientMap.continuous_iff.symm, isQuotientMap
-/
theorem comp_continuous_iff' (h : X ≃ₜ Y) {f : Y -> Z} : Continuous (f ∘ h) ↔ Continuous f :=
  h.isQuotientMap.continuous_iff.symm

/--
theorem `comp_continuousAt_iff` / 定理 `comp_continuousAt_iff`

English:
theorem comp_continuousAt_iff
  given: (h : X ≃ₜ Y) (f : Z -> X) (z : Z)
  proof: h.isInducing.continuousAt_iff.symm

中文:
定理 comp_continuousAt_iff
  条件: (h : X ≃ₜ Y) (f : Z -> X) (z : Z)
  证明: h.isInducing.continuousAt_iff.symm

Depends on / 依赖: continuousAt_iff, h.isInducing.continuousAt_iff.symm, isInducing
-/
theorem comp_continuousAt_iff (h : X ≃ₜ Y) (f : Z -> X) (z : Z) :
    ContinuousAt (h ∘ f) z ↔ ContinuousAt f z :=
  h.isInducing.continuousAt_iff.symm

/--
theorem `comp_continuousAt_iff'` / 定理 `comp_continuousAt_iff'`

English:
theorem comp_continuousAt_iff'
  given: (h : X ≃ₜ Y) (f : Y -> Z) (x : X)
  proof: h.isInducing.continuousAt_iff' (by simp)

@[simp]

中文:
定理 comp_continuousAt_iff'
  条件: (h : X ≃ₜ Y) (f : Y -> Z) (x : X)
  证明: h.isInducing.continuousAt_iff' (by simp)

@[simp]

Depends on / 依赖: continuousAt_iff, h.isInducing.continuousAt_iff, isInducing
-/
theorem comp_continuousAt_iff' (h : X ≃ₜ Y) (f : Y -> Z) (x : X) :
    ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.isInducing.continuousAt_iff' (by simp)

@[simp]
/--
theorem `comp_isOpenMap_iff` / 定理 `comp_isOpenMap_iff`

English:
theorem comp_isOpenMap_iff
  given: (h : X ≃ₜ Y) {f : Z -> X}
  statement: IsOpenMap (h ∘ f) ↔ IsOpenMap f
  proof: by
  refine ⟨?_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.id_comp f]; rw [← h.symm_comp_self]; rw [Function.comp_assoc]
  exact h.symm.isOpenMap.comp hf

@[simp]

中文:
定理 comp_isOpenMap_iff
  条件: (h : X ≃ₜ Y) {f : Z -> X}
  结论: IsOpenMap (h ∘ f) ↔ IsOpenMap f
  证明: by
  refine ⟨?_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.id_comp f]; rw [← h.symm_comp_self]; rw [Function.comp_assoc]
  exact h.symm.isOpenMap.comp hf

@[simp]

Depends on / 依赖: Function, Function.comp_assoc, Function.id_comp, comp_assoc, h.isOpenMap.comp, h.symm.isOpenMap.comp, h.symm_comp_self, id_comp, isOpenMap, symm_comp_self
-/
theorem comp_isOpenMap_iff (h : X ≃ₜ Y) {f : Z -> X} : IsOpenMap (h ∘ f) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.id_comp f]; rw [← h.symm_comp_self]; rw [Function.comp_assoc]
  exact h.symm.isOpenMap.comp hf

@[simp]
/--
theorem `comp_isOpenMap_iff'` / 定理 `comp_isOpenMap_iff'`

English:
theorem comp_isOpenMap_iff'
  given: (h : X ≃ₜ Y) {f : Y -> Z}
  statement: IsOpenMap (f ∘ h) ↔ IsOpenMap f
  proof: by
  refine ⟨?_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp_id f]; rw [← h.self_comp_symm]; rw [← Function.comp_assoc]
  exact hf.comp h.symm.isOpenMap

中文:
定理 comp_isOpenMap_iff'
  条件: (h : X ≃ₜ Y) {f : Y -> Z}
  结论: IsOpenMap (f ∘ h) ↔ IsOpenMap f
  证明: by
  refine ⟨?_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp_id f]; rw [← h.self_comp_symm]; rw [← Function.comp_assoc]
  exact hf.comp h.symm.isOpenMap

Depends on / 依赖: Function, Function.comp_assoc, Function.comp_id, comp_assoc, comp_id, h.isOpenMap, h.self_comp_symm, h.symm.isOpenMap, hf.comp, isOpenMap, self_comp_symm
-/
theorem comp_isOpenMap_iff' (h : X ≃ₜ Y) {f : Y -> Z} : IsOpenMap (f ∘ h) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp_id f]; rw [← h.self_comp_symm]; rw [← Function.comp_assoc]
  exact hf.comp h.symm.isOpenMap

/-- Open quotient maps are preserved by precomposing with a homeomorphism. -/
@[simp]
/--
theorem `isOpenQuotient_comp_iff` / 定理 `isOpenQuotient_comp_iff`

English:
theorem isOpenQuotient_comp_iff
  given: (e : X ≃ₜ Y) {f : Y -> Z}
  proof: ⟨fun h => by simpa [Function.comp_assoc] using h.comp e.symm.isOpenQuotientMap,
    fun hf => hf.comp e.isOpenQuotientMap⟩

中文:
定理 isOpenQuotient_comp_iff
  条件: (e : X ≃ₜ Y) {f : Y -> Z}
  证明: ⟨fun h => by simpa [Function.comp_assoc] using h.comp e.symm.isOpenQuotientMap,
    fun hf => hf.comp e.isOpenQuotientMap⟩

Depends on / 依赖: Function, Function.comp_assoc, comp_assoc, e.isOpenQuotientMap, e.symm.isOpenQuotientMap, h.comp, hf.comp, isOpenQuotientMap
-/
theorem isOpenQuotient_comp_iff (e : X ≃ₜ Y) {f : Y -> Z} :
    IsOpenQuotientMap (f ∘ e) ↔ IsOpenQuotientMap f :=
  ⟨fun h => by simpa [Function.comp_assoc] using h.comp e.symm.isOpenQuotientMap,
    fun hf => hf.comp e.isOpenQuotientMap⟩

/-- Open quotient maps are preserved by postcomposing with a homeomorphism. -/
@[simp]
/--
theorem `comp_isOpenQuotientMap_iff` / 定理 `comp_isOpenQuotientMap_iff`

English:
theorem comp_isOpenQuotientMap_iff
  given: (e : Y ≃ₜ Z) {f : X -> Y}
  proof: ⟨fun h => by simpa [← Function.comp_assoc] using e.symm.isOpenQuotientMap.comp h,
    fun hf => e.isOpenQuotientMap.comp hf⟩

中文:
定理 comp_isOpenQuotientMap_iff
  条件: (e : Y ≃ₜ Z) {f : X -> Y}
  证明: ⟨fun h => by simpa [← Function.comp_assoc] using e.symm.isOpenQuotientMap.comp h,
    fun hf => e.isOpenQuotientMap.comp hf⟩

Depends on / 依赖: Function, Function.comp_assoc, comp_assoc, e.isOpenQuotientMap.comp, e.symm.isOpenQuotientMap.comp, isOpenQuotientMap
-/
theorem comp_isOpenQuotientMap_iff (e : Y ≃ₜ Z) {f : X -> Y} :
    IsOpenQuotientMap (e ∘ f) ↔ IsOpenQuotientMap f :=
  ⟨fun h => by simpa [← Function.comp_assoc] using e.symm.isOpenQuotientMap.comp h,
    fun hf => e.isOpenQuotientMap.comp hf⟩

variable (X Y) in
/-- If both `X` and `Y` have a unique element, then `X ≃ₜ Y`. -/
@[simps!]
/--
Definition of `homeomorphOfUnique` / `homeomorphOfUnique` 的定义

English:
definition homeomorphOfUnique
  signature: [Unique X] [Unique Y]
  body: { Equiv.ofUnique X Y with }

@[simp]

中文:
定义 homeomorphOfUnique
  签名: [Unique X] [Unique Y]
  定义体: { Equiv.ofUnique X Y with }

@[simp]

Depends on / 依赖: Equiv.ofUnique, ofUnique
-/
def homeomorphOfUnique [Unique X] [Unique Y] : X ≃ₜ Y :=
  { Equiv.ofUnique X Y with }

@[simp]
/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  given: (h : X ≃ₜ Y) (x : X)
  statement: map h (𝓝 x) = 𝓝 (h x)
  proof: h.isEmbedding.map_nhds_of_mem _ (by simp)

中文:
定理 map_nhds_eq
  条件: (h : X ≃ₜ Y) (x : X)
  结论: map h (𝓝 x) = 𝓝 (h x)
  证明: h.isEmbedding.map_nhds_of_mem _ (by simp)

Depends on / 依赖: h.isEmbedding.map_nhds_of_mem, isEmbedding, map_nhds_of_mem
-/
theorem map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) = 𝓝 (h x) :=
  h.isEmbedding.map_nhds_of_mem _ (by simp)

/--
theorem `symm_map_nhds_eq` / 定理 `symm_map_nhds_eq`

English:
theorem symm_map_nhds_eq
  given: (h : X ≃ₜ Y) (x : X)
  statement: map h.symm (𝓝 (h x)) = 𝓝 x
  proof: by
  rw [h.symm.map_nhds_eq]; rw [h.symm_apply_apply]

中文:
定理 symm_map_nhds_eq
  条件: (h : X ≃ₜ Y) (x : X)
  结论: map h.symm (𝓝 (h x)) = 𝓝 x
  证明: by
  rw [h.symm.map_nhds_eq]; rw [h.symm_apply_apply]

Depends on / 依赖: h.symm.map_nhds_eq, h.symm_apply_apply, map_nhds_eq, symm_apply_apply
-/
theorem symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq]; rw [h.symm_apply_apply]

/--
theorem `nhds_eq_comap` / 定理 `nhds_eq_comap`

English:
theorem nhds_eq_comap
  given: (h : X ≃ₜ Y) (x : X)
  statement: 𝓝 x = comap h (𝓝 (h x))
  proof: h.isInducing.nhds_eq_comap x

@[simp]

中文:
定理 nhds_eq_comap
  条件: (h : X ≃ₜ Y) (x : X)
  结论: 𝓝 x = comap h (𝓝 (h x))
  证明: h.isInducing.nhds_eq_comap x

@[simp]

Depends on / 依赖: h.isInducing.nhds_eq_comap, isInducing, nhds_eq_comap
-/
theorem nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.isInducing.nhds_eq_comap x

@[simp]
/--
theorem `comap_nhds_eq` / 定理 `comap_nhds_eq`

English:
theorem comap_nhds_eq
  given: (h : X ≃ₜ Y) (y : Y)
  statement: comap h (𝓝 y) = 𝓝 (h.symm y)
  proof: by
  rw [h.nhds_eq_comap]; rw [h.apply_symm_apply]

中文:
定理 comap_nhds_eq
  条件: (h : X ≃ₜ Y) (y : Y)
  结论: comap h (𝓝 y) = 𝓝 (h.symm y)
  证明: by
  rw [h.nhds_eq_comap]; rw [h.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, h.apply_symm_apply, h.nhds_eq_comap, nhds_eq_comap
-/
theorem comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap]; rw [h.apply_symm_apply]

/--
theorem `isClosed_setOfPred_iff` / 定理 `isClosed_setOfPred_iff`

English:
theorem isClosed_setOfPred_iff
  statement: {p : X -> Prop} {q : Y -> Prop} (f : X ≃ₜ Y) (hs : IsClopen {x | p x})
  proof: by
  simpa [iff_def] using! (isClosed_imp hs.2 (f.isClosed_preimage.2 ht.1)).inter
    (isClosed_imp (f.isOpen_preimage.2 ht.2) hs.1)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_iff := isClosed_setOfPred_iff

中文:
定理 isClosed_setOfPred_iff
  结论: {p : X -> 命题} {q : Y -> 命题} (f : X ≃ₜ Y) (hs : IsClopen {x | p x})
  证明: by
  simpa [iff_def] using! (isClosed_imp hs.2 (f.isClosed_preimage.2 ht.1)).inter
    (isClosed_imp (f.isOpen_preimage.2 ht.2) hs.1)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_iff := isClosed_setOfPred_iff

Depends on / 依赖: f.isClosed_preimage, f.isOpen_preimage, iff_def, isClosed_imp, isClosed_preimage, isOpen_preimage
-/
theorem isClosed_setOfPred_iff {p : X -> Prop} {q : Y -> Prop} (f : X ≃ₜ Y) (hs : IsClopen {x | p x})
    (ht : IsClopen {y | q y}) : IsClosed { x : X | p x ↔ q (f x) } := by
  simpa [iff_def] using! (isClosed_imp hs.2 (f.isClosed_preimage.2 ht.1)).inter
    (isClosed_imp (f.isOpen_preimage.2 ht.2) hs.1)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_iff := isClosed_setOfPred_iff

end Homeomorph

namespace Equiv
variable {Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- An equivalence between topological spaces respecting openness is a homeomorphism. -/
@[simps toEquiv]
/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (e : X ≃ Y) (he : forall s, IsOpen (e ⁻¹' s) ↔ IsOpen s)
  body: e
  continuous_toFun := continuous_def.2 fun _ => (he _).2
  continuous_invFun := continuous_def.2 fun s => by simpa using (he (e.symm ⁻¹' s)).1

中文:
定义 toHomeomorph
  签名: (e : X ≃ Y) (he : 对任意 s, IsOpen (e ⁻¹' s) ↔ IsOpen s)
  定义体: e
  continuous_toFun := continuous_def.2 fun _ => (he _).2
  continuous_invFun := continuous_def.2 fun s => by simpa using (he (e.symm ⁻¹' s)).1
-/
def toHomeomorph (e : X ≃ Y) (he : forall s, IsOpen (e ⁻¹' s) ↔ IsOpen s) : X ≃ₜ Y where
  toEquiv := e
  continuous_toFun := continuous_def.2 fun _ => (he _).2
  continuous_invFun := continuous_def.2 fun s => by simpa using (he (e.symm ⁻¹' s)).1

/--
lemma `coe_toHomeomorph` / 引理 `coe_toHomeomorph`

English:
lemma coe_toHomeomorph
  given: (e : X ≃ Y) (he)
  statement: ⇑(e.toHomeomorph he) = e
  proof: rfl

中文:
引理 coe_toHomeomorph
  条件: (e : X ≃ Y) (he)
  结论: ⇑(e.toHomeomorph he) = e
  证明: rfl
-/
@[simp] lemma coe_toHomeomorph (e : X ≃ Y) (he) : ⇑(e.toHomeomorph he) = e := rfl
/--
lemma `toHomeomorph_apply` / 引理 `toHomeomorph_apply`

English:
lemma toHomeomorph_apply
  given: (e : X ≃ Y) (he) (x : X)
  statement: e.toHomeomorph he x = e x
  proof: rfl

中文:
引理 toHomeomorph_apply
  条件: (e : X ≃ Y) (he) (x : X)
  结论: e.toHomeomorph he x = e x
  证明: rfl
-/
lemma toHomeomorph_apply (e : X ≃ Y) (he) (x : X) : e.toHomeomorph he x = e x := rfl

/--
lemma `toHomeomorph_refl` / 引理 `toHomeomorph_refl`

English:
lemma toHomeomorph_refl
  proof: rfl

中文:
引理 toHomeomorph_refl
  证明: rfl
-/
@[simp] lemma toHomeomorph_refl :
    (Equiv.refl X).toHomeomorph (fun _s => Iff.rfl) = Homeomorph.refl _ := rfl

/--
lemma `symm_toHomeomorph` / 引理 `symm_toHomeomorph`

English:
lemma symm_toHomeomorph
  given: (e : X ≃ Y) (he)
  proof: rfl

中文:
引理 symm_toHomeomorph
  条件: (e : X ≃ Y) (he)
  证明: rfl
-/
@[simp] lemma symm_toHomeomorph (e : X ≃ Y) (he) :
    (e.toHomeomorph he).symm = e.symm.toHomeomorph fun s => by convert! (he _).symm; simp := rfl

/--
lemma `toHomeomorph_trans` / 引理 `toHomeomorph_trans`

English:
lemma toHomeomorph_trans
  given: (e : X ≃ Y) (f : Y ≃ Z) (he hf)
  proof: rfl

中文:
引理 toHomeomorph_trans
  条件: (e : X ≃ Y) (f : Y ≃ Z) (he hf)
  证明: rfl
-/
lemma toHomeomorph_trans (e : X ≃ Y) (f : Y ≃ Z) (he hf) :
    (e.trans f).toHomeomorph (fun _s => (he _).trans (hf _)) =
    (e.toHomeomorph he).trans (f.toHomeomorph hf) := rfl

/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps toEquiv]
/--
Definition of `toHomeomorphOfIsInducing` / `toHomeomorphOfIsInducing` 的定义

English:
definition toHomeomorphOfIsInducing
  signature: (f : X ≃ Y) (hf : IsInducing f)
  body: { f with
    continuous_toFun := hf.continuous
continuous_invFun := hf.continuous_iff.2 by simpa using continuous_id }

中文:
定义 toHomeomorphOfIsInducing
  签名: (f : X ≃ Y) (hf : IsInducing f)
  定义体: { f with
    continuous_toFun := hf.continuous
continuous_invFun := hf.continuous_iff.2 by simpa using continuous_id }

Depends on / 依赖: continuous, continuous_id, continuous_iff, continuous_invFun, continuous_toFun, hf.continuous, hf.continuous_iff
-/
def toHomeomorphOfIsInducing (f : X ≃ Y) (hf : IsInducing f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf.continuous
continuous_invFun := hf.continuous_iff.2 by simpa using continuous_id }

/--
lemma `toHomeomorphOfIsInducing_apply` / 引理 `toHomeomorphOfIsInducing_apply`

English:
lemma toHomeomorphOfIsInducing_apply
  given: (f : X ≃ Y) (hf : IsInducing f)
  proof: rfl

中文:
引理 toHomeomorphOfIsInducing_apply
  条件: (f : X ≃ Y) (hf : IsInducing f)
  证明: rfl
-/
@[simp] lemma toHomeomorphOfIsInducing_apply (f : X ≃ Y) (hf : IsInducing f) :
    ⇑(f.toHomeomorphOfIsInducing hf) = f := rfl

/--
lemma `toHomeomorphOfIsInducing_symm_apply` / 引理 `toHomeomorphOfIsInducing_symm_apply`

English:
lemma toHomeomorphOfIsInducing_symm_apply
  given: (f : X ≃ Y) (hf : IsInducing f)
  proof: rfl

中文:
引理 toHomeomorphOfIsInducing_symm_apply
  条件: (f : X ≃ Y) (hf : IsInducing f)
  证明: rfl
-/
@[simp] lemma toHomeomorphOfIsInducing_symm_apply (f : X ≃ Y) (hf : IsInducing f) :
    ⇑(f.toHomeomorphOfIsInducing hf).symm = f.symm := rfl

/-- If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphism. -/
@[simps! toEquiv]
/--
Definition of `toHomeomorphOfContinuousOpen` / `toHomeomorphOfContinuousOpen` 的定义

English:
definition toHomeomorphOfContinuousOpen
  signature: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e)
  body: e.toHomeomorphOfIsInducing
.toIsInducing IsOpenEmbedding.of_continuous_injective_isOpenMap h₁ e.injective h₂

@[simp]

中文:
定义 toHomeomorphOfContinuousOpen
  签名: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e)
  定义体: e.toHomeomorphOfIsInducing
.toIsInducing IsOpenEmbedding.of_continuous_injective_isOpenMap h₁ e.injective h₂

@[simp]

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.of_continuous_injective_isOpenMap, e.injective, e.toHomeomorphOfIsInducing, injective, of_continuous_injective_isOpenMap, toHomeomorphOfIsInducing, toIsInducing
-/
def toHomeomorphOfContinuousOpen (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) : X ≃ₜ Y :=
e.toHomeomorphOfIsInducing
.toIsInducing IsOpenEmbedding.of_continuous_injective_isOpenMap h₁ e.injective h₂

@[simp]
/--
theorem `toHomeomorphOfContinuousOpen_apply` / 定理 `toHomeomorphOfContinuousOpen_apply`

English:
theorem toHomeomorphOfContinuousOpen_apply
  given: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e)
  proof: rfl

@[simp]

中文:
定理 toHomeomorphOfContinuousOpen_apply
  条件: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e)
  证明: rfl

@[simp]
-/
theorem toHomeomorphOfContinuousOpen_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    ⇑(e.toHomeomorphOfContinuousOpen h₁ h₂) = e := rfl

@[simp]
/--
theorem `toHomeomorphOfContinuousOpen_symm_apply` / 定理 `toHomeomorphOfContinuousOpen_symm_apply`

English:
theorem toHomeomorphOfContinuousOpen_symm_apply
  given: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e)
  proof: rfl

中文:
定理 toHomeomorphOfContinuousOpen_symm_apply
  条件: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e)
  证明: rfl
-/
theorem toHomeomorphOfContinuousOpen_symm_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    ⇑(e.toHomeomorphOfContinuousOpen h₁ h₂).symm = e.symm := rfl

/-- If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphism. -/
@[simps! toEquiv]
/--
Definition of `toHomeomorphOfContinuousClosed` / `toHomeomorphOfContinuousClosed` 的定义

English:
definition toHomeomorphOfContinuousClosed
  signature: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e)
  body: e.toHomeomorphOfIsInducing
.toIsInducing IsClosedEmbedding.of_continuous_injective_isClosedMap h₁ e.injective h₂

@[simp]

中文:
定义 toHomeomorphOfContinuousClosed
  签名: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e)
  定义体: e.toHomeomorphOfIsInducing
.toIsInducing IsClosedEmbedding.of_continuous_injective_isClosedMap h₁ e.injective h₂

@[simp]

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.of_continuous_injective_isClosedMap, e.injective, e.toHomeomorphOfIsInducing, injective, of_continuous_injective_isClosedMap, toHomeomorphOfIsInducing, toIsInducing
-/
def toHomeomorphOfContinuousClosed (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) : X ≃ₜ Y :=
e.toHomeomorphOfIsInducing
.toIsInducing IsClosedEmbedding.of_continuous_injective_isClosedMap h₁ e.injective h₂

@[simp]
/--
theorem `toHomeomorphOfContinuousClosed_apply` / 定理 `toHomeomorphOfContinuousClosed_apply`

English:
theorem toHomeomorphOfContinuousClosed_apply
  given: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e)
  proof: rfl

@[simp]

中文:
定理 toHomeomorphOfContinuousClosed_apply
  条件: (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e)
  证明: rfl

@[simp]
-/
theorem toHomeomorphOfContinuousClosed_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) :
    ⇑(e.toHomeomorphOfContinuousClosed h₁ h₂) = e := rfl

@[simp]
/--
theorem `toHomeomorphOfContinuousClosed_symm_apply` / 定理 `toHomeomorphOfContinuousClosed_symm_apply`

English:
theorem toHomeomorphOfContinuousClosed_symm_apply
  proof: rfl

中文:
定理 toHomeomorphOfContinuousClosed_symm_apply
  证明: rfl
-/
theorem toHomeomorphOfContinuousClosed_symm_apply
    (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) :
    ⇑(e.toHomeomorphOfContinuousClosed h₁ h₂).symm = e.symm := rfl

/--
Definition of `toHomeomorphOfDiscrete` / `toHomeomorphOfDiscrete` 的定义

English:
definition toHomeomorphOfDiscrete
  signature: [DiscreteTopology X] [DiscreteTopology Y] (e : X ≃ Y)
  body: e.toHomeomorph (by simp)

中文:
定义 toHomeomorphOfDiscrete
  签名: [DiscreteTopology X] [DiscreteTopology Y] (e : X ≃ Y)
  定义体: e.toHomeomorph (by simp)

Depends on / 依赖: e.toHomeomorph, toHomeomorph
-/
def toHomeomorphOfDiscrete [DiscreteTopology X] [DiscreteTopology Y] (e : X ≃ Y) : X ≃ₜ Y :=
  e.toHomeomorph (by simp)

end Equiv

/--
Definition of `HomeomorphClass` / `HomeomorphClass` 的定义

English:
class HomeomorphClass
  parameters: (F : Type*) (A B : outParam Type*)
  axioms and operations (2):
    - map_continuous : forall (f : F), Continuous f
    - inv_continuous : forall (f : F), Continuous (h.inv f)

中文:
类 HomeomorphClass
  参数: (F : 类型) (A B : outParam 类型)
  公理与运算 (2 个):
    - map_continuous : 对任意 (f : F), Continuous f
    - inv_continuous : 对任意 (f : F), Continuous (h.inv f)
-/
class HomeomorphClass (F : Type*) (A B : outParam Type*)
    [TopologicalSpace A] [TopologicalSpace B] [h : EquivLike F A B] : Prop where
  map_continuous : forall (f : F), Continuous f
  inv_continuous : forall (f : F), Continuous (h.inv f)

namespace HomeomorphClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `HomeomorphClass F α β` into an actual
`Homeomorph`. This is declared as the default coercion from `F` to `α ≃ₜ β`. -/
@[coe]
/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: [h : HomeomorphClass F α β] (f : F)
  body: { (f : α ≃ β) with
    continuous_toFun := h.map_continuous f
    continuous_invFun := h.inv_continuous f }

@[simp]

中文:
定义 toHomeomorph
  签名: [h : HomeomorphClass F α β] (f : F)
  定义体: { (f : α ≃ β) with
    continuous_toFun := h.map_continuous f
    continuous_invFun := h.inv_continuous f }

@[simp]

Depends on / 依赖: continuous_invFun, continuous_toFun, h.inv_continuous, h.map_continuous, inv_continuous, map_continuous
-/
def toHomeomorph [h : HomeomorphClass F α β] (f : F) : α ≃ₜ β :=
  { (f : α ≃ β) with
    continuous_toFun := h.map_continuous f
    continuous_invFun := h.inv_continuous f }

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: [h : HomeomorphClass F α β] (f : F)
  statement: ⇑(h.toHomeomorph f) = ⇑f
  proof: rfl

中文:
定理 coe_coe
  条件: [h : HomeomorphClass F α β] (f : F)
  结论: ⇑(h.toHomeomorph f) = ⇑f
  证明: rfl
-/
theorem coe_coe [h : HomeomorphClass F α β] (f : F) : ⇑(h.toHomeomorph f) = ⇑f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HomeomorphClass
  signature: F α β] : CoeOut F (α ≃ₜ β)
  body: ⟨HomeomorphClass.toHomeomorph⟩

中文:
实例 [HomeomorphClass
  签名: F α β] : CoeOut F (α ≃ₜ β)
  定义体: ⟨HomeomorphClass.toHomeomorph⟩

Depends on / 依赖: HomeomorphClass, HomeomorphClass.toHomeomorph, toHomeomorph
-/
instance [HomeomorphClass F α β] : CoeOut F (α ≃ₜ β) :=
  ⟨HomeomorphClass.toHomeomorph⟩

/--
theorem `toHomeomorph_injective` / 定理 `toHomeomorph_injective`

English:
theorem toHomeomorph_injective
  given: [HomeomorphClass F α β]
  statement: Function.Injective ((↑) : F -> α ≃ₜ β)
  proof: fun _ _ e => DFunLike.ext _ _ fun a => congr_arg (fun e : α ≃ₜ β => e.toFun a) e

中文:
定理 toHomeomorph_injective
  条件: [HomeomorphClass F α β]
  结论: Function.Injective ((↑) : F -> α ≃ₜ β)
  证明: fun _ _ e => DFunLike.ext _ _ fun a => congr_arg (fun e : α ≃ₜ β => e.toFun a) e

Depends on / 依赖: DFunLike, DFunLike.ext, congr_arg, e.toFun
-/
theorem toHomeomorph_injective [HomeomorphClass F α β] : Function.Injective ((↑) : F -> α ≃ₜ β) :=
  fun _ _ e => DFunLike.ext _ _ fun a => congr_arg (fun e : α ≃ₜ β => e.toFun a) e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HomeomorphClass
  signature: F α β] : ContinuousMapClass F α β where
  body: map_continuous f

中文:
实例 [HomeomorphClass
  签名: F α β] : ContinuousMapClass F α β where
  定义体: map_continuous f

Depends on / 依赖: map_continuous
-/
instance [HomeomorphClass F α β] : ContinuousMapClass F α β where
  map_continuous f := map_continuous f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomeomorphClass (α ≃ₜ β) α β
  body: e.continuous_toFun
  inv_continuous e := e.continuous_invFun

中文:
实例 :
  签名: HomeomorphClass (α ≃ₜ β) α β
  定义体: e.continuous_toFun
  inv_continuous e := e.continuous_invFun

Depends on / 依赖: continuous_toFun, e.continuous_toFun
-/
instance : HomeomorphClass (α ≃ₜ β) α β where
  map_continuous e := e.continuous_toFun
  inv_continuous e := e.continuous_invFun

end HomeomorphClass

section IsHomeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X -> Y}

/--
Definition of `IsHomeomorph` / `IsHomeomorph` 的定义

English:
structure IsHomeomorph
  parameters: (f : X -> Y)
  axioms and operations (3):
    - continuous : Continuous f
    - isOpenMap : IsOpenMap f
    - bijective : Function.Bijective f

中文:
结构 IsHomeomorph
  参数: (f : X -> Y)
  公理与运算 (3 个):
    - continuous : Continuous f
    - isOpenMap : IsOpenMap f
    - bijective : Function.Bijective f

Depends on / 依赖: bijective, continuous, h.bijective, h.continuous, h.isOpenMap, isOpenMap
-/
structure IsHomeomorph (f : X -> Y) : Prop where
  continuous : Continuous f
  isOpenMap : IsOpenMap f
  bijective : Function.Bijective f

/--
theorem `Homeomorph.isHomeomorph` / 定理 `Homeomorph.isHomeomorph`

English:
theorem Homeomorph.isHomeomorph
  given: (h : X ≃ₜ Y)
  statement: IsHomeomorph h
  proof: ⟨h.continuous, h.isOpenMap, h.bijective⟩

中文:
定理 Homeomorph.isHomeomorph
  条件: (h : X ≃ₜ Y)
  结论: IsHomeomorph h
  证明: ⟨h.continuous, h.isOpenMap, h.bijective⟩
-/
protected theorem Homeomorph.isHomeomorph (h : X ≃ₜ Y) : IsHomeomorph h :=
  ⟨h.continuous, h.isOpenMap, h.bijective⟩

namespace IsHomeomorph

/-- Bundled homeomorphism constructed from a map that is a homeomorphism. -/
@[simps! toEquiv apply symm_apply]
/--
Definition of `homeomorph` / `homeomorph` 的定义

English:
definition homeomorph
  signature: (f : X -> Y) (hf : IsHomeomorph f)
  body: hf.1
  continuous_invFun :=
.continuous_symm_iff.2 hf.isOpenMap Equiv.ofBijective f hf.bijective
  toEquiv := Equiv.ofBijective f hf.bijective

中文:
定义 homeomorph
  签名: (f : X -> Y) (hf : IsHomeomorph f)
  定义体: hf.1
  continuous_invFun :=
.continuous_symm_iff.2 hf.isOpenMap Equiv.ofBijective f hf.bijective
  toEquiv := Equiv.ofBijective f hf.bijective
-/
noncomputable def homeomorph (f : X -> Y) (hf : IsHomeomorph f) : X ≃ₜ Y where
  continuous_toFun := hf.1
  continuous_invFun :=
.continuous_symm_iff.2 hf.isOpenMap Equiv.ofBijective f hf.bijective
  toEquiv := Equiv.ofBijective f hf.bijective

/--
lemma `injective` / 引理 `injective`

English:
lemma injective
  given: (hf : IsHomeomorph f)
  statement: Function.Injective f
  proof: hf.bijective.injective

中文:
引理 injective
  条件: (hf : IsHomeomorph f)
  结论: Function.Injective f
  证明: hf.bijective.injective
-/
protected lemma injective (hf : IsHomeomorph f) : Function.Injective f := hf.bijective.injective
/--
lemma `surjective` / 引理 `surjective`

English:
lemma surjective
  given: (hf : IsHomeomorph f)
  statement: Function.Surjective f
  proof: hf.bijective.surjective

中文:
引理 surjective
  条件: (hf : IsHomeomorph f)
  结论: Function.Surjective f
  证明: hf.bijective.surjective
-/
protected lemma surjective (hf : IsHomeomorph f) : Function.Surjective f := hf.bijective.surjective

/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: IsHomeomorph (@id X)
  proof: ⟨continuous_id, .id, Function.bijective_id⟩

中文:
引理 id
  结论: IsHomeomorph (@id X)
  证明: ⟨continuous_id, .id, Function.bijective_id⟩
-/
protected lemma id : IsHomeomorph (@id X) := ⟨continuous_id, .id, Function.bijective_id⟩

/--
theorem `image_interior` / 定理 `image_interior`

English:
theorem image_interior
  given: (hf : IsHomeomorph f) (s : Set X)
  proof: hf.homeomorph.image_interior s

中文:
定理 image_interior
  条件: (hf : IsHomeomorph f) (s : Set X)
  证明: hf.homeomorph.image_interior s

Depends on / 依赖: hf.homeomorph.image_interior, homeomorph, image_interior
-/
theorem image_interior (hf : IsHomeomorph f) (s : Set X) :
  f '' interior s = interior (f '' s) := hf.homeomorph.image_interior s

/--
theorem `image_closure` / 定理 `image_closure`

English:
theorem image_closure
  given: (hf : IsHomeomorph f) (s : Set X)
  proof: hf.homeomorph.image_closure s

中文:
定理 image_closure
  条件: (hf : IsHomeomorph f) (s : Set X)
  证明: hf.homeomorph.image_closure s

Depends on / 依赖: hf.homeomorph.image_closure, homeomorph, image_closure
-/
theorem image_closure (hf : IsHomeomorph f) (s : Set X) :
  f '' closure s = closure (f '' s) := hf.homeomorph.image_closure s

/--
theorem `image_frontier` / 定理 `image_frontier`

English:
theorem image_frontier
  given: (hf : IsHomeomorph f) (s : Set X)
  proof: hf.homeomorph.image_frontier s

中文:
定理 image_frontier
  条件: (hf : IsHomeomorph f) (s : Set X)
  证明: hf.homeomorph.image_frontier s

Depends on / 依赖: hf.homeomorph.image_frontier, homeomorph, image_frontier
-/
theorem image_frontier (hf : IsHomeomorph f) (s : Set X) :
  f '' frontier s = frontier (f '' s) := hf.homeomorph.image_frontier s

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {g : Y -> Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f)
  statement: IsHomeomorph (g ∘ f)
  proof: ⟨hg.1.comp hf.1, hg.2.comp hf.2, hg.3.comp hf.3⟩

中文:
引理 comp
  条件: {g : Y -> Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f)
  结论: IsHomeomorph (g ∘ f)
  证明: ⟨hg.1.comp hf.1, hg.2.comp hf.2, hg.3.comp hf.3⟩
-/
lemma comp {g : Y -> Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) : IsHomeomorph (g ∘ f) :=
  ⟨hg.1.comp hf.1, hg.2.comp hf.2, hg.3.comp hf.3⟩

end IsHomeomorph

end IsHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] in
/--
theorem `image_interior_preimage_comp` / 定理 `image_interior_preimage_comp`

English:
theorem image_interior_preimage_comp
  given: (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z)
  proof: by
  simp only [Set.preimage_comp, Set.image_comp, he.image_interior,
    Set.image_preimage_eq _ he.surjective]

中文:
定理 image_interior_preimage_comp
  条件: (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z)
  证明: by
  simp only [Set.preimage_comp, Set.image_comp, he.image_interior,
    Set.image_preimage_eq _ he.surjective]

Depends on / 依赖: Set.image_comp, Set.image_preimage_eq, Set.preimage_comp, he.image_interior, he.surjective, image_comp, image_interior, image_preimage_eq, preimage_comp, surjective
-/
theorem image_interior_preimage_comp (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z) :
    (f ∘ e) '' interior ((f ∘ e) ⁻¹' s) = f '' interior (f ⁻¹' s) := by
  simp only [Set.preimage_comp, Set.image_comp, he.image_interior,
    Set.image_preimage_eq _ he.surjective]

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] in
/--
theorem `image_frontier_preimage_comp` / 定理 `image_frontier_preimage_comp`

English:
theorem image_frontier_preimage_comp
  given: (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z)
  proof: by
  simp only [Set.preimage_comp, Set.image_comp, he.image_frontier,
    Set.image_preimage_eq _ he.surjective]

中文:
定理 image_frontier_preimage_comp
  条件: (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z)
  证明: by
  simp only [Set.preimage_comp, Set.image_comp, he.image_frontier,
    Set.image_preimage_eq _ he.surjective]

Depends on / 依赖: Set.image_comp, Set.image_preimage_eq, Set.preimage_comp, he.image_frontier, he.surjective, image_comp, image_frontier, image_preimage_eq, preimage_comp, surjective
-/
theorem image_frontier_preimage_comp (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z) :
    (f ∘ e) '' frontier ((f ∘ e) ⁻¹' s) = f '' frontier (f ⁻¹' s) := by
  simp only [Set.preimage_comp, Set.image_comp, he.image_frontier,
    Set.image_preimage_eq _ he.surjective]

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] in
/--
theorem `image_closure_preimage_comp` / 定理 `image_closure_preimage_comp`

English:
theorem image_closure_preimage_comp
  given: (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z)
  proof: by
  simp only [Set.preimage_comp, Set.image_comp, he.image_closure,
    Set.image_preimage_eq _ he.surjective]

中文:
定理 image_closure_preimage_comp
  条件: (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z)
  证明: by
  simp only [Set.preimage_comp, Set.image_comp, he.image_closure,
    Set.image_preimage_eq _ he.surjective]

Depends on / 依赖: Set.image_comp, Set.image_preimage_eq, Set.preimage_comp, he.image_closure, he.surjective, image_closure, image_comp, image_preimage_eq, preimage_comp, surjective
-/
theorem image_closure_preimage_comp (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z) (s : Set Z) :
    (f ∘ e) '' closure ((f ∘ e) ⁻¹' s) = f '' closure (f ⁻¹' s) := by
  simp only [Set.preimage_comp, Set.image_comp, he.image_closure,
    Set.image_preimage_eq _ he.surjective]
