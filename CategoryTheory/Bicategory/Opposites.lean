/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite bicategories

We construct the 1-cell opposite of a bicategory `B`, called `Bᵒᵖ`. It is defined as follows
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.

## Remarks
There are multiple notions of opposite categories for bicategories.
- There is 1-cell dual `Bᵒᵖ` as defined above.
- There is the 2-cell dual, `Cᶜᵒ` where only the 2-morphisms are reversed
- There is the bi-dual `Cᶜᵒᵒᵖ` where the directions of both the 1-morphisms and the 2-morphisms
  are reversed.

## TODO

* Define the 2-cell dual `Cᶜᵒ`.
* Provide various lemmas for going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.

Note: `Cᶜᵒᵒᵖ` is WIP by Christian Merten.

-/

@[expose] public section

universe w v u

open CategoryTheory Bicategory Opposite

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/--
Definition of `Hom2` / `Hom2` 的定义

English:
structure Hom2
  parameters: {a b : Bᵒᵖ} (f g : a ⟶ b)
  axioms and operations (2):
    - op2' : :
    - unop2 : f.unop ⟶ g.unop

中文:
结构 Hom2
  参数: {a b : Bᵒᵖ} (f g : a ⟶ b)
  公理与运算 (2 个):
    - op2' : :
    - unop2 : f.unop ⟶ g.unop
-/
structure Hom2 {a b : Bᵒᵖ} (f g : a ⟶ b) where
  op2' ::
  /-- `Bᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
  unop2 : f.unop ⟶ g.unop

open Hom2

@[simps!]
/--
Instance `homCategory` / 实例 `homCategory`

English:
instance homCategory
  signature: (a b : Bᵒᵖ)
  body: Hom2 f g
  id f := op2' (𝟙 f.unop)
  comp η θ := op2' (η.unop2 ≫ θ.unop2)

中文:
实例 homCategory
  签名: (a b : Bᵒᵖ)
  定义体: Hom2 f g
  id f := op2' (𝟙 f.unop)
  comp η θ := op2' (η.unop2 ≫ θ.unop2)
-/
instance homCategory (a b : Bᵒᵖ) : Category.{w} (a ⟶ b) where
  Hom f g := Hom2 f g
  id f := op2' (𝟙 f.unop)
  comp η θ := op2' (η.unop2 ≫ θ.unop2)

/--
Definition of `op2` / `op2` 的定义

English:
definition op2
  signature: {a b : B} {f g : a ⟶ b} (η : f ⟶ g)
  body: op2' η

@[simp]

中文:
定义 op2
  签名: {a b : B} {f g : a ⟶ b} (η : f ⟶ g)
  定义体: op2' η

@[simp]
-/
def op2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : f.op ⟶ g.op :=
  op2' η

@[simp]
/--
theorem `unop2_op2` / 定理 `unop2_op2`

English:
theorem unop2_op2
  given: {a b : B} {f g : a ⟶ b} (η : f ⟶ g)
  statement: (op2 η).unop2 = η
  proof: rfl

@[simp]

中文:
定理 unop2_op2
  条件: {a b : B} {f g : a ⟶ b} (η : f ⟶ g)
  结论: (op2 η).unop2 = η
  证明: rfl

@[simp]
-/
theorem unop2_op2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : (op2 η).unop2 = η :=
  rfl

@[simp]
/--
theorem `op2_unop2` / 定理 `op2_unop2`

English:
theorem op2_unop2
  given: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g)
  statement: op2 η.unop2 = η
  proof: rfl

@[simp]

中文:
定理 op2_unop2
  条件: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g)
  结论: op2 η.unop2 = η
  证明: rfl

@[simp]
-/
theorem op2_unop2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) : op2 η.unop2 = η :=
  rfl

@[simp]
/--
theorem `op2_comp` / 定理 `op2_comp`

English:
theorem op2_comp
  given: {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
  proof: rfl

@[simp]

中文:
定理 op2_comp
  条件: {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
  证明: rfl

@[simp]
-/
theorem op2_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    op2 (η ≫ θ) = (op2 η) ≫ (op2 θ) :=
  rfl

@[simp]
/--
theorem `op2_id` / 定理 `op2_id`

English:
theorem op2_id
  given: {a b : B} {f : a ⟶ b}
  statement: op2 (𝟙 f) = 𝟙 f.op
  proof: rfl

@[simp]

中文:
定理 op2_id
  条件: {a b : B} {f : a ⟶ b}
  结论: op2 (𝟙 f) = 𝟙 f.op
  证明: rfl

@[simp]

Depends on / 依赖: fromInitialModel, initiallySmall_of_initial_of_essentiallySmall
-/
theorem op2_id {a b : B} {f : a ⟶ b} : op2 (𝟙 f) = 𝟙 f.op :=
  rfl

@[simp]
/--
theorem `unop2_comp` / 定理 `unop2_comp`

English:
theorem unop2_comp
  given: {a b : Bᵒᵖ} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
  proof: rfl

@[simp]

中文:
定理 unop2_comp
  条件: {a b : Bᵒᵖ} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
  证明: rfl

@[simp]

Depends on / 依赖: fromInitialModel
-/
theorem unop2_comp {a b : Bᵒᵖ} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    unop2 (η ≫ θ) = unop2 η ≫ unop2 θ :=
  rfl

@[simp]
/--
theorem `unop2_id` / 定理 `unop2_id`

English:
theorem unop2_id
  given: {a b : Bᵒᵖ} {f : a ⟶ b}
  statement: unop2 (𝟙 f) = 𝟙 f.unop
  proof: rfl

@[simp]

中文:
定理 unop2_id
  条件: {a b : Bᵒᵖ} {f : a ⟶ b}
  结论: unop2 (𝟙 f) = 𝟙 f.unop
  证明: rfl

@[simp]

Depends on / 依赖: fromFinalModel
-/
theorem unop2_id {a b : Bᵒᵖ} {f : a ⟶ b} : unop2 (𝟙 f) = 𝟙 f.unop :=
  rfl

@[simp]
/--
theorem `unop2_id_bop` / 定理 `unop2_id_bop`

English:
theorem unop2_id_bop
  given: {a b : B} {f : a ⟶ b}
  statement: unop2 (𝟙 f.op) = 𝟙 f
  proof: rfl

@[simp]

中文:
定理 unop2_id_bop
  条件: {a b : B} {f : a ⟶ b}
  结论: unop2 (𝟙 f.op) = 𝟙 f
  证明: rfl

@[simp]
-/
theorem unop2_id_bop {a b : B} {f : a ⟶ b} : unop2 (𝟙 f.op) = 𝟙 f :=
  rfl

@[simp]
/--
theorem `op2_id_unbop` / 定理 `op2_id_unbop`

English:
theorem op2_id_unbop
  given: {a b : Bᵒᵖ} {f : a ⟶ b}
  statement: op2 (𝟙 f.unop) = 𝟙 f
  proof: rfl

中文:
定理 op2_id_unbop
  条件: {a b : Bᵒᵖ} {f : a ⟶ b}
  结论: op2 (𝟙 f.unop) = 𝟙 f
  证明: rfl
-/
theorem op2_id_unbop {a b : Bᵒᵖ} {f : a ⟶ b} : op2 (𝟙 f.unop) = 𝟙 f :=
  rfl

/-- The natural functor from the hom-category `a ⟶ b` in `B` to its bicategorical opposite
`bop b ⟶ bop a`. -/
@[simps]
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: (a b : B)
  body: f.op
  map η := op2 η

中文:
定义 opFunctor
  签名: (a b : B)
  定义体: f.op
  map η := op2 η

Depends on / 依赖: f.op
-/
def opFunctor (a b : B) : (a ⟶ b) ⥤ (op b ⟶ op a) where
  obj f := f.op
  map η := op2 η

/-- The functor from the hom-category `a ⟶ b` in `Bᵒᵖ` to its bicategorical opposite
`unop b ⟶ unop a`. -/
@[simps]
/--
Definition of `unopFunctor` / `unopFunctor` 的定义

English:
definition unopFunctor
  signature: (a b : Bᵒᵖ)
  body: f.unop
  map η := unop2 η

中文:
定义 unopFunctor
  签名: (a b : Bᵒᵖ)
  定义体: f.unop
  map η := unop2 η

Depends on / 依赖: f.unop
-/
def unopFunctor (a b : Bᵒᵖ) : (a ⟶ b) ⥤ (unop b ⟶ unop a) where
  obj f := f.unop
  map η := unop2 η

end Bicategory.Opposite

namespace CategoryTheory.Iso

open Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/--
Definition of `op2` / `op2` 的定义

English:
abbreviation op2
  signature: {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  body: (opFunctor a b).mapIso η

中文:
缩写 op2
  签名: {a b : B} {f g : a ⟶ b} (η : f ≅ g)
  定义体: (opFunctor a b).mapIso η

Depends on / 依赖: mapIso, opFunctor
-/
abbrev op2 {a b : B} {f g : a ⟶ b} (η : f ≅ g) : f.op ≅ g.op := (opFunctor a b).mapIso η

/--
Definition of `op2_unop` / `op2_unop` 的定义

English:
abbreviation op2_unop
  signature: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f.unop ≅ g.unop)
  body: (opFunctor b.unop a.unop).mapIso η

中文:
缩写 op2_unop
  签名: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f.unop ≅ g.unop)
  定义体: (opFunctor b.unop a.unop).mapIso η

Depends on / 依赖: a.unop, b.unop, mapIso, opFunctor
-/
abbrev op2_unop {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f.unop ≅ g.unop) : f ≅ g :=
  (opFunctor b.unop a.unop).mapIso η

/--
Definition of `unop2` / `unop2` 的定义

English:
abbreviation unop2
  signature: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g)
  body: (unopFunctor a b).mapIso η

中文:
缩写 unop2
  签名: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g)
  定义体: (unopFunctor a b).mapIso η

Depends on / 依赖: mapIso, unopFunctor
-/
abbrev unop2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : f.unop ≅ g.unop :=
  (unopFunctor a b).mapIso η

/--
Definition of `unop2_op` / `unop2_op` 的定义

English:
abbreviation unop2_op
  signature: {a b : B} {f g : a ⟶ b} (η : f.op ≅ g.op)
  body: (unopFunctor (op b) (op a)).mapIso η

@[simp]

中文:
缩写 unop2_op
  签名: {a b : B} {f g : a ⟶ b} (η : f.op ≅ g.op)
  定义体: (unopFunctor (op b) (op a)).mapIso η

@[simp]

Depends on / 依赖: mapIso, unopFunctor
-/
abbrev unop2_op {a b : B} {f g : a ⟶ b} (η : f.op ≅ g.op) : f ≅ g :=
  (unopFunctor (op b) (op a)).mapIso η

@[simp]
/--
theorem `unop2_op2` / 定理 `unop2_op2`

English:
theorem unop2_op2
  given: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g)
  statement: η.unop2.op2 = η
  proof: rfl

中文:
定理 unop2_op2
  条件: {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g)
  结论: η.unop2.op2 = η
  证明: rfl
-/
theorem unop2_op2 {a b : Bᵒᵖ} {f g : a ⟶ b} (η : f ≅ g) : η.unop2.op2 = η := rfl

end CategoryTheory.Iso

namespace Bicategory.Opposite

open Hom2

variable {B : Type u} [Bicategory.{w, v} B]

set_option backward.isDefEq.respectTransparency.types false in
/-- The 1-cell dual bicategory `Bᵒᵖ`.

It is defined as follows.
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.
-/
@[simps! homCategory_id_unop2 homCategory_comp_unop2 whiskerLeft_unop2 whiskerRight_unop2
  associator_hom_unop2 associator_inv_unop2 leftUnitor_hom_unop2 leftUnitor_inv_unop2
  rightUnitor_hom_unop2 rightUnitor_inv_unop2]
/--
Instance `bicategory` / 实例 `bicategory`

English:
instance bicategory
  signature: : Bicategory.{w, v} Bᵒᵖ where
  body: homCategory
whiskerLeft f g h η := op2 (unop2 η) ▷ f.unop
whiskerRight η h := op2 h.unop ◁ unop2 η
  associator f g h := (associator h.unop g.unop f.unop).op2_unop.symm
  leftUnitor f := (rightUnitor f.unop).op2_unop
  rightUnitor f := (leftUnitor f.unop).op2_unop
whisker_exchange η θ := congrArg op2 (whisker_exchange _ _).symm
whisker_assoc f g g' η i := congrArg op2 by simp
pentagon f g h i := congrArg op2 by simp
triangle f g := congrArg op2 by simp

@[simp]

中文:
实例 bicategory
  签名: : 双范畴.{w, v} Bᵒᵖ where
  定义体: homCategory
whiskerLeft f g h η := op2 (unop2 η) ▷ f.unop
whiskerRight η h := op2 h.unop ◁ unop2 η
  associator f g h := (associator h.unop g.unop f.unop).op2_unop.symm
  leftUnitor f := (rightUnitor f.unop).op2_unop
  rightUnitor f := (leftUnitor f.unop).op2_unop
whisker_exchange η θ := congrArg op2 (whisker_exchange _ _).symm
whisker_assoc f g g' η i := congrArg op2 by simp
pentagon f g h i := congrArg op2 by simp
triangle f g := congrArg op2 by simp

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl_obj, comp_obj, homCategory, incl_obj, infer_instance
-/
instance bicategory : Bicategory.{w, v} Bᵒᵖ where
  homCategory := homCategory
whiskerLeft f g h η := op2 (unop2 η) ▷ f.unop
whiskerRight η h := op2 h.unop ◁ unop2 η
  associator f g h := (associator h.unop g.unop f.unop).op2_unop.symm
  leftUnitor f := (rightUnitor f.unop).op2_unop
  rightUnitor f := (leftUnitor f.unop).op2_unop
whisker_exchange η θ := congrArg op2 (whisker_exchange _ _).symm
whisker_assoc f g g' η i := congrArg op2 by simp
pentagon f g h i := congrArg op2 by simp
triangle f g := congrArg op2 by simp

@[simp]
/--
lemma `op2_whiskerLeft` / 引理 `op2_whiskerLeft`

English:
lemma op2_whiskerLeft
  given: {a b c : B} {f : a ⟶ b} {g g' : b ⟶ c} (η : g ⟶ g')
  proof: rfl

@[simp]

中文:
引理 op2_whiskerLeft
  条件: {a b c : B} {f : a ⟶ b} {g g' : b ⟶ c} (η : g ⟶ g')
  证明: rfl

@[simp]
-/
lemma op2_whiskerLeft {a b c : B} {f : a ⟶ b} {g g' : b ⟶ c} (η : g ⟶ g') :
    op2 (f ◁ η) = (op2 η) ▷ f.op :=
  rfl

@[simp]
/--
lemma `op2_whiskerRight` / 引理 `op2_whiskerRight`

English:
lemma op2_whiskerRight
  given: {a b c : B} {f f' : a ⟶ b} {g : b ⟶ c} (η : f ⟶ f')
  proof: rfl

@[simp]

中文:
引理 op2_whiskerRight
  条件: {a b c : B} {f f' : a ⟶ b} {g : b ⟶ c} (η : f ⟶ f')
  证明: rfl

@[simp]
-/
lemma op2_whiskerRight {a b c : B} {f f' : a ⟶ b} {g : b ⟶ c} (η : f ⟶ f') :
    op2 (η ▷ g) = g.op ◁ (op2 η) :=
  rfl

@[simp]
/--
lemma `op2_associator` / 引理 `op2_associator`

English:
lemma op2_associator
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: rfl

@[simp]

中文:
引理 op2_associator
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: rfl

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.inclusionCreatesFiniteLimits, inclusionCreatesFiniteLimits
-/
lemma op2_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).op2 = (α_ h.op g.op f.op).symm :=
  rfl

@[simp]
/--
lemma `op2_associator_hom` / 引理 `op2_associator_hom`

English:
lemma op2_associator_hom
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: rfl

@[simp]

中文:
引理 op2_associator_hom
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: rfl

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl, hasLimit_of_created
-/
lemma op2_associator_hom {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    op2 (α_ f g h).hom = (α_ h.op g.op f.op).symm.hom :=
  rfl

@[simp]
/--
lemma `op2_associator_inv` / 引理 `op2_associator_inv`

English:
lemma op2_associator_inv
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: rfl

@[simp]

中文:
引理 op2_associator_inv
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: rfl

@[simp]
-/
lemma op2_associator_inv {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    op2 (α_ f g h).inv = (α_ h.op g.op f.op).symm.inv :=
  rfl

@[simp]
/--
lemma `op2_leftUnitor` / 引理 `op2_leftUnitor`

English:
lemma op2_leftUnitor
  given: {a b : B} (f : a ⟶ b)
  proof: rfl

@[simp]

中文:
引理 op2_leftUnitor
  条件: {a b : B} (f : a ⟶ b)
  证明: rfl

@[simp]
-/
lemma op2_leftUnitor {a b : B} (f : a ⟶ b) :
    (fun_ f).op2 = ρ_ f.op :=
  rfl

@[simp]
/--
lemma `op2_leftUnitor_hom` / 引理 `op2_leftUnitor_hom`

English:
lemma op2_leftUnitor_hom
  given: {a b : B} (f : a ⟶ b)
  proof: rfl

@[simp]

中文:
引理 op2_leftUnitor_hom
  条件: {a b : B} (f : a ⟶ b)
  证明: rfl

@[simp]
-/
lemma op2_leftUnitor_hom {a b : B} (f : a ⟶ b) :
    op2 (fun_ f).hom = (ρ_ f.op).hom :=
  rfl

@[simp]
/--
lemma `op2_leftUnitor_inv` / 引理 `op2_leftUnitor_inv`

English:
lemma op2_leftUnitor_inv
  given: {a b : B} (f : a ⟶ b)
  proof: rfl

@[simp]

中文:
引理 op2_leftUnitor_inv
  条件: {a b : B} (f : a ⟶ b)
  证明: rfl

@[simp]
-/
lemma op2_leftUnitor_inv {a b : B} (f : a ⟶ b) :
    op2 (fun_ f).inv = (ρ_ f.op).inv :=
  rfl

@[simp]
/--
lemma `op2_rightUnitor` / 引理 `op2_rightUnitor`

English:
lemma op2_rightUnitor
  given: {a b : B} (f : a ⟶ b)
  proof: rfl

@[simp]

中文:
引理 op2_rightUnitor
  条件: {a b : B} (f : a ⟶ b)
  证明: rfl

@[simp]
-/
lemma op2_rightUnitor {a b : B} (f : a ⟶ b) :
    (ρ_ f).op2 = fun_ f.op :=
  rfl

@[simp]
/--
lemma `op2_rightUnitor_hom` / 引理 `op2_rightUnitor_hom`

English:
lemma op2_rightUnitor_hom
  given: {a b : B} (f : a ⟶ b)
  proof: rfl

@[simp]

中文:
引理 op2_rightUnitor_hom
  条件: {a b : B} (f : a ⟶ b)
  证明: rfl

@[simp]
-/
lemma op2_rightUnitor_hom {a b : B} (f : a ⟶ b) :
    op2 (ρ_ f).hom = (fun_ f.op).hom :=
  rfl

@[simp]
/--
lemma `op2_rightUnitor_inv` / 引理 `op2_rightUnitor_inv`

English:
lemma op2_rightUnitor_inv
  given: {a b : B} (f : a ⟶ b)
  proof: rfl

中文:
引理 op2_rightUnitor_inv
  条件: {a b : B} (f : a ⟶ b)
  证明: rfl
-/
lemma op2_rightUnitor_inv {a b : B} (f : a ⟶ b) :
    op2 (ρ_ f).inv = (fun_ f.op).inv :=
  rfl

end Opposite

end Bicategory
