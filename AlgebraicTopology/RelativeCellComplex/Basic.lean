/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Relative cell complexes

In this file, we define a structure `RelativeCellComplex` which expresses
that a morphism `f : X ⟶ Y` is a transfinite composition of morphisms,
all of which consist in attaching cells. Here, we allow a different
family of authorized cells at each step. For example, (relative)
CW-complexes are defined in the file `Mathlib/Topology/CWComplex/Abstract/Basic.lean`
by requiring that at the `n`th step, we attach `n`-disks along their
boundaries.

This structure `RelativeCellComplex` is also used in the
formalization of the small object argument,
see the file `Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean`.

## References
* https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section

universe w w' t v u

open CategoryTheory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J -> Type t} {A B : (j : J) -> α j -> C}
  (basicCell : (j : J) -> (i : α j) -> A j i ⟶ B j i) {X Y : C} (f : X ⟶ Y)

/--
Definition of `RelativeCellComplex` / `RelativeCellComplex` 的定义

English:
structure RelativeCellComplex
  extends: TransfiniteCompositionOfShape J f
  axioms and operations (1):
    - attachCells((j : J) (hj : ¬ IsMax j)) : AttachCells.{w} (basicCell j) (F.map (homOfLE (Order.le_succ j)))

中文:
结构 RelativeCellComplex
  继承: TransfiniteCompositionOfShape J f
  公理与运算 (1 个):
    - attachCells((j : J) (hj : ¬ IsMax j)) : AttachCells.{w} (basicCell j) (F.map (homOfLE (Order.le_succ j)))
-/
structure RelativeCellComplex
    extends TransfiniteCompositionOfShape J f where
  /-- If `j` is not the maximum element, `F.obj (Order.succ j)` is obtained
  from `F.obj j` by attaching cells in the family of morphisms `basicCell j`. -/
  attachCells (j : J) (hj : ¬ IsMax j) :
    AttachCells.{w} (basicCell j) (F.map (homOfLE (Order.le_succ j)))

namespace RelativeCellComplex

variable {basicCell f} (c : RelativeCellComplex basicCell f)

/--
Definition of `Cells` / `Cells` 的定义

English:
structure Cells
  parameters: where
  axioms and operations (3):
    - j : J
    - hj : ¬ IsMax j
    - k : (c.attachCells j hj).ι

中文:
结构 Cells
  参数: where
  公理与运算 (3 个):
    - j : J
    - hj : ¬ IsMax j
    - k : (c.attachCells j hj).ι
-/
structure Cells where
  /-- the step where the cell is added -/
  j : J
  hj : ¬ IsMax j
  /-- the index of the cell -/
  k : (c.attachCells j hj).ι

variable {c} in
/--
Definition of `Cells.i` / `Cells.i` 的定义

English:
definition Cells.i
  signature: (γ : Cells c)
  body: (c.attachCells γ.j γ.hj).π γ.k

中文:
定义 Cells.i
  签名: (γ : Cells c)
  定义体: (c.attachCells γ.j γ.hj).π γ.k

Depends on / 依赖: attachCells, c.attachCells
-/
def Cells.i (γ : Cells c) : α γ.j := (c.attachCells γ.j γ.hj).π γ.k

variable {c} in
/--
Definition of `Cells.ι` / `Cells.ι` 的定义

English:
definition Cells.ι
  signature: (γ : Cells c)
  body: (c.attachCells γ.j γ.hj).cell γ.k ≫ c.incl.app (Order.succ γ.j)

中文:
定义 Cells.ι
  签名: (γ : Cells c)
  定义体: (c.attachCells γ.j γ.hj).cell γ.k ≫ c.incl.app (Order.succ γ.j)

Depends on / 依赖: Order.succ, attachCells, c.attachCells, c.incl.app
-/
def Cells.ι (γ : Cells c) : B γ.j γ.i ⟶ Y :=
  (c.attachCells γ.j γ.hj).cell γ.k ≫ c.incl.app (Order.succ γ.j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂)
  proof: by
  refine c.isColimit.hom_ext (fun j => ?_)
  dsimp
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa [← cancel_epi c.isoBot.inv] using h₀
  | succ j hj hj' =>
    apply (c.attachCells j hj).hom_ext
    · simpa using hj'
    · intro i
      simpa

中文:
引理 hom_ext
  结论: {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂)
  证明: by
  refine c.isColimit.hom_ext (fun j => ?_)
  dsimp
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa [← cancel_epi c.isoBot.inv] using h₀
  | succ j hj hj' =>
    apply (c.attachCells j hj).hom_ext
    · simpa using hj'
    · intro i
      simpa

Depends on / 依赖: Category, Category.assoc, SuccOrder, SuccOrder.limitRecOn, attachCells, c.F.isColimitOfIsWellOrderContinuous, c.attachCells, c.isColimit.hom_ext, c.isoBot.inv, cancel_epi, eq_bot, hj.eq_bot, hom_ext, isColimit, isColimitOfIsWellOrderContinuous, isSuccLimit, isoBot, limitRecOn
-/
lemma hom_ext {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂)
    (h : forall (γ : Cells c), γ.ι ≫ φ₁ = γ.ι ≫ φ₂) :
    φ₁ = φ₂ := by
  refine c.isColimit.hom_ext (fun j => ?_)
  dsimp
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa [← cancel_epi c.isoBot.inv] using h₀
  | succ j hj hj' =>
    apply (c.attachCells j hj).hom_ext
    · simpa using hj'
    · intro i
      simpa only [Category.assoc, Cells.ι] using h ({ hj := hj, k := i, .. })
  | isSuccLimit j hj hj' =>
    exact (c.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
      (fun ⟨k, hk⟩ => by simpa using hj' k hk)

open MorphismProperty in
/-- If `f` is a relative cell complex with respect to a constant
family of morphisms `g`, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in the family `g`. -/
@[simps toTransfiniteCompositionOfShape]
/--
Definition of `transfiniteCompositionOfShape` / `transfiniteCompositionOfShape` 的定义

English:
definition transfiniteCompositionOfShape
  body: c.toTransfiniteCompositionOfShape
  map_mem j hj := (c.attachCells j hj).pushouts_coproducts

中文:
定义 transfiniteCompositionOfShape
  定义体: c.toTransfiniteCompositionOfShape
  map_mem j hj := (c.attachCells j hj).pushouts_coproducts

Depends on / 依赖: c.toTransfiniteCompositionOfShape, toTransfiniteCompositionOfShape
-/
def transfiniteCompositionOfShape
    {α : Type*} {A B : α -> C} (g : (i : α) -> (A i ⟶ B i))
    (c : RelativeCellComplex.{w} (fun (_ : J) => g) f) :
    (coproducts.{w} (ofHoms g)).pushouts.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
  map_mem j hj := (c.attachCells j hj).pushouts_coproducts

open MorphismProperty in
/-- If `f` is a relative cell complex, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in `I : MorphismProperty C` if
for any `s : c.Cells`, the morphism `basicCell s.j s.i` belongs to `I`. -/
@[simps toTransfiniteCompositionOfShape]
/--
Definition of `transfiniteCompositionOfShape'` / `transfiniteCompositionOfShape'` 的定义

English:
definition transfiniteCompositionOfShape'
  signature: (c : RelativeCellComplex.{w} basicCell f)
  body: c.toTransfiniteCompositionOfShape
  map_mem j hj := by
    let a := c.attachCells j hj
    exact ⟨_, _, _, _, _,
      colimitsOfShape_le_coproducts _ a.ι _
        (colimitsOfShape.mk' _ _ _ _ a.isColimit₁ a.isColimit₂
        (Discrete.natTrans (fun _ => basicCell _ _))
        (fun ⟨k⟩ => hc { j 

中文:
定义 transfiniteCompositionOfShape'
  签名: (c : RelativeCellComplex.{w} basicCell f)
  定义体: c.toTransfiniteCompositionOfShape
  map_mem j hj := by
    let a := c.attachCells j hj
    exact ⟨_, _, _, _, _,
      colimitsOfShape_le_coproducts _ a.ι _
        (colimitsOfShape.mk' _ _ _ _ a.isColimit₁ a.isColimit₂
        (Discrete.natTrans (fun _ => basicCell _ _))
        (fun ⟨k⟩ => hc { j 

Depends on / 依赖: c.toTransfiniteCompositionOfShape, toTransfiniteCompositionOfShape
-/
def transfiniteCompositionOfShape' (c : RelativeCellComplex.{w} basicCell f)
    {I : MorphismProperty C} (hc : forall (s : c.Cells), I (basicCell s.j s.i)) :
    (coproducts.{w} I).pushouts.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
  map_mem j hj := by
    let a := c.attachCells j hj
    exact ⟨_, _, _, _, _,
      colimitsOfShape_le_coproducts _ a.ι _
        (colimitsOfShape.mk' _ _ _ _ a.isColimit₁ a.isColimit₂
        (Discrete.natTrans (fun _ => basicCell _ _))
        (fun ⟨k⟩ => hc { j := j, hj := hj, k := k }) _
        (fun _ => a.hm _)),
      a.isPushout⟩

end RelativeCellComplex

end HomotopicalAlgebra
