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
  {α : J → Type t} {A B : (j : J) → α j → C}
  (basicCell : (j : J) → (i : α j) → A j i ⟶ B j i) {X Y : C} (f : X ⟶ Y)

/-- Let `J` be a well-ordered type. Assume that for each `j : J`, we
have a family `basicCell j` of morphisms. A relative cell complex
is a morphism `f : X ⟶ Y` which is a transfinite composition of morphisms
in such a way that at the step `j : J`, we attach cells in the family `basicCell j`. -/
/-
**HomotopicalAlgebra.RelativeCellComplex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homotopica
lAlgebra`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w'} →       [inst_1 : LinearOrder J] →         [OrderBot J] →           [SuccOr
der J] →             [WellFoundedLT J] →               {α : J → Type t} →       
          {A B : (j : J) → α j → C} →                   ((j : J) → (i : α j) → A
 j i ⟶ B j i) →                     {X Y : C} → (X ⟶ Y) → Type (max (max (max (m
ax t u) v) (w + 1)) w')
参数：j : J；(j : J) → (i : α j) → A j i ⟶ B j i；X ⟶ Y；max (max (max (max t u) v) (w
 + 1)) w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `J` be a well-ordered type. Assume that for each `j : J`, we
have a family `basicCell j` of morphisms. A relative cell complex
is a morphism `f : X ⟶ Y` which is a transfinite composition of morphisms
in such a way that at the step `j : J`, we attach cells in the family `basicCell
 j`.
-/
structure RelativeCellComplex
    extends TransfiniteCompositionOfShape J f where
  /-- If `j` is not the maximum element, `F.obj (Order.succ j)` is obtained
  from `F.obj j` by attaching cells in the family of morphisms `basicCell j`. -/
  attachCells (j : J) (hj : ¬ IsMax j) :
    AttachCells.{w} (basicCell j) (F.map (homOfLE (Order.le_succ j)))

namespace RelativeCellComplex

variable {basicCell f} (c : RelativeCellComplex basicCell f)

/-- The index type of cells in a relative cell complex. -/
/-
**HomotopicalAlgebra.RelativeCellComplex.Cells** 是 Mathlib 中的一个归纳类型，位于命名空间 `Homo
topicalAlgebra.RelativeCellComplex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w'} →       [inst_1 : LinearOrder J] →         [inst_2 : OrderBot J] →         
  [inst_3 : SuccOrder J] →             [inst_4 : WellFoundedLT J] →             
  {α : J → Type t} →                 {A B : (j : J) → α j → C} →                
   {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} →                     {X Y 
: C} → {f : X ⟶ Y} → HomotopicalAlgebra.RelativeCellComplex basicCell f → Type (
max u_1 w')
参数：j : J；j : J；i : α j；max u_1 w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index type of cells in a relative cell complex.
-/
structure Cells where
  /-- the step where the cell is added -/
  j : J
  hj : ¬ IsMax j
  /-- the index of the cell -/
  k : (c.attachCells j hj).ι

variable {c} in
/-- Given a cell `γ` in a relative cell complex, this is the corresponding
index in the family of morphisms `basicCell γ.j`. -/
/-
**HomotopicalAlgebra.RelativeCellComplex.Cells.i** 是 Mathlib 中的一个定义，位于命名空间 `Homo
topicalAlgebra.RelativeCellComplex.Cells`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 w'} →       [inst_1 : LinearOrder J] →         [inst_2 : OrderBot J] →         
  [inst_3 : SuccOrder J] →             [inst_4 : WellFoundedLT J] →             
  {α : J → Type t} →                 {A B : (j : J) → α j → C} →                
   {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} →                     {X Y 
: C} →                       {f : X ⟶ Y} → {c : HomotopicalAlgebra.RelativeCellC
omplex basicCell f} → (γ : c.Cells) → α γ.j
参数：j : J；j : J；i : α j；γ : c.Cells。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopicalAlgebra.RelativeCellComplex.Cells.hj`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {J : Type w'} [inst_1 : LinearOrder J] [inst_2
 : OrderBot J]   [inst_3 : SuccOrder …

--- 原说明 ---
Given a cell `γ` in a relative cell complex, this is the corresponding
index in the family of morphisms `basicCell γ.j`.
-/
def Cells.i (γ : Cells c) : α γ.j := (c.attachCells γ.j γ.hj).π γ.k

variable {c} in
/-- The inclusion of a cell. -/
/-
**HomotopicalAlgebra.RelativeCellComplex.Cells.** 是 Mathlib 中的一个定义，位于命名空间 `Homot
opicalAlgebra.RelativeCellComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a cell.
-/
def Cells.ι (γ : Cells c) : B γ.j γ.i ⟶ Y :=
  (c.attachCells γ.j γ.hj).cell γ.k ≫ c.incl.app (Order.succ γ.j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomotopicalAlgebra.RelativeCellComplex.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra.RelativeCellComplex`。
形式化陈述：hom_ext {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂) (h : forall (γ : Ce
lls c), γ.ι ≫ φ₁ = γ.ι ≫ φ₂) : φ₁ = φ₂
参数：h₀ : f ≫ φ₁ = f ≫ φ₂；h : forall (γ : Cells c), γ.ι ≫ φ₁ = γ.ι ≫ φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.TransfiniteCompositionOfShape.fac_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : LinearOrder J] [
inst_2 : OrderBot J]   {X Y : C} {f : X ⟶ Y}…
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用引理 `HomotopicalAlgebra.AttachCells.hom_ext`：hom_ext {Z : C} {φ φ' : X₂ ⟶ Z} 
(h₀ : f ≫ φ = f ≫ φ') (h : forall i, c.cell i ≫ φ = c.cell i ≫ φ') : φ = φ'
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `HomotopicalAlgebra.RelativeCellComplex.Cells.hj`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {J : Type w'} [inst_1 : LinearOrder J] [inst_2
 : OrderBot J]   [inst_3 : SuccOrder …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `PrincipalSeg.monotone`：monotone [PartialOrder α] (f : α <i β) : Monotone
 f
· 使用定理 `CategoryTheory.TransfiniteCompositionOfShape.isWellOrderContinuous`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type w} [inst_1 : Line
arOrder J] [inst_2 : OrderBot J]   {X Y : C} {f : X ⟶ Y}…
-/
lemma hom_ext {Z : C} {φ₁ φ₂ : Y ⟶ Z} (h₀ : f ≫ φ₁ = f ≫ φ₂)
    (h : ∀ (γ : Cells c), γ.ι ≫ φ₁ = γ.ι ≫ φ₂) :
    φ₁ = φ₂ := by
  refine c.isColimit.hom_ext (fun j ↦ ?_)
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
      (fun ⟨k, hk⟩ ↦ by simpa using hj' k hk)

open MorphismProperty in
/-- If `f` is a relative cell complex with respect to a constant
family of morphisms `g`, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in the family `g`. -/
@[simps toTransfiniteCompositionOfShape]
/-
**HomotopicalAlgebra.RelativeCellComplex.transfiniteCompositionOfShape** 是 Mathl
ib 中的一个定义，位于命名空间 `HomotopicalAlgebra.RelativeCellComplex`。
形式化陈述：transfiniteCompositionOfShape {α : Type*} {A B : α -> C} (g : (i : α) -> (
A i ⟶ B i)) (c : RelativeCellComplex.{w} (fun (_ : J) => g) f) : (coproducts.{w}
 (ofHoms g)).pushouts.TransfiniteCompositionOfShape J f where toTransfiniteCompo
sitionOfShape
参数：g : (i : α) -> (A i ⟶ B i)；c : RelativeCellComplex.{w} (fun (_ : J) => g) f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a relative cell complex with respect to a constant
family of morphisms `g`, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in the family `g`.
-/
def transfiniteCompositionOfShape
    {α : Type*} {A B : α → C} (g : (i : α) → (A i ⟶ B i))
    (c : RelativeCellComplex.{w} (fun (_ : J) ↦ g) f) :
    (coproducts.{w} (ofHoms g)).pushouts.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
  map_mem j hj := (c.attachCells j hj).pushouts_coproducts

open MorphismProperty in
/-- If `f` is a relative cell complex, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in `I : MorphismProperty C` if
for any `s : c.Cells`, the morphism `basicCell s.j s.i` belongs to `I`. -/
@[simps toTransfiniteCompositionOfShape]
/-
**HomotopicalAlgebra.RelativeCellComplex.transfiniteCompositionOfShape'** 是 Math
lib 中的一个定义，位于命名空间 `HomotopicalAlgebra.RelativeCellComplex`。
形式化陈述：transfiniteCompositionOfShape' (c : RelativeCellComplex.{w} basicCell f) {
I : MorphismProperty C} (hc : forall (s : c.Cells), I (basicCell s.j s.i)) : (co
products.{w} I).pushouts.TransfiniteCompositionOfShape J f where toTransfiniteCo
mpositionOfShape
参数：c : RelativeCellComplex.{w} basicCell f；hc : forall (s : c.Cells), I (basicCe
ll s.j s.i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a relative cell complex, then `f` is a transfinite composition
of pushouts of coproducts of morphisms in `I : MorphismProperty C` if
for any `s : c.Cells`, the morphism `basicCell s.j s.i` belongs to `I`.
-/
def transfiniteCompositionOfShape' (c : RelativeCellComplex.{w} basicCell f)
    {I : MorphismProperty C} (hc : ∀ (s : c.Cells), I (basicCell s.j s.i)) :
    (coproducts.{w} I).pushouts.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
  map_mem j hj := by
    let a := c.attachCells j hj
    exact ⟨_, _, _, _, _,
      colimitsOfShape_le_coproducts _ a.ι _
        (colimitsOfShape.mk' _ _ _ _ a.isColimit₁ a.isColimit₂
        (Discrete.natTrans (fun _ ↦ basicCell _ _))
        (fun ⟨k⟩ ↦ hc { j := j, hj := hj, k := k }) _
        (fun _ ↦ a.hm _)),
      a.isPushout⟩

end RelativeCellComplex

end HomotopicalAlgebra

