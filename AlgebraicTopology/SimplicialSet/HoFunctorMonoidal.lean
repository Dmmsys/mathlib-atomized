/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# The homotopy category functor is monoidal

Given `2`-truncated simplicial sets `X` and `Y`, we introduce ad operation
`Truncated.Edge.tensor : Edge x x' → Edge y y' → Edge (x, y) (x', y')`.
We use this in order to construct an equivalence of categories
`(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace Edge

variable {X Y X' Y' Z : Truncated.{u} 2}

/-- The external product of edges of `2`-truncated simplicial sets. -/
@[simps]
/-
**SSet.Truncated.Edge.tensor** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：tensor {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y')
 : Edge (X
参数：e₁ : Edge x x'；e₂ : Edge y y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The external product of edges of `2`-truncated simplicial sets.
-/
def tensor {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    Edge (X := X ⊗ Y) (x, y) (x', y') where
  edge := (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq
/-
**SSet.Truncated.Edge.tensor_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncate
d.Edge`。
形式化陈述：tensor_surjective {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂} (e : Edge (X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_surjective {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
    (e : Edge (X := X ⊗ Y) (x, y) (x', y')) :
    ∃ (e₁ : Edge x x') (e₂ : Edge y y'), e₁.tensor e₂ = e :=
  ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

@[simp]
/-
**SSet.Truncated.Edge.id_tensor_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Edg
e`。
形式化陈述：id_tensor_id (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (id x).tensor (id y) = id (X
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_tensor_id (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (id x).tensor (id y) = id (X := X ⊗ Y) (x, y) := rfl

@[simp]
/-
**SSet.Truncated.Edge.map_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Ed
ge`。
形式化陈述：map_tensorHom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edg
e y y') (f : X ⟶ X') (g : Y ⟶ Y') : (e₁.tensor e₂).map (f otimesₘ g) = (e₁.map f
).tensor (e₂.map g)
参数：e₁ : Edge x x'；e₂ : Edge y y'；f : X ⟶ X'；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_tensorHom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (f ⊗ₘ g) =
      (e₁.map f).tensor (e₂.map g) := rfl

@[simp]
/-
**SSet.Truncated.Edge.map_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated
.Edge`。
形式化陈述：map_whiskerRight {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : 
Edge y y') (f : X ⟶ X') : (e₁.tensor e₂).map (f ▷ _) = (e₁.map f).tensor e₂
参数：e₁ : Edge x x'；e₂ : Edge y y'；f : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_whiskerRight {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') :
    (e₁.tensor e₂).map (f ▷ _) =
      (e₁.map f).tensor e₂ := rfl

@[simp]
/-
**SSet.Truncated.Edge.map_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.
Edge`。
形式化陈述：map_whiskerLeft {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : E
dge y y') (g : Y ⟶ Y') : (e₁.tensor e₂).map (_ ◁ g) = e₁.tensor (e₂.map g)
参数：e₁ : Edge x x'；e₂ : Edge y y'；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_whiskerLeft {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (_ ◁ g) =
      e₁.tensor (e₂.map g) := rfl

@[simp]
/-
**SSet.Truncated.Edge.map_associator_hom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncat
ed.Edge`。
形式化陈述：map_associator_hom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ 
: Edge y y') {z z' : Z _⦋0⦌₂} (e₃ : Edge z z') : ((e₁.tensor e₂).tensor e₃).map 
(α_ _ _ _).hom = e₁.tensor (e₂.tensor e₃)
参数：e₁ : Edge x x'；e₂ : Edge y y'；e₃ : Edge z z'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_associator_hom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y')
    {z z' : Z _⦋0⦌₂} (e₃ : Edge z z') :
    ((e₁.tensor e₂).tensor e₃).map (α_ _ _ _).hom = e₁.tensor (e₂.tensor e₃) :=
  rfl

@[simp]
/-
**SSet.Truncated.Edge.map_fst** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：map_fst {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y'
) : (e₁.tensor e₂).map (fst _ _) = e₁
参数：e₁ : Edge x x'；e₂ : Edge y y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_fst {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (fst _ _) = e₁ := rfl

@[simp]
/-
**SSet.Truncated.Edge.map_snd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.Edge`。
形式化陈述：map_snd {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y'
) : (e₁.tensor e₂).map (snd _ _) = e₂
参数：e₁ : Edge x x'；e₂ : Edge y y'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_snd {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (snd _ _) = e₂ := rfl

/-- The external product of `CompStruct` between edges of `2`-truncated simplicial sets. -/
@[simps simplex_fst simplex_snd]
/-
**SSet.Truncated.Edge.CompStruct.tensor** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncate
d.Edge.CompStruct`。
形式化陈述：{X Y : SSet.Truncated 2} →   {x₀ x₁ x₂ : X.obj (Opposite.op { obj := { len
 := 0 }, property := SSet.Truncated.Edge.tensor._proof_1 })} →     {e₀₁ : SSet.T
runcated.Edge x₀ x₁} →       {e₁₂ : SSet.Truncated.Edge x₁ x₂} →         {e₀₂ : 
SSet.Truncated.Edge x₀ x₂} →           e₀₁.CompStruct e₁₂ e₀₂ →             {y₀ 
y₁ y₂ : Y.obj (Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edg
e.tensor._proof_1 })} →               {e'₀₁ : SSet.Truncated.Edge y₀ y₁} →      
           {e'₁₂ : SSet.Truncated.Edge y₁ y₂} →                   {e'₀₂ : SSet.T
runcated.Edge y₀ y₂} →                     e'₀₁.CompStruct e'₁₂ e'₀₂ → (e₀₁.tens
or e'₀₁).CompStruct (e₁₂.tensor e'₁₂) (e₀₂.tensor e'₀₂)
参数：Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge.tensor._pr
oof_1 }；Opposite.op { obj := { len := 0 }, property := SSet.Truncated.Edge.tenso
r._proof_1 }；e₀₁.tensor e'₀₁；e₁₂.tensor e'₁₂；e₀₂.tensor e'₀₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The external product of `CompStruct` between edges of `2`-truncated simplicial s
ets.
-/
def CompStruct.tensor
    {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (hx : CompStruct e₀₁ e₁₂ e₀₂)
    {y₀ y₁ y₂ : Y _⦋0⦌₂} {e'₀₁ : Edge y₀ y₁} {e'₁₂ : Edge y₁ y₂} {e'₀₂ : Edge y₀ y₂}
    (hy : CompStruct e'₀₁ e'₁₂ e'₀₂) :
    CompStruct (e₀₁.tensor e'₀₁) (e₁₂.tensor e'₁₂) (e₀₂.tensor e'₀₂) where
  simplex := (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

end Edge

namespace HomotopyCategory

/-
**SSet.Truncated.HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated.Hom
otopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    Unique ((𝟙_ (Truncated.{u} n)).obj d) :=
  inferInstanceAs (Unique PUnit)

/-- If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
this is the isomorphism `Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal` in `Cat`. -/
/-
**SSet.Truncated.HomotopyCategory.isoTerminal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Tr
uncated.HomotopyCategory`。
形式化陈述：isoTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌
₂)] : Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal
参数：X : Truncated.{u} 2；X _⦋0⦌₂；X _⦋1⦌₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
this is the isomorphism `Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal` in `Cat
`.
-/
def isoTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal :=
  IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

namespace BinaryProduct

/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.square** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：square {X Y : Truncated.{u} 2} {x₀ x₁ : X _⦋0⦌₂} (ex : Edge x₀ x₁) {y₀ y₁ 
: Y _⦋0⦌₂} (ey : Edge y₀ y₁) : homMk (ex.tensor (.id y₀)) ≫ homMk (Edge.tensor (
.id x₁) ey) = homMk (Edge.tensor (.id x₀) ey) ≫ homMk (ex.tensor (.id y₁))
参数：ex : Edge x₀ x₁；ey : Edge y₀ y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.homMk_comp_homMk`：homMk_comp_homMk {x₀ x
₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} (h : Ed
ge.CompStruct e₀₁ e₁₂ e₀₂) : homMk e₀₁…
-/
lemma square {X Y : Truncated.{u} 2}
    {x₀ x₁ : X _⦋0⦌₂} (ex : Edge x₀ x₁) {y₀ y₁ : Y _⦋0⦌₂} (ey : Edge y₀ y₁) :
    homMk (ex.tensor (.id y₀)) ≫ homMk (Edge.tensor (.id x₁) ey) =
      homMk (Edge.tensor (.id x₀) ey) ≫ homMk (ex.tensor (.id y₁)) := by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey)),
    homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

variable {X X' Y Y' Z : Truncated.{u} 2}

variable (X Y) in
/-- The functor `(X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functor** 是 Mathlib 中的一个定义，位于命名空
间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functor : (X otimes Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyC
ategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets.
-/
def functor : (X ⊗ Y).HomotopyCategory ⥤ X.HomotopyCategory × Y.HomotopyCategory :=
  (mapHomotopyCategory (fst _ _)).prod' (mapHomotopyCategory (snd _ _))

@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functor_obj** 是 Mathlib 中的一个引理，位
于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functor_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (functor X Y).obj (mk (x, y)) = 
(mk x, mk y)
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functor X Y).obj (mk (x, y)) = (mk x, mk y) := rfl

@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functor_map** 是 Mathlib 中的一个引理，位
于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functor_map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) {y₀ y₁ : Y _⦋0⦌₂} (e' : Edg
e y₀ y₁) : (functor X Y).map (homMk (e.tensor e')) = (homMk e, homMk e')
参数：e : Edge x₀ x₁；e' : Edge y₀ y₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_map {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (functor X Y).map (homMk (e.tensor e')) = (homMk e, homMk e') := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/-- The functor `X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.curriedInverse** 是 Mathlib 中的一个定
义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：curriedInverse : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X otimes Y).Ho
motopyCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets.
-/
def curriedInverse : X.HomotopyCategory ⥤ Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  lift (fun x ↦ lift (fun y ↦ mk (x, y)) (fun {y₀ y₁} e ↦ homMk (Edge.tensor (.id _) e)) (by simp)
    (fun {y₀ y₁ y₁ e₀₁ e₁₂ e₀₂ h} ↦ homMk_comp_homMk ((Edge.CompStruct.idCompId x).tensor h)))
    (fun {x₀ x₁} e ↦ mkNatTrans (fun y ↦ homMk (V := X ⊗ Y) (x₀ := (x₀, y))
      (x₁ := (x₁, y)) (e.tensor (.id y))) (fun y₀ y₁ e' ↦ by simp [square]))
    (by cat_disch) (fun {x₀ x₁ x₂ e₀₁ e₁₂ e₀₂} h ↦ by
      ext y
      obtain ⟨y, rfl⟩ := mk_surjective y
      simpa using homMk_comp_homMk (h.tensor (.idCompId y)))

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/-- The functor `X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse** 是 Mathlib 中的一个定义，位于命名空
间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X otimes Y).HomotopyC
ategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets.
-/
def inverse : X.HomotopyCategory × Y.HomotopyCategory ⥤ (X ⊗ Y).HomotopyCategory :=
  Functor.uncurry.obj (curriedInverse X Y)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_obj** 是 Mathlib 中的一个引理，位
于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverse X Y).obj (mk x, mk y) =
 mk (x, y)
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverse_obj (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverse X Y).obj (mk x, mk y) = mk (x, y) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_map_mkHom_homMk_id** 是 M
athlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_map_mkHom_homMk_id {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (y : Y _⦋0⦌₂
) : (inverse X Y).map (Prod.mkHom (homMk e) (𝟙 (mk y))) = homMk (e.tensor (.id y
))
参数：e : Edge x₀ x₁；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverse_map_mkHom_homMk_id {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) (y : Y _⦋0⦌₂) :
    (inverse X Y).map (Prod.mkHom (homMk e) (𝟙 (mk y))) = homMk (e.tensor (.id y)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_map_mkHom_id_homMk** 是 M
athlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_map_mkHom_id_homMk (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : Edge y₀ y₁
) : (inverse X Y).map (Prod.mkHom (𝟙 (mk x)) (homMk e)) = homMk ((Edge.id x).ten
sor e)
参数：x : X _⦋0⦌₂；e : Edge y₀ y₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverse_map_mkHom_id_homMk (x : X _⦋0⦌₂) {y₀ y₁ : Y _⦋0⦌₂} (e : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (𝟙 (mk x)) (homMk e)) = homMk ((Edge.id x).tensor e) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_map_mkHom_homMk_homMk** 
是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_map_mkHom_homMk_homMk {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁) {y₀ y₁ : 
Y _⦋0⦌₂} (e' : Edge y₀ y₁) : (inverse X Y).map (Prod.mkHom (homMk e) (homMk e'))
 = homMk (e.tensor e')
参数：e : Edge x₀ x₁；e' : Edge y₀ y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Truncated.HomotopyCategory.homMk_comp_homMk`：homMk_comp_homMk {x₀ x
₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂} (h : Ed
ge.CompStruct e₀₁ e₁₂ e₀₂) : homMk e₀₁…
-/
lemma inverse_map_mkHom_homMk_homMk {x₀ x₁ : X _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : Y _⦋0⦌₂} (e' : Edge y₀ y₁) :
    (inverse X Y).map (Prod.mkHom (homMk e) (homMk e')) = homMk (e.tensor e') :=
  homMk_comp_homMk ((Edge.CompStruct.compId e).tensor (Edge.CompStruct.idComp e'))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (X Y) in
/-- Auxiliary definition for `equivalence`. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functorCompInverseIso** 是 Mathli
b 中的一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functorCompInverseIso : functor X Y ⋙ inverse X Y ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivalence`.
-/
def functorCompInverseIso : functor X Y ⋙ inverse X Y ≅ 𝟭 _ :=
  mkNatIso (fun _ ↦ Iso.refl _) (by
    rintro ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ e
    obtain ⟨ex, ey, rfl⟩ := e.tensor_surjective
    dsimp
    rw [Category.comp_id, Category.id_comp, inverse_map_mkHom_homMk_homMk])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functorCompInverseIso_hom_app** 
是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functorCompInverseIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (functorCompIn
verseIso X Y).hom.app (mk (x, y)) = 𝟙 _
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorCompInverseIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).hom.app (mk (x, y)) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functorCompInverseIso_inv_app** 
是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functorCompInverseIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (functorCompIn
verseIso X Y).inv.app (mk (x, y)) = 𝟙 _
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorCompInverseIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (functorCompInverseIso X Y).inv.app (mk (x, y)) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (X Y) in
/-- Auxiliary definition for `equivalence`. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverseCompFunctorIso** 是 Mathli
b 中的一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverseCompFunctorIso : inverse X Y ⋙ functor X Y ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivalence`.
-/
def inverseCompFunctorIso : inverse X Y ⋙ functor X Y ≅ 𝟭 _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _))
      (fun x₀ x₁ e ↦ by
        ext y : 2
        obtain ⟨y, rfl⟩ := y.mk_surjective
        cat_disch))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverseCompFunctorIso_hom_app** 
是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverseCompFunctorIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverseCompFu
nctorIso X Y).hom.app (mk x, mk y) = 𝟙 _
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseCompFunctorIso_hom_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).hom.app (mk x, mk y) = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverseCompFunctorIso_inv_app** 
是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverseCompFunctorIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) : (inverseCompFu
nctorIso X Y).inv.app (mk x, mk y) = 𝟙 _
参数：x : X _⦋0⦌₂；y : Y _⦋0⦌₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseCompFunctorIso_inv_app (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (inverseCompFunctorIso X Y).inv.app (mk x, mk y) = 𝟙 _ := rfl

variable (X Y)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.functor_comp_inverse** 是 Mathlib
 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：functor_comp_inverse : functor X Y ⋙ inverse X Y = 𝟭 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma functor_comp_inverse : functor X Y ⋙ inverse X Y = 𝟭 _ :=
  Functor.ext_of_iso (functorCompInverseIso X Y) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_comp_functor** 是 Mathlib
 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_comp_functor : inverse X Y ⋙ functor X Y = 𝟭 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma inverse_comp_functor : inverse X Y ⋙ functor X Y = 𝟭 _ :=
  Functor.ext_of_iso (inverseCompFunctorIso X Y) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory ⥤ Y.HomotopyCategory`
when `X` and `Y` are `2`-truncated simplicial sets. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.equivalence** 是 Mathlib 中的一个定义，位
于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：equivalence : (X otimes Y).HomotopyCategory ≌ X.HomotopyCategory × Y.Homot
opyCategory where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory ⥤ Y.HomotopyCateg
ory`
when `X` and `Y` are `2`-truncated simplicial sets.
-/
def equivalence :
    (X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory where
  functor := functor X Y
  inverse := inverse X Y
  unitIso := (functorCompInverseIso X Y).symm
  counitIso := inverseCompFunctorIso X Y

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of categories between
`(X ⊗ Y).HomotopyCategory` and `X.HomotopyCategory ⥤ Y.HomotopyCategory`. -/
@[simps]
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.iso** 是 Mathlib 中的一个定义，位于命名空间 `S
Set.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：iso : Cat.of ((X otimes Y).HomotopyCategory) ≅ Cat.of (X.HomotopyCategory 
× Y.HomotopyCategory) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of categories between
`(X ⊗ Y).HomotopyCategory` and `X.HomotopyCategory ⥤ Y.HomotopyCategory`.
-/
def iso :
    Cat.of ((X ⊗ Y).HomotopyCategory) ≅ Cat.of (X.HomotopyCategory × Y.HomotopyCategory) where
  hom := Cat.Hom.ofFunctor (functor X Y)
  inv := Cat.Hom.ofFunctor (inverse X Y)
  hom_inv_id := by ext; exact functor_comp_inverse X Y
  inv_hom_id := by ext; exact inverse_comp_functor X Y

set_option backward.isDefEq.respectTransparency.types false in
variable {X} in
/-- The naturality of `HomotopyCategory.BinaryProduct.inverse`
with respect to the first variable. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.mapHomotopyCategoryProdIdCompInv
erseIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct
`。
形式化陈述：mapHomotopyCategoryProdIdCompInverseIso (f : X ⟶ X') : (mapHomotopyCategor
y f).prod (𝟭 _) ⋙ inverse X' Y ≅ inverse X Y ⋙ mapHomotopyCategory (f ▷ Y)
参数：f : X ⟶ X'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The naturality of `HomotopyCategory.BinaryProduct.inverse`
with respect to the first variable.
-/
def mapHomotopyCategoryProdIdCompInverseIso (f : X ⟶ X') :
    (mapHomotopyCategory f).prod (𝟭 _) ⋙ inverse X' Y ≅
      inverse X Y ⋙ mapHomotopyCategory (f ▷ Y) :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

set_option backward.isDefEq.respectTransparency.types false in
variable {Y} in
/-- The naturality of `HomotopyCategory.BinaryProduct.inverse`
with respect to the second variable. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.idProdMapHomotopyCategoryCompInv
erseIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct
`。
形式化陈述：idProdMapHomotopyCategoryCompInverseIso (g : Y ⟶ Y') : Functor.prod (𝟭 _) 
(mapHomotopyCategory g) ⋙ inverse X Y' ≅ inverse X Y ⋙ mapHomotopyCategory (X ◁ 
g)
参数：g : Y ⟶ Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The naturality of `HomotopyCategory.BinaryProduct.inverse`
with respect to the second variable.
-/
def idProdMapHomotopyCategoryCompInverseIso (g : Y ⟶ Y') :
    Functor.prod (𝟭 _) (mapHomotopyCategory g) ⋙ inverse X Y' ≅
      inverse X Y ⋙ mapHomotopyCategory (X ◁ g) :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp
      rfl))

set_option backward.isDefEq.respectTransparency.types false in
variable {X} in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.mapHomotopyCategory_prod_id_comp
_inverse** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduc
t`。
形式化陈述：mapHomotopyCategory_prod_id_comp_inverse (f : X ⟶ X') : (mapHomotopyCatego
ry f).prod (𝟭 _) ⋙ inverse X' Y = inverse X Y ⋙ mapHomotopyCategory (f ▷ Y)
参数：f : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma mapHomotopyCategory_prod_id_comp_inverse (f : X ⟶ X') :
    (mapHomotopyCategory f).prod (𝟭 _) ⋙ inverse X' Y =
      inverse X Y ⋙ mapHomotopyCategory (f ▷ Y) :=
  Functor.ext_of_iso (mapHomotopyCategoryProdIdCompInverseIso _ _) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency.types false in
variable {Y} in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.id_prod_mapHomotopyCategory_comp
_inverse** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduc
t`。
形式化陈述：id_prod_mapHomotopyCategory_comp_inverse (g : Y ⟶ Y') : Functor.prod (𝟭 _)
 (mapHomotopyCategory g) ⋙ inverse X Y' = inverse X Y ⋙ mapHomotopyCategory (X ◁
 g)
参数：g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma id_prod_mapHomotopyCategory_comp_inverse (g : Y ⟶ Y') :
    Functor.prod (𝟭 _) (mapHomotopyCategory g) ⋙ inverse X Y' =
      inverse X Y ⋙ mapHomotopyCategory (X ◁ g) :=
  Functor.ext_of_iso (idProdMapHomotopyCategoryCompInverseIso _ _) (fun _ ↦ rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to the first projection. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverseCompMapHomotopyCategoryFs
tIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverseCompMapHomotopyCategoryFstIso : inverse X Y ⋙ mapHomotopyCategory (
fst _ _) ≅ CategoryTheory.Prod.fst _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to the first projection.
-/
def inverseCompMapHomotopyCategoryFstIso :
    inverse X Y ⋙ mapHomotopyCategory (fst _ _) ≅ CategoryTheory.Prod.fst _ _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _) (fun y₀ y₁ e ↦ by
      dsimp
      rw [Category.comp_id]
      exact homMk_id x)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to the second projection. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverseCompMapHomotopyCategorySn
dIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverseCompMapHomotopyCategorySndIso : inverse X Y ⋙ mapHomotopyCategory (
snd _ _) ≅ CategoryTheory.Prod.snd _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to the second projection.
-/
def inverseCompMapHomotopyCategorySndIso :
    inverse X Y ⋙ mapHomotopyCategory (snd _ _) ≅ CategoryTheory.Prod.snd _ _ :=
  Functor.fullyFaithfulCurry.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ Iso.refl _)) (fun x₀ x₁ e ↦ by
      ext y
      obtain ⟨y, rfl⟩ := y.mk_surjective
      dsimp
      simp only [Category.comp_id]
      exact homMk_id y))

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_comp_mapHomotopyCategory
_fst** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_comp_mapHomotopyCategory_fst : inverse X Y ⋙ mapHomotopyCategory (
fst _ _) = CategoryTheory.Prod.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma inverse_comp_mapHomotopyCategory_fst :
    inverse X Y ⋙ mapHomotopyCategory (fst _ _) = CategoryTheory.Prod.fst _ _ :=
  Functor.ext_of_iso (inverseCompMapHomotopyCategoryFstIso _ _) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_comp_mapHomotopyCategory
_snd** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：inverse_comp_mapHomotopyCategory_snd : inverse X Y ⋙ mapHomotopyCategory (
snd _ _) = CategoryTheory.Prod.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
-/
lemma inverse_comp_mapHomotopyCategory_snd :
    inverse X Y ⋙ mapHomotopyCategory (snd _ _) = CategoryTheory.Prod.snd _ _ :=
  Functor.ext_of_iso (inverseCompMapHomotopyCategorySndIso _ _) (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.left_unitality** 是 Mathlib 中的一个引
理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：left_unitality [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] : CategoryTheor
y.Prod.snd _ _ = Functor.prod (isoTerminal X).inv.toFunctor (𝟭 _) ⋙ inverse X Y 
⋙ mapHomotopyCategory (snd _ _)
参数：X _⦋0⦌₂；X _⦋1⦌₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_comp_mapHomotopyCa
tegory_snd`：inverse_comp_mapHomotopyCategory_snd : inverse X Y ⋙ mapHomotopyCate
gory (snd _ _) = CategoryTheory.Prod.snd _ _
-/
lemma left_unitality [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    CategoryTheory.Prod.snd _ _ = Functor.prod (isoTerminal X).inv.toFunctor (𝟭 _) ⋙
      inverse X Y ⋙ mapHomotopyCategory (snd _ _) := by
  rw [inverse_comp_mapHomotopyCategory_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.right_unitality** 是 Mathlib 中的一个
引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：right_unitality [Unique (Y _⦋0⦌₂)] [Subsingleton (Y _⦋1⦌₂)] : CategoryTheo
ry.Prod.fst _ _ = Functor.prod (𝟭 _) (isoTerminal Y).inv.toFunctor ⋙ inverse X Y
 ⋙ mapHomotopyCategory (fst _ _)
参数：Y _⦋0⦌₂；Y _⦋1⦌₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_comp_mapHomotopyCa
tegory_fst`：inverse_comp_mapHomotopyCategory_fst : inverse X Y ⋙ mapHomotopyCate
gory (fst _ _) = CategoryTheory.Prod.fst _ _
-/
lemma right_unitality [Unique (Y _⦋0⦌₂)] [Subsingleton (Y _⦋1⦌₂)] :
    CategoryTheory.Prod.fst _ _ = Functor.prod (𝟭 _) (isoTerminal Y).inv.toFunctor ⋙
      inverse X Y ⋙ mapHomotopyCategory (fst _ _) := by
  rw [inverse_comp_mapHomotopyCategory_fst]
  rfl

variable (Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `associativityIso`. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.associativity'Iso** 是 Mathlib 中的
一个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：(X Y Z : SSet.Truncated 2) →   (CategoryTheory.prod.associativity X.Homoto
pyCategory Y.HomotopyCategory Z.HomotopyCategory).inverse.comp       (((SSet.Tru
ncated.HomotopyCategory.BinaryProduct.inverse X Y).prod             (CategoryThe
ory.Functor.id Z.HomotopyCategory)).comp         ((SSet.Truncated.HomotopyCatego
ry.BinaryProduct.inverse (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y)  
             Z).comp           (SSet.Truncated.mapHomotopyCategory (CategoryTheo
ry.MonoidalCategoryStruct.associator X Y Z).hom))) ≅     ((CategoryTheory.Functo
r.id X.HomotopyCategory).prod           (SSet.Truncated.HomotopyCategory.BinaryP
roduct.inverse Y Z)).comp       (SSet.Truncated.HomotopyCategory.BinaryProduct.i
nverse X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))
参数：(SSet.Truncated.HomotopyCategory.BinaryProduct.inverse X Y).prod             
(CategoryTheory.Functor.id Z.HomotopyCategory)；(SSet.Truncated.HomotopyCategory.
BinaryProduct.inverse (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y)     
          Z).comp           (SSet.Truncated.mapHomotopyCategory (CategoryTheory.
MonoidalCategoryStruct.associator X Y Z).hom)；CategoryTheory.Functor.id X.Homoto
pyCategory；SSet.Truncated.HomotopyCategory.BinaryProduct.inverse Y Z；CategoryThe
ory.MonoidalCategoryStruct.tensorObj Y Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `associativityIso`.
-/
def associativity'Iso :
    (prod.associativity ..).inverse ⋙ (inverse X Y).prod (𝟭 _) ⋙ inverse (X ⊗ Y) Z ⋙
      mapHomotopyCategory (α_ _ _ _).hom ≅
    Functor.prod (𝟭 _) (inverse Y Z) ⋙ inverse X (Y ⊗ Z) :=
  Functor.fullyFaithfulCurry₃.preimageIso
    (mkNatIso (fun x ↦ mkNatIso (fun y ↦ mkNatIso (fun z ↦ Iso.refl _)
      (fun z₀ z₁ e ↦ by
        dsimp
        rw [Category.comp_id, Category.id_comp, ← prod_id,
          inverse_map_mkHom_id_homMk, inverse_map_mkHom_id_homMk,
          CategoryTheory.Functor.map_id]
        dsimp [← Edge.id_tensor_id]))
      (fun y₀ y₁ e ↦ by
        ext z
        obtain ⟨z, rfl⟩ := z.mk_surjective
        dsimp
        rw [Category.comp_id, Category.id_comp,
          inverse_map_mkHom_homMk_id, inverse_map_mkHom_id_homMk]))
      (fun x₀ x₁ e ↦ by
        ext y z
        obtain ⟨y, rfl⟩ := y.mk_surjective
        obtain ⟨z, rfl⟩ := z.mk_surjective
        dsimp
        simp only [Category.comp_id, Category.id_comp, ← prod_id',
          CategoryTheory.Functor.map_id, inverse_obj, inverse_map_mkHom_homMk_id]))

set_option backward.isDefEq.respectTransparency.types false in
variable {X Y Z} in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.associativity'Iso_hom_app** 是 Ma
thlib 中的一个定理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：∀ {X Y Z : SSet.Truncated 2} (xyz : X.HomotopyCategory × Y.HomotopyCategor
y × Z.HomotopyCategory),   (SSet.Truncated.HomotopyCategory.BinaryProduct.associ
ativity'Iso X Y Z).hom.app xyz =     CategoryTheory.CategoryStruct.id       (((C
ategoryTheory.prod.associativity X.HomotopyCategory Y.HomotopyCategory Z.Homotop
yCategory).inverse.comp             (((SSet.Truncated.HomotopyCategory.BinaryPro
duct.inverse X Y).prod                   (CategoryTheory.Functor.id Z.HomotopyCa
tegory)).comp               ((SSet.Truncated.HomotopyCategory.BinaryProduct.inve
rse                     (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)
.comp                 (SSet.Truncated.mapHomotopyCategory (CategoryTheory.Monoid
alCategoryStruct.associator X Y Z).hom)))).obj         xyz)
参数：xyz : X.HomotopyCategory × Y.HomotopyCategory × Z.HomotopyCategory；SSet.Trunc
ated.HomotopyCategory.BinaryProduct.associativity'Iso X Y Z；((CategoryTheory.pro
d.associativity X.HomotopyCategory Y.HomotopyCategory Z.HomotopyCategory).invers
e.comp             (((SSet.Truncated.HomotopyCategory.BinaryProduct.inverse X Y)
.prod                   (CategoryTheory.Functor.id Z.HomotopyCategory)).comp    
           ((SSet.Truncated.HomotopyCategory.BinaryProduct.inverse              
       (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z).comp            
     (SSet.Truncated.mapHomotopyCategory (CategoryTheory.MonoidalCategoryStruct.
associator X Y Z).hom)))).obj         xyz。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma associativity'Iso_hom_app (xyz) :
    (associativity'Iso X Y Z).hom.app xyz = 𝟙 _ := by
  change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
open Functor in
/-- The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to associators. -/
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.associativityIso** 是 Mathlib 中的一
个定义，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：associativityIso : (inverse X Y).prod (𝟭 _) ⋙ inverse (X otimes Y) Z ⋙ map
HomotopyCategory (α_ _ _ _).hom ≅ (prod.associativity _ _ _).functor ⋙ Functor.p
rod (𝟭 _) (inverse Y Z) ⋙ inverse X (Y otimes Z)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The compatibility of `HomotopyCategory.BinaryProduct.inverse`
with respect to associators.
-/
def associativityIso :
    (inverse X Y).prod (𝟭 _) ⋙ inverse (X ⊗ Y) Z ⋙ mapHomotopyCategory (α_ _ _ _).hom ≅
      (prod.associativity _ _ _).functor ⋙ Functor.prod (𝟭 _) (inverse Y Z) ⋙
        inverse X (Y ⊗ Z) :=
  (Functor.leftUnitor _).symm ≪≫ isoWhiskerRight (Equivalence.unitIso _) _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (prod.associativity _ _ _).functor (associativity'Iso X Y Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {X Y Z} in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.associativityIso_hom_app** 是 Mat
hlib 中的一个引理，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：associativityIso_hom_app (xyz) : (associativityIso X Y Z).hom.app xyz = 𝟙 
_
参数：xyz。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Truncated.HomotopyCategory.BinaryProduct.associativity'Iso_hom_app`
：∀ {X Y Z : SSet.Truncated 2} (xyz : X.HomotopyCategory × Y.HomotopyCategory × Z
.HomotopyCategory),   (SSet.Truncated.HomotopyCategory.Binary…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.prod_id`：prod_id (X : C) (Y : D) : 𝟙 (X, Y) = 𝟙 X ×ₘ 𝟙 Y
-/
lemma associativityIso_hom_app (xyz) :
    (associativityIso X Y Z).hom.app xyz = 𝟙 _ := by
  dsimp [associativityIso]
  rw [associativity'Iso_hom_app _]
  dsimp
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.comp_id, ← prod_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Truncated.HomotopyCategory.BinaryProduct.associativity** 是 Mathlib 中的一个引理
，位于命名空间 `SSet.Truncated.HomotopyCategory.BinaryProduct`。
形式化陈述：associativity : (inverse X Y).prod (𝟭 _) ⋙ inverse (X otimes Y) Z ⋙ mapHom
otopyCategory (α_ _ _ _).hom = (prod.associativity _ _ _).functor ⋙ Functor.prod
 (𝟭 _) (inverse Y Z) ⋙ inverse X (Y otimes Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用引理 `SSet.Truncated.HomotopyCategory.BinaryProduct.associativityIso_hom_app`：
associativityIso_hom_app (xyz) : (associativityIso X Y Z).hom.app xyz = 𝟙 _
-/
lemma associativity :
    (inverse X Y).prod (𝟭 _) ⋙ inverse (X ⊗ Y) Z ⋙ mapHomotopyCategory (α_ _ _ _).hom =
    (prod.associativity _ _ _).functor ⋙ Functor.prod (𝟭 _) (inverse Y Z) ⋙
      inverse X (Y ⊗ Z) :=
  Functor.ext_of_iso (associativityIso _ _ _) (fun _ ↦ rfl) associativityIso_hom_app

end BinaryProduct

end HomotopyCategory

set_option backward.isDefEq.respectTransparency.types false in
open HomotopyCategory.BinaryProduct in
/-
**SSet.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Truncated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : hoFunctor₂.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (HomotopyCategory.isoTerminal _).symm
      μIso X Y := (iso X Y).symm
      μIso_hom_natural_left _ _ := by ext; apply mapHomotopyCategory_prod_id_comp_inverse
      μIso_hom_natural_right _ _ := by ext; apply id_prod_mapHomotopyCategory_comp_inverse
      left_unitality Y := by ext; apply left_unitality
      right_unitality X := by ext; apply right_unitality
      associativity _ _ _ := by ext; apply associativity }

set_option backward.isDefEq.respectTransparency.types false in
/-- The homotopy category functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is (cartesian) monoidal. -/
/-
**SSet.Truncated.hoFunctor.monoidal** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Truncated.ho
Functor`。
形式化陈述：SSet.hoFunctor.Monoidal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy category functor `hoFunctor : SSet.{u} ⥤ Cat.{u, u}` is (cartesian)
 monoidal.
-/
instance hoFunctor.monoidal : hoFunctor.{u}.Monoidal :=
  inferInstanceAs (truncation 2 ⋙ hoFunctor₂).Monoidal

end Truncated

/-- An equivalence between the vertices of a simplicial set `X` and the
objects of `hoFunctor.obj X`. -/
/-
**SSet.hoFunctor.unitHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.hoFunctor`。
形式化陈述：(X : _root_.SSet) →   (CategoryTheory.MonoidalCategoryStruct.tensorUnit _r
oot_.SSet ⟶ X) ≃     CategoryTheory.Functor ↑CategoryTheory.Cat.chosenTerminal ↑
(SSet.hoFunctor.obj X)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between the vertices of a simplicial set `X` and the
objects of `hoFunctor.obj X`.
-/
def hoFunctor.unitHomEquiv (X : SSet.{u}) :
    (𝟙_ SSet ⟶ X) ≃ Cat.chosenTerminal ⥤ hoFunctor.obj X :=
  (SSet.unitHomEquiv X).trans <|
    (hoFunctor.obj.equiv.{u} X).symm.trans Cat.fromChosenTerminalEquiv.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.hoFunctor.unitHomEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `SSet.hoFunctor`。
形式化陈述：∀ (X : _root_.SSet) (x : CategoryTheory.MonoidalCategoryStruct.tensorUnit 
_root_.SSet ⟶ X),   (SSet.hoFunctor.unitHomEquiv X) x =     (CategoryTheory.Func
tor.LaxMonoidal.ε SSet.hoFunctor).toFunctor.comp (SSet.hoFunctor.map x).toFuncto
r
参数：X : _root_.SSet；x : CategoryTheory.MonoidalCategoryStruct.tensorUnit _root_.S
Set ⟶ X；SSet.hoFunctor.unitHomEquiv X；CategoryTheory.Functor.LaxMonoidal.ε SSet.
hoFunctor；SSet.hoFunctor.map x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hoFunctor.unitHomEquiv_eq (X : SSet.{u}) (x : 𝟙_ SSet ⟶ X) :
    hoFunctor.unitHomEquiv X x =
      (Functor.LaxMonoidal.ε hoFunctor.{u}).toFunctor ⋙ (hoFunctor.map x).toFunctor :=
  rfl

end SSet

