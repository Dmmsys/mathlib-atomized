/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Finset
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Order.Preorder.Finite

/-!
# The standard simplex

We define the standard simplices `Δ[n]` as simplicial sets.
See files `SimplicialSet.Boundary` and `SimplicialSet.Horn`
for their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open Simplicial`.)

-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

/-- The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the standard simplex `Δ[n]` is a
cosimplicial object in the category of simplicial sets. (This functor is essentially given by the
Yoneda embedding). -/
/-
**SSet.stdSimplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：stdSimplex : CosimplicialObject SSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the standard simplex `
Δ[n]` is a
cosimplicial object in the category of simplicial sets. (This functor is essenti
ally given by the
Yoneda embedding).
-/
def stdSimplex : CosimplicialObject SSet.{u} := uliftYoneda

@[inherit_doc SSet.stdSimplex]
scoped[Simplicial] notation3 "Δ[" n "]" => SSet.stdSimplex.obj (SimplexCategory.mk n)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited SSet :=
  ⟨Δ[0]⟩
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(truncation n).obj <| Δ[0]⟩

namespace stdSimplex

open Finset Opposite SimplexCategory

/-- The functor `stdSimplex : SimplexCategory ⥤ SSet` is fully faithful. -/
/-
**SSet.stdSimplex.fullyFaithful** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：fullyFaithful : stdSimplex.{u}.FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `stdSimplex : SimplexCategory ⥤ SSet` is fully faithful.
-/
abbrev fullyFaithful : stdSimplex.{u}.FullyFaithful :=
  ULiftYoneda.fullyFaithful SimplexCategory
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : stdSimplex.{u}.Full := fullyFaithful.full
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : stdSimplex.{u}.Faithful := fullyFaithful.faithful

@[simp]
/-
**SSet.stdSimplex.map_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：map_id (n : SimplexCategory) : (SSet.stdSimplex.map (SimplexCategory.Hom.m
k OrderHom.id : n ⟶ n)) = 𝟙 _
参数：n : SimplexCategory。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma map_id (n : SimplexCategory) :
    (SSet.stdSimplex.map (SimplexCategory.Hom.mk OrderHom.id : n ⟶ n)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- Simplices of the standard simplex identify to morphisms in `SimplexCategory`. -/
/-
**SSet.stdSimplex.objEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：objEquiv {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} : (stdSimplex.{u}.o
bj n).obj m ≃ (m.unop ⟶ n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simplices of the standard simplex identify to morphisms in `SimplexCategory`.
-/
def objEquiv {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    (stdSimplex.{u}.obj n).obj m ≃ (m.unop ⟶ n) :=
  Equiv.ulift.{u, 0}
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) (m : SimplexCategoryᵒᵖ) :
    DecidableEq ((stdSimplex.{u}.obj n).obj m) :=
  fun a b ↦ decidable_of_iff (stdSimplex.objEquiv a = stdSimplex.objEquiv b) (by simp)

/-- If `x : Δ[n] _⦋d⦌` and `i : Fin (d + 1)`, we may evaluate `x i : Fin (n + 1)`. -/
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x : Δ[n] _⦋d⦌` and `i : Fin (d + 1)`, we may evaluate `x i : Fin (n + 1)`.
-/
instance (n i : ℕ) : FunLike (Δ[n] _⦋i⦌) (Fin (i + 1)) (Fin (n + 1)) where
  coe x j := (objEquiv x).toOrderHom j
  coe_injective _ _ h := objEquiv.injective (by ext : 3; apply congr_fun h)
/-
**SSet.stdSimplex.monotone_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：monotone_apply {n i : Nat} (x : Δ[n] _⦋i⦌) : Monotone (fun (j : Fin (i + 1
)) => x j)
参数：x : Δ[n] _⦋i⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
lemma monotone_apply {n i : ℕ} (x : Δ[n] _⦋i⦌) :
    Monotone (fun (j : Fin (i + 1)) ↦ x j) :=
  (objEquiv x).toOrderHom.monotone

@[ext]
/-
**SSet.stdSimplex.ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：ext {n d : Nat} (x y : Δ[n] _⦋d⦌) (h : forall (i : Fin (d + 1)), x i = y i
) : x = y
参数：x y : Δ[n] _⦋d⦌；h : forall (i : Fin (d + 1)), x i = y i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
lemma ext {n d : ℕ} (x y : Δ[n] _⦋d⦌) (h : ∀ (i : Fin (d + 1)), x i = y i) : x = y :=
  DFunLike.ext _ _ h

@[simp]
/-
**SSet.stdSimplex.objEquiv_toOrderHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdS
implex`。
形式化陈述：objEquiv_toOrderHom_apply {n i : Nat} (x : (stdSimplex.{u} ^⦋n⦌).obj (op ⦋
i⦌)) (j : Fin (i + 1)) : DFunLike.coe (F
参数：x : (stdSimplex.{u} ^⦋n⦌).obj (op ⦋i⦌)；j : Fin (i + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_toOrderHom_apply {n i : ℕ}
    (x : (stdSimplex.{u} ^⦋n⦌).obj (op ⦋i⦌)) (j : Fin (i + 1)) :
    DFunLike.coe (F := Fin (i + 1) →o Fin (n + 1))
      ((DFunLike.coe (F := Δ[n].obj (op ⦋i⦌) ≃ (⦋i⦌ ⟶ ⦋n⦌))
        objEquiv x)).toOrderHom j = x j :=
  rfl
/-
**SSet.stdSimplex.objEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`
。
形式化陈述：objEquiv_symm_comp {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ} (f : m
.unop ⟶ n) (g : n ⟶ n') : objEquiv.{u}.symm (f ≫ g) = (stdSimplex.map g).app _ (
objEquiv.{u}.symm f)
参数：f : m.unop ⟶ n；g : n ⟶ n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma objEquiv_symm_comp {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : n ⟶ n') :
    objEquiv.{u}.symm (f ≫ g) =
      (stdSimplex.map g).app _ (objEquiv.{u}.symm f) := rfl
/-
**SSet.stdSimplex.map_objEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：map_objEquiv_symm {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ} (f : m.
unop ⟶ n) (g : m ⟶ m') : (stdSimplex.{u}.obj n).map g (objEquiv.symm f) = objEqu
iv.symm (g.unop ≫ f)
参数：f : m.unop ⟶ n；g : m ⟶ m'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma map_objEquiv_symm {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : m ⟶ m') :
    (stdSimplex.{u}.obj n).map g (objEquiv.symm f) =
      objEquiv.symm (g.unop ≫ f) :=
  rfl

@[simp]
/-
**SSet.stdSimplex.objEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex
`。
形式化陈述：objEquiv_symm_apply {n m : Nat} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) : (objEq
uiv.{u}.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i
参数：f : ⦋m⦌ ⟶ ⦋n⦌；i : Fin (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma objEquiv_symm_apply {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (objEquiv.{u}.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i := rfl

@[simp]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk (n + 1) ⟶ m) (i : Fin (n + 2)) :
    dsimp% (stdSimplex.obj _).δ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n⦌)).symm (SimplexCategory.δ i ≫ f) := by
  rfl

@[simp]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk n ⟶ m) (i : Fin (n + 1)) :
    dsimp% (stdSimplex.obj _).σ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n + 1⦌)).symm (SimplexCategory.σ i ≫ f) := by
  rfl

/-- Constructor for simplices of the standard simplex which takes a `OrderHom` as an input. -/
/-
**SSet.stdSimplex.objMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} (f : Fin (len m.unop +
 1) ->o Fin (n.len + 1)) : (stdSimplex.{u}.obj n).obj m
参数：f : Fin (len m.unop + 1) ->o Fin (n.len + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for simplices of the standard simplex which takes a `OrderHom` as an
 input.
-/
abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) →o Fin (n.len + 1)) :
    (stdSimplex.{u}.obj n).obj m :=
  objEquiv.symm (Hom.mk f)

@[simp]
/-
**SSet.stdSimplex.objMk_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：objMk_apply {n m : Nat} (f : Fin (m + 1) ->o Fin (n + 1)) (i : Fin (m + 1)
) : objMk.{u} (n
参数：f : Fin (m + 1) ->o Fin (n + 1)；i : Fin (m + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objMk_apply {n m : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := ⦋n⦌) (m := op ⦋m⦌) f i = f i :=
  rfl
/-
**SSet.stdSimplex.objMk_bijective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：objMk_bijective {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} : Function.B
ijective (objMk (n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
lemma objMk_bijective {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    Function.Bijective (objMk (n := n) (m := m)) :=
  (objEquiv.trans homEquivOrderHom).symm.bijective

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `Fin (m+1)` to `Fin (n+1)`. -/
/-
**SSet.stdSimplex.asOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin
 (n + 1))
参数：α : Δ[n].obj m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `Fin (m+1)` to `Fin (n+1)`.
-/
def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.down.toOrderHom
/-
**SSet.stdSimplex.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory} 
(x : (stdSimplex.{u}.obj n).obj m₁) : (stdSimplex.{u}.obj n).map f x = objEquiv.
symm (f.unop ≫ objEquiv x)
参数：f : m₁ ⟶ m₂；x : (stdSimplex.{u}.obj n).obj m₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory}
    (x : (stdSimplex.{u}.obj n).obj m₁) :
    (stdSimplex.{u}.obj n).map f x = objEquiv.symm (f.unop ≫ objEquiv x) := by
  rfl

@[simp]
/-
**SSet.stdSimplex.coe_asOrderHom_objEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `SSet.s
tdSimplex`。
形式化陈述：coe_asOrderHom_objEquiv_symm {n m : Nat} (α : ⦋n⦌ ⟶ ⦋m⦌) : ⇑(asOrderHom (o
bjEquiv.{u}.symm α)) = α
参数：α : ⦋n⦌ ⟶ ⦋m⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_asOrderHom_objEquiv_symm {n m : ℕ} (α : ⦋n⦌ ⟶ ⦋m⦌) :
    ⇑(asOrderHom (objEquiv.{u}.symm α)) = α := rfl

end stdSimplex

/-- The canonical bijection `(stdSimplex.obj n ⟶ X) ≃ X.obj (op n)`. -/
/-
**SSet.yonedaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv {X : SSet.{u}} {n : SimplexCategory} : (stdSimplex.obj n ⟶ X) 
≃ X.obj (op n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical bijection `(stdSimplex.obj n ⟶ X) ≃ X.obj (op n)`.
-/
def yonedaEquiv {X : SSet.{u}} {n : SimplexCategory} :
    (stdSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  uliftYonedaEquiv
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : SSet.{u}) (n : SimplexCategory) [DecidableEq (X.obj (op n))] :
    DecidableEq (stdSimplex.obj n ⟶ X) :=
  fun a b ↦ decidable_of_iff (yonedaEquiv a = yonedaEquiv b) (by simp)

@[simp]
/-
**SSet._root_.SSet.yonedaEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SSet.yonedaEquiv_symm_comp {X Y : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    (f : X ⟶ Y) :
    yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app _ x) :=
  uliftYonedaEquiv_symm_comp ..

set_option backward.isDefEq.respectTransparency false in
/-
**SSet._root_.SSet.yonedaEquiv_const** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SSet.yonedaEquiv_const {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv (const x : Δ[0] ⟶ X) = x := by
  simp [yonedaEquiv, uliftYonedaEquiv]

@[simp]
/-
**SSet._root_.SSet.yonedaEquiv_symm_zero** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SSet.yonedaEquiv_symm_zero {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv.symm x = const x := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_const]
/-
**SSet.yonedaEquiv_map** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m) : yonedaEquiv.{u} (std
Simplex.map f) = stdSimplex.objEquiv.symm f
参数：f : n ⟶ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m) :
    yonedaEquiv.{u} (stdSimplex.map f) = stdSimplex.objEquiv.symm f :=
  yonedaEquiv.symm.injective rfl

@[deprecated (since := "2026-03-21")] alias stdSimplex.yonedaEquiv_map := yonedaEquiv_map

@[simp]
/-
**SSet.yonedaEquiv_symm_app** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_symm_app {S : SSet} (n : SimplexCategory) (x : S.obj (op n)) (
α : (stdSimplex.obj n).obj (op n)) : (yonedaEquiv.symm x).app (op n) α = S.map (
SSet.stdSimplex.objEquiv α).op x
参数：n : SimplexCategory；x : S.obj (op n)；α : (stdSimplex.obj n).obj (op n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma yonedaEquiv_symm_app {S : SSet} (n : SimplexCategory) (x : S.obj (op n))
    (α : (stdSimplex.obj n).obj (op n)) :
    (yonedaEquiv.symm x).app (op n) α = S.map (SSet.stdSimplex.objEquiv α).op x := rfl

@[simp]
/-
**SSet.yonedaEquiv_symm_stdSimplex_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_symm_stdSimplex_id (n : SimplexCategory) : yonedaEquiv.symm (S
Set.stdSimplex.objEquiv.symm (β
参数：n : SimplexCategory。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
lemma yonedaEquiv_symm_stdSimplex_id (n : SimplexCategory) :
    yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm (β := n ⟶ _) (𝟙 n)) = 𝟙 (stdSimplex.obj n) :=
  yonedaEquiv.symm_apply_eq.mpr rfl

open Finset Opposite SimplexCategory
/-
**SSet.yonedaEquiv_symm_app_objEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_symm_app_objEquiv_symm {X : SSet.{u}} {n : SimplexCategory} (x
 : X.obj (op n)) {m : SimplexCategoryᵒᵖ} (f : unop m ⟶ n) : dsimp% (yonedaEquiv.
symm x).app _ (stdSimplex.objEquiv.symm f) = X.map f.op x
参数：x : X.obj (op n)；f : unop m ⟶ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma yonedaEquiv_symm_app_objEquiv_symm {X : SSet.{u}} {n : SimplexCategory}
    (x : X.obj (op n)) {m : SimplexCategoryᵒᵖ} (f : unop m ⟶ n) :
    dsimp% (yonedaEquiv.symm x).app _ (stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl
/-
**SSet.opObjEquiv_yonedaEquiv_const** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：opObjEquiv_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X.o
p _⦋0⦌) : opObjEquiv (n
参数：x : X.op _⦋0⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opObjEquiv_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X.op _⦋0⦌) :
    opObjEquiv (n := op n) (yonedaEquiv (const x)) =
      yonedaEquiv (const (opObjEquiv x)) := rfl
/-
**SSet.opObjEquiv_symm_yonedaEquiv_const** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：opObjEquiv_symm_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x 
: X _⦋0⦌) : (opObjEquiv (n
参数：x : X _⦋0⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma opObjEquiv_symm_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X _⦋0⦌) :
    (opObjEquiv (n := op n)).symm (yonedaEquiv (const x)) =
      yonedaEquiv (const (opObjEquiv.symm x)) := rfl

namespace stdSimplex

/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_apply {n d : ℕ} (x : (Δ[n] _⦋d + 1⦌ : Type u)) (i : Fin (d + 2)) (j : Fin (d + 1)) :
    Δ[n].δ i x j = x (i.succAbove j) := rfl
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_apply {n d : ℕ} (x : (Δ[n] _⦋d⦌ : Type u)) (i : Fin (d + 1)) (j : Fin (d + 2)) :
    Δ[n].σ i x j = x (i.predAbove j) := rfl

@[simp]
/-
**SSet.stdSimplex.objEquiv_yonedaEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSim
plex`。
形式化陈述：objEquiv_yonedaEquiv_id (n : Nat) : dsimp% objEquiv (yonedaEquiv.{u} (𝟙 Δ[
n])) = 𝟙 _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma objEquiv_yonedaEquiv_id (n : ℕ) :
    dsimp% objEquiv (yonedaEquiv.{u} (𝟙 Δ[n])) = 𝟙 _ := rfl
/-
**SSet.stdSimplex.map_objEquiv_op_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimpl
ex`。
形式化陈述：map_objEquiv_op_apply {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op 
n)) {m : SimplexCategoryᵒᵖ} (y : (stdSimplex.obj n).obj m) : dsimp% X.map (stdSi
mplex.objEquiv y).op x = (yonedaEquiv.symm x).app m y
参数：x : X.obj (op n)；y : (stdSimplex.obj n).obj m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_objEquiv_op_apply
    {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    {m : SimplexCategoryᵒᵖ} (y : (stdSimplex.obj n).obj m) :
    dsimp% X.map (stdSimplex.objEquiv y).op x = (yonedaEquiv.symm x).app m y := by
  rfl

/-- The (degenerate) `m`-simplex in the standard simplex concentrated in vertex `k`. -/
/-
**SSet.stdSimplex.const** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：const (n : Nat) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m
参数：n : Nat；k : Fin (n + 1)；m : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (degenerate) `m`-simplex in the standard simplex concentrated in vertex `k`.
-/
def const (n : ℕ) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k)

@[simp]
/-
**SSet.stdSimplex.const_down_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimpl
ex`。
形式化陈述：const_down_toOrderHom (n : Nat) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) 
: (const n k m).down.toOrderHom = OrderHom.const _ k
参数：n : Nat；k : Fin (n + 1)；m : SimplexCategoryᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_down_toOrderHom (n : ℕ) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) :
    (const n k m).down.toOrderHom = OrderHom.const _ k :=
  rfl

/-- The `0`-simplices of `Δ[n]` identify to the elements in `Fin (n + 1)`. -/
@[simps]
/-
**SSet.stdSimplex.obj** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `0`-simplices of `Δ[n]` identify to the elements in `Fin (n + 1)`.
-/
def obj₀Equiv {n : ℕ} : Δ[n] _⦋0⦌ ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_one_eq_const : stdSimplex.{u}.δ (1 : Fin 2) = SSet.const (obj₀Equiv.symm 0) := by
  decide
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_eq_const : stdSimplex.{u}.δ (0 : Fin 2) = SSet.const (obj₀Equiv.symm 1) := by
  decide

/-- The edge of the standard simplex with endpoints `a` and `b`. -/
/-
**SSet.stdSimplex.edge** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：edge (n : Nat) (a b : Fin (n + 1)) (hab : a <= b) : Δ[n] _⦋1⦌
参数：n : Nat；a b : Fin (n + 1)；hab : a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge of the standard simplex with endpoints `a` and `b`.
-/
def edge (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n] _⦋1⦌ := by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab
/-
**SSet.stdSimplex.coe_edge_down_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSi
mplex`。
形式化陈述：coe_edge_down_toOrderHom (n : Nat) (a b : Fin (n + 1)) (hab : a <= b) : ↑(
edge n a b hab).down.toOrderHom = ![a, b]
参数：n : Nat；a b : Fin (n + 1)；hab : a <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_edge_down_toOrderHom (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    ↑(edge n a b hab).down.toOrderHom = ![a, b] :=
  rfl

/-- The triangle in the standard simplex with vertices `a`, `b`, and `c`. -/
/-
**SSet.stdSimplex.triangle** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：triangle {n : Nat} (a b c : Fin (n + 1)) (hab : a <= b) (hbc : b <= c) : Δ
[n] _⦋2⦌
参数：a b c : Fin (n + 1)；hab : a <= b；hbc : b <= c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle in the standard simplex with vertices `a`, `b`, and `c`.
-/
def triangle {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) : Δ[n] _⦋2⦌ := by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, true_and]
/-
**SSet.stdSimplex.coe_triangle_down_toOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `SSet.s
tdSimplex`。
形式化陈述：coe_triangle_down_toOrderHom {n : Nat} (a b c : Fin (n + 1)) (hab : a <= b
) (hbc : b <= c) : ↑(triangle a b c hab hbc).down.toOrderHom = ![a, b, c]
参数：a b c : Fin (n + 1)；hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_triangle_down_toOrderHom {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) :
    ↑(triangle a b c hab hbc).down.toOrderHom = ![a, b, c] :=
  rfl

attribute [local simp] image_subset_iff

/-- Given `S : Finset (Fin (n + 1))`, this is the corresponding face of `Δ[n]`,
as a subcomplex. -/
@[simps -isSimp obj]
/-
**SSet.stdSimplex.face** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：face {n : Nat} (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex w
here obj U
参数：S : Finset (Fin (n + 1))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `S : Finset (Fin (n + 1))`, this is the corresponding face of `Δ[n]`,
as a subcomplex.
-/
def face {n : ℕ} (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj U := Set.ofPred (fun f ↦ Finset.image (objEquiv f).toOrderHom ⊤ ≤ S)
  map {U V} i := by aesop

attribute [local simp] face_obj

@[simp]
/-
**SSet.stdSimplex.mem_face_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：mem_face_iff {n : Nat} (S : Finset (Fin (n + 1))) {d : Nat} (x : (Δ[n] : S
Set.{u}) _⦋d⦌) : x in (face S).obj _ ↔ forall (i : Fin (d + 1)), x i in S
参数：S : Finset (Fin (n + 1))；x : (Δ[n] : SSet.{u}) _⦋d⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.stdSimplex.face_obj`：∀ {n : ℕ} (S : Finset (Fin (n + 1))) (U : Simp
lexCategoryᵒᵖ),   (SSet.stdSimplex.face S).obj U =     {f | Finset.image ⇑(Simpl
exCategory.Hom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_face_iff {n : ℕ} (S : Finset (Fin (n + 1))) {d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (face S).obj _ ↔ ∀ (i : Fin (d + 1)), x i ∈ S := by
  simp
/-
**SSet.stdSimplex.face_inter_face** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：face_inter_face {n : Nat} (S₁ S₂ : Finset (Fin (n + 1))) : face S₁ ⊓ face 
S₂ = face (S₁ ⊓ S₂)
参数：S₁ S₂ : Finset (Fin (n + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.stdSimplex.face_obj`：∀ {n : ℕ} (S : Finset (Fin (n + 1))) (U : Simp
lexCategoryᵒᵖ),   (SSet.stdSimplex.face S).obj U =     {f | Finset.image ⇑(Simpl
exCategory.Hom…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma face_inter_face {n : ℕ} (S₁ S₂ : Finset (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  aesop

@[simp]
/-
**SSet.stdSimplex.face_empty** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：face_empty (n : Nat) : face.{u} (∅ : Finset (Fin (n + 1))) = ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SSet.stdSimplex.face_obj`：∀ {n : ℕ} (S : Finset (Fin (n + 1))) (U : Simp
lexCategoryᵒᵖ),   (SSet.stdSimplex.face S).obj U =     {f | Finset.image ⇑(Simpl
exCategory.Hom…
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用引理 `Finset.univ_neq_empty`：univ_neq_empty (α : Type*) [Fintype α] [Nonempty 
α] : (Finset.univ : Finset α) != ∅
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma face_empty (n : ℕ) :
    face.{u} (∅ : Finset (Fin (n + 1))) = ⊥ := by
  ext
  simpa using Finset.univ_neq_empty _

@[simp]
/-
**SSet.stdSimplex.face_univ** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：face_univ (n : Nat) : face.{u} (.univ : Finset (Fin (n + 1))) = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
-/
lemma face_univ (n : ℕ) :
    face.{u} (.univ : Finset (Fin (n + 1))) = ⊤ := by
  ext
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  apply Finset.subset_univ

end stdSimplex

/-
**SSet.yonedaEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_comp {X Y : SSet.{u}} {n : SimplexCategory} (f : stdSimplex.ob
j n ⟶ X) (g : X ⟶ Y) : yonedaEquiv (f ≫ g) = g.app _ (yonedaEquiv f)
参数：f : stdSimplex.obj n ⟶ X；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaEquiv_comp {X Y : SSet.{u}} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ X) (g : X ⟶ Y) :
    yonedaEquiv (f ≫ g) = g.app _ (yonedaEquiv f) := rfl

@[simp high]
/-
**SSet.yonedaEquiv_symm_app_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_symm_app_id {X : SSet.{u}} {n : Nat} (x : X _⦋n⦌) : (yonedaEqu
iv.symm x).app _ (yonedaEquiv (𝟙 _)) = x
参数：x : X _⦋n⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma yonedaEquiv_symm_app_id {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    (yonedaEquiv.symm x).app _ (yonedaEquiv (𝟙 _)) = x := by
  simp
/-
**SSet.yonedaEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_naturality {X : SSet} {m n : SimplexCategory} (f : m ⟶ n) (g :
 stdSimplex.obj n ⟶ X) : X.map f.op (yonedaEquiv g) = yonedaEquiv (stdSimplex.ma
p f ≫ g)
参数：f : m ⟶ n；g : stdSimplex.obj n ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.uliftYonedaEquiv_naturality`：uliftYonedaEquiv_naturality 
{X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)} (f : uliftYoneda.{w}.obj (unop X) ⟶ F) (
g : X ⟶ Y) : F.map g (uliftYoned…
-/
lemma yonedaEquiv_naturality {X : SSet} {m n : SimplexCategory}
    (f : m ⟶ n) (g : stdSimplex.obj n ⟶ X) :
    X.map f.op (yonedaEquiv g) = yonedaEquiv (stdSimplex.map f ≫ g) :=
  uliftYonedaEquiv_naturality _ _

@[reassoc]
/-
**SSet.yonedaEquiv_symm_naturality_left** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：yonedaEquiv_symm_naturality_left {X : SSet} {m n : SimplexCategory} (f : m
 ⟶ n) (g : X.obj (Opposite.op n)) : stdSimplex.map f ≫ yonedaEquiv.symm g = yone
daEquiv.symm (X.map f.op g)
参数：f : m ⟶ n；g : X.obj (Opposite.op n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.yonedaEquiv_naturality`：yonedaEquiv_naturality {X : SSet} {m n : Si
mplexCategory} (f : m ⟶ n) (g : stdSimplex.obj n ⟶ X) : X.map f.op (yonedaEquiv 
g) = yonedaEquiv …
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma yonedaEquiv_symm_naturality_left {X : SSet} {m n : SimplexCategory}
    (f : m ⟶ n) (g : X.obj (Opposite.op n)) :
    stdSimplex.map f ≫ yonedaEquiv.symm g = yonedaEquiv.symm (X.map f.op g) := by
  rw [yonedaEquiv.eq_symm_apply, ← yonedaEquiv_naturality, yonedaEquiv.apply_symm_apply]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stdSimplex.δ_comp_yonedaEquiv_symm
    {X : SSet.{u}} {n : ℕ} (x : X _⦋n + 1⦌) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.δ i x) :=
  yonedaEquiv_symm_naturality_left ..
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stdSimplex.σ_comp_yonedaEquiv_symm
    {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) (i : Fin (n + 1)) :
    stdSimplex.σ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.σ i x) :=
  yonedaEquiv_symm_naturality_left ..
/-
**SSet.stdSimplex.yonedaEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stdSimplex.yonedaEquiv_δ_comp
    {X : SSet.{u}} {n : ℕ} (g : Δ[n + 1] ⟶ X) (i : Fin (n + 2)) :
    yonedaEquiv (stdSimplex.δ i ≫ g) = X.δ i (yonedaEquiv g) :=
  (yonedaEquiv_naturality ..).symm
/-
**SSet.stdSimplex.yonedaEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma stdSimplex.yonedaEquiv_σ_comp
    {X : SSet.{u}} {n : ℕ} (g : Δ[n] ⟶ X) (i : Fin (n + 1)) :
    yonedaEquiv (stdSimplex.σ i ≫ g) = X.σ i (yonedaEquiv g) :=
  (yonedaEquiv_naturality ..).symm

namespace Subcomplex

variable {X : SSet.{u}}

/-
**SSet.Subcomplex.range_eq_ofSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`
。
形式化陈述：range_eq_ofSimplex {n : Nat} (f : Δ[n] ⟶ X) : range f = ofSimplex (yonedaE
quiv f)
参数：f : Δ[n] ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subfunctor.range_eq_ofSection'`：range_eq_ofSection' {X : 
C} (f : yoneda.obj X ⋙ uliftFunctor.{w} ⟶ F) : range f = ofSection (uliftYonedaE
quiv f)
-/
lemma range_eq_ofSimplex {n : ℕ} (f : Δ[n] ⟶ X) :
    range f = ofSimplex (yonedaEquiv f) :=
  Subfunctor.range_eq_ofSection' _
/-
**SSet.Subcomplex.yonedaEquiv_coe** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
形式化陈述：yonedaEquiv_coe {A : X.Subcomplex} {n : SimplexCategory} (f : stdSimplex.o
bj n ⟶ A) : (yonedaEquiv f).val = yonedaEquiv (f ≫ A.ι)
参数：f : stdSimplex.obj n ⟶ A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaEquiv_coe {A : X.Subcomplex} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ A) :
    (yonedaEquiv f).val = yonedaEquiv (f ≫ A.ι) := by
  rfl

end Subcomplex

namespace stdSimplex

/-
**SSet.stdSimplex.obj** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma obj₀Equiv_symm_mem_face_iff
    {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (obj₀Equiv.symm i) ∈ (face.{u} S).obj (op (.mk 0)) ↔ i ∈ S :=
  ⟨fun h ↦ by simpa using! h, by aesop⟩
/-
**SSet.stdSimplex.face_le_face_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：face_le_face_iff {n : Nat} (S₁ S₂ : Finset (Fin (n + 1))) : face.{u} S₁ <=
 face S₂ ↔ S₁ <= S₂
参数：S₁ S₂ : Finset (Fin (n + 1))。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.stdSimplex.obj₀Equiv_symm_mem_face_iff`：obj₀Equiv_symm_mem_face_iff
 {n : Nat} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) : (obj₀Equiv.symm i) in 
(face.{u} S).obj (op (.mk 0)) ↔ i…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma face_le_face_iff {n : ℕ} (S₁ S₂ : Finset (Fin (n + 1))) :
    face.{u} S₁ ≤ face S₂ ↔ S₁ ≤ S₂ := by
  refine ⟨fun h i hi ↦ ?_, fun h d a ha ↦ ha.trans h⟩
  simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
  exact h _ hi
/-
**SSet.stdSimplex.face_eq_ofSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：face_eq_ofSimplex {n : Nat} (S : Finset (Fin (n + 1))) (m : Nat) (e : Fin 
(m + 1) ≃o S) : face.{u} S = Subcomplex.ofSimplex (X
参数：S : Finset (Fin (n + 1))；m : Nat；e : Fin (m + 1) ≃o S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.mem_face_iff`：mem_face_iff {n : Nat} (S : Finset (Fin (n
 + 1))) {d : Nat} (x : (Δ[n] : SSet.{u}) _⦋d⦌) : x in (face S).obj _ ↔ forall (i
 : Fin (d + 1)), x…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用引理 `SSet.stdSimplex.ext`：ext {n d : Nat} (x y : Δ[n] _⦋d⦌) (h : forall (i : 
Fin (d + 1)), x i = y i) : x = y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderHom.Subtype.val_coe`：∀ {α : Type u_2} [inst : Preorder α] (p : α → 
Prop), ⇑(OrderHom.Subtype.val p) = Subtype.val
· 使用定理 `OrderEmbedding.toOrderHom_coe`：∀ {X : Type u_6} {Y : Type u_7} [inst : P
reorder X] [inst_1 : Preorder Y] (f : X ↪o Y), ⇑f.toOrderHom = ⇑f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma face_eq_ofSimplex {n : ℕ} (S : Finset (Fin (n + 1))) (m : ℕ) (e : Fin (m + 1) ≃o S) :
    face.{u} S =
      Subcomplex.ofSimplex (X := Δ[n])
        (objMk ((OrderHom.Subtype.val _).comp
          e.toOrderEmbedding.toOrderHom)) := by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction k using SimplexCategory.rec with | _ k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) →o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv x).toOrderHom.monotone }
    refine ⟨Quiver.Hom.op
      (SimplexCategory.Hom.mk ((e.symm.toOrderEmbedding.toOrderHom.comp φ))), ?_⟩
    ext j : 1
    simpa only [Subtype.ext_iff] using! e.apply_symm_apply ⟨_, hx j⟩
  · simp

set_option backward.defeqAttrib.useBackward true in
/-- If `S : Finset (Fin (n + 1))` is order isomorphic to `Fin (m + 1)`,
then the face `face S` of `Δ[n]` is representable by `m`,
i.e. `face S` is isomorphic to `Δ[m]`, see `stdSimplex.isoOfRepresentableBy`. -/
/-
**SSet.stdSimplex.faceRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex
`。
形式化陈述：faceRepresentableBy {n : Nat} (S : Finset (Fin (n + 1))) (m : Nat) (e : Fi
n (m + 1) ≃o S) : (face S : SSet.{u}).RepresentableBy ⦋m⦌ where homEquiv {j}
参数：S : Finset (Fin (n + 1))；m : Nat；e : Fin (m + 1) ≃o S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S : Finset (Fin (n + 1))` is order isomorphic to `Fin (m + 1)`,
then the face `face S` of `Δ[n]` is representable by `m`,
i.e. `face S` is isomorphic to `Δ[m]`, see `stdSimplex.isoOfRepresentableBy`.
-/
def faceRepresentableBy {n : ℕ} (S : Finset (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy ⦋m⦌ where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val (· ∈ S)).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := fun ⟨x, hx⟩ ↦ SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv x).toOrderHom i, hx (by simp)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ ↦ by
        induction j using SimplexCategory.rec with | _ j
        dsimp
        ext i : 2
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

/-- If a simplicial set `X` is representable by `⦋m⦌` for some `m : ℕ`, then this is the
corresponding isomorphism `Δ[m] ≅ X`. -/
/-
**SSet.stdSimplex.isoOfRepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimple
x`。
形式化陈述：isoOfRepresentableBy {X : SSet.{u}} {m : Nat} (h : X.RepresentableBy ⦋m⦌) 
: Δ[m] ≅ X
参数：h : X.RepresentableBy ⦋m⦌。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If a simplicial set `X` is representable by `⦋m⦌` for some `m : ℕ`, then this is
 the
corresponding isomorphism `Δ[m] ≅ X`.
-/
def isoOfRepresentableBy {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy ⦋m⦌) :
    Δ[m] ≅ X :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (objEquiv.trans h.homEquiv))
    (fun _ ↦ by ext; apply h.homEquiv_comp)
/-
**SSet.stdSimplex.ofSimplex_yonedaEquiv_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimp
lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofSimplex_yonedaEquiv_δ {n : ℕ} (i : Fin (n + 2)) :
    Subcomplex.ofSimplex (yonedaEquiv (stdSimplex.δ i)) = face.{u} {i}ᶜ :=
  (face_eq_ofSimplex _ _ (Fin.succAboveOrderIso i)).symm

@[simp]
/-
**SSet.stdSimplex.range_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_δ {n : ℕ} (i : Fin (n + 2)) :
    Subcomplex.range (stdSimplex.δ i) = face.{u} {i}ᶜ := by
  rw [Subcomplex.range_eq_ofSimplex]
  exact ofSimplex_yonedaEquiv_δ i

/-- The standard simplex identifies to the nerve to the preordered type
`ULift (Fin (n + 1))`. -/
@[pp_with_univ]
/-
**SSet.stdSimplex.isoNerve** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：isoNerve (n : Nat) : (Δ[n] : SSet.{u}) ≅ nerve (ULift.{u} (Fin (n + 1)))
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The standard simplex identifies to the nerve to the preordered type
`ULift (Fin (n + 1))`.
-/
def isoNerve (n : ℕ) :
    (Δ[n] : SSet.{u}) ≅ nerve (ULift.{u} (Fin (n + 1))) :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso (objEquiv.trans
    { toFun f := (ULift.orderIso.symm.monotone.comp f.toOrderHom.monotone).functor
      invFun f :=
        SimplexCategory.Hom.mk
          (ULift.orderIso.toOrderEmbedding.toOrderHom.comp f.toOrderHom)
      left_inv _ := by aesop }))

@[simp]
/-
**SSet.stdSimplex.isoNerve_hom_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimp
lex`。
形式化陈述：isoNerve_hom_app_apply {n d : Nat} (s : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) : d
simp% ((isoNerve.{u} n).hom.app _ s).obj i = ULift.up (s i)
参数：s : (Δ[n] _⦋d⦌)；i : Fin (d + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoNerve_hom_app_apply {n d : ℕ}
    (s : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) :
    dsimp% ((isoNerve.{u} n).hom.app _ s).obj i = ULift.up (s i) := rfl

@[simp]
/-
**SSet.stdSimplex.isoNerve_inv_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimp
lex`。
形式化陈述：isoNerve_inv_app_apply {n d : Nat} (F : (nerve (ULift.{u} (Fin (n + 1)))) 
_⦋d⦌) (i : Fin (d + 1)) : dsimp% (isoNerve.{u} n).inv.app _ F i = (F.obj i).down
参数：F : (nerve (ULift.{u} (Fin (n + 1)))) _⦋d⦌；i : Fin (d + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoNerve_inv_app_apply {n d : ℕ}
    (F : (nerve (ULift.{u} (Fin (n + 1)))) _⦋d⦌) (i : Fin (d + 1)) :
    dsimp% (isoNerve.{u} n).inv.app _ F i = (F.obj i).down := rfl
/-
**SSet.stdSimplex.mem_nonDegenerate_iff_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.stdSimplex`。
形式化陈述：mem_nonDegenerate_iff_strictMono {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) 
: s in Δ[n].nonDegenerate d ↔ StrictMono s
参数：s : (Δ[n] : SSet.{u}) _⦋d⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.nonDegenerate_iff_of_mono`：nonDegenerate_iff_of_mono {Y : SSet.{u}}
 (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) : f.app _ x in Y.nonDegenerate n ↔ x in X.non
Degenerate n
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
· 使用引理 `PartialOrder.mem_nerve_nonDegenerate_iff_strictMono`：mem_nerve_nonDegene
rate_iff_strictMono (s : (nerve X) _⦋n⦌) : s in (nerve X).nonDegenerate n ↔ Stri
ctMono s.obj
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_nonDegenerate_iff_strictMono {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s ∈ Δ[n].nonDegenerate d ↔ StrictMono s := by
  rw [← nonDegenerate_iff_of_mono (isoNerve n).hom,
    PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl
/-
**SSet.stdSimplex.mem_nonDegenerate_iff_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet.std
Simplex`。
形式化陈述：mem_nonDegenerate_iff_mono {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) : s in
 Δ[n].nonDegenerate d ↔ Mono (objEquiv s)
参数：s : (Δ[n] : SSet.{u}) _⦋d⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.mem_nonDegenerate_iff_strictMono`：mem_nonDegenerate_iff_
strictMono {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) : s in Δ[n].nonDegenerate d 
↔ StrictMono s
· 使用定理 `SimplexCategory.mono_iff_injective`：mono_iff_injective {n m : SimplexCat
egory} {f : n ⟶ m} : Mono f ↔ Function.Injective f.toOrderHom
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Fin.strictMono_iff_lt_succ`：strictMono_iff_lt_succ : StrictMono f ↔ fora
ll i : Fin n, f (castSucc i) < f i.succ
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用引理 `SSet.stdSimplex.monotone_apply`：monotone_apply {n i : Nat} (x : Δ[n] _⦋i
⦌) : Monotone (fun (j : Fin (i + 1)) => x j)
· 使用定理 `Fin.castSucc_le_succ`：castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i
.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma mem_nonDegenerate_iff_mono {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s ∈ Δ[n].nonDegenerate d ↔ Mono (objEquiv s) := by
  rw [mem_nonDegenerate_iff_strictMono,
    SimplexCategory.mono_iff_injective]
  refine ⟨fun h ↦ h.injective, fun h ↦ ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain h' | h' := (stdSimplex.monotone_apply s i.castSucc_le_succ).lt_or_eq
  · exact h'
  · simpa [Fin.ext_iff] using h h'
/-
**SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.stdSimplex`。
形式化陈述：objEquiv_symm_mem_nonDegenerate_iff_mono {n d : Nat} (f : ⦋d⦌ ⟶ ⦋n⦌) : (ob
jEquiv.{u} (m
参数：f : ⦋d⦌ ⟶ ⦋n⦌。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma objEquiv_symm_mem_nonDegenerate_iff_mono {n d : ℕ} (f : ⦋d⦌ ⟶ ⦋n⦌) :
    (objEquiv.{u} (m := (op ⦋d⦌))).symm f ∈ Δ[n].nonDegenerate d ↔ Mono f := by
  simp [mem_nonDegenerate_iff_mono]

/-- Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to order embeddings `Fin (d + 1) ↪o Fin (n + 1)`. -/
@[simps! apply_apply symm_apply_coe]
/-
**SSet.stdSimplex.nonDegenerateEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`
。
形式化陈述：nonDegenerateEquiv {n d : Nat} : (Δ[n] : SSet.{u}).nonDegenerate d ≃ (Fin 
(d + 1) ↪o Fin (n + 1)) where toFun s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to order embeddings `Fin (d + 1) ↪o Fin (n + 1)`.
-/
def nonDegenerateEquiv {n d : ℕ} :
    (Δ[n] : SSet.{u}).nonDegenerate d ≃ (Fin (d + 1) ↪o Fin (n + 1)) where
  toFun s := OrderEmbedding.ofStrictMono _ ((mem_nonDegenerate_iff_strictMono _).1 s.2)
  invFun s := ⟨objEquiv.symm (.mk s.toOrderHom), by
    simpa [mem_nonDegenerate_iff_strictMono] using! s.strictMono⟩
  left_inv _ := by aesop
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : (Δ[n] : SSet.{u}).HasDimensionLE n where
  degenerate_eq_top i hi := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    have : Mono (objEquiv x) := by rwa [← mem_nonDegenerate_iff_mono]
    have := SimplexCategory.len_le_of_mono (objEquiv x)
    dsimp at this
    lia

/-- If `i : Fin (n + 2)`, this is the order isomorphism between `Fin (n +1)`
and the complement of `{i}` as a finset. -/
/-
**SSet.stdSimplex.finSuccAboveOrderIsoFinset** 是 Mathlib 中的一个定义，位于命名空间 `SSet.std
Simplex`。
形式化陈述：finSuccAboveOrderIsoFinset {n : Nat} (i : Fin (n + 2)) : Fin (n + 1) ≃o ({
i}ᶜ : Finset _) where toEquiv
参数：i : Fin (n + 2)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `i : Fin (n + 2)`, this is the order isomorphism between `Fin (n +1)`
and the complement of `{i}` as a finset.
-/
def finSuccAboveOrderIsoFinset {n : ℕ} (i : Fin (n + 2)) :
    Fin (n + 1) ≃o ({i}ᶜ : Finset _) where
  toEquiv := (finSuccAboveEquiv (p := i)).trans
    { toFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
      invFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩ }
  map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff
/-
**SSet.stdSimplex.face_singleton_compl** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimple
x`。
形式化陈述：face_singleton_compl {n : Nat} (i : Fin (n + 2)) : face.{u} {i}ᶜ = Subcomp
lex.ofSimplex (objEquiv.symm (SimplexCategory.δ i))
参数：i : Fin (n + 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.stdSimplex.face_eq_ofSimplex`：face_eq_ofSimplex {n : Nat} (S : Fins
et (Fin (n + 1))) (m : Nat) (e : Fin (m + 1) ≃o S) : face.{u} S = Subcomplex.ofS
implex (X
-/
lemma face_singleton_compl {n : ℕ} (i : Fin (n + 2)) :
    face.{u} {i}ᶜ =
      Subcomplex.ofSimplex (objEquiv.symm (SimplexCategory.δ i)) :=
  face_eq_ofSimplex _ _ (finSuccAboveOrderIsoFinset i)

/-- In `Δ[n + 1]`, the face corresponding to the complement of `{i}`
for `i : Fin (n + 2)` is isomorphic to `Δ[n]`. -/
/-
**SSet.stdSimplex.faceSingletonComplIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimpl
ex`。
形式化陈述：faceSingletonComplIso {n : Nat} (i : Fin (n + 2)) : Δ[n] ≅ (face {i}ᶜ : SS
et.{u})
参数：i : Fin (n + 2)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In `Δ[n + 1]`, the face corresponding to the complement of `{i}`
for `i : Fin (n + 2)` is isomorphic to `Δ[n]`.
-/
def faceSingletonComplIso {n : ℕ} (i : Fin (n + 2)) :
    Δ[n] ≅ (face {i}ᶜ : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (finSuccAboveOrderIsoFinset i))

@[reassoc (attr := simp)]
/-
**SSet.stdSimplex.faceSingletonComplIso_hom_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.std
Simplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceSingletonComplIso_hom_ι {n : ℕ} (i : Fin (n + 2)) :
    (faceSingletonComplIso.{u} i).hom ≫ (face {i}ᶜ).ι =
      stdSimplex.δ i := rfl

/-- The order isomorphism between `Fin n` and `{i, j}ᶜ` when `i < j` are
elements in `Fin (n + 2)`. -/
/-
**SSet.stdSimplex.finOrderIsoPairCompl** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimple
x`。
形式化陈述：finOrderIsoPairCompl {n : Nat} (i j : Fin (n + 2)) (h : i < j) : Fin n ≃o 
({i, j}ᶜ : Finset _) where toEquiv
参数：i j : Fin (n + 2)；h : i < j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism between `Fin n` and `{i, j}ᶜ` when `i < j` are
elements in `Fin (n + 2)`.
-/
noncomputable def finOrderIsoPairCompl {n : ℕ} (i j : Fin (n + 2)) (h : i < j) :
    Fin n ≃o ({i, j}ᶜ : Finset _) where
  toEquiv := by
    refine Equiv.ofBijective
      (fun k ↦ ⟨j.succAbove ((i.castPred (Fin.ne_last_of_lt h)).succAbove k), ?_⟩)
        ⟨fun _ _ hk ↦ ?_, fun ⟨l, hl⟩ ↦ ?_⟩
    · grind [compl_insert, mem_compl, Fin.succAbove, Fin.castPred]
    · exact ((Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h))).trans
        (Fin.succAboveOrderEmb j)).injective (by rwa [Subtype.ext_iff] at hk)
    · obtain ⟨m, rfl⟩ : l ∈ Set.range j.succAbove := by
        grind [Fin.range_succAbove, mem_compl, Fin.succAbove]
      obtain ⟨k, hk⟩ : m ∈ Set.range (i.castPred (Fin.ne_last_of_lt h)).succAbove := by
        grind [Fin.range_succAbove, compl_insert, Fin.succAbove, Fin.castPred]
      exact ⟨k, by simp [hk]⟩
  map_rel_iff' :=
    ((Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h))).trans
      (Fin.succAboveOrderEmb j)).map_rel_iff
/-
**SSet.stdSimplex.finOrderIsoPairCompl_apply_val** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.stdSimplex`。
形式化陈述：finOrderIsoPairCompl_apply_val {n : Nat} (i j : Fin (n + 2)) (h : i < j) (
k : Fin n) : (finOrderIsoPairCompl i j h k).val = j.succAbove ((i.castPred (Fin.
ne_last_of_lt h)).succAbove k)
参数：i j : Fin (n + 2)；h : i < j；k : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finOrderIsoPairCompl_apply_val {n : ℕ} (i j : Fin (n + 2)) (h : i < j) (k : Fin n) :
    (finOrderIsoPairCompl i j h k).val =
      j.succAbove ((i.castPred (Fin.ne_last_of_lt h)).succAbove k) := rfl

/-- If `i < j` are in `Fin (n + 3)`, this is the isomorphism between `Δ[n]`
and the face of `Δ[n + 2]` corresponding to `{i, j}ᶜ`. -/
/-
**SSet.stdSimplex.facePairComplIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：facePairComplIso {n : Nat} (i j : Fin (n + 3)) (h : i < j) : Δ[n] ≅ (face 
{i, j}ᶜ : SSet.{u})
参数：i j : Fin (n + 3)；h : i < j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `i < j` are in `Fin (n + 3)`, this is the isomorphism between `Δ[n]`
and the face of `Δ[n + 2]` corresponding to `{i, j}ᶜ`.
-/
noncomputable def facePairComplIso {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    Δ[n] ≅ (face {i, j}ᶜ : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (finOrderIsoPairCompl i j h))

@[reassoc]
/-
**SSet.stdSimplex.facePairComplIso_hom_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimpl
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma facePairComplIso_hom_ι {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ stdSimplex.δ j :=
  rfl

@[reassoc]
/-
**SSet.stdSimplex.facePairComplIso_hom_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimpl
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma facePairComplIso_hom_ι' {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ stdSimplex.δ i := by
  rw [facePairComplIso_hom_ι]
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ, stdSimplex.δ_comp_δ (by grind)]

@[reassoc]
/-
**SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_** 是
 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred {n : ℕ}
    (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (by simp [face_le_face_iff]) ≫
      (faceSingletonComplIso.{u} i).inv =
    (facePairComplIso i j h).inv ≫ stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) := by
  simp [← cancel_mono (faceSingletonComplIso i).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι']

@[reassoc]
/-
**SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_** 是
 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred
    {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (by simp [face_le_face_iff]) ≫
      (faceSingletonComplIso.{u} j).inv =
    (facePairComplIso i j h).inv ≫ stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) := by
  simp [← cancel_mono (faceSingletonComplIso j).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι]

/-- Given `i : Fin (n + 1)`, this is the isomorphism from `Δ[0]` to the face
of `Δ[n]` corresponding to `{i}`. -/
/-
**SSet.stdSimplex.faceSingletonIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：faceSingletonIso {n : Nat} (i : Fin (n + 1)) : Δ[0] ≅ (face {i} : SSet.{u}
)
参数：i : Fin (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i : Fin (n + 1)`, this is the isomorphism from `Δ[0]` to the face
of `Δ[n]` corresponding to `{i}`.
-/
noncomputable def faceSingletonIso {n : ℕ} (i : Fin (n + 1)) :
    Δ[0] ≅ (face {i} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

@[reassoc]
/-
**SSet.stdSimplex.faceSingletonIso_zero_hom_comp_** 是 Mathlib 中的一个引理，位于命名空间 `SSe
t.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceSingletonIso_zero_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (0 : Fin 2)).hom ≫ (face {0}).ι = stdSimplex.δ 1 := by
  decide

@[reassoc]
/-
**SSet.stdSimplex.faceSingletonIso_one_hom_comp_** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma faceSingletonIso_one_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (1 : Fin 2)).hom ≫ (face {1}).ι = stdSimplex.δ 0 := by
  decide

/-- Given `i` and `j` in `Fin (n + 1)` such that `i < j`,
this is the isomorphism from `Δ[1]` to the face
of `Δ[n]` corresponding to `{i, j}`. -/
/-
**SSet.stdSimplex.facePairIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：facePairIso {n : Nat} (i j : Fin (n + 1)) (hij : i < j) : Δ[1] ≅ (face {i,
 j} : SSet.{u})
参数：i j : Fin (n + 1)；hij : i < j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `i` and `j` in `Fin (n + 1)` such that `i < j`,
this is the isomorphism from `Δ[1]` to the face
of `Δ[n]` corresponding to `{i, j}`.
-/
noncomputable def facePairIso {n : ℕ} (i j : Fin (n + 1)) (hij : i < j) :
    Δ[1] ≅ (face {i, j} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

set_option backward.defeqAttrib.useBackward true in
variable (n) in
/-
**SSet.stdSimplex.bijective_image_objEquiv_toOrderHom_univ** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma bijective_image_objEquiv_toOrderHom_univ (m : ℕ) :
    Function.Bijective (fun (⟨x, hx⟩ : (Δ[n] : SSet.{u}).nonDegenerate m) ↦
      (⟨Finset.image (objEquiv x).toOrderHom .univ, by
        dsimp
        rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective] at hx
        rw [Finset.card_image_of_injective _ (by exact hx), Finset.card_univ,
          Fintype.card_fin]⟩ : { S : Finset (Fin (n + 1)) | S.card = m + 1 })) := by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := objEquiv.symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := objEquiv.symm.surjective x₂
    simp only [mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply,
      SimplexCategory.mono_iff_injective, SimplexCategory.len_mk] at h₁ h₂
    simp only [Set.mem_ofPred_eq, SimplexCategory.len_mk, Equiv.apply_symm_apply,
      Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h₃ ⊢
    apply SimplexCategory.Hom.ext
    rw [← OrderHom.range_eq_iff h₁ h₂]
    ext x
    simpa using congr_fun (congrArg Membership.mem h₃) x
  · intro ⟨S, hS⟩
    dsimp at hS
    let e := monoEquivOfFin S (k := m + 1) (by simpa using hS)
    refine ⟨⟨objMk ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom), ?_⟩, ?_⟩
    · rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective]
      intro a b h
      grind [e.injective, dsimp% h]
    · simp [e, ← Finset.image_image, Finset.image_univ_of_surjective e.surjective]

/-- Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to subsets of `Fin (n + 1)` of cardinality `d + 1`. -/
/-
**SSet.stdSimplex.nonDegenerateEquiv'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex
`。
形式化陈述：nonDegenerateEquiv'_iff {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d
) (j : Fin (n + 1)) : j in (nonDegenerateEquiv' x).val ↔ exists (i : Fin (d + 1)
), x.val i = j
参数：x : (Δ[n] : SSet.{u}).nonDegenerate d；j : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex.0.SSet.stdSi
mplex.bijective_image_objEquiv_toOrderHom_univ`：∀ (n m : ℕ),   Function.Bijectiv
e fun x =>     match x with     | ⟨x, hx⟩ => ⟨Finset.image (⇑(SimplexCategory.Ho
m.toOrderHom (SSet.stdSimple…

--- 原说明 ---
Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to subsets of `Fin (n + 1)` of cardinality `d + 1`.
-/
@[no_expose] noncomputable def nonDegenerateEquiv' {n d : ℕ} :
    (Δ[n] : SSet.{u}).nonDegenerate d ≃ { S : Finset (Fin (n + 1)) | S.card = d + 1 } :=
  Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_univ n d)
/-
**SSet.stdSimplex.nonDegenerateEquiv'_iff** 是 Mathlib 中的一个定理，位于命名空间 `SSet.stdSim
plex`。
形式化陈述：∀ {n d : ℕ} (x : ↑((SSet.stdSimplex.obj { len := n }).nonDegenerate d)) (j
 : Fin (n + 1)),   j ∈ ↑(SSet.stdSimplex.nonDegenerateEquiv' x) ↔ ∃ i, ↑x i = j
参数：x : ↑((SSet.stdSimplex.obj { len := n }).nonDegenerate d)；j : Fin (n + 1)；SSe
t.stdSimplex.nonDegenerateEquiv' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.stdSimplex.nonDegenerateEquiv'`：nonDegenerateEquiv'_iff {n d : Nat}
 (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) : j in (nonDegenerate
Equiv' x).val ↔ exists (i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex.0.SSet.stdSi
mplex.bijective_image_objEquiv_toOrderHom_univ`：∀ (n m : ℕ),   Function.Bijectiv
e fun x =>     match x with     | ⟨x, hx⟩ => ⟨Finset.image (⇑(SimplexCategory.Ho
m.toOrderHom (SSet.stdSimple…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonDegenerateEquiv'_iff {n d : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) :
    j ∈ (nonDegenerateEquiv' x).val ↔ ∃ (i : Fin (d + 1)), x.val i = j := by
  unfold nonDegenerateEquiv'
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `x` is a nondegenerate `d`-simplex of `Δ[n]`, this is the order isomorphism
between `Fin (d + 1)` and the corresponding subset of `Fin (n + 1)` of cardinality `d + 1`. -/
/-
**SSet.stdSimplex.orderIsoOfNonDegenerate** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSim
plex`。
形式化陈述：{n d : ℕ} →   (x : ↑((SSet.stdSimplex.obj { len := n }).nonDegenerate d)) 
→ Fin (d + 1) ≃o ↥↑(SSet.stdSimplex.nonDegenerateEquiv' x)
参数：x : ↑((SSet.stdSimplex.obj { len := n }).nonDegenerate d)；d + 1；SSet.stdSimpl
ex.nonDegenerateEquiv' x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.stdSimplex.nonDegenerateEquiv'`：nonDegenerateEquiv'_iff {n d : Nat}
 (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) : j in (nonDegenerate
Equiv' x).val ↔ exists (i…

--- 原说明 ---
If `x` is a nondegenerate `d`-simplex of `Δ[n]`, this is the order isomorphism
between `Fin (d + 1)` and the corresponding subset of `Fin (n + 1)` of cardinali
ty `d + 1`.
-/
@[no_expose] noncomputable def orderIsoOfNonDegenerate
    {n d : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    Fin (d + 1) ≃o nonDegenerateEquiv' x where
  toEquiv := Equiv.ofBijective (fun i ↦ ⟨x.val i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_nonDegenerate_iff_mono x.val).1 x.property
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h ↦ this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegenerateEquiv'_iff] at hj
      aesop)
  map_rel_iff' := by
    have := (mem_nonDegenerate_iff_mono x.val).1 x.property
    rw [SimplexCategory.mono_iff_injective] at this
    intro a b
    dsimp
    simp only [Subtype.mk_le_mk]
    constructor
    · rw [← not_lt, ← not_lt]
      intro h h'
      apply h
      obtain h'' | h'' := (monotone_apply x.val h'.le).lt_or_eq
      · assumption
      · simp only [this h'', lt_self_iff_false] at h'
    · intro h
      exact monotone_apply _ h
/-
**SSet.stdSimplex.face_nonDegenerateEquiv'** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSi
mplex`。
形式化陈述：face_nonDegenerateEquiv' {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate 
d) : face (nonDegenerateEquiv' x) = Subcomplex.ofSimplex x.val
参数：x : (Δ[n] : SSet.{u}).nonDegenerate d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.stdSimplex.face_eq_ofSimplex`：face_eq_ofSimplex {n : Nat} (S : Fins
et (Fin (n + 1))) (m : Nat) (e : Fin (m + 1) ≃o S) : face.{u} S = Subcomplex.ofS
implex (X
· 使用引理 `SSet.stdSimplex.nonDegenerateEquiv'`：nonDegenerateEquiv'_iff {n d : Nat}
 (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) : j in (nonDegenerate
Equiv' x).val ↔ exists (i…
-/
lemma face_nonDegenerateEquiv' {n d : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    face (nonDegenerateEquiv' x) = Subcomplex.ofSimplex x.val :=
  face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**SSet.stdSimplex.nonDegenerateEquiv'_symm_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `
SSet.stdSimplex`。
形式化陈述：∀ {n d : ℕ} (S : ↑{S | S.card = d + 1}) (i : Fin (d + 1)), ↑(SSet.stdSimpl
ex.nonDegenerateEquiv'.symm S) i ∈ ↑S
参数：S : ↑{S | S.card = d + 1}；i : Fin (d + 1)；SSet.stdSimplex.nonDegenerateEquiv'
.symm S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.stdSimplex.nonDegenerateEquiv'`：nonDegenerateEquiv'_iff {n d : Nat}
 (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) : j in (nonDegenerate
Equiv' x).val ↔ exists (i…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `_private.Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex.0.SSet.stdSi
mplex.bijective_image_objEquiv_toOrderHom_univ`：∀ (n m : ℕ),   Function.Bijectiv
e fun x =>     match x with     | ⟨x, hx⟩ => ⟨Finset.image (⇑(SimplexCategory.Ho
m.toOrderHom (SSet.stdSimple…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Equiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply (f : α 
-> β) (hf : Bijective f) (x : α) : (ofBijective f hf).symm (f x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma nonDegenerateEquiv'_symm_apply_mem {n d : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = d + 1 }) (i : Fin (d + 1)) :
      (nonDegenerateEquiv'.{u}.symm S).val i ∈ S.val := by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  dsimp [nonDegenerateEquiv']
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩
/-
**SSet.stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le** 是 Mathlib 中的一个定理，位于
命名空间 `SSet.stdSimplex`。
形式化陈述：∀ {n d : ℕ} (S : ↑{S | S.card = d + 1}) (A : (SSet.stdSimplex.obj { len :=
 n }).Subcomplex),   ↑(SSet.stdSimplex.nonDegenerateEquiv'.symm S) ∈ A.obj (Oppo
site.op { len := d }) ↔ SSet.stdSimplex.face ↑S ≤ A
参数：S : ↑{S | S.card = d + 1}；A : (SSet.stdSimplex.obj { len := n }).Subcomplex；S
Set.stdSimplex.nonDegenerateEquiv'.symm S；Opposite.op { len := d }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.stdSimplex.nonDegenerateEquiv'`：nonDegenerateEquiv'_iff {n d : Nat}
 (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) : j in (nonDegenerate
Equiv' x).val ↔ exists (i…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.face_nonDegenerateEquiv'`：face_nonDegenerateEquiv' {n d 
: Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d) : face (nonDegenerateEquiv' x) = 
Subcomplex.ofSimplex x.val
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `SSet.Subcomplex.ofSimplex_le_iff`：ofSimplex_le_iff {n : Nat} (x : X _⦋n⦌
) (A : X.Subcomplex) : ofSimplex x <= A ↔ x in A.obj _
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonDegenerateEquiv'_symm_mem_iff_face_le {n d : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = d + 1 })
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (nonDegenerateEquiv'.symm S).val ∈ A.obj _ ↔ face S ≤ A := by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  rw [face_nonDegenerateEquiv' x, Equiv.symm_apply_apply, Subcomplex.ofSimplex_le_iff]
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) (d : SimplexCategoryᵒᵖ) :
    Finite ((stdSimplex.{u}.obj n).obj d) := by
  rw [objEquiv.finite_iff]
  infer_instance
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Finite := by
  induction n using SimplexCategory.rec with | _ n
  exact finite_of_hasDimensionLT _ (n + 1) inferInstance
/-
**SSet.stdSimplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.stdSimplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    SSet.Finite (Subcomplex.ofSimplex x) := by
  obtain ⟨f, rfl⟩ := yonedaEquiv.surjective x
  rw [← Subcomplex.range_eq_ofSimplex]
  infer_instance
/-
**SSet.stdSimplex.hasDimensionLT_face** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex
`。
形式化陈述：hasDimensionLT_face {n : Nat} (S : Finset (Fin (n + 1))) (d : Nat) (hd : S
.card <= d) : HasDimensionLT (face.{u} S) d
参数：S : Finset (Fin (n + 1))；d : Nat；hd : S.card <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.face_empty`：face_empty (n : Nat) : face.{u} (∅ : Finset 
(Fin (n + 1))) = ⊥
· 使用定理 `SSet.instHasDimensionLTToSSetBotSubcomplex`：∀ {X : _root_.SSet} (n : ℕ),
 ⊥.toSSet.HasDimensionLT n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用引理 `SSet.hasDimensionLT_iff_of_iso`：hasDimensionLT_iff_of_iso {X Y : SSet.{u
}} (e : X ≅ Y) (d : Nat) : X.HasDimensionLT d ↔ Y.HasDimensionLT d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用引理 `SSet.hasDimensionLT_of_le`：hasDimensionLT_of_le (hn : d <= n
· 使用定理 `SSet.stdSimplex.instHasDimensionLEObjSimplexCategoryMk`：∀ (n : ℕ), (SSet
.stdSimplex.obj { len := n }).HasDimensionLE n
-/
lemma hasDimensionLT_face {n : ℕ} (S : Finset (Fin (n + 1)))
    (d : ℕ) (hd : S.card ≤ d) :
    HasDimensionLT (face.{u} S) d := by
  generalize hm : S.card = m
  obtain _ | m := m
  · obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
    rw [face_empty]
    infer_instance
  · rw [← hasDimensionLT_iff_of_iso
      (isoOfRepresentableBy (faceRepresentableBy S m (monoEquivOfFin S (by simpa))))]
    exact hasDimensionLT_of_le _ (m + 1) _
/-
**SSet.stdSimplex.ofSimplex_objEquiv_symm_id** 是 Mathlib 中的一个引理，位于命名空间 `SSet.std
Simplex`。
形式化陈述：ofSimplex_objEquiv_symm_id (n : Nat) : Subcomplex.ofSimplex (objEquiv.{u}.
symm (𝟙 ⦋n⦌)) = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.map_objEquiv_symm`：map_objEquiv_symm {n : SimplexCategor
y} {m m' : SimplexCategoryᵒᵖ} (f : m.unop ⟶ n) (g : m ⟶ m') : (stdSimplex.{u}.ob
j n).map g (objEquiv.sy…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofSimplex_objEquiv_symm_id (n : ℕ) :
    Subcomplex.ofSimplex (objEquiv.{u}.symm (𝟙 ⦋n⦌)) = ⊤ :=
  le_antisymm (by simp) (fun _ x _ ↦ by
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    simp only [Subcomplex.mem_ofSimplex_obj_iff, op_unop]
    exact ⟨f, by simp [map_objEquiv_symm.{u}]⟩)
/-
**SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.stdSimplex`。
形式化陈述：objEquiv_symm_id_mem_nonDegenerate (n : Nat) : (objEquiv (m
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.stdSimplex.mem_nonDegenerate_iff_strictMono`：mem_nonDegenerate_iff_
strictMono {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) : s in Δ[n].nonDegenerate d 
↔ StrictMono s
-/
lemma objEquiv_symm_id_mem_nonDegenerate (n : ℕ) :
    (objEquiv (m := (op ⦋n⦌))).symm (𝟙 _) ∈ (Δ[n] : SSet.{u}).nonDegenerate n := by
  rw [mem_nonDegenerate_iff_strictMono]
  exact fun _ _ h ↦ h
/-
**SSet.stdSimplex.nonDegenerate_top_dim** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimpl
ex`。
形式化陈述：nonDegenerate_top_dim (n : Nat) : (Δ[n] : SSet.{u}).nonDegenerate n = {(ob
jEquiv (m
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SSet.stdSimplex.mem_nonDegenerate_iff_mono`：mem_nonDegenerate_iff_mono {
n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) : s in Δ[n].nonDegenerate d ↔ Mono (objE
quiv s)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `SimplexCategory.eq_id_of_mono`：eq_id_of_mono {x : SimplexCategory} (i : 
x ⟶ x) [Mono i] : i = 𝟙 _
· 使用引理 `SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate`：objEquiv_symm_id_mem
_nonDegenerate (n : Nat) : (objEquiv (m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma nonDegenerate_top_dim (n : ℕ) :
    (Δ[n] : SSet.{u}).nonDegenerate n = {(objEquiv (m := (op ⦋n⦌))).symm (𝟙 _)} := by
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    have : Mono f := by simpa using (mem_nonDegenerate_iff_mono _).mp h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using SimplexCategory.eq_id_of_mono f
  · rintro rfl
    apply objEquiv_symm_id_mem_nonDegenerate
/-
**SSet.stdSimplex.not_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimplex`
。
形式化陈述：not_hasDimensionLT (n : Nat) (_ : HasDimensionLT.{u} Δ[n] n
参数：n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用引理 `SSet.dim_lt_of_nonDegenerate`：dim_lt_of_nonDegenerate {n : Nat} (x : X.n
onDegenerate n) (d : Nat) [X.HasDimensionLT d] : n < d
-/
lemma not_hasDimensionLT (n : ℕ) (_ : HasDimensionLT.{u} Δ[n] n := by infer_instance) :
    False :=
  (lt_self_iff_false n).1 (Δ[n].dim_lt_of_nonDegenerate
    (nonDegenerateEquiv.2 (.refl _)) n)

/-- The bijection `(stdSimplex.obj n).op.obj d ≃ (stdSimplex.obj n).obj d` for any
`n : ℕ` and `d : ℕ`. See also `stdSimplex.opIso`. -/
/-
**SSet.stdSimplex.opObjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：{n : SimplexCategory} → {d : SimplexCategoryᵒᵖ} → (SSet.stdSimplex.obj n).
op.obj d ≃ (SSet.stdSimplex.obj n).obj d
参数：SSet.stdSimplex.obj n；SSet.stdSimplex.obj n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The bijection `(stdSimplex.obj n).op.obj d ≃ (stdSimplex.obj n).obj d` for any
`n : ℕ` and `d : ℕ`. See also `stdSimplex.opIso`.
-/
protected def opObjEquiv {n : SimplexCategory} {d : SimplexCategoryᵒᵖ} :
    (stdSimplex.{u}.obj n).op.obj d ≃ (stdSimplex.obj n).obj d :=
  SSet.opObjEquiv.trans (objEquiv.trans
    (SimplexCategory.revEquivalence.fullyFaithfulFunctor.homEquiv.trans objEquiv.symm))
/-
**SSet.stdSimplex.opObjEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `SSet.stdSimplex`。
形式化陈述：∀ {d n : ℕ} (f : (SSet.stdSimplex.obj { len := n }).op.obj (Opposite.op { 
len := d })) (i : Fin (d + 1)),   (SSet.stdSimplex.opObjEquiv f) i = ((SSet.opOb
jEquiv f) i.rev).rev
参数：f : (SSet.stdSimplex.obj { len := n }).op.obj (Opposite.op { len := d })；i : 
Fin (d + 1)；SSet.stdSimplex.opObjEquiv f；(SSet.opObjEquiv f) i.rev。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma opObjEquiv_apply {d n : ℕ} (f : Δ[n].op _⦋d⦌) (i : Fin (d + 1)) :
    stdSimplex.opObjEquiv.{u} f i = (opObjEquiv f i.rev).rev := rfl
/-
**SSet.stdSimplex.opObjEquiv_opObjEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `SS
et.stdSimplex`。
形式化陈述：opObjEquiv_opObjEquiv_symm_apply {d n : Nat} (f : (Δ[n] _⦋d⦌)) (i : Fin (d
 + 1)) : SSet.opObjEquiv (stdSimplex.opObjEquiv.{u}.symm f) i = (f i.rev).rev
参数：f : (Δ[n] _⦋d⦌)；i : Fin (d + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma opObjEquiv_opObjEquiv_symm_apply {d n : ℕ} (f : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) :
    SSet.opObjEquiv (stdSimplex.opObjEquiv.{u}.symm f) i = (f i.rev).rev :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-
**SSet.stdSimplex.map_rev_map_op_apply** 是 Mathlib 中的一个引理，位于命名空间 `SSet.stdSimple
x`。
形式化陈述：map_rev_map_op_apply {n d d' : Nat} (f : ⦋d⦌ ⟶ ⦋d'⦌) (g : Δ[n] _⦋d'⦌) (i :
 Fin (d + 1)) : dsimp% (show Δ[n] _⦋d⦌ from (Δ[n] : SSet.{u}).map (rev.map f).op
 g : Δ[n] _⦋d⦌) i = g (f i.rev).rev
参数：f : ⦋d⦌ ⟶ ⦋d'⦌；g : Δ[n] _⦋d'⦌；i : Fin (d + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_rev_map_op_apply {n d d' : ℕ} (f : ⦋d⦌ ⟶ ⦋d'⦌) (g : Δ[n] _⦋d'⦌) (i : Fin (d + 1)) :
    dsimp% (show Δ[n] _⦋d⦌ from (Δ[n] : SSet.{u}).map (rev.map f).op g : Δ[n] _⦋d⦌) i =
      g (f i.rev).rev := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The opposite of `Δ[n]` is isomorphic to `Δ[n]`. -/
@[simps! hom_app_hom_apply inv_app_hom_apply]
/-
**SSet.stdSimplex.opIso** 是 Mathlib 中的一个定义，位于命名空间 `SSet.stdSimplex`。
形式化陈述：opIso (n : SimplexCategory) : (stdSimplex.{u}.obj n).op ≅ stdSimplex.obj n
参数：n : SimplexCategory。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of `Δ[n]` is isomorphic to `Δ[n]`.
-/
def opIso (n : SimplexCategory) :
    (stdSimplex.{u}.obj n).op ≅ stdSimplex.obj n :=
  NatIso.ofComponents (fun d ↦ stdSimplex.opObjEquiv.toIso) (fun {d d'} f ↦ by
    ext g
    refine stdSimplex.ext _ _ (fun i ↦ ?_)
    dsimp
    rw [stdSimplex.opObjEquiv_apply, op_map]
    erw [Equiv.apply_symm_apply]
    dsimp
    rw [map_rev_map_op_apply]
    aesop)

end stdSimplex

section Examples

open Simplicial

/-- The simplicial circle. -/
/-
**SSet.S1** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：S1 : SSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial circle.
-/
noncomputable def S1 : SSet :=
  Limits.colimit <|
    Limits.parallelPair (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) (stdSimplex.δ 1)

end Examples

namespace Augmented

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor which sends `⦋n⦌` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets. -/
@[simps]
/-
**SSet.Augmented.stdSimplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Augmented`。
形式化陈述：stdSimplex : SimplexCategory ⥤ SSet.Augmented.{u} where obj Δ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends `⦋n⦌` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets.
-/
noncomputable def stdSimplex : SimplexCategory ⥤ SSet.Augmented.{u} where
  obj Δ :=
    { left := SSet.stdSimplex.obj Δ
      right := terminal _
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.stdSimplex.map θ
      right := terminal.from _ }

end Augmented

namespace Subcomplex

variable {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)

/-- Given `x : X _⦋n⦌`, this is the epimorphism from `Δ[n]`
to the subcomplex of `X` generated by `x`. -/
/-
**SSet.Subcomplex.toOfSimplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：toOfSimplex : Δ[n] ⟶ ofSimplex x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `x : X _⦋n⦌`, this is the epimorphism from `Δ[n]`
to the subcomplex of `X` generated by `x`.
-/
def toOfSimplex : Δ[n] ⟶ ofSimplex x :=
  Subcomplex.lift (yonedaEquiv.symm x) (by simp [range_eq_ofSimplex])

@[reassoc (attr := simp)]
/-
**SSet.Subcomplex.toOfSimplex_** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toOfSimplex_ι :
    toOfSimplex x ≫ (ofSimplex x).ι = yonedaEquiv.symm x := rfl

@[simp]
/-
**SSet.Subcomplex.yonedaEquiv_toOfSimplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcom
plex`。
形式化陈述：yonedaEquiv_toOfSimplex : yonedaEquiv (toOfSimplex x) = ⟨x, mem_ofSimplex_
obj x⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `SSet.Subcomplex.mem_ofSimplex_obj`：mem_ofSimplex_obj {n : Nat} (x : X _⦋
n⦌) : x in (ofSimplex x).obj _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma yonedaEquiv_toOfSimplex :
    yonedaEquiv (toOfSimplex x) = ⟨x, mem_ofSimplex_obj x⟩ :=
  yonedaEquiv.symm.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (toOfSimplex x) := by
  rw [← range_eq_top_iff]
  ext m ⟨_, u, rfl⟩
  simp only [range_eq_ofSimplex, yonedaEquiv_toOfSimplex, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  refine ⟨u, ?_⟩
  dsimp
  ext
  rw [← yonedaEquiv.right_inv x]
  aesop
/-
**SSet.Subcomplex.isIso_toOfSimplex_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcompl
ex`。
形式化陈述：isIso_toOfSimplex_iff : IsIso (toOfSimplex x) ↔ Mono (yonedaEquiv.symm x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.toOfSimplex_ι`：toOfSimplex_ι : toOfSimplex x ≫ (ofSimple
x x).ι = yonedaEquiv.symm x
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
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
· 使用定理 `SSet.Subcomplex.instMonoι`：∀ {X : _root_.SSet} (A : X.Subcomplex), Categ
oryTheory.Mono A.ι
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `SSet.instBalanced`：CategoryTheory.Balanced _root_.SSet
· 使用定理 `SSet.Subcomplex.instEpiToOfSimplex`：∀ {X : _root_.SSet} {n : ℕ} (x : X.o
bj (Opposite.op { len := n })), CategoryTheory.Epi (SSet.Subcomplex.toOfSimplex 
x)
-/
lemma isIso_toOfSimplex_iff :
    IsIso (toOfSimplex x) ↔ Mono (yonedaEquiv.symm x) := by
  constructor
  · intro
    rw [← toOfSimplex_ι]
    infer_instance
  · intro h
    have := mono_of_mono_fac (toOfSimplex_ι x)
    apply isIso_of_mono_of_epi

end Subcomplex

end SSet

