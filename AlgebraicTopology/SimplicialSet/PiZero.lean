/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Connected components of simplicial sets

In this file, we define the type `π₀ X` of connected components
of a simplicial sets. We also introduce typeclasses
`IsPreconnected X` and `IsConnected X`.

## TODO

* Define the subcomplex of `X` corresponding to an element in `π₀ X` (@joelriou)
* Show `π₀ X` is a coequalizer of the two face maps `X _⦋1⦌ → X _⦋0⦌` (@joelriou)
* Show `π₀ X` identifies to the colimit of `X` as a functor to types

## References:

- [Kerodon 00G5: Connected Components of Simplicial Sets](https://kerodon.net/tag/00G5)

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits Opposite TypeCat

namespace SSet

variable {X Y Z : SSet.{u}}

/-- The homotopy relation on `0`-simplices of a simplicial set. It holds
for `x₀` and `x₁` when there exists an edge from `x₀` to `x₁`. -/
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy relation on `0`-simplices of a simplicial set. It holds
for `x₀` and `x₁` when there exists an edge from `x₀` to `x₁`.
-/
def π₀Rel (x₀ x₁ : X _⦋0⦌) : Prop :=
  Nonempty (Edge x₀ x₁)

variable (X) in
/-- The type of connected components of a simplicial set. -/
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of connected components of a simplicial set.
-/
def π₀ : Type u := Quot (π₀Rel (X := X))

attribute [irreducible] π₀

namespace π₀

unseal π₀ in
/-- The connected component of a `0`-simplex of a simplicial set. -/
/-
**SSet.π₀.mk** 是 Mathlib 中的一个定义，位于命名空间 `SSet.π₀`。
形式化陈述：mk : X _⦋0⦌ -> π₀ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connected component of a `0`-simplex of a simplicial set.
-/
def mk : X _⦋0⦌ → π₀ X := Quot.mk _

unseal π₀ in
/-
**SSet.π₀.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SSet.π₀`。
形式化陈述：mk_surjective : Function.Surjective (π₀.mk (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
lemma mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

unseal π₀ in
/-
**SSet.π₀.sound** 是 Mathlib 中的一个引理，位于命名空间 `SSet.π₀`。
形式化陈述：sound {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) : π₀.mk x₀ = π₀.mk x₁
参数：e : Edge x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sound {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    π₀.mk x₀ = π₀.mk x₁ :=
  Quot.sound ⟨e⟩

unseal π₀ in
/-
**SSet.π₀.mk_eq_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet.π₀`。
形式化陈述：mk_eq_mk_iff (x₀ x₁ : X _⦋0⦌) : π₀.mk x₀ = π₀.mk x₁ ↔ Relation.EqvGen π₀Re
l x₀ x₁
参数：x₀ x₁ : X _⦋0⦌。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
-/
lemma mk_eq_mk_iff (x₀ x₁ : X _⦋0⦌) :
    π₀.mk x₀ = π₀.mk x₁ ↔ Relation.EqvGen π₀Rel x₀ x₁ :=
  Quot.eq

@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**SSet.π₀.rec** 是 Mathlib 中的一个引理，位于命名空间 `SSet.π₀`。
形式化陈述：rec {motive : π₀ X -> Prop} (mk : forall (x : X _⦋0⦌), motive (.mk x)) (x 
: π₀ X) : motive x
参数：mk : forall (x : X _⦋0⦌), motive (.mk x)；x : π₀ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.π₀.mk_surjective`：mk_surjective : Function.Surjective (π₀.mk (X
-/
lemma rec {motive : π₀ X → Prop} (mk : ∀ (x : X _⦋0⦌), motive (.mk x)) (x : π₀ X) :
    motive x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact mk x

unseal π₀ in
/-- Constructor for maps from the type of connected components of a simplicial set. -/
/-
**SSet.π₀.lift** 是 Mathlib 中的一个定义，位于命名空间 `SSet.π₀`。
形式化陈述：lift {T : Type*} (f : X _⦋0⦌ -> T) (hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Ed
ge x₀ x₁), f x₀ = f x₁) : π₀ X -> T
参数：f : X _⦋0⦌ -> T；hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for maps from the type of connected components of a simplicial set.
-/
def lift {T : Type*} (f : X _⦋0⦌ → T) (hf : ∀ ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁) :
    π₀ X → T :=
  Quot.lift f (by rintro x y ⟨e⟩; exact hf e)

@[simp]
/-
**SSet.π₀.lift_mk** 是 Mathlib 中的一个引理，位于命名空间 `SSet.π₀`。
形式化陈述：lift_mk {T : Type*} (f : X _⦋0⦌ -> T) (hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X
.Edge x₀ x₁), f x₀ = f x₁) (x : X _⦋0⦌) : lift f hf (.mk x) = f x
参数：f : X _⦋0⦌ -> T；hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁；
x : X _⦋0⦌。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_mk {T : Type*} (f : X _⦋0⦌ → T)
    (hf : ∀ ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁) (x : X _⦋0⦌) :
    lift f hf (.mk x) = f x :=
  rfl

end π₀

/-- The map `π₀ X → π₀ Y` induced by a morphism `X ⟶ Y` of simplicial sets. -/
/-
**SSet.map** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `π₀ X → π₀ Y` induced by a morphism `X ⟶ Y` of simplicial sets.
-/
def mapπ₀ (f : X ⟶ Y) : π₀ X → π₀ Y :=
  π₀.lift (π₀.mk ∘ f.app _) (fun _ _ e ↦ π₀.sound (e.map f))

@[simp]
/-
**SSet.map** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapπ₀_mk (f : X ⟶ Y) (x₀ : X _⦋0⦌) :
    mapπ₀ f (π₀.mk x₀) = π₀.mk (f.app _ x₀) :=
  rfl

@[simp]
/-
**SSet.map** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapπ₀_id_apply (x : π₀ X) : mapπ₀ (𝟙 X) x = x := by
  induction x
  simp

@[simp]
/-
**SSet.map** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X) :
    mapπ₀ (f ≫ g) x = mapπ₀ g (mapπ₀ f x) := by
  induction x
  simp

/-- The functor which sends a simplicial set to the type of its connected components. -/
@[simps]
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends a simplicial set to the type of its connected components
.
-/
def π₀Functor : SSet.{u} ⥤ Type u where
  obj X := π₀ X
  map f := ↾(mapπ₀ f)

/-- The map `π₀.mk : X _⦋0⦌ ⟶ π₀ X` for all simplicial sets `X`,
as a natural transformation. -/
/-
**SSet.to** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `π₀.mk : X _⦋0⦌ ⟶ π₀ X` for all simplicial sets `X`,
as a natural transformation.
-/
def toπ₀NatTrans : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor.{u} where
  app X := ↾π₀.mk

/-- The (colimit) cofork expressing `π₀ X` as a coequalizer
of `X.δ 0 : X _⦋1⦌ → X _⦋0⦌` and `X.δ 1`. -/
/-
**SSet.cofork** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (colimit) cofork expressing `π₀ X` as a coequalizer
of `X.δ 0 : X _⦋1⦌ → X _⦋0⦌` and `X.δ 1`.
-/
abbrev coforkπ₀ : Cofork (X.δ (1 : Fin 2)) (X.δ 0) :=
  Cofork.ofπ (↾π₀.mk) (by ext s; exact π₀.sound (Edge.mk' s))

/-- If `X` is a simplicial set, `£₀ X` is a coequalizer
of `X.δ 0 : X _⦋1⦌ → X _⦋0⦌` and `X.δ 1`. -/
/-
**SSet.isColimitCofork** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a simplicial set, `£₀ X` is a coequalizer
of `X.δ 0 : X _⦋1⦌ → X _⦋0⦌` and `X.δ 1`.
-/
def isColimitCoforkπ₀ : IsColimit X.coforkπ₀ :=
  Cofork.IsColimit.mk _
    (fun s ↦ ↾π₀.lift s.π (fun x₀ x₁ e ↦ by
      simpa only [← e.src_eq, ← e.tgt_eq] using!
        ConcreteCategory.congr_hom s.condition e.edge))
    (fun s ↦ rfl)
    (fun s m hm ↦ by
      ext (x : π₀ X)
      induction x
      exact ConcreteCategory.congr_hom hm _)

/-- The colimit cofork exhibiting the natural transformation
`toπ₀NatTrans : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor`
as a coequalizer of the two face maps, considered as
natural transformations of functors `SSet.{u} ⥤ Type u`. -/
/-
**SSet.cofork** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cofork exhibiting the natural transformation
`toπ₀NatTrans : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor`
as a coequalizer of the two face maps, considered as
natural transformations of functors `SSet.{u} ⥤ Type u`.
-/
abbrev coforkπ₀Functor :
    Cofork (SSet.evaluation.{u}.map (SimplexCategory.δ (1 : Fin 2)).op)
      (SSet.evaluation.map (SimplexCategory.δ (0 : Fin 2)).op) :=
  Cofork.ofπ toπ₀NatTrans (by ext X s; exact π₀.sound (Edge.mk' s))

/-- The functor `π₀Functor : SSet.{u} ⥤ Type u` is the coequalizer
of the two face maps `δ (0 : Fin 2)` and `δ 1`, considered
as natural transformations. -/
/-
**SSet.isColimitCofork** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `π₀Functor : SSet.{u} ⥤ Type u` is the coequalizer
of the two face maps `δ (0 : Fin 2)` and `δ 1`, considered
as natural transformations.
-/
def isColimitCoforkπ₀Functor : IsColimit coforkπ₀Functor.{u} :=
  evaluationJointlyReflectsColimits _ (fun X ↦
    (isColimitMapCoconeCoforkEquiv _ _).2 X.isColimitCoforkπ₀)

variable (X)

@[simp]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π₀.nonempty_iff : Nonempty (π₀ X) ↔ X.Nonempty :=
  ⟨fun _ ↦ ⟨(π₀.mk_surjective (Classical.arbitrary (π₀ X))).choose⟩,
    fun _ ↦ ⟨.mk (Classical.arbitrary _)⟩⟩

/-- A simplicial set is preconnected when it has at most one connected component. -/
/-
**SSet.IsPreconnected** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set is preconnected when it has at most one connected component.
-/
protected abbrev IsPreconnected : Prop := Subsingleton (π₀ X)

/-- A simplicial set is econnected when it has exactly one connected component. -/
/-
**SSet.IsConnected** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set is econnected when it has exactly one connected component.
-/
protected class IsConnected : Prop extends SSet.IsPreconnected X where
  nonempty : X.Nonempty := by infer_instance

attribute [instance] IsConnected.nonempty
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.IsConnected] : Nonempty (π₀ X) := ⟨π₀.mk (Classical.arbitrary _)⟩
/-
**SSet.isConnected_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：isConnected_iff : X.IsConnected ↔ X.IsPreconnected ∧ X.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.IsConnected.toSubsingleton`：∀ {X : _root_.SSet} [self : X.IsConnect
ed], Subsingleton X.π₀
· 使用定理 `SSet.IsConnected.nonempty`：∀ {X : _root_.SSet} [self : X.IsConnected], X
.Nonempty
-/
lemma isConnected_iff :
    X.IsConnected ↔ X.IsPreconnected ∧ X.Nonempty :=
  ⟨fun h ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨by assumption⟩⟩
/-
**SSet.isConnected_iff_nonempty_unique** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：isConnected_iff_nonempty_unique : X.IsConnected ↔ Nonempty (Unique (π₀ X))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.isConnected_iff`：isConnected_iff : X.IsConnected ↔ X.IsPreconnected
 ∧ X.Nonempty
· 使用定理 `unique_iff_subsingleton_and_nonempty`：unique_iff_subsingleton_and_nonemp
ty (α : Sort u) : Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α
· 使用定理 `SSet.π₀.nonempty_iff`：∀ (X : _root_.SSet), Nonempty X.π₀ ↔ X.Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isConnected_iff_nonempty_unique :
    X.IsConnected ↔ Nonempty (Unique (π₀ X)) := by
  rw [isConnected_iff, unique_iff_subsingleton_and_nonempty, π₀.nonempty_iff]

end SSet

