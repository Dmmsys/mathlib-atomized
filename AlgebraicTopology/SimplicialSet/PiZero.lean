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

/--
Definition of `π₀Rel` / `π₀Rel` 的定义

English:
definition π₀Rel
  signature: (x₀ x₁ : X _⦋0⦌)
  body: Nonempty (Edge x₀ x₁)

中文:
定义 π₀Rel
  签名: (x₀ x₁ : X _⦋0⦌)
  定义体: Nonempty (Edge x₀ x₁)

Depends on / 依赖: Nonempty
-/
def π₀Rel (x₀ x₁ : X _⦋0⦌) : Prop :=
  Nonempty (Edge x₀ x₁)

variable (X) in
/--
Definition of `π₀` / `π₀` 的定义

English:
definition π₀
  signature: : Type u
  body: Quot (π₀Rel (X := X))

中文:
定义 π₀
  签名: : 类型u
  定义体: Quot (π₀Rel (X := X))
-/
def π₀ : Type u := Quot (π₀Rel (X := X))

attribute [irreducible] π₀

namespace π₀

unseal π₀ in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : X _⦋0⦌ -> π₀ X
  body: Quot.mk _

unseal π₀ in

中文:
定义 mk
  签名: : X _⦋0⦌ -> π₀ X
  定义体: Quot.mk _

unseal π₀ in

Depends on / 依赖: Quot.mk
-/
def mk : X _⦋0⦌ -> π₀ X := Quot.mk _

unseal π₀ in
/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  statement: Function.Surjective (π₀.mk (X := X))
  proof: Quot.mk_surjective

unseal π₀ in

中文:
引理 mk_surjective
  结论: 函数.满射 (π₀.mk (X := X))
  证明: Quot.mk_surjective

unseal π₀ in

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
lemma mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

unseal π₀ in
/--
lemma `sound` / 引理 `sound`

English:
lemma sound
  given: {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁)
  proof: Quot.sound ⟨e⟩

unseal π₀ in

中文:
引理 sound
  条件: {x₀ x₁ : X _⦋0⦌} (e : 边 x₀ x₁)
  证明: Quot.sound ⟨e⟩

unseal π₀ in

Depends on / 依赖: Quot.sound
-/
lemma sound {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁) :
    π₀.mk x₀ = π₀.mk x₁ :=
  Quot.sound ⟨e⟩

unseal π₀ in
/--
lemma `mk_eq_mk_iff` / 引理 `mk_eq_mk_iff`

English:
lemma mk_eq_mk_iff
  given: (x₀ x₁ : X _⦋0⦌)
  proof: Quot.eq

@[elab_as_elim, cases_eliminator, induction_eliminator]

中文:
引理 mk_eq_mk_iff
  条件: (x₀ x₁ : X _⦋0⦌)
  证明: Quot.eq

@[elab_as_elim, cases_eliminator, induction_eliminator]

Depends on / 依赖: Quot.eq
-/
lemma mk_eq_mk_iff (x₀ x₁ : X _⦋0⦌) :
    π₀.mk x₀ = π₀.mk x₁ ↔ Relation.EqvGen π₀Rel x₀ x₁ :=
  Quot.eq

@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
lemma `rec` / 引理 `rec`

English:
lemma rec
  given: {motive : π₀ X -> Prop} (mk : forall (x : X _⦋0⦌), motive (.mk x)) (x : π₀ X)
  proof: by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact mk x

unseal π₀ in

中文:
引理 rec
  条件: {motive : π₀ X -> 命题} (mk : 对任意 (x : X _⦋0⦌), motive (.mk x)) (x : π₀ X)
  证明: by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact mk x

unseal π₀ in

Depends on / 依赖: mk_surjective, x.mk_surjective
-/
lemma rec {motive : π₀ X -> Prop} (mk : forall (x : X _⦋0⦌), motive (.mk x)) (x : π₀ X) :
    motive x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact mk x

unseal π₀ in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {T : Type*} (f : X _⦋0⦌ -> T) (hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁)
  body: Quot.lift f (by rintro x y ⟨e⟩; exact hf e)

@[simp]

中文:
定义 lift
  签名: {T : 类型} (f : X _⦋0⦌ -> T) (hf : 对任意 ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.边 x₀ x₁), f x₀ = f x₁)
  定义体: Quot.lift f (by rintro x y ⟨e⟩; exact hf e)

@[simp]

Depends on / 依赖: Quot.lift
-/
def lift {T : Type*} (f : X _⦋0⦌ -> T) (hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁) :
    π₀ X -> T :=
  Quot.lift f (by rintro x y ⟨e⟩; exact hf e)

@[simp]
/--
lemma `lift_mk` / 引理 `lift_mk`

English:
lemma lift_mk
  statement: {T : Type*} (f : X _⦋0⦌ -> T)
  proof: rfl

中文:
引理 lift_mk
  结论: {T : 类型} (f : X _⦋0⦌ -> T)
  证明: rfl
-/
lemma lift_mk {T : Type*} (f : X _⦋0⦌ -> T)
    (hf : forall ⦃x₀ x₁ : X _⦋0⦌⦄ (_ : X.Edge x₀ x₁), f x₀ = f x₁) (x : X _⦋0⦌) :
    lift f hf (.mk x) = f x :=
  rfl

end π₀

/--
Definition of `mapπ₀` / `mapπ₀` 的定义

English:
definition mapπ₀
  signature: (f : X ⟶ Y)
  body: π₀.lift (π₀.mk ∘ f.app _) (fun _ _ e => π₀.sound (e.map f))

@[simp]

中文:
定义 mapπ₀
  签名: (f : X ⟶ Y)
  定义体: π₀.lift (π₀.mk ∘ f.app _) (fun _ _ e => π₀.sound (e.map f))

@[simp]

Depends on / 依赖: e.map, f.app
-/
def mapπ₀ (f : X ⟶ Y) : π₀ X -> π₀ Y :=
  π₀.lift (π₀.mk ∘ f.app _) (fun _ _ e => π₀.sound (e.map f))

@[simp]
/--
lemma `mapπ₀_mk` / 引理 `mapπ₀_mk`

English:
lemma mapπ₀_mk
  given: (f : X ⟶ Y) (x₀ : X _⦋0⦌)
  proof: rfl

@[simp]

中文:
引理 mapπ₀_mk
  条件: (f : X ⟶ Y) (x₀ : X _⦋0⦌)
  证明: rfl

@[simp]
-/
lemma mapπ₀_mk (f : X ⟶ Y) (x₀ : X _⦋0⦌) :
    mapπ₀ f (π₀.mk x₀) = π₀.mk (f.app _ x₀) :=
  rfl

@[simp]
/--
lemma `mapπ₀_id_apply` / 引理 `mapπ₀_id_apply`

English:
lemma mapπ₀_id_apply
  given: (x : π₀ X)
  statement: mapπ₀ (𝟙 X) x = x
  proof: by
  induction x
  simp

@[simp]

中文:
引理 mapπ₀_id_apply
  条件: (x : π₀ X)
  结论: mapπ₀ (𝟙 X) x = x
  证明: by
  induction x
  simp

@[simp]
-/
lemma mapπ₀_id_apply (x : π₀ X) : mapπ₀ (𝟙 X) x = x := by
  induction x
  simp

@[simp]
/--
lemma `mapπ₀_comp_apply` / 引理 `mapπ₀_comp_apply`

English:
lemma mapπ₀_comp_apply
  given: (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X)
  proof: by
  induction x
  simp

中文:
引理 mapπ₀_comp_apply
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X)
  证明: by
  induction x
  simp
-/
lemma mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X) :
    mapπ₀ (f ≫ g) x = mapπ₀ g (mapπ₀ f x) := by
  induction x
  simp

/-- The functor which sends a simplicial set to the type of its connected components. -/
@[simps]
/--
Definition of `π₀Functor` / `π₀Functor` 的定义

English:
definition π₀Functor
  signature: : SSet.{u} ⥤ Type u where
  body: π₀ X
  map f := ↾(mapπ₀ f)

中文:
定义 π₀Functor
  签名: : SSet.{u} ⥤ 类型u where
  定义体: π₀ X
  map f := ↾(mapπ₀ f)
-/
def π₀Functor : SSet.{u} ⥤ Type u where
  obj X := π₀ X
  map f := ↾(mapπ₀ f)

/--
Definition of `toπ₀NatTrans` / `toπ₀NatTrans` 的定义

English:
definition toπ₀NatTrans
  signature: : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor.{u} where
  body: ↾π₀.mk

中文:
定义 toπ₀自然数Trans
  签名: : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor.{u} where
  定义体: ↾π₀.mk
-/
def toπ₀NatTrans : SSet.evaluation.obj (op ⦋0⦌) ⟶ π₀Functor.{u} where
  app X := ↾π₀.mk

/--
Definition of `coforkπ₀` / `coforkπ₀` 的定义

English:
abbreviation coforkπ₀
  signature: : Cofork (X.δ (1 : Fin 2)) (X.δ 0)
  body: Cofork.ofπ (↾π₀.mk) (by ext s; exact π₀.sound (Edge.mk' s))

中文:
缩写 coforkπ₀
  签名: : 余叉 (X.δ (1 : 有限集 2)) (X.δ 0)
  定义体: Cofork.ofπ (↾π₀.mk) (by ext s; exact π₀.sound (Edge.mk' s))

Depends on / 依赖: Cofork, Cofork.of, Edge.mk
-/
abbrev coforkπ₀ : Cofork (X.δ (1 : Fin 2)) (X.δ 0) :=
  Cofork.ofπ (↾π₀.mk) (by ext s; exact π₀.sound (Edge.mk' s))

/--
Definition of `isColimitCoforkπ₀` / `isColimitCoforkπ₀` 的定义

English:
definition isColimitCoforkπ₀
  signature: : IsColimit X.coforkπ₀
  body: Cofork.IsColimit.mk _
    (fun s => ↾π₀.lift s.π (fun x₀ x₁ e => by
      simpa only [← e.src_eq, ← e.tgt_eq] using!
        ConcreteCategory.congr_hom s.condition e.edge))
    (fun s => rfl)
    (fun s m hm => by
      ext (x : π₀ X)
      induction x
      exact ConcreteCategory.congr_hom hm _)

中文:
定义 isColimitCoforkπ₀
  签名: : 是余极限 X.coforkπ₀
  定义体: Cofork.IsColimit.mk _
    (fun s => ↾π₀.lift s.π (fun x₀ x₁ e => by
      simpa only [← e.src_eq, ← e.tgt_eq] using!
        ConcreteCategory.congr_hom s.condition e.edge))
    (fun s => rfl)
    (fun s m hm => by
      ext (x : π₀ X)
      induction x
      exact ConcreteCategory.congr_hom hm _)

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, ConcreteCategory, ConcreteCategory.congr_hom, IsColimit, condition, congr_hom, e.edge, e.src_eq, e.tgt_eq, s.condition, src_eq, tgt_eq
-/
def isColimitCoforkπ₀ : IsColimit X.coforkπ₀ :=
  Cofork.IsColimit.mk _
    (fun s => ↾π₀.lift s.π (fun x₀ x₁ e => by
      simpa only [← e.src_eq, ← e.tgt_eq] using!
        ConcreteCategory.congr_hom s.condition e.edge))
    (fun s => rfl)
    (fun s m hm => by
      ext (x : π₀ X)
      induction x
      exact ConcreteCategory.congr_hom hm _)

/--
Definition of `coforkπ₀Functor` / `coforkπ₀Functor` 的定义

English:
abbreviation coforkπ₀Functor
  signature: :
  body: Cofork.ofπ toπ₀NatTrans (by ext X s; exact π₀.sound (Edge.mk' s))

中文:
缩写 coforkπ₀Functor
  签名: :
  定义体: Cofork.ofπ toπ₀NatTrans (by ext X s; exact π₀.sound (Edge.mk' s))

Depends on / 依赖: Cofork, Cofork.of, Edge.mk
-/
abbrev coforkπ₀Functor :
    Cofork (SSet.evaluation.{u}.map (SimplexCategory.δ (1 : Fin 2)).op)
      (SSet.evaluation.map (SimplexCategory.δ (0 : Fin 2)).op) :=
  Cofork.ofπ toπ₀NatTrans (by ext X s; exact π₀.sound (Edge.mk' s))

/--
Definition of `isColimitCoforkπ₀Functor` / `isColimitCoforkπ₀Functor` 的定义

English:
definition isColimitCoforkπ₀Functor
  signature: : IsColimit coforkπ₀Functor.{u}
  body: evaluationJointlyReflectsColimits _ (fun X =>
    (isColimitMapCoconeCoforkEquiv _ _).2 X.isColimitCoforkπ₀)

中文:
定义 isColimitCoforkπ₀Functor
  签名: : 是余极限 coforkπ₀Functor.{u}
  定义体: evaluationJointlyReflectsColimits _ (fun X =>
    (isColimitMapCoconeCoforkEquiv _ _).2 X.isColimitCoforkπ₀)

Depends on / 依赖: X.isColimitCofork, evaluationJointlyReflectsColimits, isColimitMapCoconeCoforkEquiv
-/
def isColimitCoforkπ₀Functor : IsColimit coforkπ₀Functor.{u} :=
  evaluationJointlyReflectsColimits _ (fun X =>
    (isColimitMapCoconeCoforkEquiv _ _).2 X.isColimitCoforkπ₀)

variable (X)

@[simp]
/--
lemma `π₀.nonempty_iff` / 引理 `π₀.nonempty_iff`

English:
lemma π₀.nonempty_iff
  statement: Nonempty (π₀ X) ↔ X.Nonempty
  proof: ⟨fun _ => ⟨(π₀.mk_surjective (Classical.arbitrary (π₀ X))).choose⟩,
    fun _ => ⟨.mk (Classical.arbitrary _)⟩⟩

中文:
引理 π₀.nonempty_iff
  结论: 非空 (π₀ X) ↔ X.非空
  证明: ⟨fun _ => ⟨(π₀.mk_surjective (Classical.arbitrary (π₀ X))).choose⟩,
    fun _ => ⟨.mk (Classical.arbitrary _)⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, mk_surjective
-/
lemma π₀.nonempty_iff : Nonempty (π₀ X) ↔ X.Nonempty :=
  ⟨fun _ => ⟨(π₀.mk_surjective (Classical.arbitrary (π₀ X))).choose⟩,
    fun _ => ⟨.mk (Classical.arbitrary _)⟩⟩

/--
Definition of `IsPreconnected` / `IsPreconnected` 的定义

English:
abbreviation IsPreconnected
  signature: : Prop
  body: Subsingleton (π₀ X)

中文:
缩写 是预连通
  签名: : 命题
  定义体: Subsingleton (π₀ X)
-/
protected abbrev IsPreconnected : Prop := Subsingleton (π₀ X)

/--
Definition of `IsConnected` / `IsConnected` 的定义

English:
class IsConnected
  parameters: : Prop extends SSet.IsPreconnected X where
  extends: SSet.IsPreconnected X
  axioms and operations (1):
    - nonempty : X.Nonempty  [default: by infer_instance]

中文:
类 是连通
  参数: : 命题 extends SSet.是预连通 X where
  继承: SSet.是预连通 X
  公理与运算 (1 个):
    - nonempty : X.非空  [默认: by infer_instance]
-/
protected class IsConnected : Prop extends SSet.IsPreconnected X where
  nonempty : X.Nonempty := by infer_instance

attribute [instance] IsConnected.nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.IsConnected]
  signature: : Nonempty (π₀ X)
  body: ⟨π₀.mk (Classical.arbitrary _)⟩

中文:
实例 [X.是连通]
  签名: : 非空 (π₀ X)
  定义体: ⟨π₀.mk (Classical.arbitrary _)⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
instance [X.IsConnected] : Nonempty (π₀ X) := ⟨π₀.mk (Classical.arbitrary _)⟩

/--
lemma `isConnected_iff` / 引理 `isConnected_iff`

English:
lemma isConnected_iff
  proof: ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨by assumption⟩⟩

中文:
引理 isConnected_iff
  证明: ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨by assumption⟩⟩
-/
lemma isConnected_iff :
    X.IsConnected ↔ X.IsPreconnected ∧ X.Nonempty :=
  ⟨fun h => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨by assumption⟩⟩

/--
lemma `isConnected_iff_nonempty_unique` / 引理 `isConnected_iff_nonempty_unique`

English:
lemma isConnected_iff_nonempty_unique
  proof: by
  rw [isConnected_iff]; rw [unique_iff_subsingleton_and_nonempty]; rw [π₀.nonempty_iff]

中文:
引理 isConnected_iff_nonempty_unique
  证明: by
  rw [isConnected_iff]; rw [unique_iff_subsingleton_and_nonempty]; rw [π₀.nonempty_iff]

Depends on / 依赖: isConnected_iff, nonempty_iff, unique_iff_subsingleton_and_nonempty
-/
lemma isConnected_iff_nonempty_unique :
    X.IsConnected ↔ Nonempty (Unique (π₀ X)) := by
  rw [isConnected_iff]; rw [unique_iff_subsingleton_and_nonempty]; rw [π₀.nonempty_iff]

end SSet
