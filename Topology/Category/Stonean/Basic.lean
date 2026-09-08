/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.Topology.Category.CompHaus.Projective
public import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected compact Hausdorff spaces.

## Overview

This file defines the type `Stonean` of all extremally (note: not "extremely"!)
disconnected compact Hausdorff spaces, gives it the structure of a large category,
and proves some basic observations about this category and various functors from it.

The Lean implementation: a term of type `Stonean` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

## Main definitions

* `Stonean` : the category of extremally disconnected compact Hausdorff spaces.
* `Stonean.toCompHaus` : the forgetful functor `Stonean ⥤ CompHaus` from Stonean
  spaces to compact Hausdorff spaces
* `Stonean.toProfinite` : the functor from Stonean spaces to profinite spaces.

## Implementation

The category `Stonean` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

@[expose] public section
universe u

open CategoryTheory
open scoped Topology

/-- `Stonean` is the category of extremally disconnected compact Hausdorff spaces. -/
/-
**Stonean** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Stonean
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Stonean` is the category of extremally disconnected compact Hausdorff spaces.
-/
abbrev Stonean := CompHausLike (fun X ↦ ExtremallyDisconnected X)

namespace CompHaus

/-- `Projective` implies `ExtremallyDisconnected`. -/
/-
**CompHaus.** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Projective` implies `ExtremallyDisconnected`.
-/
instance (X : CompHaus.{u}) [Projective X] : ExtremallyDisconnected X := by
  apply CompactT2.Projective.extremallyDisconnected
  intro A B _ _ _ _ _ _ f g hf hg hsurj
  let A' : CompHaus := CompHaus.of A
  let B' : CompHaus := CompHaus.of B
  let f' : X ⟶ B' := CompHausLike.ofHom _ ⟨f, hf⟩
  let g' : A' ⟶ B' := CompHausLike.ofHom _ ⟨g,hg⟩
  have : Epi g' := by
    rw [CompHaus.epi_iff_surjective]
    assumption
  obtain ⟨h, hh⟩ := Projective.factors f' g'
  refine ⟨h, h.hom.hom.2, ?_⟩
  ext t
  apply_fun (fun e => e t) at hh
  exact hh

/-- `Projective` implies `Stonean`. -/
@[simps!]
/-
**CompHaus.toStonean** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
形式化陈述：toStonean (X : CompHaus.{u}) [Projective X] : Stonean where toTop
参数：X : CompHaus.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop

--- 原说明 ---
`Projective` implies `Stonean`.
-/
def toStonean (X : CompHaus.{u}) [Projective X] :
    Stonean where
  toTop := X.toTop
  prop := inferInstance

end CompHaus

namespace Stonean

/-- The (forgetful) functor from Stonean spaces to compact Hausdorff spaces. -/
/-
**Stonean.toCompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 `Stonean`。
形式化陈述：toCompHaus : Stonean.{u} ⥤ CompHaus.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (forgetful) functor from Stonean spaces to compact Hausdorff spaces.
-/
abbrev toCompHaus : Stonean.{u} ⥤ CompHaus.{u} :=
  compHausLikeToCompHaus _

/-- The forgetful functor `Stonean ⥤ CompHaus` is fully faithful. -/
/-
**Stonean.fullyFaithfulToCompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 `Stonean`。
形式化陈述：fullyFaithfulToCompHaus : toCompHaus.FullyFaithful
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor `Stonean ⥤ CompHaus` is fully faithful.
-/
abbrev fullyFaithfulToCompHaus : toCompHaus.FullyFaithful :=
  CompHausLike.fullyFaithfulToCompHausLike _

open CompHausLike
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [TopologicalSpace X]
    [ExtremallyDisconnected X] : HasProp (fun Y ↦ ExtremallyDisconnected Y) X :=
  ⟨(inferInstance : ExtremallyDisconnected X)⟩

/-- Construct a term of `Stonean` from a type endowed with the structure of a
compact, Hausdorff and extremally disconnected topological space.
-/
/-
**Stonean.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Stonean`。
形式化陈述：of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Extremal
lyDisconnected X] : Stonean
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Stonean.instHasPropExtremallyDisconnectedCarrier`：∀ (X : Type u_1) [inst
 : TopologicalSpace X] [ExtremallyDisconnected X],   CompHausLike.HasProp (fun Y
 => ExtremallyDisconnected ↑Y) X

--- 原说明 ---
Construct a term of `Stonean` from a type endowed with the structure of a
compact, Hausdorff and extremally disconnected topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : Stonean := CompHausLike.of _ X
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Stonean.{u}) : ExtremallyDisconnected X := X.prop

/-- The functor from Stonean spaces to profinite spaces. -/
/-
**Stonean.toProfinite** 是 Mathlib 中的一个缩写定义，位于命名空间 `Stonean`。
形式化陈述：toProfinite : Stonean.{u} ⥤ Profinite.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from Stonean spaces to profinite spaces.
-/
abbrev toProfinite : Stonean.{u} ⥤ Profinite.{u} :=
  CompHausLike.toCompHausLike (fun _ ↦ inferInstance)

/--
A finite discrete space as a Stonean space.
-/
/-
**Stonean.mkFinite** 是 Mathlib 中的一个定义，位于命名空间 `Stonean`。
形式化陈述：mkFinite (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X] 
: Stonean where toTop
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X

--- 原说明 ---
A finite discrete space as a Stonean space.
-/
def mkFinite (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X] : Stonean where
  toTop := (CompHaus.of X).toTop
  prop := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)

set_option backward.isDefEq.respectTransparency false in
/--
A morphism in `Stonean` is an epi iff it is surjective.
-/
/-
**Stonean.epi_iff_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Stonean`。
形式化陈述：epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) : Epi f ↔ Function.Surjecti
ve f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsClosed.compl_mem_nhds`：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx :
 x ∉ s) : sᶜ in 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `isTopologicalBasis_isClopen`：isTopologicalBasis_isClopen : IsTopological
Basis { s : Set X | IsClopen s }
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `instTotallySeparatedSpaceOfExtremallyDisconnectedOfT2Space`：∀ (X : Type 
u) [inst : TopologicalSpace X] [ExtremallyDisconnected X] [T2Space X], TotallySe
paratedSpace X
· 使用定理 `Stonean.instExtremallyDisconnectedCarrierToTop`：∀ (X : Stonean), Extrema
llyDisconnected ↑X.toTop
· 使用定理 `instFiniteULift`：∀ {α : Type v} [Finite α], Finite (ULift.{u, v} α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instDiscreteTopologyULift`：∀ {X : Type u} [inst : TopologicalSpace X] [D
iscreteTopology X], DiscreteTopology (ULift.{u_5, u} X)
· 使用定理 `instDiscreteTopologyFin`：∀ {n : ℕ}, DiscreteTopology (Fin n)
· 使用定理 `LocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : LocallyConstant X Y),   Conti
nuous ⇑f
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
A morphism in `Stonean` is an epi iff it is surjective.
-/
lemma epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  refine ⟨?_, fun h => ConcreteCategory.epi_of_surjective f h⟩
  dsimp [Function.Surjective]
  intro h y
  by_contra! hy
  let C := Set.range f
  have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
  let U := Cᶜ
  have hUy : U ∈ 𝓝 y := by
    simp only [U, C, Set.mem_range, hy, exists_false, not_false_eq_true, hC.compl_mem_nhds]
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext -- why is `ext` not doing this automatically?
    change 1 = ite _ _ _ -- why is `dsimp` not getting me here?
    rw [if_neg]
    refine mt (hVU ·) ?_ -- what would be an idiomatic tactic for this step?
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using! exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H -- why is `dsimp at H` not getting me here?
  rw [if_pos hyV] at H
  exact one_ne_zero H

/-- Every Stonean space is projective in `CompHaus` -/
/-
**Stonean.instProjectiveCompHausCompHaus** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
形式化陈述：instProjectiveCompHausCompHaus (X : Stonean) : Projective (toCompHaus.obj 
X) where factors
参数：X : Stonean。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.prop`：∀ {P : TopCat → Prop} (self : CompHausLike P), P self
.toTop
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompHaus.epi_iff_surjective`：epi_iff_surjective {X Y : CompHaus.{u}} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CompactT2.ExtremallyDisconnected.projective`：∀ {A : Type u} [inst : Topo
logicalSpace A] [ExtremallyDisconnected A] [CompactSpace A] [T2Space A],   Compa
ctT2.Projective A
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHaus.instHasPropTrue`：∀ (X : Type u_1) [inst : TopologicalSpace X], 
CompHausLike.HasProp (fun x => True) X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Every Stonean space is projective in `CompHaus`
-/
instance instProjectiveCompHausCompHaus (X : Stonean) : Projective (toCompHaus.obj X) where
  factors := by
    intro B C φ f _
    have : ExtremallyDisconnected (toCompHaus.obj X).toTop := X.prop
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Profinite` -/
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Stonean space is projective in `Profinite`
-/
instance (X : Stonean) : Projective (toProfinite.obj X) where
  factors := by
    intro B C φ f _
    have : ExtremallyDisconnected (toProfinite.obj X) := X.prop
    have hf : Function.Surjective f := by rwa [← Profinite.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Stonean`. -/
/-
**Stonean.** 是 Mathlib 中的一个实例，位于命名空间 `Stonean`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Stonean space is projective in `Stonean`.
-/
instance (X : Stonean) : Projective X where
  factors := by
    intro B C φ f _
    have : ExtremallyDisconnected X.toTop := X.prop
    have hf : Function.Surjective f := by rwa [← Stonean.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is a Stonean space equipped with an epimorphism
  down to `X` (see `CompHaus.presentation.π` and `CompHaus.presentation.epi_π`). It is a
  "constructive" witness to the fact that `CompHaus` has enough projectives. -/
noncomputable
/-
**CompHaus.presentation** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
形式化陈述：presentation (X : CompHaus) : Stonean where toTop
参数：X : CompHaus。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def presentation (X : CompHaus) : Stonean where
  toTop := (projectivePresentation X).p.1
  prop := instExtremallyDisconnectedCarrierToTopTrueOfProjective X.projectivePresentation.p

/-- The morphism from `presentation X` to `X`. -/
noncomputable
/-
**CompHaus.presentation.** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def presentation.π (X : CompHaus) : Stonean.toCompHaus.obj X.presentation ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
/-
**CompHaus.presentation.epi_** 是 Mathlib 中的一个实例，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi

/-- The underlying `CompHaus` of a `Stonean`. -/
/-
**CompHaus._root_.Stonean.compHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHaus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying `CompHaus` of a `Stonean`.
-/
abbrev _root_.Stonean.compHaus (X : Stonean) := Stonean.toCompHaus.obj X

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `CompHaus` and `e : Z ⟶ Y` is arbitrary, then
`lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It exists because
`Z` is a projective object in `CompHaus`.
-/
noncomputable
/-
**CompHaus.lift** 是 Mathlib 中的一个定义，位于命名空间 `CompHaus`。
形式化陈述：lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi 
f] : Z.compHaus ⟶ X
参数：e : Z.compHaus ⟶ Y；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
/-
**CompHaus.lift_lifts** 是 Mathlib 中的一个引理，位于命名空间 `CompHaus`。
形式化陈述：lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y)
 [Epi f] : lift e f ≫ f = e
参数：e : Z.compHaus ⟶ Y；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]
/-
**CompHaus.Gleason** 是 Mathlib 中的一个引理，位于命名空间 `CompHaus`。
形式化陈述：Gleason (X : CompHaus.{u}) : Projective X ↔ ExtremallyDisconnected X
参数：X : CompHaus.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stonean.instExtremallyDisconnectedCarrierToTop`：∀ (X : Stonean), Extrema
llyDisconnected ↑X.toTop
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop
-/
lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    change ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X.toTop, inferInstance⟩
    change Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus

end CompHaus

namespace Profinite

/-- If `X` is profinite, `presentation X` is a Stonean space equipped with an epimorphism down to
`X` (see `Profinite.presentation.π` and `Profinite.presentation.epi_π`). -/
noncomputable
/-
**Profinite.presentation** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：presentation (X : Profinite) : Stonean where toTop
参数：X : Profinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def presentation (X : Profinite) : Stonean where
  toTop := (profiniteToCompHaus.obj X).projectivePresentation.p.toTop
  prop := (profiniteToCompHaus.obj X).presentation.prop

/-- The morphism from `presentation X` to `X`. -/
noncomputable
/-
**Profinite.presentation.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def presentation.π (X : Profinite) : Stonean.toProfinite.obj X.presentation ⟶ X :=
  InducedCategory.homMk (profiniteToCompHaus.obj X).projectivePresentation.f.hom

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
/-
**Profinite.presentation.epi_** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance presentation.epi_π (X : Profinite) : Epi (π X) := by
  have := (profiniteToCompHaus.obj X).projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `Profinite` and `e : Z ⟶ Y` is arbitrary,
then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It is
`CompHaus.lift e f` as a morphism in `Profinite`.
-/
noncomputable
/-
**Profinite.lift** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (
f : X ⟶ Y) [Epi f] : Stonean.toProfinite.obj Z ⟶ X
参数：e : Stonean.toProfinite.obj Z ⟶ Y；f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Stonean.instProjectiveProfiniteObjToProfinite`：∀ (X : Stonean), Category
Theory.Projective (Stonean.toProfinite.obj X)
-/
def lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Stonean.toProfinite.obj Z ⟶ X := Projective.factorThru e f

@[simp, reassoc]
/-
**Profinite.lift_lifts** 是 Mathlib 中的一个引理，位于命名空间 `Profinite`。
形式化陈述：lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z 
⟶ Y) (f : X ⟶ Y) [Epi f] : lift e f ≫ f = e
参数：e : Stonean.toProfinite.obj Z ⟶ Y；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.factorThru_comp`：factorThru_comp {P X E : C} [
Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : factorThru f e ≫ e = f
· 使用定理 `Stonean.instProjectiveProfiniteObjToProfinite`：∀ (X : Stonean), Category
Theory.Projective (Stonean.toProfinite.obj X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
    [Epi f] : lift e f ≫ f = e := by simp [lift]
/-
**Profinite.projective_of_extrDisc** 是 Mathlib 中的一个引理，位于命名空间 `Profinite`。
形式化陈述：projective_of_extrDisc {X : Profinite.{u}} (hX : ExtremallyDisconnected X)
 : Projective X
参数：hX : ExtremallyDisconnected X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `Stonean.instProjectiveProfiniteObjToProfinite`：∀ (X : Stonean), Category
Theory.Projective (Stonean.toProfinite.obj X)
-/
lemma projective_of_extrDisc {X : Profinite.{u}} (hX : ExtremallyDisconnected X) :
    Projective X := by
  change Projective (Stonean.toProfinite.obj ⟨X.toTop, inferInstance⟩)
  exact inferInstance

end Profinite

