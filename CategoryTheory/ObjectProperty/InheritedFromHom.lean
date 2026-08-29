/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Object properties transported along morphisms

In this file we define the predicates `InheritedFromSource` and `InheritedFromTarget`
for an object property `P` along a morphism property `Q`.
`P` is inherited from the source (resp. target) along `Q` if for every morphism
`f : X ⟶ Y` with `Q f`, `P X` implies `P Y` (resp. `P Y` implies `P X`).
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace ObjectProperty

variable (P P' : ObjectProperty C) (Q Q' : MorphismProperty C)

/--
Definition of `InheritedFromSource` / `InheritedFromSource` 的定义

English:
class InheritedFromSource
  parameters: (P : ObjectProperty C) (Q : MorphismProperty C)
  axioms and operations (1):
    - of_hom_of_source({X Y : C} (f : X ⟶ Y) (hf : Q f)) : P X -> P Y

中文:
类 InheritedFromSource
  参数: (P : ObjectProperty C) (Q : MorphismProperty C)
  公理与运算 (1 个):
    - of_hom_of_source({X Y : C} (f : X ⟶ Y) (hf : Q f)) : P X -> P Y
-/
class InheritedFromSource (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_source {X Y : C} (f : X ⟶ Y) (hf : Q f) : P X -> P Y

/--
Definition of `InheritedFromTarget` / `InheritedFromTarget` 的定义

English:
class InheritedFromTarget
  parameters: (P : ObjectProperty C) (Q : MorphismProperty C)
  axioms and operations (1):
    - of_hom_of_target({X Y : C} (f : X ⟶ Y) (hf : Q f)) : P Y -> P X

中文:
类 InheritedFromTarget
  参数: (P : ObjectProperty C) (Q : MorphismProperty C)
  公理与运算 (1 个):
    - of_hom_of_target({X Y : C} (f : X ⟶ Y) (hf : Q f)) : P Y -> P X
-/
class InheritedFromTarget (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_target {X Y : C} (f : X ⟶ Y) (hf : Q f) : P Y -> P X

export InheritedFromSource (of_hom_of_source)
export InheritedFromTarget (of_hom_of_target)

namespace InheritedFromSource

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: :
  body: P.prop_of_iso (asIso f) h

中文:
实例 [P.在同构下封闭]
  签名: :
  定义体: P.prop_of_iso (asIso f) h

Depends on / 依赖: P.prop_of_iso, prop_of_iso
-/
instance [P.IsClosedUnderIsomorphisms] :
    P.InheritedFromSource (MorphismProperty.isomorphisms C) where
  of_hom_of_source f (_ : IsIso f) h := P.prop_of_iso (asIso f) h

/--
Instance `op` / 实例 `op`

English:
instance op
  signature: [P.InheritedFromSource Q]
  body: P.of_hom_of_source f.unop hf h

中文:
实例 op
  签名: [P.InheritedFromSource Q]
  定义体: P.of_hom_of_source f.unop hf h

Depends on / 依赖: P.of_hom_of_source, f.unop, of_hom_of_source
-/
instance op [P.InheritedFromSource Q] : P.op.InheritedFromTarget Q.op where
  of_hom_of_target f hf h := P.of_hom_of_source f.unop hf h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.InheritedFromSource
  signature: Q] [P'.InheritedFromSource Q] :
  body: ⟨P.of_hom_of_source f hf h.1, P'.of_hom_of_source f hf h.2⟩

中文:
实例 [P.InheritedFromSource
  签名: Q] [P'.InheritedFromSource Q] :
  定义体: ⟨P.of_hom_of_source f hf h.1, P'.of_hom_of_source f hf h.2⟩

Depends on / 依赖: P.of_hom_of_source, of_hom_of_source
-/
instance [P.InheritedFromSource Q] [P'.InheritedFromSource Q] :
    (P ⊓ P').InheritedFromSource Q where
  of_hom_of_source f hf h := ⟨P.of_hom_of_source f hf h.1, P'.of_hom_of_source f hf h.2⟩

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: (hQ : Q <= Q') [P.InheritedFromSource Q']
  statement: P.InheritedFromSource Q where
  proof: P.of_hom_of_source f (hQ _ hf) h

中文:
引理 of_le
  条件: (hQ : Q <= Q') [P.InheritedFromSource Q']
  结论: P.InheritedFromSource Q where
  证明: P.of_hom_of_source f (hQ _ hf) h

Depends on / 依赖: P.of_hom_of_source, of_hom_of_source
-/
lemma of_le (hQ : Q <= Q') [P.InheritedFromSource Q'] : P.InheritedFromSource Q where
  of_hom_of_source f hf h := P.of_hom_of_source f (hQ _ hf) h

end InheritedFromSource

namespace InheritedFromTarget

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: :
  body: P.prop_of_iso (asIso f).symm h

中文:
实例 [P.在同构下封闭]
  签名: :
  定义体: P.prop_of_iso (asIso f).symm h

Depends on / 依赖: P.prop_of_iso, prop_of_iso
-/
instance [P.IsClosedUnderIsomorphisms] :
    P.InheritedFromTarget (MorphismProperty.isomorphisms C) where
  of_hom_of_target f (_ : IsIso f) h := P.prop_of_iso (asIso f).symm h

/--
Instance `op` / 实例 `op`

English:
instance op
  signature: [P.InheritedFromTarget Q]
  body: P.of_hom_of_target f.unop hf h

中文:
实例 op
  签名: [P.InheritedFromTarget Q]
  定义体: P.of_hom_of_target f.unop hf h

Depends on / 依赖: P.of_hom_of_target, f.unop, of_hom_of_target
-/
instance op [P.InheritedFromTarget Q] : P.op.InheritedFromSource Q.op where
  of_hom_of_source f hf h := P.of_hom_of_target f.unop hf h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.InheritedFromTarget
  signature: Q] [P'.InheritedFromTarget Q] :
  body: ⟨P.of_hom_of_target f hf h.1, P'.of_hom_of_target f hf h.2⟩

中文:
实例 [P.InheritedFromTarget
  签名: Q] [P'.InheritedFromTarget Q] :
  定义体: ⟨P.of_hom_of_target f hf h.1, P'.of_hom_of_target f hf h.2⟩

Depends on / 依赖: P.of_hom_of_target, of_hom_of_target
-/
instance [P.InheritedFromTarget Q] [P'.InheritedFromTarget Q] :
    (P ⊓ P').InheritedFromTarget Q where
  of_hom_of_target f hf h := ⟨P.of_hom_of_target f hf h.1, P'.of_hom_of_target f hf h.2⟩

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: (hQ : Q <= Q') [P.InheritedFromTarget Q']
  statement: P.InheritedFromTarget Q where
  proof: P.of_hom_of_target f (hQ _ hf) h

中文:
引理 of_le
  条件: (hQ : Q <= Q') [P.InheritedFromTarget Q']
  结论: P.InheritedFromTarget Q where
  证明: P.of_hom_of_target f (hQ _ hf) h

Depends on / 依赖: P.of_hom_of_target, of_hom_of_target
-/
lemma of_le (hQ : Q <= Q') [P.InheritedFromTarget Q'] : P.InheritedFromTarget Q where
  of_hom_of_target f hf h := P.of_hom_of_target f (hQ _ hf) h

end InheritedFromTarget

/--
lemma `IsClosedUnderIsomorphisms.of_inheritedFromSource` / 引理 `IsClosedUnderIsomorphisms.of_inheritedFromSource`

English:
lemma IsClosedUnderIsomorphisms.of_inheritedFromSource
  statement: [P.InheritedFromSource Q] [Q.RespectsIso]
  proof: P.of_hom_of_source e.hom (Q.of_isIso e.hom) h

中文:
引理 在同构下封闭.of_inheritedFromSource
  结论: [P.InheritedFromSource Q] [Q.RespectsIso]
  证明: P.of_hom_of_source e.hom (Q.of_isIso e.hom) h

Depends on / 依赖: P.of_hom_of_source, Q.of_isIso, e.hom, of_hom_of_source, of_isIso
-/
lemma IsClosedUnderIsomorphisms.of_inheritedFromSource [P.InheritedFromSource Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_source e.hom (Q.of_isIso e.hom) h

/--
lemma `IsClosedUnderIsomorphisms.of_inheritedFromTarget` / 引理 `IsClosedUnderIsomorphisms.of_inheritedFromTarget`

English:
lemma IsClosedUnderIsomorphisms.of_inheritedFromTarget
  statement: [P.InheritedFromTarget Q] [Q.RespectsIso]
  proof: P.of_hom_of_target e.inv (Q.of_isIso e.inv) h

中文:
引理 在同构下封闭.of_inheritedFromTarget
  结论: [P.InheritedFromTarget Q] [Q.RespectsIso]
  证明: P.of_hom_of_target e.inv (Q.of_isIso e.inv) h

Depends on / 依赖: P.of_hom_of_target, Q.of_isIso, e.inv, of_hom_of_target, of_isIso
-/
lemma IsClosedUnderIsomorphisms.of_inheritedFromTarget [P.InheritedFromTarget Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_target e.inv (Q.of_isIso e.inv) h

end ObjectProperty

end CategoryTheory
